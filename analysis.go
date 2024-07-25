package main

import (
	"context"
	"database/sql"
	"errors"
	"fmt"
	"github.com/go-git/go-git/v5/plumbing"
	"go/build"
	"go/parser"
	"go/token"
	"go/types"
	"hash/fnv"
	"io"
	"net/http"
	"os"
	"os/exec"
	"path/filepath"
	"regexp"
	"strconv"
	"strings"

	"github.com/go-git/go-git/v5"
	"github.com/google/go-github/v57/github"
	ghdiff "github.com/kmesiab/go-github-diff"
	"github.com/pingcap/log"
	"go.uber.org/zap"
	"golang.org/x/tools/go/callgraph"
	"golang.org/x/tools/go/callgraph/cha"
	"golang.org/x/tools/go/callgraph/rta"
	"golang.org/x/tools/go/callgraph/static"
	"golang.org/x/tools/go/packages"
	"golang.org/x/tools/go/pointer"
	"golang.org/x/tools/go/ssa"
	"golang.org/x/tools/go/ssa/ssautil"
)

type CallGraphType string

const (
	CallGraphTypeStatic  CallGraphType = "static"
	CallGraphTypeCha                   = "cha"
	CallGraphTypeRta                   = "rta"
	CallGraphTypePointer               = "pointer"
)

// ==[ type def/func: analysis   ]===============================================
type renderOpts struct {
	cacheDir         string
	focus            string
	group            []string
	ignore           []string
	include          []string
	limit            []string
	nointer          bool
	refresh          bool
	nostd            bool
	algo             CallGraphType
	modifyPackage    bool
	influencePackage bool
}

// mainPackages returns the main packages to analyze.
// Each resulting package is named "main" and has a main function.
func mainPackages(pkgs []*ssa.Package) ([]*ssa.Package, error) {
	var mains []*ssa.Package
	for _, p := range pkgs {
		if p != nil && p.Pkg.Name() == "main" && p.Func("main") != nil {
			mains = append(mains, p)
		}
	}
	if len(mains) == 0 {
		return nil, fmt.Errorf("no main packages")
	}
	return mains, nil
}

// ==[ type def/func: analysis   ]===============================================
type analysis struct {
	opts                  *renderOpts
	prog                  *ssa.Program
	pkgs                  []*ssa.Package
	mainPkg               *ssa.Package
	callgraph             *callgraph.Graph
	modifyPackages        map[packageInfo]modifyFunctions
	influenceFunctions    map[packageInfo]map[string]struct{}
	influencePackagesRoot *goListNode
	prURL                 string
	prCommit              string
	goList                map[packageInfo]map[string]struct{}
	funcInfo              map[functionInfo]map[functionInfo]struct{}
	sql                   string
	args                  []interface{}
}

type packageInfo struct {
	pkgName    string
	importPath string
}

type modifyFunctions struct {
	functions []string
}

var Analysis *analysis

func (a *analysis) DoAnalysis(
	algo CallGraphType,
	dir string,
	tests bool,
	args []string,
) error {
	cfg := &packages.Config{
		Mode:       packages.LoadAllSyntax,
		Tests:      tests,
		Dir:        dir,
		BuildFlags: getBuildFlags(),
	}

	initial, err := packages.Load(cfg, args...)
	if err != nil {
		return err
	}

	if packages.PrintErrors(initial) > 0 {
		return fmt.Errorf("packages contain errors")
	}

	// Create and build SSA-form program representation.
	prog, pkgs := ssautil.AllPackages(initial, 0)
	prog.Build()

	var graph *callgraph.Graph
	var mainPkg *ssa.Package

	switch algo {
	case CallGraphTypeStatic:
		graph = static.CallGraph(prog)
	case CallGraphTypeCha:
		graph = cha.CallGraph(prog)
	case CallGraphTypeRta:
		mains, err := mainPackages(prog.AllPackages())
		if err != nil {
			return err
		}
		var roots []*ssa.Function
		mainPkg = mains[0]
		for _, main := range mains {
			roots = append(roots, main.Func("main"))
		}
		graph = rta.Analyze(roots, true).CallGraph
	case CallGraphTypePointer:
		mains, err := mainPackages(prog.AllPackages())
		if err != nil {
			return err
		}
		mainPkg = mains[0]
		config := &pointer.Config{
			Mains:          mains,
			BuildCallGraph: true,
		}
		ptares, err := pointer.Analyze(config)
		if err != nil {
			return err
		}
		graph = ptares.CallGraph
	default:
		return fmt.Errorf("invalid call graph type: %s", a.opts.algo)
	}

	//cg.DeleteSyntheticNodes()

	a.prog = prog
	a.pkgs = pkgs
	a.mainPkg = mainPkg
	a.callgraph = graph
	return nil
}

func (a *analysis) OptsSetup() {
	a.opts = &renderOpts{
		cacheDir: *cacheDir,
		focus:    *focusFlag,
		group:    []string{*groupFlag},
		ignore:   []string{*ignoreFlag},
		include:  []string{*includeFlag},
		limit:    []string{*limitFlag},
		nointer:  *nointerFlag,
		nostd:    *nostdFlag,
	}
}

func (a *analysis) ProcessListArgs() (e error) {
	var groupBy []string
	var ignorePaths []string
	var includePaths []string
	var limitPaths []string

	for _, g := range strings.Split(a.opts.group[0], ",") {
		g := strings.TrimSpace(g)
		if g == "" {
			continue
		}
		if g != "pkg" && g != "type" {
			e = errors.New("invalid group option")
			return
		}
		groupBy = append(groupBy, g)
	}

	for _, p := range strings.Split(a.opts.ignore[0], ",") {
		p = strings.TrimSpace(p)
		if p != "" {
			ignorePaths = append(ignorePaths, p)
		}
	}

	for _, p := range strings.Split(a.opts.include[0], ",") {
		p = strings.TrimSpace(p)
		if p != "" {
			includePaths = append(includePaths, p)
		}
	}

	for _, p := range strings.Split(a.opts.limit[0], ",") {
		p = strings.TrimSpace(p)
		if p != "" {
			limitPaths = append(limitPaths, p)
		}
	}

	a.opts.group = groupBy
	a.opts.ignore = ignorePaths
	a.opts.include = includePaths
	a.opts.limit = limitPaths

	return
}

func getDB() (*sql.DB, error) {
	dsnTmp := "%s:%s@tcp(%s:%s)/%s"
	db, err := sql.Open("mysql", fmt.Sprintf(dsnTmp,
		os.Getenv("user"), os.Getenv("password"), os.Getenv("host"), os.Getenv("port"), os.Getenv("dbname")))
	return db, err
}

func DbExecuteWithoutLog(ctx context.Context, query string, args ...interface{}) (int64, error) {
	db, err := getDB()
	if err != nil {
		return 0, err
	}
	defer db.Close()
	_, err = db.ExecContext(ctx, "set @@time_zone = 'UTC';")
	if err != nil && !errors.Is(err, context.Canceled) {
		return 0, err
	}
	ret, err := db.ExecContext(ctx, query, args...)
	if err != nil {
		if errors.Is(err, context.Canceled) {
			return 0, nil
		} else {
			return 0, err
		}
	}
	if strings.HasPrefix(query, "insert") {
		return ret.LastInsertId()
	} else {
		return 0, err
	}
}

func commitAnalyzeDone(branch, commit string) (bool, error) {
	db, err := getDB()
	if err != nil {
		return false, err
	}
	defer db.Close()
	_, err = db.Exec("set @@time_zone = 'UTC';")
	if err != nil {
		return false, err
	}
	row, err := db.Query(fmt.Sprintf("select id from done_pr where branch = \"%s\" and pr_commit = \"%s\"", branch, commit))

	if err != nil {
		return false, err
	}
	if row.Next() {
		return true, nil
	} else {
		return false, nil
	}
}

func (a *analysis) OverrideByHTTP(r *http.Request) {
	if f := r.FormValue("f"); f == "all" {
		a.opts.focus = ""
	} else if f != "" {
		a.opts.focus = f
	}
	if std := r.FormValue("std"); std != "" {
		a.opts.nostd = false
	}
	if inter := r.FormValue("nointer"); inter != "" {
		a.opts.nointer = true
	}
	if refresh := r.FormValue("refresh"); refresh != "" {
		a.opts.refresh = true
	}
	if g := r.FormValue("group"); g != "" {
		a.opts.group[0] = g
	}
	if l := r.FormValue("limit"); l != "" {
		a.opts.limit[0] = l
	}
	if ign := r.FormValue("ignore"); ign != "" {
		a.opts.ignore[0] = ign
	}
	if inc := r.FormValue("include"); inc != "" {
		a.opts.include[0] = inc
	}
	return
}

// basically do printOutput() with previously checking
// focus option and respective package
func (a *analysis) Render() ([]byte, error) {
	var (
		err      error
		ssaPkg   *ssa.Package
		focusPkg *types.Package
	)

	if a.opts.focus != "" {
		if ssaPkg = a.prog.ImportedPackage(a.opts.focus); ssaPkg == nil {
			if strings.Contains(a.opts.focus, "/") {
				return nil, fmt.Errorf("focus failed: %v", err)
			}
			// try to find package by pkgName
			var foundPaths []string
			for _, p := range a.pkgs {
				if p.Pkg.Name() == a.opts.focus {
					foundPaths = append(foundPaths, p.Pkg.Path())
				}
			}
			if len(foundPaths) == 0 {
				return nil, fmt.Errorf("focus failed, could not find package: %v", a.opts.focus)
			} else if len(foundPaths) > 1 {
				for _, p := range foundPaths {
					fmt.Fprintf(os.Stderr, " - %s\n", p)
				}
				return nil, fmt.Errorf("focus failed, found multiple packages with pkgName: %v", a.opts.focus)
			}
			// found single package
			if ssaPkg = a.prog.ImportedPackage(foundPaths[0]); ssaPkg == nil {
				return nil, fmt.Errorf("focus failed: %v", err)
			}
		}
		focusPkg = ssaPkg.Pkg
		logf("focusing: %v", focusPkg.Path())
	}

	dot, err := printOutput(
		a.prog,
		a.mainPkg,
		a.callgraph,
		focusPkg,
		a.opts.limit,
		a.opts.ignore,
		a.opts.include,
		a.opts.group,
		a.opts.nostd,
		a.opts.nointer,
	)
	if err != nil {
		return nil, fmt.Errorf("processing failed: %v", err)
	}

	return dot, nil
}

func (a *analysis) FindCachedImg() string {
	if a.opts.cacheDir == "" || a.opts.refresh {
		return ""
	}

	focus := a.opts.focus
	if focus == "" {
		focus = "all"
	}
	focusFilePath := focus + "." + *outputFormat
	absFilePath := filepath.Join(a.opts.cacheDir, focusFilePath)

	if exists, err := pathExists(absFilePath); err != nil || !exists {
		logf("not cached img: %v", absFilePath)
		return ""
	}

	logf("hit cached img")
	return absFilePath
}

func (a *analysis) CacheImg(img string) error {
	if a.opts.cacheDir == "" || img == "" {
		return nil
	}

	focus := a.opts.focus
	if focus == "" {
		focus = "all"
	}
	absCacheDirPrefix := filepath.Join(a.opts.cacheDir, focus)
	absCacheDirPath := strings.TrimRightFunc(absCacheDirPrefix, func(r rune) bool {
		return r != '\\' && r != '/'
	})
	err := os.MkdirAll(absCacheDirPath, os.ModePerm)
	if err != nil {
		return err
	}

	absFilePath := absCacheDirPrefix + "." + *outputFormat
	_, err = copyFile(img, absFilePath)
	if err != nil {
		return err
	}

	return nil
}

func pathExists(path string) (bool, error) {
	_, err := os.Stat(path)
	if err == nil {
		return true, nil
	}
	if os.IsNotExist(err) {
		return false, nil
	}
	return false, err
}

func copyFile(src, dst string) (int64, error) {
	sourceFileStat, err := os.Stat(src)

	if err != nil {
		return 0, err
	}

	if !sourceFileStat.Mode().IsRegular() {
		return 0, fmt.Errorf("%s is not a regular file", src)
	}

	source, err := os.Open(src)
	if err != nil {
		return 0, err
	}
	defer source.Close()

	destination, err := os.Create(dst)
	if err != nil {
		return 0, err
	}
	defer destination.Close()
	nBytes, err := io.Copy(destination, source)
	return nBytes, err
}

func getBuildFlags() []string {
	buildFlagTags := getBuildFlagTags(build.Default.BuildTags)
	if len(buildFlagTags) == 0 {
		return nil
	}

	return []string{buildFlagTags}
}

func getBuildFlagTags(buildTags []string) string {
	if len(buildTags) > 0 {
		return "-tags=" + strings.Join(buildTags, ",")
	}

	return ""
}
func hash(s string) string {
	h := fnv.New32a()
	h.Write([]byte(s))
	return strconv.FormatUint(uint64(h.Sum32()), 10)
}

func (a *analysis) checkout(branch, commit string) error {
	r, err := git.PlainOpenWithOptions(".", &git.PlainOpenOptions{DetectDotGit: true})
	if err != nil {
		return err
	}

	logf("git show-ref --head HEAD")
	ref, err := r.Head()
	if err != nil {
		return err
	}
	logf("git head ref %v", ref.Hash())
	remote, err := r.Remote("origin")
	if err == git.ErrRemoteNotFound {
		log.Warn("get origin remote failure")
		return err
	}
	if err = remote.Fetch(&git.FetchOptions{}); err != nil {
		log.Warn("fetch origin remote failure", zap.Error(err))
	}

	w, err := r.Worktree()
	if err != nil {
		return err
	}
	if err = w.Reset(&git.ResetOptions{
		Mode: git.HardReset,
	}); err != nil {
		return err
	}

	logf("git checkout %s", commit)
	err = w.Checkout(&git.CheckoutOptions{
		Branch: plumbing.NewBranchReferenceName(fmt.Sprintf("origin/%s", branch)),
	})
	if err != nil {
		return err
	}
	logf("git show-ref --head HEAD")
	ref, err = r.Head()
	if err != nil {
		return err
	}
	log.Info("git head hash", zap.Any("sha", ref.Hash()))
	return nil
}

type goListNode struct {
	pkgName packageInfo
	next    []*goListNode
}
type functionInfo struct {
	importPath   string
	functionName string
}

func printGraph(root *goListNode, pathStr string) {
	if len(root.next) == 0 {
		fmt.Println(pathStr)
		return
	} else {
		for _, v := range root.next {
			printGraph(v, pathStr+"<-"+root.pkgName.importPath)
		}
	}
}
func dfs(root *goListNode, goList *map[packageInfo]map[string]struct{}, s string, done map[packageInfo]struct{}, goListNodeMap map[packageInfo]*goListNode) {
	if _, ok := done[root.pkgName]; ok {
		return
	}
	for k, v := range *goList {
		if _, ok := v[root.pkgName.importPath]; ok {
			root.next = append(root.next, goListNodeMap[k])
		}

	}

	var list string
	for _, v := range root.next {
		list += v.pkgName.importPath + ", "
	}
	// fmt.Printf("%v was imported by {%v}\n", root.pkgName, list)
	for _, v := range root.next {
		if _, ok := done[v.pkgName]; ok {
			continue
		}
		// fmt.Printf("%v was imported by %v\n", root.pkgName, v.pkgName)
		// fmt.Printf("%v call dfs for %v\n", root.pkgName, v.pkgName)
		dfs(v, goList, s+"<-"+root.pkgName.importPath, done, goListNodeMap)
	}
	// fmt.Println(s)
	done[root.pkgName] = struct{}{}
}

func (a *analysis) parseInfluencePackages() error {
	a.goList = make(map[packageInfo]map[string]struct{})
	cmd := exec.Command("go", "list", "-f", "\"{{.ImportPath}} {{.Imports}}\"", "./...")
	var out strings.Builder
	cmd.Stdout = &out
	err := cmd.Run()
	if err != nil {
		return err
	}
	lines := strings.Split(out.String(), "\n")
	for _, line := range lines {
		if len(line) == 0 {
			continue
		}
		re := regexp.MustCompile(`(\S+)\s+(.*)`)
		matches := re.FindStringSubmatch(line[1 : len(line)-1])
		if len(matches) > 0 {
			url := matches[1]
			if strings.Contains(url, "mock") {
				continue
			}
			pkgName := strings.Split(url, "/")[len(strings.Split(url, "/"))-1]
			importPkgPaths := strings.Split(matches[2][1:len(matches[2])-1], " ")
			if pkgName, err = getPkgName(url); err != nil {
				logf("get pkg name failure %v", err)
				continue
			}
			a.goList[packageInfo{pkgName: pkgName, importPath: url}] = make(map[string]struct{})
			for _, importPkgPath := range importPkgPaths {
				a.goList[packageInfo{pkgName: pkgName, importPath: url}][importPkgPath] = struct{}{}
			}
		}
	}

	a.influencePackagesRoot = &goListNode{pkgName: packageInfo{pkgName: "root", importPath: "root"}, next: []*goListNode{}}
	done := make(map[packageInfo]struct{})
	goListNodeMap := make(map[packageInfo]*goListNode)
	for k := range a.goList {
		goListNodeMap[k] = &goListNode{pkgName: k, next: []*goListNode{}}
	}
	for k := range Analysis.modifyPackages {
		if _, ok := goListNodeMap[k]; ok {
			a.influencePackagesRoot.next = append(a.influencePackagesRoot.next, goListNodeMap[k])
		}
	}
	dfs(a.influencePackagesRoot, &a.goList, "", done, goListNodeMap)
	fmt.Println("------------")
	// printGraph(&root, "")
	return nil
}

func (a *analysis) parsePR(urlStr, repo, commit string) error {
	url, _ := ghdiff.ParsePullRequestURL(urlStr)
	client := github.NewClient(nil)
	githubToken := os.Getenv("GITHUB_TOKEN")
	if githubToken != "" {
		client = client.WithAuthToken(githubToken)
	}
	ghClient := ghdiff.GitHubClientWrapper{Client: client}
	details, err := ghdiff.GetPullRequestWithDetails(context.TODO(), url, &ghClient)
	if err != nil {
		return err
	}
	prCommit := *details.Head.SHA
	if len(commit) != 0 {
		prCommit = commit
	}
	a.prCommit = prCommit
	done, err := commitAnalyzeDone(*details.Head.Label, prCommit)
	if err != nil {
		return err
	}
	if done && !*dryRun {
		return errors.New("commit have analyze")
	}
	if err = a.checkout(*details.Head.Label, prCommit); err != nil {
		prCommit = *details.Base.SHA
		a.prCommit = prCommit
		if err = a.checkout(*details.Base.Label, prCommit); err != nil {
			return err
		} else {
			DbExecuteWithoutLog(context.Background(), "insert into done_pr (url, branch, bot) value(?, ?)", url, *details.Base.Label, commit)
		}
	} else {
		DbExecuteWithoutLog(context.Background(), "insert into done_pr (url, branch, bot) value(?, ?)", url, *details.Head.Label, commit)
	}
	prString, err := ghdiff.GetPullRequestWithClient(context.TODO(), url, &ghClient)
	if err != nil {
		log.Info("Error getting pull request", zap.Error(err))
		return err
	}
	ignoreList := []string{".mod", "_test.go", ".bazel"}
	diffFiles := ghdiff.ParseGitDiff(prString, ignoreList)
	a.modifyPackages = make(map[packageInfo]modifyFunctions)
	for _, diffFile := range diffFiles {
		log.Info("modify file path", zap.String("old", diffFile.FilePathOld), zap.String("new", diffFile.FilePathNew))
		functions := parseDiffContentsGetModifyFunctions(diffFile.DiffContents)
		log.Info("parse diff contents get modify functions", zap.Strings("functions", functions))
		fset := token.NewFileSet()
		node, err2 := parser.ParseFile(fset, "./"+strings.TrimPrefix(diffFile.FilePathNew, "b/"), nil, parser.PackageClauseOnly)
		var pkgName string
		if err2 != nil {
			log.Warn("parse file get error", zap.Error(err2))
			for _, line := range strings.Split(diffFile.DiffContents, "\n") {
				if strings.Contains(line, "-package ") {
					pkgName = strings.TrimPrefix(line, "-package ")
					break
				}
			}
		} else {
			pkgName = node.Name.String()
		}

		var importPath string
		for i, s := range strings.Split("github.com/"+*details.Base.Repo.FullName+"/"+strings.TrimPrefix(diffFile.FilePathNew, "b/"), "/") {
			if i == len(strings.Split("github.com/"+*details.Base.Repo.FullName+"/"+strings.TrimPrefix(diffFile.FilePathNew, "b/"), "/"))-1 {
				break
			}
			importPath += s + "/"
		}
		importPath = importPath[:len(importPath)-1]
		if strings.Contains(importPath, "mock") {
			log.Warn("detect mock package", zap.String("path", importPath))
			continue
		} else if strings.Contains(importPath, "test") {
			log.Warn("detect test package", zap.String("path", importPath))
			continue
		}
		if pkgName == "tidb-server" {
			pkgName = "main"
		}
		if v, ok := a.modifyPackages[packageInfo{pkgName: pkgName, importPath: importPath}]; !ok {
			a.modifyPackages[packageInfo{pkgName: pkgName, importPath: importPath}] = modifyFunctions{functions: functions}
		} else {
			a.modifyPackages[packageInfo{pkgName: pkgName, importPath: importPath}] = modifyFunctions{functions: append(v.functions, functions...)}
		}
		log.Info("update modify packages", zap.String("pkg pkgName", pkgName), zap.String("import path", importPath), zap.Strings("functions", a.modifyPackages[packageInfo{pkgName: pkgName, importPath: importPath}].functions))
	}
	return nil
}

func parseDiffContentsGetModifyFunctions(diffContents string) []string {
	var functions []string
	lines := strings.Split(diffContents, "\n")
	for _, line := range lines {
		if strings.Contains(line, " func") {
			log.Info("compile context", zap.String("context", line))
			functions = append(functions, extractFuncName(line))
		}
	}
	return functions
}

func extractFuncName(s string) string {
	re := regexp.MustCompile(`func\s*(?:\(\w+\s*\*?\s*\w+\)\s*)?(\w+)\(`)
	match := re.FindStringSubmatch(s)
	if len(match) > 1 {
		return match[1]
	} else {
		logf("%s can not compile\n", s)
	}
	return ""
}
