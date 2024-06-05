package main

import (
	"context"
	"errors"
	"fmt"
	"github.com/go-git/go-git/v5"
	"github.com/go-git/go-git/v5/config"
	"github.com/go-git/go-git/v5/plumbing"
	"github.com/google/go-github/v57/github"
	ghdiff "github.com/kmesiab/go-github-diff"
	"github.com/pingcap/log"
	"go.uber.org/zap"
	"go/build"
	"go/parser"
	"go/token"
	"go/types"
	"golang.org/x/tools/go/callgraph"
	"golang.org/x/tools/go/callgraph/cha"
	"golang.org/x/tools/go/callgraph/rta"
	"golang.org/x/tools/go/callgraph/static"
	"golang.org/x/tools/go/packages"
	"golang.org/x/tools/go/pointer"
	"golang.org/x/tools/go/ssa"
	"golang.org/x/tools/go/ssa/ssautil"
	"hash/fnv"
	"io"
	"net/http"
	"os"
	"os/exec"
	"path/filepath"
	"regexp"
	"strconv"
	"strings"
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
	cacheDir string
	focus    string
	group    []string
	ignore   []string
	include  []string
	limit    []string
	nointer  bool
	refresh  bool
	nostd    bool
	algo     CallGraphType
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
	opts              *renderOpts
	prog              *ssa.Program
	pkgs              []*ssa.Package
	mainPkg           *ssa.Package
	callgraph         *callgraph.Graph
	modifyPackages    map[packageInfo]modifyFunctions
	influencePackages map[packageInfo]struct{}
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

func (a *analysis) checkout(cloneURL, repo, commit string) error {
	r, err := git.PlainOpen(".")
	if err != nil {
		return err
	}

	logf("git show-ref --head HEAD")
	ref, err := r.Head()
	if err != nil {
		return err
	}
	fmt.Println(ref.Hash())

	_, err = r.CreateRemote(&config.RemoteConfig{
		Name: hash(fmt.Sprintf(commit)),
		URLs: []string{cloneURL},
	})
	if err := r.Fetch(&git.FetchOptions{
		RemoteName: hash(fmt.Sprintf(commit)),
	}); err != nil {
		return err
	}

	w, err := r.Worktree()
	if err != nil {
		return err
	}

	logf("git checkout %s", commit)
	err = w.Checkout(&git.CheckoutOptions{
		Hash: plumbing.NewHash(commit),
	})
	if err != nil {
		return err
	}
	logf("git show-ref --head HEAD")
	ref, err = r.Head()
	if err != nil {
		return err
	}
	fmt.Println(ref.Hash())
	return nil
}

func (a *analysis) parseInfluencePackages() error {
	cmd := exec.Command("go", "list", "-f", "\"{{.ImportPath}} {{.Imports}}\"", "./...")
	var out strings.Builder
	cmd.Stdout = &out
	err := cmd.Run()
	if err != nil {
		return err
	}
	a.influencePackages = make(map[packageInfo]struct{})
	//log.Info("go list all import package", zap.String("package list", out.String()))
	lines := strings.Split(out.String(), "\n")
	for _, line := range lines {
		if len(line) == 0 {
			continue
		}
		re := regexp.MustCompile(`(\S+)\s+(.*)`)
		matches := re.FindStringSubmatch(line[1 : len(line)-1])
		if len(matches) > 0 {
			url := matches[1]
			pkgName := strings.Split(url, "/")[len(strings.Split(url, "/"))-1]
			importPkgPaths := strings.Split(matches[2][1:len(matches[2])-1], " ")
			if pkgName == "tidb-server" {
				pkgName = "main"
			}
			for _, importPkgPath := range importPkgPaths {
				for k := range a.modifyPackages {
					if k.importPath == importPkgPath {
						if _, ok := a.influencePackages[packageInfo{pkgName: pkgName, importPath: url}]; ok {
							log.Info("duplicate influence package", zap.String("url", url), zap.String("pkg pkgName", pkgName), zap.String("cause pkg", importPkgPath))
						} else {
							log.Info("potential influence package", zap.String("url", url), zap.String("pkg pkgName", pkgName), zap.String("cause pkg", importPkgPath))
							a.influencePackages[packageInfo{pkgName: pkgName, importPath: url}] = struct{}{}
						}
					}
				}
			}
		}
	}
	return nil
}

func (a *analysis) parsePR(urlStr, repo string) error {
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
	cloneURL, commit := *details.Head.Repo.CloneURL, *details.Head.SHA
	if err = a.checkout(cloneURL, repo, commit); err != nil {
		return err
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
		node, err2 := parser.ParseFile(fset, "./"+strings.TrimLeft(diffFile.FilePathNew, "b/"), nil, parser.PackageClauseOnly)
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
		for i, s := range strings.Split("github.com/pingcap/"+repo+"/"+strings.TrimLeft(diffFile.FilePathNew, "b/"), "/") {
			if i == len(strings.Split("github.com/pingcap/"+repo+"/"+strings.TrimLeft(diffFile.FilePathNew, "b/"), "/"))-1 {
				break
			}
			importPath += s + "/"
		}
		importPath = importPath[:len(importPath)-1]
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
