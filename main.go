// go-callvis: a tool to help visualize the call graph of a Go program.
package main

import (
	"context"
	"flag"
	"fmt"
	"go.uber.org/zap"
	"go/build"
	"golang.org/x/tools/go/packages"
	"log"
	"net"
	"net/http"
	"net/url"
	"os"
	"strings"
	"time"

	logutil "github.com/pingcap/log"
	"github.com/pkg/browser"
	"golang.org/x/tools/go/buildutil"
)

const Usage = `go-callvis: visualize call graph of a Go program.

Usage:

  go-callvis [flags] package

  Package should be main package, otherwise -tests flag must be used.

Flags:

`

var (
	focusFlag     = flag.String("focus", "", "Focus specific package using pkgName or import path.")
	groupFlag     = flag.String("group", "pkg", "Grouping modifyPackages by packages and/or types [pkg, type] (separated by comma)")
	limitFlag     = flag.String("limit", "", "Limit package paths to given prefixes (separated by comma)")
	ignoreFlag    = flag.String("ignore", "", "Ignore package paths containing given prefixes (separated by comma)")
	includeFlag   = flag.String("include", "", "Include package paths with given prefixes (separated by comma)")
	nostdFlag     = flag.Bool("nostd", false, "Omit calls to/from packages in standard library.")
	nointerFlag   = flag.Bool("nointer", false, "Omit calls to unexported modifyPackages.")
	testFlag      = flag.Bool("tests", false, "Include test code.")
	graphvizFlag  = flag.Bool("graphviz", false, "Use Graphviz's dot program to render images.")
	httpFlag      = flag.String("http", ":7878", "HTTP service address.")
	skipBrowser   = flag.Bool("skipbrowser", false, "Skip opening browser.")
	outputFile    = flag.String("file", "", "output filename - omit to use server mode")
	outputFormat  = flag.String("format", "svg", "output file format [svg | png | jpg | ...]")
	cacheDir      = flag.String("cacheDir", "", "Enable caching to avoid unnecessary re-rendering, you can force rendering by adding 'refresh=true' to the URL query or emptying the cache directory")
	callgraphAlgo = flag.String("algo", CallGraphTypePointer, fmt.Sprintf("The algorithm used to construct the call graph. Possible values inlcude: %q, %q, %q, %q",
		CallGraphTypeStatic, CallGraphTypeCha, CallGraphTypeRta, CallGraphTypePointer))

	debugFlag   = flag.Bool("debug", false, "Enable verbose log.")
	versionFlag = flag.Bool("version", false, "Show version and exit.")
	prURL       = flag.String("prURL", "", "github pr url")
	repo        = flag.String("repo", "", "github repo pkgName")
	dryRun      = flag.Bool("dryRun", false, "dry run")
	commitHash  = flag.String("commit", "", "commit hash")
)

func init() {
	flag.Var((*buildutil.TagsFlag)(&build.Default.BuildTags), "tags", buildutil.TagsFlagDoc)
	// Graphviz options
	flag.UintVar(&minlen, "minlen", 2, "Minimum edge length (for wider output).")
	flag.Float64Var(&nodesep, "nodesep", 0.5, "Minimum space between two adjacent nodes in the same rank (for taller output).")
	flag.StringVar(&nodeshape, "nodeshape", "box", "graph node shape (see graphvis manpage for valid values)")
	flag.StringVar(&nodestyle, "nodestyle", "filled,rounded", "graph node style (see graphvis manpage for valid values)")
	flag.StringVar(&rankdir, "rankdir", "LR", "Direction of graph layout [LR | RL | TB | BT]")
}

func logf(f string, a ...interface{}) {
	if *debugFlag {
		log.Printf(f, a...)
	}
}

func parseHTTPAddr(addr string) string {
	host, port, _ := net.SplitHostPort(addr)
	if host == "" {
		host = "localhost"
	}
	if port == "" {
		port = "80"
	}
	u := url.URL{
		Scheme: "http",
		Host:   fmt.Sprintf("%s:%s", host, port),
	}
	return u.String()
}

func openBrowser(url string) {
	time.Sleep(time.Millisecond * 100)
	if err := browser.OpenURL(url); err != nil {
		log.Printf("OpenURL error: %v", err)
	}
}

func outputDot(fname string, outputFormat string, skipOutput bool) {
	// get cmdline default for analysis
	Analysis.OptsSetup()

	if e := Analysis.ProcessListArgs(); e != nil {
		log.Fatalf("%v\n", e)
	}

	output, err := Analysis.Render()
	if err != nil {
		log.Printf("%v\n", err)
		return
	}
	if skipOutput {
		return
	}

	log.Println("writing dot output..")

	writeErr := os.WriteFile(fmt.Sprintf("%s.gv", fname), output, 0755)
	if writeErr != nil {
		log.Fatalf("%v\n", writeErr)
	}

	log.Printf("converting dot to %s..\n", outputFormat)

	_, err = dotToImage(fname, outputFormat, output)
	if err != nil {
		log.Fatalf("%v\n", err)
	}
}

func callEdgeDFS(funcInfo functionInfo, set map[functionInfo]struct{}, s string) {
	if callerFuncs, ok := Analysis.funcInfo[funcInfo]; ok {
		for k := range callerFuncs {
			if _, ok := set[k]; ok {
				if len(Analysis.sql) == 0 {
					Analysis.sql = "insert into call_graph_analyzer (prURL, pr_commit, caller, modify_pkg, chain) value(?, ?, ?, ?, ?)"
				} else {
					Analysis.sql += ",(?, ?, ?, ?, ?)"
				}
				isModifyPkg := 0
				logf("pkgname: %v, import path %v", strings.Split(k.importPath, "/")[len(strings.Split(k.importPath, "/"))-1], k.importPath)
				if _, ok = Analysis.modifyPackages[packageInfo{pkgName: strings.Split(k.importPath, "/")[len(strings.Split(k.importPath, "/"))-1], importPath: k.importPath}]; ok {
					isModifyPkg = 1
				}
				Analysis.args = append(Analysis.args, Analysis.prURL, Analysis.prCommit, k.importPath, isModifyPkg, s)
				if len(Analysis.args) > 2000 {
					if _, err := DbExecuteWithoutLog(context.Background(), Analysis.sql, Analysis.args...); err != nil {
						logutil.Error("record fail", zap.Error(err))
					}
					Analysis.sql = ""
					Analysis.args = []interface{}{}
				}

				logutil.Info("edge end", zap.String("edge", s))
				continue
			}
			set[k] = struct{}{}
			callEdgeDFS(k, set, fmt.Sprintf("%s<-%s.(%s)", s, k.importPath, k.functionName))
			delete(set, k)
		}
	} else {
		if len(Analysis.sql) == 0 {
			Analysis.sql = "insert into call_graph_analyzer (prURL, pr_commit, caller, modify_pkg, chain) value(?, ?, ?, ?, ?)"
		} else {
			Analysis.sql += ",(?, ?, ?, ?, ?)"
		}
		isModifyPkg := 0
		logf("pkgname: %v, import path %v", strings.Split(funcInfo.importPath, "/")[len(strings.Split(funcInfo.importPath, "/"))-1], funcInfo.importPath)
		if _, ok = Analysis.modifyPackages[packageInfo{pkgName: strings.Split(funcInfo.importPath, "/")[len(strings.Split(funcInfo.importPath, "/"))-1], importPath: funcInfo.importPath}]; ok {
			isModifyPkg = 1
		}
		Analysis.args = append(Analysis.args, Analysis.prURL, Analysis.prCommit, funcInfo.importPath, isModifyPkg, s)

		if _, err := DbExecuteWithoutLog(context.Background(), Analysis.sql, Analysis.args...); err != nil {
			logf("record fail err:%v", err)
		}
		Analysis.sql = ""
		Analysis.args = []interface{}{}
		logutil.Info("edge end", zap.String("edge", s))
		return
	}
}

func main() {
	flag.Parse()

	if *versionFlag {
		fmt.Fprintln(os.Stderr, Version())
		os.Exit(0)
	}
	if *debugFlag {
		log.SetFlags(log.Lmicroseconds)
	}

	if flag.NArg() != 1 {
		fmt.Fprint(os.Stderr, Usage)
		flag.PrintDefaults()
		os.Exit(2)
	}

	args := flag.Args()
	tests := *testFlag
	httpAddr := *httpFlag
	checkoutCommit := *commitHash
	urlAddr := parseHTTPAddr(httpAddr)

	Analysis = new(analysis)
	Analysis.influenceFunctions = make(map[packageInfo]map[string]struct{})
	Analysis.funcInfo = make(map[functionInfo]map[functionInfo]struct{})
	if *prURL != "" {
		Analysis.prURL = *prURL
		if err := Analysis.parsePR(*prURL, *repo, checkoutCommit); err != nil {
			log.Fatal(err)
		}
		for k := range Analysis.modifyPackages {
			DbExecuteWithoutLog(context.Background(), "insert into call_graph_pr_modify_packages(prURL, modify_packages) value(?, ?)", Analysis.prURL, k.importPath)
		}

		if err := Analysis.parseInfluencePackages(); err != nil {
			log.Fatal(err)
		}
		for pkgInfo, v := range Analysis.modifyPackages {
			if _, ok := Analysis.influenceFunctions[pkgInfo]; !ok {
				Analysis.influenceFunctions[pkgInfo] = make(map[string]struct{})
			}
			for _, f := range v.functions {
				if _, ok := Analysis.influenceFunctions[pkgInfo][f]; !ok {
					Analysis.influenceFunctions[pkgInfo][f] = struct{}{}
				}
			}
		}

		queue := Analysis.influencePackagesRoot.next
		set := make(map[string]struct{})
		args = []string{}
		for {
			length := len(set)
			for _, pkg := range queue {
				if _, ok := set[pkg.pkgName.importPath]; !ok {
					args = append(args, pkg.pkgName.importPath)
					set[pkg.pkgName.importPath] = struct{}{}
				}
			}
			if length == len(set) {
				break
			}
			length = len(queue)
			for _, pkgs := range queue {
				for _, pkg := range pkgs.next {
					if _, ok := set[pkg.pkgName.importPath]; !ok {
						queue = append(queue, pkg)
					}
				}
			}
			queue = queue[length:]
		}
		if len(args) == 0 {
			for k := range Analysis.goList {
				args = append(args, k.importPath)
			}
		}
		pkgs := ""
		for _, arg := range args {
			pkgs = fmt.Sprintf("%s,%s", pkgs, arg)
		}
		if len(pkgs) > 0 {
			log.Printf("analyze packages list[%s]", pkgs[1:])
		}

		if err := Analysis.DoAnalysis(CallGraphType(*callgraphAlgo), "",
			tests, args); err != nil {
			log.Fatal(err)
		}

		outputDot(time.Now().GoString(), *outputFormat, true)
		for k, v := range Analysis.funcInfo {
			s := fmt.Sprintf("%s.(%s) called by: ", k.importPath, k.functionName)
			for k2 := range v {
				s = fmt.Sprintf("%s, %s.(%s)", s, k2.importPath, k2.functionName)
			}
			if strings.Contains(s, "tidb") {
				logf(s)
			}
		}

		for k, functions := range Analysis.influenceFunctions {
			for f := range functions {
				set := make(map[functionInfo]struct{})
				callEdgeDFS(functionInfo{importPath: k.importPath, functionName: f}, set, fmt.Sprintf("%s.(%s)", k.importPath, f))
			}
		}
		// dfs all functions in `Analysis.funcInfo`
		if strings.Contains(Analysis.prURL, "/master") {
			for k, functions := range Analysis.funcInfo {
				for f := range functions {
					set := make(map[functionInfo]struct{})
					callEdgeDFS(functionInfo{importPath: k.importPath, functionName: f.functionName}, set, fmt.Sprintf("%s.(%s)", k.importPath, f))
				}
			}
		}

	} else {
		if err := Analysis.DoAnalysis(CallGraphType(*callgraphAlgo), "", tests, args); err != nil {
			log.Fatal(err)
		}

		if *outputFile == "" {
			*outputFile = "output"
			if !*skipBrowser {
				go openBrowser(urlAddr)
			}

			log.Printf("http serving at %s", urlAddr)
			if err := http.ListenAndServe(httpAddr, nil); err != nil {
				log.Fatal(err)
			}
		} else {
			outputDot(*outputFile, *outputFormat, false)
		}
	}
}

func getPkgName(importPath string) (string, error) {
	cfg := &packages.Config{
		Mode:       packages.NeedName,
		BuildFlags: getBuildFlags(),
	}

	initial, err := packages.Load(cfg, importPath)
	if err != nil {
		return "", err
	}
	return initial[0].Name, nil
}
