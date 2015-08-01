// reckt analyses Go programs for explicit panics which may reach a root of the callgraph.
//
// Usage: reckt [-tests] pkg
package main

import (
	"flag"
	"fmt"
	"os"

	"golang.org/x/tools/go/callgraph"
	"golang.org/x/tools/go/loader"
	"golang.org/x/tools/go/pointer"
	"golang.org/x/tools/go/ssa"
	"golang.org/x/tools/go/ssa/ssautil"
)

var tests = flag.Bool("tests", false, "include tests in analysis")

func main() {
	flag.Parse()

	prog, err := loadProgram(flag.Args(), *tests)
	if err != nil {
		fmt.Fprintf(os.Stderr, "rect: %s", err)
		os.Exit(1)
	}

	panics := findPanics(prog)

	cg, err := doCallgraph(prog, *tests)
	if err != nil {
		fmt.Fprintf(os.Stderr, "rect: %s", err)
		os.Exit(1)
	}
	for _, p := range panics {
		path := pathToRoot(p, cg)
		if len(path) != 0 {
			fmt.Println("Panic at", prog.Fset.Position(p.Pos()), "reaches root")
			for _, pth := range path {
				if pth.Site != nil {
					fmt.Println("\t", prog.Fset.Position(pth.Pos()), pth.Site.String())
				} else {
					fmt.Println("\t", pth)
				}
			}
		}
	}
}

// It would seem that we could check each node
// see if it has a recover defer, remove it from
// the callgraph and then just run callgraph.PathSearch
// on it. However, the callgraph returned needs to stop the search
// when we find A root, not the root and go calls are considered just edges of
// the graph. So for go function calls, it will
// incorrectly infer that there is no path from the root to the panic we're
// testing.
//
// So we have to do this instead. Start from the panic and
// path search back to the root or to a go call which doesn't go
// through a node with a defer in it.
//
func pathToRoot(p *ssa.Panic, cg *callgraph.Graph) []*callgraph.Edge {
	stack := make([]*callgraph.Edge, 0, 32)
	seen := make(map[*callgraph.Node]bool)
	var search func(n *callgraph.Node) []*callgraph.Edge
	search = func(n *callgraph.Node) []*callgraph.Edge {
		if !seen[n] {
			seen[n] = true
			end, deadend := end(cg.Root, n)
			if deadend {
				return nil
			} else if end {
				return stack
			}
			for _, e := range n.In {
				stack = append(stack, e) // push
				if found := search(e.Caller); found != nil {
					return stack
				}
				stack = stack[:len(stack)-1] // pop
			}
		}
		return nil
	}
	panicfunc := cg.Nodes[p.Parent()]
	return search(panicfunc)
}

func end(root, n *callgraph.Node) (isend bool, isdeadend bool) {
	// we need to figure out if this is a root or dead end
	// Does this function defer a call?
	defers := make(map[*ssa.Defer][]*callgraph.Node)
	if n == nil {
		return true, false
	}
	for _, o := range n.Out {
		dn, ok := o.Site.(*ssa.Defer)
		if !ok {
			continue
		}
		defers[dn] = append(defers[dn], o.Callee)
	}
	// does one of these defers only dispatch to functions that calls recover?
	for _, e := range defers {
		if allrecovers(e) {
			return false, true
		}
	}
	// ok, this function doesn't recover,
	// is it a root
	if n == root {
		return true, false
	}
	for _, in := range n.In {
		_, ok := in.Site.(*ssa.Go)
		if ok {
			return true, false
		}
	}
	// not a root and doesn't recover
	// so continue the search
	return false, false
}

func allrecovers(o []*callgraph.Node) bool {
	for _, f := range o {
		if !hasRecover(f.Func) {
			return false
		}
	}
	return true
}

// control flow can make it so that recover isn't called
// or we can have multiple recovers in a function, where one
// is a no-op
//
// anyone who writes code like that wouldn't use this tool
// because they're already far gone. Prove me wrong!
func hasRecover(f *ssa.Function) bool {
	for _, b := range f.Blocks {
		for _, i := range b.Instrs {
			c, ok := i.(*ssa.Call)
			if !ok {
				continue
			}
			built, ok := c.Call.Value.(*ssa.Builtin)
			if !ok {
				continue
			}
			if built.Name() == "recover" {
				return true
			}
		}
	}
	return false
}

// find all panic instructions in program
// TODO: handle go panic() and defer panic(). They're handled
// as builtin calls, but unlikely to show up in real code.
func findPanics(prog *ssa.Program) []*ssa.Panic {
	var panics []*ssa.Panic
	for f := range ssautil.AllFunctions(prog) {
		for _, b := range f.Blocks {
			for _, i := range b.Instrs {
				p, ok := i.(*ssa.Panic)
				if ok {
					panics = append(panics, p)
				}
			}
		}
	}
	return panics
}

var Usage = "Usage: reckt [-test] pkg"

func loadProgram(args []string, tests bool) (*ssa.Program, error) {
	conf := loader.Config{}

	if len(args) == 0 {
		fmt.Fprintln(os.Stderr, Usage)
		os.Exit(1)
	}

	// Use the initial packages from the command line.
	args, err := conf.FromArgs(args, tests)
	if err != nil {
		return nil, err
	}

	// Load, parse and type-check the whole program.
	iprog, err := conf.Load()
	if err != nil {
		return nil, err
	}

	// Create and build SSA-form program representation.
	prog := ssautil.CreateProgram(iprog, 0)
	prog.BuildAll()
	return prog, nil
}

// boilerplate callgraph code stolen off golang.org/x/tools/cmd/callgraph
func doCallgraph(prog *ssa.Program, tests bool) (*callgraph.Graph, error) {
	main, err := mainPackage(prog, tests)
	if err != nil {
		return nil, err
	}
	config := &pointer.Config{
		Mains:          []*ssa.Package{main},
		BuildCallGraph: true,
	}
	ptares, err := pointer.Analyze(config)
	if err != nil {
		return nil, err // internal error in pointer analysis
	}
	cg := ptares.CallGraph
	cg.DeleteSyntheticNodes()
	return cg, nil
}

// stolen from callgraph tool
// mainPackage returns the main package to analyze.
// The resulting package has a main() function.
func mainPackage(prog *ssa.Program, tests bool) (*ssa.Package, error) {
	pkgs := prog.AllPackages()

	// TODO(adonovan): allow independent control over tests, mains and libraries.
	// TODO(adonovan): put this logic in a library; we keep reinventing it.

	if tests {
		// If -test, use all packages' tests.
		if len(pkgs) > 0 {
			if main := prog.CreateTestMainPackage(pkgs...); main != nil {
				return main, nil
			}
		}
		return nil, fmt.Errorf("no tests")
	}

	// Otherwise, use the first package named main.
	for _, pkg := range pkgs {
		if pkg.Object.Name() == "main" {
			if pkg.Func("main") == nil {
				return nil, fmt.Errorf("no func main() in main package")
			}
			return pkg, nil
		}
	}

	return nil, fmt.Errorf("no main package")
}
