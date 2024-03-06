/*
 * Tai-e: A Static Analysis Framework for Java
 *
 * Copyright (C) 2022 Tian Tan <tiantan@nju.edu.cn>
 * Copyright (C) 2022 Yue Li <yueli@nju.edu.cn>
 *
 * This file is part of Tai-e.
 *
 * Tai-e is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License
 * as published by the Free Software Foundation, either version 3
 * of the License, or (at your option) any later version.
 *
 * Tai-e is distributed in the hope that it will be useful,but WITHOUT
 * ANY WARRANTY; without even the implied warranty of MERCHANTABILITY
 * or FITNESS FOR A PARTICULAR PURPOSE. See the GNU Lesser General
 * Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public
 * License along with Tai-e. If not, see <https://www.gnu.org/licenses/>.
 */

package pascal.taie.analysis.pta.ci;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import pascal.taie.World;
import pascal.taie.analysis.graph.callgraph.CallGraphs;
import pascal.taie.analysis.graph.callgraph.CallKind;
import pascal.taie.analysis.graph.callgraph.DefaultCallGraph;
import pascal.taie.analysis.graph.callgraph.Edge;
import pascal.taie.analysis.pta.core.heap.HeapModel;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.ir.exp.InvokeExp;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.proginfo.MethodRef;
import pascal.taie.ir.stmt.Copy;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.ir.stmt.LoadArray;
import pascal.taie.ir.stmt.LoadField;
import pascal.taie.ir.stmt.New;
import pascal.taie.ir.stmt.StmtVisitor;
import pascal.taie.ir.stmt.StoreArray;
import pascal.taie.ir.stmt.StoreField;
import pascal.taie.language.classes.ClassHierarchy;
import pascal.taie.language.classes.JMethod;
import pascal.taie.util.AnalysisException;
import pascal.taie.language.type.Type;

import java.awt.print.PageFormat;
import java.util.List;
import java.util.stream.Collectors;

class Solver {

    private static final Logger logger = LogManager.getLogger(Solver.class);

    private final HeapModel heapModel;

    private DefaultCallGraph callGraph;

    private PointerFlowGraph pointerFlowGraph;

    private WorkList workList;

    private StmtProcessor stmtProcessor;

    private ClassHierarchy hierarchy;

    Solver(HeapModel heapModel) {
        this.heapModel = heapModel;
    }

    /**
     * we need to handle these stmts:
     *  x = new T
     *  x = y
     *  x.f = y
     *  T.f = y
     *  y = x.f
     *  y = T.f
     *  x[i] = y
     *  y = x[i]
     *  y = x.m
     *  y = T.m
     */

    /**
     * Runs pointer analysis algorithm.
     */
    void solve() {
        initialize();
        analyze();
    }

    /**
     * Initializes pointer analysis.
     */
    private void initialize() {
        workList = new WorkList();
        pointerFlowGraph = new PointerFlowGraph();
        callGraph = new DefaultCallGraph();
        stmtProcessor = new StmtProcessor();
        hierarchy = World.get().getClassHierarchy();
        // initialize main method
        JMethod main = World.get().getMainMethod();
        callGraph.addEntryMethod(main);
        addReachable(main);
    }

    /**
     * Processes new reachable method.
     *
     * need to handle stmt in loc l
     *  x = new T
     *  x = y
     *  T.f = y
     *  y = T.f
     *  x = T.m
     */
    private void addReachable(JMethod method) {
        if (callGraph.contains(method)) {
            return ;
        }
        callGraph.addReachableMethod(method);
        for (var stmt: method.getIR().getStmts()) {
            stmt.accept(stmtProcessor);
        }
    }

    /**
     * Processes statements in new reachable methods.
     *
     * x = new T
     * x = y
     * T.f = y
     * y = T.f
     * x = T.m(params)
     */
    private class StmtProcessor implements StmtVisitor<Void> {
        // TODO - if you choose to implement addReachable()
        //  via visitor pattern, then finish me

        public Void visit(New stmt) {
            var v = stmt.getLValue();
            var obj = heapModel.getObj(stmt);
            workList.addEntry(pointerFlowGraph.getVarPtr(v), new PointsToSet(obj));
            return null;
        }

        public Void visit(Copy cp) {
            var lhs = cp.getLValue();
            var rhs = cp.getRValue();
            addPFGEdge(pointerFlowGraph.getVarPtr(rhs), pointerFlowGraph.getVarPtr(lhs));
            return null;
        }

        public Void visit(StoreField sf) {
            if (!sf.isStatic()) {
                return null;
            }
            var target = sf.getFieldAccess();
            var source = sf.getRValue();
            addPFGEdge(pointerFlowGraph.getVarPtr(source), pointerFlowGraph.getStaticField(target.getFieldRef().resolve()));
            return null;
        }

        public Void visit(LoadField lf) {
            if (!lf.isStatic()) {
                return null;
            }
            var target = lf.getLValue();
            var source = lf.getFieldAccess();
            addPFGEdge(pointerFlowGraph.getStaticField(source.getFieldRef().resolve()), pointerFlowGraph.getVarPtr(target));
            return null;
        }

        public Void visit(Invoke invoke) {
            if (!invoke.isStatic()) {
                return null;
            }

            var staticM = resolveCallee(null, invoke);

            callGraph.addEdge(new Edge<>(CallKind.STATIC, invoke, staticM));

            addReachable(staticM);
            var paramNum = staticM.getParamCount();
            for (int i = 0; i < paramNum; i++) {
                // arg of invoke -> param of static method
                addPFGEdge(pointerFlowGraph.getVarPtr(invoke.getInvokeExp().getArg(i)), pointerFlowGraph.getVarPtr(staticM.getIR().getParam(i)));
            }
            if (invoke.getResult() == null) {
                return null;
            }
            for (var retVar: staticM.getIR().getReturnVars()) {
                // ret of static method -> receiver of invoke
                addPFGEdge(pointerFlowGraph.getVarPtr(retVar), pointerFlowGraph.getVarPtr(invoke.getResult()));
            }
            return null;
        }
     }

    /**
     * Adds an edge "source -> target" to the PFG.
     */
    private void addPFGEdge(Pointer source, Pointer target) {
        var changed = pointerFlowGraph.addEdge(source, target);
        if (!changed) {
            return;
        }
        if (!(source.getPointsToSet().isEmpty())) {
            workList.addEntry(target, source.getPointsToSet());
        }
    }

    private String PFGOut() {
        var s = "";
        for (var v: pointerFlowGraph.getPointers()) {
            s += String.format("%s:\n\tsucc: %s\n\tpts: %s\n\n", v, pointerFlowGraph.getSuccsOf(v), v.getPointsToSet());
        }
        return s;
    }

    /**
     * Processes work-list entries until the work-list is empty.
     */
    private void analyze() {
        while (!workList.isEmpty()) {
//            System.out.println("------------------------\nbegin PFG:\n"+
//                PFGOut()
//            );
            var entry = workList.pollEntry();
            var n = entry.pointer();
            var pts = entry.pointsToSet();

//            System.out.println("analyzing pointer "+
//                n+
//                "\nwith pts:"+
//                pts+
//                "\nwith succs:"+
//                pointerFlowGraph.getSuccsOf(n)+"\n"
//            );

            var delta = propagate(n, pts);
            if (n instanceof VarPtr varPtr) {
                var x = varPtr.getVar();
                for (var o: delta) {
//                    System.out.println(x+" 's new object "+o);
                    // x.f = y dynamic
                    // y = x.f dynamic
                    // x[i] = y
                    // y = x[i]
                    // y = x.m dynamic

                    // x.f = y
                    for (var sf: x.getStoreFields()) {
                        if (sf.isStatic()) continue;
                        var y = sf.getRValue();
                        var xf = sf.getFieldAccess();
                        addPFGEdge(
                            pointerFlowGraph.getVarPtr(y),
                            pointerFlowGraph.getInstanceField(o, xf.getFieldRef().resolve())
                        );
                    }

                    // y = x.f
                    for (var lf: x.getLoadFields()) {
                        if (lf.isStatic()) continue;
                        var y = lf.getLValue();
                        var xf = lf.getFieldAccess();
                        addPFGEdge(
                            pointerFlowGraph.getInstanceField(o, xf.getFieldRef().resolve()),
                            pointerFlowGraph.getVarPtr(y)
                        );
                    }

                    // x[i] = y
                    for (var sa: x.getStoreArrays()) {
                        var y = sa.getRValue();
                        addPFGEdge(
                            pointerFlowGraph.getVarPtr(y),
                            pointerFlowGraph.getArrayIndex(o)
                        );
                    }

                    // y = x[i]
                    for (var la: x.getLoadArrays()) {
                        var y = la.getLValue();
                        addPFGEdge(
                            pointerFlowGraph.getArrayIndex(o),
                            pointerFlowGraph.getVarPtr(y)
                        );
                    }

                    processCall(x, o);
                }
            }
//            System.out.println("------------------------\nEnd PFG:\n"+PFGOut());
        }
    }

    /**
     * Propagates pointsToSet to pt(pointer) and its PFG successors,
     * returns the difference set of pointsToSet and pt(pointer).
     */
    private PointsToSet propagate(Pointer pointer, PointsToSet pointsToSet) {
        var delta = new PointsToSet();
        if (pointsToSet.isEmpty()) {
            return delta;
        }
        for (var o: pointsToSet) {
            if (!pointer.getPointsToSet().contains(o)) {
                delta.addObject(o);
                pointer.getPointsToSet().addObject(o);
            }
        }

        for (var succ: pointerFlowGraph.getSuccsOf(pointer)) {
            workList.addEntry(succ, delta);
        }
        return delta;
    }

    /**
     * Processes instance calls when points-to set of the receiver variable changes.
     *
     * @param var the variable that holds receiver objects
     * @param recv a new discovered object pointed by the variable.
     */
    private void processCall(Var var, Obj recv) {
        for (var invoke: var.getInvokes()) {
            if (invoke.isStatic()) continue;
//            System.out.println("processing call: " + invoke);
            var m = resolveCallee(recv, invoke);

            workList.addEntry(pointerFlowGraph.getVarPtr(m.getIR().getThis()), new PointsToSet(recv));

            var changed = callGraph.addEdge(new Edge(CallGraphs.getCallKind(invoke), invoke, m));
            if (changed) {
                addReachable(m);
                int i = 0;
                while (i < m.getParamCount()) {
                    addPFGEdge(
                        pointerFlowGraph.getVarPtr(invoke.getInvokeExp().getArg(i)),
                        pointerFlowGraph.getVarPtr(m.getIR().getParam(i))
                    );
                    i++;
                }
                if (invoke.getLValue() == null) {
                    continue;
                }
                for (var retVar: m.getIR().getReturnVars()) {
                    addPFGEdge(
                        pointerFlowGraph.getVarPtr(retVar),
                        pointerFlowGraph.getVarPtr(invoke.getLValue())
                    );
                }
            }
        }
    }

    /**
     * Resolves the callee of a call site with the receiver object.
     *
     * @param recv     the receiver object of the method call. If the callSite
     *                 is static, this parameter is ignored (i.e., can be null).
     * @param callSite the call site to be resolved.
     * @return the resolved callee.
     */
    private JMethod resolveCallee(Obj recv, Invoke callSite) {
        Type type = recv != null ? recv.getType() : null;
        return CallGraphs.resolveCallee(type, callSite);
    }

    CIPTAResult getResult() {
        return new CIPTAResult(pointerFlowGraph, callGraph);
    }
}
