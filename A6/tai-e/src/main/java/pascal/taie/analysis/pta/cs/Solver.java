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

package pascal.taie.analysis.pta.cs;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import pascal.taie.World;
import pascal.taie.analysis.graph.callgraph.CallGraphs;
import pascal.taie.analysis.graph.callgraph.CallKind;
import pascal.taie.analysis.graph.callgraph.Edge;
import pascal.taie.analysis.pta.PointerAnalysisResult;
import pascal.taie.analysis.pta.PointerAnalysisResultImpl;
import pascal.taie.analysis.pta.core.cs.CSCallGraph;
import pascal.taie.analysis.pta.core.cs.context.Context;
import pascal.taie.analysis.pta.core.cs.element.ArrayIndex;
import pascal.taie.analysis.pta.core.cs.element.CSCallSite;
import pascal.taie.analysis.pta.core.cs.element.CSManager;
import pascal.taie.analysis.pta.core.cs.element.CSMethod;
import pascal.taie.analysis.pta.core.cs.element.CSObj;
import pascal.taie.analysis.pta.core.cs.element.CSVar;
import pascal.taie.analysis.pta.core.cs.element.InstanceField;
import pascal.taie.analysis.pta.core.cs.element.MapBasedCSManager;
import pascal.taie.analysis.pta.core.cs.element.Pointer;
import pascal.taie.analysis.pta.core.cs.element.StaticField;
import pascal.taie.analysis.pta.core.cs.selector.ContextSelector;
import pascal.taie.analysis.pta.core.heap.HeapModel;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.analysis.pta.pts.PointsToSet;
import pascal.taie.analysis.pta.pts.PointsToSetFactory;
import pascal.taie.config.AnalysisOptions;
import pascal.taie.ir.exp.InvokeExp;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.Copy;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.ir.stmt.LoadArray;
import pascal.taie.ir.stmt.LoadField;
import pascal.taie.ir.stmt.New;
import pascal.taie.ir.stmt.StmtVisitor;
import pascal.taie.ir.stmt.StoreArray;
import pascal.taie.ir.stmt.StoreField;
import pascal.taie.language.classes.JField;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.type.Type;

class Solver {

    private static final Logger logger = LogManager.getLogger(Solver.class);

    private final AnalysisOptions options;

    private final HeapModel heapModel;

    private final ContextSelector contextSelector;

    private CSManager csManager;

    private CSCallGraph callGraph;

    private PointerFlowGraph pointerFlowGraph;

    private WorkList workList;

    private PointerAnalysisResult result;

    Solver(AnalysisOptions options, HeapModel heapModel,
           ContextSelector contextSelector) {
        this.options = options;
        this.heapModel = heapModel;
        this.contextSelector = contextSelector;
    }

    void solve() {
        initialize();
        analyze();
    }

    private void initialize() {
        csManager = new MapBasedCSManager();
        callGraph = new CSCallGraph(csManager);
        pointerFlowGraph = new PointerFlowGraph();
        workList = new WorkList();
        // process program entry, i.e., main method
        Context defContext = contextSelector.getEmptyContext();
        JMethod main = World.get().getMainMethod();
        CSMethod csMethod = csManager.getCSMethod(defContext, main);
        callGraph.addEntryMethod(csMethod);
        addReachable(csMethod);
    }

    /**
     * Processes new reachable context-sensitive method.
     */
    private void addReachable(CSMethod csMethod) {
        if (callGraph.contains(csMethod)) return ;
        callGraph.addReachableMethod(csMethod);
        var stmtProcessor = new StmtProcessor(csMethod);
        for (var stmt: csMethod.getMethod().getIR()) {
            stmt.accept(stmtProcessor);
        }
    }

    /**
     * Processes the statements in context-sensitive new reachable methods.
     *
     * x = new T
     * x = y
     * T.f = y
     * y = T.f
     * x = T.m()
     */
    private class StmtProcessor implements StmtVisitor<Void> {

        private final CSMethod csMethod;

        private final Context context;

        private StmtProcessor(CSMethod csMethod) {
            this.csMethod = csMethod;
            this.context = csMethod.getContext();
        }

        // TODO - if you choose to implement addReachable()
        //  via visitor pattern, then finish me
        public Void visit(New stmt) {
            var cx = csManager.getCSVar(context, stmt.getLValue());
            var co = csManager.getCSObj(contextSelector.selectHeapContext(csMethod, heapModel.getObj(stmt)), heapModel.getObj(stmt));
            workList.addEntry(cx, PointsToSetFactory.make(co));
            return null;
        }

        public Void visit(Copy stmt) {
            var cx = csManager.getCSVar(context, stmt.getLValue());
            var cy = csManager.getCSVar(context, stmt.getRValue());
            addPFGEdge(cy, cx);
            return null;
        }

        public Void visit(StoreField stmt) {
            if (!stmt.isStatic()) return null;
            var tf = csManager.getStaticField(stmt.getFieldAccess().getFieldRef().resolve());
            var cy = csManager.getCSVar(context, stmt.getRValue());
            addPFGEdge(cy, tf);
            return null;
        }

        public Void visit(LoadField stmt) {
            if (!stmt.isStatic()) return null;
            var tf = csManager.getStaticField(stmt.getFieldAccess().getFieldRef().resolve());
            var cy = csManager.getCSVar(context, stmt.getLValue());
            addPFGEdge(tf, cy);
            return null;
        }

        public Void visit(Invoke stmt) {
            if (!stmt.isStatic()) return null;

            var staticM = resolveCallee(null, stmt);
            var csCallSite = csManager.getCSCallSite(context, stmt);

            var calleeCtx = contextSelector.selectContext(csCallSite, staticM);
            var cm = csManager.getCSMethod(calleeCtx, staticM);

            callGraph.addEdge(new Edge<>(CallKind.STATIC, csCallSite, cm));

            addReachable(cm);

            for (int i = 0; i < staticM.getParamCount(); i++) {
                addPFGEdge(
                    csManager.getCSVar(context, stmt.getInvokeExp().getArg(i)),
                    csManager.getCSVar(calleeCtx, staticM.getIR().getParam(i))
                );
            }

            if (stmt.getResult() == null) return null;
            for (var retVar: staticM.getIR().getReturnVars()) {
                addPFGEdge(
                    csManager.getCSVar(calleeCtx, retVar),
                    csManager.getCSVar(context, stmt.getLValue())
                );
            }

            return null;
        }
    }

    /**
     * Adds an edge "source -> target" to the PFG.
     */
    private void addPFGEdge(Pointer source, Pointer target) {
        if (pointerFlowGraph.addEdge(source, target)) {
            if (!source.getPointsToSet().isEmpty()) {
                workList.addEntry(target, source.getPointsToSet());
            }
        }
    }

    /**
     * Processes work-list entries until the work-list is empty.
     */
    private void analyze() {
        while (!workList.isEmpty()) {
            var entry = workList.pollEntry();
            var n = entry.pointer();
            var pts = entry.pointsToSet();

            var delta = propagate(n, pts);
            if (n instanceof CSVar varPtr) {
                var x = varPtr.getVar();
                var ctxX = varPtr.getContext();
                for (var o: delta) {
                    x.getStoreFields().forEach(stmt -> {
                        if (stmt.isStatic()) return;
                        var cy = csManager.getCSVar(ctxX, stmt.getRValue());
                        var ctxOf = csManager.getInstanceField(o, stmt.getFieldAccess().getFieldRef().resolve());
                        addPFGEdge(cy, ctxOf);
                    });
                    x.getLoadFields().forEach(stmt -> {
                        if (stmt.isStatic()) return;
                        var cy = csManager.getCSVar(ctxX, stmt.getLValue());
                        var ctxOf = csManager.getInstanceField(o, stmt.getFieldAccess().getFieldRef().resolve());
                        addPFGEdge(ctxOf, cy);
                    });
                    x.getStoreArrays().forEach(stmt -> {
                        var cy = csManager.getCSVar(ctxX, stmt.getRValue());
                        var ctxOarrIdx = csManager.getArrayIndex(o);
                        addPFGEdge(cy, ctxOarrIdx);
                    });
                    x.getLoadArrays().forEach(stmt -> {
                        var cy = csManager.getCSVar(ctxX, stmt.getLValue());
                        var ctxOarrIdx = csManager.getArrayIndex(o);
                        addPFGEdge(ctxOarrIdx, cy);
                    });

                    processCall(varPtr, o);
                }
            }
        }
    }

    /**
     * Propagates pointsToSet to pt(pointer) and its PFG successors,
     * returns the difference set of pointsToSet and pt(pointer).
     */
    private PointsToSet propagate(Pointer pointer, PointsToSet pointsToSet) {
        var delta = PointsToSetFactory.make();
        for (var o: pointsToSet) {
            if (!pointer.getPointsToSet().contains(o)) {
                delta.addObject(o);
                pointer.getPointsToSet().addObject(o);
            }
        }

        if (delta.isEmpty()) return delta;

        for (var succ: pointerFlowGraph.getSuccsOf(pointer)) {
            workList.addEntry(succ, delta);
        }
        return delta;
    }

    /**
     * Processes instance calls when points-to set of the receiver variable changes.
     *
     * @param recv    the receiver variable
     * @param recvObj set of new discovered objects pointed by the variable.
     */
    private void processCall(CSVar recv, CSObj recvObj) {
        for (var invoke: recv.getVar().getInvokes()) {
            if (invoke.isStatic()) continue;
            var m = resolveCallee(recvObj, invoke);
            var currCtx = recv.getContext();
            var csCallSite = csManager.getCSCallSite(currCtx, invoke);

            var calleeCtx = contextSelector.selectContext(csCallSite, recvObj, m);
            var csCallee = csManager.getCSMethod(calleeCtx, m);

            workList.addEntry(csManager.getCSVar(calleeCtx, m.getIR().getThis()), PointsToSetFactory.make(recvObj));

            // System.out.println("new context "+calleeCtx+":::for @invoke: "+invoke
            //        +"\nby selectContext("+csCallSite+", "+recvObj+"\n");

            if (callGraph.addEdge(new Edge<>(CallGraphs.getCallKind(invoke), csCallSite, csCallee))) {
                addReachable(csCallee);
                for (int i = 0; i < m.getParamCount(); i++) {
                    addPFGEdge(
                        csManager.getCSVar(currCtx, invoke.getInvokeExp().getArg(i)),
                        csManager.getCSVar(calleeCtx, m.getIR().getParam(i))
                    );
                }

                if (invoke.getLValue() == null) continue;
                for (var retVar: m.getIR().getReturnVars()) {
                    addPFGEdge(
                        csManager.getCSVar(calleeCtx, retVar),
                        csManager.getCSVar(currCtx, invoke.getLValue())
                    );
                }
            }
        }
    }

    /**
     * Resolves the callee of a call site with the receiver object.
     *
     * @param recv the receiver object of the method call. If the callSite
     *             is static, this parameter is ignored (i.e., can be null).
     * @param callSite the call site to be resolved.
     * @return the resolved callee.
     */
    private JMethod resolveCallee(CSObj recv, Invoke callSite) {
        Type type = recv != null ? recv.getObject().getType() : null;
        return CallGraphs.resolveCallee(type, callSite);
    }

    PointerAnalysisResult getResult() {
        if (result == null) {
            result = new PointerAnalysisResultImpl(csManager, callGraph);
        }
        return result;
    }
}
