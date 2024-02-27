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

package pascal.taie.analysis.dataflow.inter;

import pascal.taie.analysis.dataflow.fact.DataflowResult;
import pascal.taie.analysis.graph.icfg.ICFG;
import pascal.taie.util.collection.SetQueue;

import java.util.*;
import java.util.stream.Collectors;

/**
 * Solver for inter-procedural data-flow analysis.
 * The workload of inter-procedural analysis is heavy, thus we always
 * adopt work-list algorithm for efficiency.
 */
class InterSolver<Method, Node, Fact> {

    private final InterDataflowAnalysis<Node, Fact> analysis;

    private final ICFG<Method, Node> icfg;

    private DataflowResult<Node, Fact> result;

    private Queue<Node> workList;

    InterSolver(InterDataflowAnalysis<Node, Fact> analysis,
                ICFG<Method, Node> icfg) {
        this.analysis = analysis;
        this.icfg = icfg;
    }

    DataflowResult<Node, Fact> solve() {
        result = new DataflowResult<>();
        initialize();
        doSolve();
        return result;
    }

    private void initialize() {
        var entryNodeForEntryMethod = getEntryMethodsEntryNodes();
        for (var entryNode: entryNodeForEntryMethod) {
            result.setInFact(entryNode, analysis.newInitialFact());
            result.setOutFact(entryNode, analysis.newBoundaryFact(entryNode));
        }
        for (var node: icfg) {
            if (!entryNodeForEntryMethod.contains(node)) {
                result.setInFact(node, analysis.newInitialFact());
                result.setOutFact(node, analysis.newInitialFact());
            }
        }
    }

    private HashSet<Node> getEntryMethodsEntryNodes() {
        var entryNodeSet = new HashSet<Node>();
        icfg.entryMethods().forEach((entry) -> {
            entryNodeSet.add(icfg.getEntryOf(entry));
        });
        return entryNodeSet;
    }

    private void doSolve() {
        workList = new LinkedList<>();
        workList.addAll(icfg.getNodes());
        while (!workList.isEmpty()) {
            var top = workList.remove();
            System.out.println("get " + top);

            // reset in fact
            for (var inEdge: icfg.getInEdgesOf(top)) {
                var inNode = inEdge.getSource();
                var infact = analysis.transferEdge(inEdge, result.getOutFact(inNode));
                analysis.meetInto(infact, result.getInFact(top));
            }
            // transfer node
            var changed = analysis.transferNode(top, result.getInFact(top), result.getOutFact(top));
            System.out.println("transfer node for " + top + " " + changed
                    + " with\nin: " + result.getInFact(top)
                    + "\nout: " + result.getOutFact(top));

            // push succ if changed
            if (changed) {
                System.out.println("pushed " + icfg.getSuccsOf(top));
                workList.addAll(icfg.getSuccsOf(top));
            }
        }
    }
}
