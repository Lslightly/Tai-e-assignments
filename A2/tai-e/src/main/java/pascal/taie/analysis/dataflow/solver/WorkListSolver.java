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

package pascal.taie.analysis.dataflow.solver;

import pascal.taie.analysis.dataflow.analysis.DataflowAnalysis;
import pascal.taie.analysis.dataflow.fact.DataflowResult;
import pascal.taie.analysis.graph.cfg.CFG;

import java.util.LinkedList;

class WorkListSolver<Node, Fact> extends Solver<Node, Fact> {

    WorkListSolver(DataflowAnalysis<Node, Fact> analysis) {
        super(analysis);
    }

    @Override
    protected void doSolveForward(CFG<Node> cfg, DataflowResult<Node, Fact> result) {
        var worklist = new LinkedList<Node>();
        var entry = cfg.getEntry();
        for (var node: cfg) {
            if (node != entry) {
                worklist.add(node);
            }
        }
        while (!worklist.isEmpty()) {
            var node = worklist.pop();
            System.out.println("analyzing " + node
            + "\npred: " + cfg.getPredsOf(node)
            + "\nsucc: " + cfg.getSuccsOf(node)
            + "\nin: " + result.getInFact(node)
            + "\nout: " + result.getOutFact(node));
            for (var pred: cfg.getPredsOf(node)) {
                analysis.meetInto(result.getOutFact(pred), result.getInFact(node));
            }
            System.out.println("after meetInto " + node
            + "\nin: " + result.getInFact(node));
            if (analysis.transferNode(node, result.getInFact(node), result.getOutFact(node))) {
                worklist.addAll(cfg.getSuccsOf(node));
                System.out.println("push to work list " + cfg.getSuccsOf(node));
            }
            System.out.println("after transferNode " + node
                    + "\nout: " + result.getOutFact(node));
        }
    }

    @Override
    protected void doSolveBackward(CFG<Node> cfg, DataflowResult<Node, Fact> result) {
        throw new UnsupportedOperationException();
    }
}
