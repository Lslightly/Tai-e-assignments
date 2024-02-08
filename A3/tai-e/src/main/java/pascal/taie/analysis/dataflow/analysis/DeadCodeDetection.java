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

package pascal.taie.analysis.dataflow.analysis;

import pascal.taie.analysis.MethodAnalysis;
import pascal.taie.analysis.dataflow.analysis.constprop.CPFact;
import pascal.taie.analysis.dataflow.analysis.constprop.ConstantPropagation;
import pascal.taie.analysis.dataflow.fact.DataflowResult;
import pascal.taie.analysis.dataflow.fact.SetFact;
import pascal.taie.analysis.graph.cfg.CFG;
import pascal.taie.analysis.graph.cfg.CFGBuilder;
import pascal.taie.analysis.graph.cfg.Edge;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.*;
import pascal.taie.ir.stmt.AssignStmt;
import pascal.taie.ir.stmt.If;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.ir.stmt.SwitchStmt;

import java.util.*;

public class DeadCodeDetection extends MethodAnalysis {

    public static final String ID = "deadcode";

    public DeadCodeDetection(AnalysisConfig config) {
        super(config);
    }

    @Override
    public Set<Stmt> analyze(IR ir) {
        // obtain CFG
        CFG<Stmt> cfg = ir.getResult(CFGBuilder.ID);
        // obtain result of constant propagation
        DataflowResult<Stmt, CPFact> constants =
                ir.getResult(ConstantPropagation.ID);
        // obtain result of live variable analysis
        DataflowResult<Stmt, SetFact<Var>> liveVars =
                ir.getResult(LiveVariableAnalysis.ID);
        // keep statements (dead code) sorted in the resulting set
        var deadCode = controlFlowUnreachable(cfg);
        unreachableBranch(cfg, constants, deadCode);
        deadVariables(cfg, liveVars, deadCode);
        return deadCode;
//        var remainStmts = new TreeSet<Stmt>(Comparator.comparing(Stmt::getIndex));
//        remainStmts.addAll(ir.getStmts());
//        remainStmts.removeAll(deadCode);
//        return remainStmts;
    }


    /**
     * @return control-flow unreachable stmts
     */
    private TreeSet<Stmt> controlFlowUnreachable(CFG<Stmt> cfg) {
        TreeSet<Stmt> deadCodes = new TreeSet<>(Comparator.comparing(Stmt::getIndex));
        deadCodes.addAll(cfg.getNodes());
        deadCodes.remove(cfg.getEntry());
        deadCodes.remove(cfg.getExit());

        TreeSet<Stmt> visited = new TreeSet<>(Comparator.comparing(Stmt::getIndex));

        var worklist = new LinkedList<Stmt>();
        worklist.addLast(cfg.getEntry());
        while (!worklist.isEmpty()) {
            var top = worklist.removeFirst();
            if (!visited.contains(top)) {
                visited.add(top);
                for (var outEdge: cfg.getOutEdgesOf(top)) {
                    if (outEdge.getKind() == Edge.Kind.RETURN)
                        continue;
                    worklist.add(outEdge.getTarget());
                }
            }
        }
        deadCodes.removeAll(visited);

        return deadCodes;
    }

    /**
     * @return unreachable branch stmts
     */
    private void unreachableBranch(CFG<Stmt> cfg, DataflowResult<Stmt, CPFact> constants, TreeSet<Stmt> deadCodes) {
        for (var stmt: cfg) {
            if (!(stmt instanceof If || stmt instanceof SwitchStmt))
                continue;
            if (deadCodes.contains(stmt))
                continue;
            if (stmt instanceof If ifStmt) {
                IfUnreachable(ifStmt, cfg, constants, deadCodes);
                continue;
            }
            unreachableCases((SwitchStmt) stmt, cfg, constants, deadCodes);
        }

    }

    private void IfUnreachable(If ifStmt, CFG<Stmt> cfg, DataflowResult<Stmt, CPFact> constants, TreeSet<Stmt> deadCodes) {
        var cond = ifStmt.getCondition();
        var res = evalCondition(cond, constants.getInFact(ifStmt));
        if (!res.isConst)
            return ;
        Stmt trueStmt, falseStmt;
        trueStmt = ifStmt.getTarget();
        falseStmt = trueStmt;
        for (var succ: cfg.getSuccsOf(ifStmt)) {
            if (succ != trueStmt) {
                falseStmt = succ;
                break;
            }
        }
        if (res.value) { // if true goto S
            // remove all code in false branch
            // if falseStmt == trueStmt, then
            // there is no code in false branch
            // and therefore no code to be removed
            if (falseStmt != trueStmt) {
                markDeadStmtAndSuccs(falseStmt, cfg, deadCodes);
            } else {
                // do nothing
            }
            return ;
        }

        // if false goto S, remove S, S.succ, ...
        markDeadStmtAndSuccs(trueStmt, cfg, deadCodes);
    }

    /**
     * @param stmt Statement to be removed
     * @param cfg
     * @param deadCodes
     *
     * remove stmt and its following stmts which
     * have no live predecessors.
     */
    private void markDeadStmtAndSuccs(Stmt stmt, CFG<Stmt> cfg, TreeSet<Stmt> deadCodes) {
        deadCodes.add(stmt);
        var workList = new LinkedList<Stmt>();
        for (var succ: cfg.getOutEdgesOf(stmt)) {
            if (succ.getKind() == Edge.Kind.RETURN)
                continue;
            workList.addLast(succ.getTarget());
        }

        while (!workList.isEmpty()) {
            var top = workList.removeFirst();
            boolean allPredDead = true;
            for (var pred: cfg.getPredsOf(top)) {
                allPredDead &= deadCodes.contains(pred);
            }
            if (allPredDead) {
                deadCodes.add(top);
                for (var succ: cfg.getOutEdgesOf(top)) {
                    if (succ.getKind() == Edge.Kind.RETURN)
                        continue;
                    workList.addLast(succ.getTarget());
                }
            }
        }
    }

    class Result {
        boolean isConst;
        boolean value;
    }
    /**
     * @return {isConst, value}
     */
    private Result evalCondition(ConditionExp cond, CPFact constants) {
        var res = new Result();
        var op1 = constants.get(cond.getOperand1());
        var op2 = constants.get(cond.getOperand2());
        var op = cond.getOperator();
        if (op1.isConstant() && op2.isConstant()) {
            var op1c = op1.getConstant();
            var op2c = op2.getConstant();
            res.isConst = true;
            res.value = switch (op) {
                case EQ -> op1c == op2c;
                case NE -> op1c != op2c;
                case LT -> op1c < op2c;
                case GT -> op1c > op2c;
                case LE -> op1c <= op2c;
                case GE -> op1c >= op2c;
            };
        } else {
            res.isConst = false;
            res.value = false;
        }
        return res;
    }

    private void unreachableCases(SwitchStmt stmt, CFG<Stmt> cfg, DataflowResult<Stmt, CPFact> constants, TreeSet<Stmt> resDeadCode) {
        var switchVar = stmt.getVar();
        if (!constants.getInFact(stmt).get(switchVar).isConstant())
            return;

        var deadCases = new TreeSet<Stmt>(Comparator.comparing(Stmt::getIndex));

        var c = constants.getInFact(stmt).get(switchVar).getConstant();
        Stmt selectedStmt = null;
        for (var pair: stmt.getCaseTargets()) {
            var caseValue = pair.first();
            var caseStmt = pair.second();

            markDeadStmtAndSuccs(caseStmt, cfg, deadCases);
            if (caseValue == c) {
                selectedStmt = caseStmt;
            }
        }

        markDeadStmtAndSuccs(stmt.getDefaultTarget(), cfg, deadCases);
        if (selectedStmt == null) {
            selectedStmt = stmt.getDefaultTarget();
        }

        var workList = new LinkedList<Stmt>();
        workList.addLast(selectedStmt);

        while (!workList.isEmpty()) {
            var top = workList.removeFirst();
            if (deadCases.contains(top)) {
                deadCases.remove(top);
                for (var succ: cfg.getSuccsOf(top)) {
                    workList.addLast(succ);
                }
            }
        }

        resDeadCode.addAll(deadCases);
    }

    private void deadVariables(CFG<Stmt> cfg, DataflowResult<Stmt, SetFact<Var>> liveVars, TreeSet<Stmt> deadCodes) {
        for (var stmt: cfg) {
            if (!(stmt instanceof AssignStmt))
                continue;
            if (deadCodes.contains(stmt))
                continue;
            AssignStmt<Var, RValue> assign = (AssignStmt<Var, RValue>)stmt;
            var lhsVar = assign.getLValue();
            if (!hasNoSideEffect(assign.getRValue()))
                continue;
            var shouldLive = liveVars.getOutFact(stmt);
            if (!shouldLive.contains(lhsVar)) {
                deadCodes.add(stmt);
            }
        }
    }

    /**
     * @return true if given RValue has no side effect, otherwise false.
     */
    private static boolean hasNoSideEffect(RValue rvalue) {
        // new expression modifies the heap
        if (rvalue instanceof NewExp ||
                // cast may trigger ClassCastException
                rvalue instanceof CastExp ||
                // static field access may trigger class initialization
                // instance field access may trigger NPE
                rvalue instanceof FieldAccess ||
                // array access may trigger NPE
                rvalue instanceof ArrayAccess) {
            return false;
        }
        if (rvalue instanceof ArithmeticExp) {
            ArithmeticExp.Op op = ((ArithmeticExp) rvalue).getOperator();
            // may trigger DivideByZeroException
            return op != ArithmeticExp.Op.DIV && op != ArithmeticExp.Op.REM;
        }
        return true;
    }
}
