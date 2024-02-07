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

package pascal.taie.analysis.dataflow.analysis.constprop;

import fj.P;
import pascal.taie.analysis.dataflow.analysis.AbstractDataflowAnalysis;
import pascal.taie.analysis.graph.cfg.CFG;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.ArithmeticExp;
import pascal.taie.ir.exp.BinaryExp;
import pascal.taie.ir.exp.BitwiseExp;
import pascal.taie.ir.exp.ConditionExp;
import pascal.taie.ir.exp.Exp;
import pascal.taie.ir.exp.IntLiteral;
import pascal.taie.ir.exp.ShiftExp;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.DefinitionStmt;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.language.type.PrimitiveType;
import pascal.taie.language.type.Type;
import pascal.taie.util.AnalysisException;

public class ConstantPropagation extends
        AbstractDataflowAnalysis<Stmt, CPFact> {

    public static final String ID = "constprop";

    public ConstantPropagation(AnalysisConfig config) {
        super(config);
    }

    @Override
    public boolean isForward() {
        return true;
    }

    @Override
    public CPFact newBoundaryFact(CFG<Stmt> cfg) {
        var ir = cfg.getIR();
        var res = new CPFact();
        for (var param: ir.getParams()) {
            res.update(param, Value.getNAC());
        }
        return res;
    }

    @Override
    public CPFact newInitialFact() {
        return new CPFact();
    }

    @Override
    public void meetInto(CPFact fact, CPFact target) {
        fact.forEach((v, state) -> {
            var targetState = target.get(v);
            var newState = meetValue(state, targetState);
            if (newState != targetState) {
                target.update(v, newState);
            }
        });
    }

    /**
     * Meets two Values.
     */
    public Value meetValue(Value v1, Value v2) {
        if (v1.isUndef()) {
            return v2;
        } else if (v1.isNAC()) {
            return v1;
        } else {
            if (v2.isUndef()) {
                return v1;
            } else if (v2.isNAC()) {
                return v2;
            }
            var v1c = v1.getConstant();
            var v2c = v2.getConstant();
            if (v1c == v2c) {
                return v1;
            } else {
                return Value.getNAC();
            }
        }
    }

    @Override
    public boolean transferNode(Stmt stmt, CPFact in, CPFact out) {
        var oldOut = out.copy();
        out.copyFrom(in);

        if (!(stmt instanceof DefinitionStmt<?,?> defStmt)) {
            return !out.equals(oldOut);
        }

        if (!(defStmt.getLValue() instanceof Var def)) {
            return !out.equals(oldOut);
        }
        if (!canHoldInt(def)) {
            return !out.equals(oldOut);
        }

        var exp = defStmt.getRValue();
        var tmp = evaluate(exp, in);
        switch ((PrimitiveType)def.getType()) {
            case BYTE:
                out.update(def, Value.makeConstant((byte)tmp.getConstant()));
                break;
            case SHORT:
                out.update(def, Value.makeConstant((short)tmp.getConstant()));
                break;
            case CHAR:
                out.update(def, Value.makeConstant((char)tmp.getConstant()));
                break;
            case INT:
            case BOOLEAN:
                out.update(def, tmp);
                break;
        }
        out.update(def, tmp);
        System.out.println("oldOut: " + oldOut
        + "\nnew Out: " + out);
        return !out.equals(oldOut);
    }

    /**
     * @return true if the given variable can hold integer value, otherwise false.
     */
    public static boolean canHoldInt(Var var) {
        Type type = var.getType();
        if (type instanceof PrimitiveType) {
            switch ((PrimitiveType) type) {
                case BYTE:
                case SHORT:
                case INT:
                case CHAR:
                case BOOLEAN:
                    return true;
            }
        }
        return false;
    }

    /**
     * Evaluates the {@link Value} of given expression.
     *
     * @param exp the expression to be evaluated
     * @param in  IN fact of the statement
     * @return the resulting {@link Value}
     */
    public static Value evaluate(Exp exp, CPFact in) {
        if (exp instanceof IntLiteral) {
            return Value.makeConstant(((IntLiteral) exp).getValue());
        } else if (exp instanceof Var) {
            return in.get((Var)exp);
        } else if (exp instanceof BinaryExp) {
            try {
                var bexp = (BinaryExp) exp;
                var op1 = bexp.getOperand1();
                var op2 = bexp.getOperand2();
                if (!canHoldInt(op1) || !canHoldInt(op2)) {
                    return Value.getNAC();
                }
                var op1State = in.get(op1);
                var op2State = in.get(op2);
                if (op1State.isNAC() || op2State.isNAC()) {
                    return Value.getNAC();
                }
                if (op1State.isUndef() || op2State.isUndef()) {
                    return Value.getUndef();
                }
                var op1c = op1State.getConstant();
                var op2c = op2State.getConstant();
                op1c = truncBits(op1.getType(), op1c);
                op2c = truncBits(op2.getType(), op2c);
                var op = bexp.getOperator();
                var res = 0;
                if (bexp instanceof ArithmeticExp) {
                    if (op == ArithmeticExp.Op.ADD) {
                        res = op1c + op2c;
                    } else if (op == ArithmeticExp.Op.SUB) {
                        res = op1c - op2c;
                    } else if (op == ArithmeticExp.Op.MUL) {
                        res = op1c * op2c;
                    } else if (op == ArithmeticExp.Op.DIV) {
                        if (op2c == 0) {
                            return Value.getUndef();
                        }
                        res = op1c / op2c;
                    } else if (op == ArithmeticExp.Op.REM) {
                        if (op2c == 0) {
                            return Value.getUndef();
                        }
                        res = op1c % op2c;
                    }
                } else if (bexp instanceof BitwiseExp) {
                    if (op == BitwiseExp.Op.OR) {
                        res = op1c | op2c;
                    } else if (op == BitwiseExp.Op.AND) {
                        res = op1c & op2c;
                    } else if (op == BitwiseExp.Op.XOR) {
                        res = op1c ^ op2c;
                    }
                } else if (bexp instanceof ConditionExp) {
                    BooleanToIntFunction bool2int = (boolean b) -> b ? 1 : 0;
                    if (op == ConditionExp.Op.EQ) {
                        res = bool2int.apply(op1c == op2c);
                    } else if (op == ConditionExp.Op.NE) {
                        res = bool2int.apply(op1c != op2c);
                    } else if (op == ConditionExp.Op.LT) {
                        res = bool2int.apply(op1c < op2c);
                    } else if (op == ConditionExp.Op.GT) {
                        res = bool2int.apply(op1c > op2c);
                    } else if (op == ConditionExp.Op.LE) {
                        res = bool2int.apply(op1c <= op2c);
                    } else if (op == ConditionExp.Op.GE) {
                        res = bool2int.apply(op1c >= op2c);
                    }
                } else if (bexp instanceof ShiftExp) {
                    if (op == ShiftExp.Op.SHL) {
                        res = op1c << op2c;
                    } else if (op == ShiftExp.Op.SHR) {
                        res = op1c >> op2c;
                    } else if (op == ShiftExp.Op.USHR) {
                        res = op1c >>> op2c;
                    }
                }
                return Value.makeConstant(res);
            } catch (Exception e) {
                return Value.getUndef();
            }
        } else {
            return Value.getNAC();
        }
    }

    private static int truncBits(Type t, int v) {
        return switch ((PrimitiveType) t) {
            case BYTE -> (byte) v;
            case SHORT -> (short) v;
            case CHAR -> (char) v;
            case BOOLEAN -> {
                BooleanToIntFunction bool2int = (boolean b) -> b ? 1 : 0;
                yield bool2int.apply(v != 0);
            }
            default -> v;
        };
    }
}

@FunctionalInterface
interface BooleanToIntFunction {
    int apply(boolean b);
}