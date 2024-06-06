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

import pascal.taie.analysis.dataflow.analysis.AbstractDataflowAnalysis;
import pascal.taie.analysis.graph.cfg.CFG;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.exp.*;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.language.type.PrimitiveType;
import pascal.taie.language.type.Type;

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
        CPFact res = new CPFact();
        for (Var v : cfg.getIR().getParams()) {
            if (!canHoldInt(v)) {
                continue;
            }
            try {
                res.update(v, Value.getNAC());
            } catch (ClassCastException ignored) {

            }
        }
        return res;
    }

    @Override
    public CPFact newInitialFact() {
        return new CPFact();
    }

    @Override
    public void meetInto(CPFact fact, CPFact target) {
        fact.entries().forEach(varValueEntry ->
                target.update(
                        varValueEntry.getKey(),
                        meetValue(varValueEntry.getValue(), target.get(varValueEntry.getKey()))
                )
        );
    }

    /**
     * Meets two Values.
     */
    public Value meetValue(Value v1, Value v2) {
        if (v1.isNAC() || v2.isNAC()) {
            return Value.getNAC();
        }
        if (v1.isUndef() && v2.isUndef()) {
            return Value.getUndef();
        }
        if (v1.isUndef()) {
            return Value.makeConstant(v2.getConstant());
        }
        if (v2.isUndef()) {
            return Value.makeConstant(v1.getConstant());
        }
        if (v1.getConstant() == v2.getConstant()) {
            return Value.makeConstant(v1.getConstant());
        }
        return Value.getNAC();
    }

    @Override
    public boolean transferNode(Stmt stmt, CPFact in, CPFact out) {
        CPFact cur = in.copy();
        if (stmt.getDef().isPresent()) {
            stmt.getUses().forEach(rValue -> {
                try {
                    Value tmp = evaluate(rValue, in);
                    if (tmp != null) {
                        if (canHoldInt((Var) stmt.getDef().get())) {
                            cur.update((Var) stmt.getDef().get(), tmp);
                        }
                    }
                } catch (ClassCastException ignored) {

                }
            });
        }
        return out.copyFrom(cur);
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
        if (exp instanceof Var) {
            return in.get((Var) exp);
        }
        if (exp instanceof IntLiteral) {
            return Value.makeConstant(((IntLiteral) exp).getValue());
        }
        if (exp instanceof BinaryExp) {
            return evaluateBinaryExp((BinaryExp) exp, in);
        }
        return Value.getNAC();
    }

    private static Value evaluateBinaryExp(BinaryExp exp, CPFact in) {
        if (in.get(exp.getOperand1()).isUndef() || in.get(exp.getOperand2()).isUndef()) {
            return Value.getUndef();
        }
        if (in.get(exp.getOperand1()).isConstant()) {
            Value tmp = evaluateFromOperand1(exp.getOperator(), in.get(exp.getOperand1()).getConstant());
            if (tmp != null) {
                return tmp;
            }
        }
        if (in.get(exp.getOperand2()).isConstant()) {
            Value tmp = evaluateFromOperand2(exp.getOperator(), in.get(exp.getOperand2()).getConstant());
            if (tmp != null) {
                return tmp;
            }
        }
        if (in.get(exp.getOperand1()).isNAC() || in.get(exp.getOperand2()).isNAC()) {
            return Value.getNAC();
        }
        int x = in.get(exp.getOperand1()).getConstant();
        int y = in.get(exp.getOperand2()).getConstant();
        if (exp.getOperator() == ArithmeticExp.Op.ADD) {
            return Value.makeConstant(x + y);
        }
        if (exp.getOperator() == BitwiseExp.Op.AND) {
            return Value.makeConstant(x & y);
        }
        if (exp.getOperator() == ArithmeticExp.Op.DIV) {
            return Value.makeConstant(x / y);
        }
        if (exp.getOperator() == ConditionExp.Op.EQ) {
            return Value.makeConstant(x == y ? 1 : 0);
        }
        if (exp.getOperator() == ConditionExp.Op.GE) {
            return Value.makeConstant(x >= y ? 1 : 0);
        }
        if (exp.getOperator() == ConditionExp.Op.GT) {
            return Value.makeConstant(x > y ? 1 : 0);
        }
        if (exp.getOperator() == ConditionExp.Op.LE) {
            return Value.makeConstant(x <= y ? 1 : 0);
        }
        if (exp.getOperator() == ConditionExp.Op.LT) {
            return Value.makeConstant(x < y ? 1 : 0);
        }
        if (exp.getOperator() == ArithmeticExp.Op.MUL) {
            return Value.makeConstant(x * y);
        }
        if (exp.getOperator() == ConditionExp.Op.NE) {
            return Value.makeConstant(x != y ? 1 : 0);
        }
        if (exp.getOperator() == BitwiseExp.Op.OR) {
            return Value.makeConstant(x | y);
        }
        if (exp.getOperator() == ArithmeticExp.Op.REM) {
            return Value.makeConstant(x % y);
        }
        if (exp.getOperator() == ShiftExp.Op.SHL) {
            return Value.makeConstant(x << y);
        }
        if (exp.getOperator() == ShiftExp.Op.SHR) {
            return Value.makeConstant(x >> y);
        }
        if (exp.getOperator() == ArithmeticExp.Op.SUB) {
            return Value.makeConstant(x - y);
        }
        if (exp.getOperator() == ShiftExp.Op.USHR) {
            return Value.makeConstant(x >>> y);
        }
        return null;
    }

    private static Value evaluateFromOperand1(BinaryExp.Op op, int val) {
        if (op == BitwiseExp.Op.AND && val == 0) {
            return Value.makeConstant(0);
        }
        if (op == ArithmeticExp.Op.MUL && val == 0) {
            return Value.makeConstant(0);
        }
        if (op == ShiftExp.Op.SHL && val == 0) {
            return Value.makeConstant(0);
        }
        if (op == ShiftExp.Op.SHR && val == 0) {
            return Value.makeConstant(0);
        }
        if (op == ShiftExp.Op.USHR && val == 0) {
            return Value.makeConstant(0);
        }
        return null;
    }

    private static Value evaluateFromOperand2(BinaryExp.Op op, int val) {
        if (op == BitwiseExp.Op.AND && val == 0) {
            return Value.makeConstant(0);
        }
        if (op == ArithmeticExp.Op.MUL && val == 0) {
            return Value.makeConstant(0);
        }
        return null;
    }
}
