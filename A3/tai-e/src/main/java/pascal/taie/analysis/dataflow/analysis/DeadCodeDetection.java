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
import pascal.taie.analysis.dataflow.analysis.constprop.Value;
import pascal.taie.analysis.dataflow.fact.DataflowResult;
import pascal.taie.analysis.dataflow.fact.SetFact;
import pascal.taie.analysis.graph.cfg.CFG;
import pascal.taie.analysis.graph.cfg.CFGBuilder;
import pascal.taie.analysis.graph.cfg.Edge;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.*;
import pascal.taie.ir.stmt.*;
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
        Set<Stmt> deadCode = new TreeSet<>(Comparator.comparing(Stmt::getIndex));
        Set<Edge<Stmt>> ignoreEdges = new HashSet<>();

        // If and Branch Statement Unreachable Branches
        for (Stmt n : cfg.getNodes()) {
            if (n instanceof If) {
                Value res = ConstantPropagation.evaluate(((If) n).getCondition(), constants.getInFact(n));
                if (res.isConstant()) {
                    if (res.getConstant() == 0) {
                        for (Edge<Stmt> e : cfg.getOutEdgesOf(n)) {
                            if (e.getKind() == Edge.Kind.IF_TRUE) {
                                ignoreEdges.add(e);
                            }
                        }
                    } else {
                        for (Edge<Stmt> e : cfg.getOutEdgesOf(n)) {
                            if (e.getKind() == Edge.Kind.IF_FALSE) {
                                ignoreEdges.add(e);
                            }
                        }
                    }
                }
            }
            if (n instanceof SwitchStmt) {
                Value res = constants.getInFact(n).get(((SwitchStmt) n).getVar());
                if (res.isConstant()) {
                    boolean seen = false;
                    for (Edge<Stmt> e : cfg.getOutEdgesOf(n)) {
                        if (e.getKind() == Edge.Kind.SWITCH_CASE) {
                            if (e.getCaseValue() == res.getConstant()) {
                                seen = true;
                            } else {
                                ignoreEdges.add(e);
                            }
                        }
                    }
                    if (seen) {
                        for (Edge<Stmt> e : cfg.getOutEdgesOf(n)) {
                            if (e.getKind() == Edge.Kind.SWITCH_DEFAULT) {
                                ignoreEdges.add(e);
                            }
                        }
                    }
                }
            }
        }

        for (Stmt n : cfg.getNodes()) {
            if (n instanceof AssignStmt<?,?>) {
                if (!liveVars.getOutFact(n).contains((Var) ((AssignStmt<?,?>) n).getLValue())) {
                    if (hasNoSideEffect(((AssignStmt<?, ?>) n).getRValue())) {
                        deadCode.add(n);
                    }
                }
            }
        }

        // Control Flow Unreachable Nodes Detection
        LinkedList<Stmt> reachable = new LinkedList<>();
        Set<Stmt> unseen = new TreeSet<>(Comparator.comparing(Stmt::getIndex));
        unseen.addAll(cfg.getNodes());

        unseen.remove(cfg.getEntry());
        reachable.add(cfg.getEntry());
        while (!reachable.isEmpty()) {
            Stmt n = reachable.pop();
            for (Edge<Stmt> e : cfg.getOutEdgesOf(n)) {
                if (!ignoreEdges.contains(e) && unseen.contains(e.getTarget())) {
                    reachable.add(e.getTarget());
                    unseen.remove(e.getTarget());
                }
            }
        }
        unseen.remove(cfg.getExit());

        deadCode.addAll(unseen);

        return deadCode;
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
