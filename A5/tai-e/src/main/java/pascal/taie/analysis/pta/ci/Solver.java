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
import pascal.taie.analysis.graph.callgraph.*;
import pascal.taie.analysis.pta.core.heap.HeapModel;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.ir.exp.InvokeExp;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.proginfo.MethodRef;
import pascal.taie.ir.stmt.*;
import pascal.taie.language.classes.ClassHierarchy;
import pascal.taie.language.classes.JMethod;
import pascal.taie.util.AnalysisException;
import pascal.taie.language.type.Type;

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
     */
    private void addReachable(JMethod method) {
        // TODO - finish me
        // System.out.println("addReachable " + method);
        if (!callGraph.addReachableMethod(method)) {
            return;
        }
        for (Stmt stmt : method.getIR().getStmts()) {
            // System.out.println("\t" + stmt);
            if (stmt instanceof AssignStmt<?,?>) {
                if (stmt instanceof New newStmt) {
                    if (newStmt.getDef().isPresent()) {
                        if (newStmt.getDef().get() instanceof Var v) {
                            // System.out.println("\t\t" + v);
                            workList.addEntry(pointerFlowGraph.getVarPtr(v), new PointsToSet(heapModel.getObj(newStmt)));
                        }
                    }
                }
                if (stmt instanceof Copy copyStmt) {
                    addPFGEdge(pointerFlowGraph.getVarPtr((Var) copyStmt.getUses().get(0)), pointerFlowGraph.getVarPtr((Var) copyStmt.getDef().get()));
                }
            }
        }
    }

    /**
     * Processes statements in new reachable methods.
     */
    private class StmtProcessor implements StmtVisitor<Void> {
        // TODO - if you choose to implement addReachable()
        //  via visitor pattern, then finish me
    }

    /**
     * Adds an edge "source -> target" to the PFG.
     */
    private void addPFGEdge(Pointer source, Pointer target) {
        // System.out.println("Adding edge " + source + " " + target);
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
        WorkList.Entry e;
        while ((e = workList.pollEntry()) != null) {
            // System.out.println("*** " + e);
            PointsToSet d = propagate(e.pointer(), e.pointsToSet());
            if (e.pointer() instanceof VarPtr ePtr) {
                d.forEach(obj -> {
                    //stmtSet.forEach(stmt -> {
                    //});
                    processCall(ePtr.getVar(), obj);
                });
            }
        }
    }

    /**
     * Propagates pointsToSet to pt(pointer) and its PFG successors,
     * returns the difference set of pointsToSet and pt(pointer).
     */
    private PointsToSet propagate(Pointer pointer, PointsToSet pointsToSet) {
        PointsToSet res = new PointsToSet();
        if (!pointsToSet.isEmpty()) {
            // System.out.println("--- " + pointer + " & " + pointer.getPointsToSet());
            pointsToSet.forEach(obj -> {
                if (pointer.getPointsToSet().addObject(obj)) {
                    res.addObject(obj);
                }
            });
            // System.out.println("--- " + pointerFlowGraph.getSuccsOf(pointer));
            if (!res.isEmpty()) {
                pointerFlowGraph.getSuccsOf(pointer).forEach(s -> {
                    workList.addEntry(s, pointsToSet);
                });
            }
            // System.out.println("--- " + pointer + " & " + pointer.getPointsToSet());
        }
        return res;
    }

    /**
     * Processes instance calls when points-to set of the receiver variable changes.
     *
     * @param var the variable that holds receiver objects
     * @param recv a new discovered object pointed by the variable.
     */
    private void processCall(Var var, Obj recv) {
        // System.out.println("Call " + var + " - " + recv);
        var.getInvokes().forEach(invokeStmt -> {
            JMethod callee = resolveCallee(recv, invokeStmt);
            // System.out.println("Set for var = " + var + " : " + pointerFlowGraph.getVarPtr(callee.getIR().getThis()).getPointsToSet());
            // System.out.println("Stmt is " + invokeStmt);
            // System.out.println("Add entry " + pointerFlowGraph.getVarPtr(callee.getIR().getThis()) + " | " + recv);
            workList.addEntry(pointerFlowGraph.getVarPtr(callee.getIR().getThis()), new PointsToSet(recv));
            if (callGraph.addEdge(new Edge<>(CallGraphs.getCallKind(invokeStmt), invokeStmt, callee))) {
                addReachable(callee);
                for (int i = 0; i < invokeStmt.getInvokeExp().getArgCount(); i++) {
                    addPFGEdge(pointerFlowGraph.getVarPtr(invokeStmt.getInvokeExp().getArg(i)), pointerFlowGraph.getVarPtr(callee.getIR().getParam(i)));
                }
                callee.getIR().getReturnVars().forEach(r -> {
                    addPFGEdge(pointerFlowGraph.getVarPtr(r), pointerFlowGraph.getVarPtr(invokeStmt.getResult()));
                });
            }
        });
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
