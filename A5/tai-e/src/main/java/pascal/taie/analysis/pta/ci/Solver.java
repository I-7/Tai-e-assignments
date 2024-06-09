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
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.*;
import pascal.taie.language.classes.ClassHierarchy;
import pascal.taie.language.classes.JMethod;
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
        if (!callGraph.addReachableMethod(method)) {
            return;
        }
        for (Stmt stmt : method.getIR().getStmts()) {
            if (stmt instanceof Invoke invokeStmt) {
                if (invokeStmt.isStatic()) {
                    JMethod callee = resolveCallee(null, invokeStmt);
                    if (callGraph.addEdge(new Edge<>(CallGraphs.getCallKind(invokeStmt), invokeStmt, callee))) {
                        addReachable(callee);
                        for (int i = 0; i < invokeStmt.getInvokeExp().getArgCount(); i++) {
                            addPFGEdge(pointerFlowGraph.getVarPtr(invokeStmt.getInvokeExp().getArg(i)), pointerFlowGraph.getVarPtr(callee.getIR().getParam(i)));
                        }
                        callee.getIR().getReturnVars().forEach(r -> {
                            if (invokeStmt.getResult() != null) {
                                addPFGEdge(pointerFlowGraph.getVarPtr(r), pointerFlowGraph.getVarPtr(invokeStmt.getResult()));
                            }
                        });
                    }
                }
            }
            if (stmt instanceof AssignStmt<?,?>) {
                if (stmt instanceof New newStmt) {
                    if (newStmt.getDef().isPresent()) {
                        if (newStmt.getDef().get() instanceof Var v) {
                            workList.addEntry(pointerFlowGraph.getVarPtr(v), new PointsToSet(heapModel.getObj(newStmt)));
                        }
                    }
                }
                if (stmt instanceof Copy copyStmt) {
                    addPFGEdge(pointerFlowGraph.getVarPtr((Var) copyStmt.getUses().get(0)), pointerFlowGraph.getVarPtr((Var) copyStmt.getDef().get()));
                }
                if (stmt instanceof StoreField sf) {
                    if (sf.isStatic()) {
                        addPFGEdge(pointerFlowGraph.getVarPtr((Var) sf.getUses().get(0)), pointerFlowGraph.getStaticField(sf.getFieldRef().resolve()));
                    }
                }
                if (stmt instanceof LoadField lf) {
                    if (lf.isStatic()) {
                        addPFGEdge(pointerFlowGraph.getStaticField(lf.getFieldRef().resolve()), pointerFlowGraph.getVarPtr((Var) lf.getDef().get()));
                    }
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
            PointsToSet d = propagate(e.pointer(), e.pointsToSet());
            if (e.pointer() instanceof VarPtr ePtr) {
                d.forEach(obj -> {
                    ePtr.getVar().getStoreFields().forEach(sf -> {
                        addPFGEdge(pointerFlowGraph.getVarPtr(sf.getRValue()), pointerFlowGraph.getInstanceField(obj, sf.getFieldRef().resolve()));
                    });
                    ePtr.getVar().getLoadFields().forEach(lf -> {
                        addPFGEdge(pointerFlowGraph.getInstanceField(obj, lf.getFieldRef().resolve()), pointerFlowGraph.getVarPtr(lf.getLValue()));
                    });
                    ePtr.getVar().getStoreArrays().forEach(sa -> {
                        addPFGEdge(pointerFlowGraph.getVarPtr(sa.getRValue()), pointerFlowGraph.getArrayIndex(obj));
                    });
                    ePtr.getVar().getLoadArrays().forEach(la -> {
                        addPFGEdge(pointerFlowGraph.getArrayIndex(obj), pointerFlowGraph.getVarPtr(la.getLValue()));
                    });
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
            pointsToSet.forEach(obj -> {
                if (pointer.getPointsToSet().addObject(obj)) {
                    res.addObject(obj);
                }
            });
            if (!res.isEmpty()) {
                pointerFlowGraph.getSuccsOf(pointer).forEach(s -> {
                    workList.addEntry(s, pointsToSet);
                });
            }
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
        var.getInvokes().forEach(invokeStmt -> {
            if (invokeStmt.isStatic()) {
                return;
            }
            JMethod callee = resolveCallee(recv, invokeStmt);
            workList.addEntry(pointerFlowGraph.getVarPtr(callee.getIR().getThis()), new PointsToSet(recv));
            if (callGraph.addEdge(new Edge<>(CallGraphs.getCallKind(invokeStmt), invokeStmt, callee))) {
                addReachable(callee);
                for (int i = 0; i < invokeStmt.getInvokeExp().getArgCount(); i++) {
                    addPFGEdge(pointerFlowGraph.getVarPtr(invokeStmt.getInvokeExp().getArg(i)), pointerFlowGraph.getVarPtr(callee.getIR().getParam(i)));
                }
                callee.getIR().getReturnVars().forEach(r -> {
                    if (invokeStmt.getResult() != null) {
                        addPFGEdge(pointerFlowGraph.getVarPtr(r), pointerFlowGraph.getVarPtr(invokeStmt.getResult()));
                    }
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
