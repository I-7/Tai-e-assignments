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
import pascal.taie.ir.stmt.*;
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
        if (!callGraph.addReachableMethod(csMethod)) {
            return;
        }
        for (Stmt stmt : csMethod.getMethod().getIR().getStmts()) {
            if (stmt instanceof Invoke invokeStmt) {
                if (invokeStmt.isStatic()) {
                    JMethod callee = resolveCallee(null, invokeStmt);
                    Context c = csMethod.getContext();
                    Context ct = contextSelector.selectContext(csManager.getCSCallSite(c, invokeStmt), callee);
                    if (callGraph.addEdge(new Edge<>(CallGraphs.getCallKind(invokeStmt), csManager.getCSCallSite(c, invokeStmt), csManager.getCSMethod(ct, callee)))) {
                        addReachable(csManager.getCSMethod(ct, callee));
                        for (int i = 0; i < invokeStmt.getInvokeExp().getArgCount(); i++) {
                            addPFGEdge(
                                    csManager.getCSVar(c, invokeStmt.getInvokeExp().getArg(i)),
                                    csManager.getCSVar(ct, callee.getIR().getParam(i))
                            );
                        }
                        callee.getIR().getReturnVars().forEach(r -> {
                            if (invokeStmt.getResult() != null) {
                                addPFGEdge(
                                        csManager.getCSVar(ct, r),
                                        csManager.getCSVar(c, invokeStmt.getResult())
                                );
                            }
                        });
                    }
                }
            }
            if (stmt instanceof AssignStmt<?,?>) {
                if (stmt instanceof New newStmt) {
                    if (newStmt.getDef().isPresent()) {
                        if (newStmt.getDef().get() instanceof Var v) {
                            Obj obj = heapModel.getObj(newStmt);
                            workList.addEntry(
                                    csManager.getCSVar(csMethod.getContext(), v),
                                    PointsToSetFactory.make(csManager.getCSObj(contextSelector.selectHeapContext(csMethod, obj), obj))
                            );
                        }
                    }
                }
                if (stmt instanceof Copy copyStmt) {
                    addPFGEdge(
                            csManager.getCSVar(csMethod.getContext(), (Var) copyStmt.getUses().get(0)),
                            csManager.getCSVar(csMethod.getContext(), (Var) copyStmt.getDef().get())
                    );
                }
                if (stmt instanceof StoreField sf) {
                    if (sf.isStatic()) {
                        addPFGEdge(
                                csManager.getCSVar(csMethod.getContext(), (Var) sf.getUses().get(0)),
                                csManager.getStaticField(sf.getFieldRef().resolve())
                        );
                    }
                }
                if (stmt instanceof LoadField lf) {
                    if (lf.isStatic()) {
                        addPFGEdge(
                                csManager.getStaticField(lf.getFieldRef().resolve()),
                                csManager.getCSVar(csMethod.getContext(), (Var) lf.getDef().get())
                        );
                    }
                }
            }
        }
    }

    /**
     * Processes the statements in context-sensitive new reachable methods.
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
            if (e.pointer() instanceof CSVar ePtr) {
                d.forEach(obj -> {
                    ePtr.getVar().getStoreFields().forEach(sf -> {
                        addPFGEdge(
                                csManager.getCSVar(ePtr.getContext(), sf.getRValue()),
                                csManager.getInstanceField(obj, sf.getFieldRef().resolve())
                        );
                    });
                    ePtr.getVar().getLoadFields().forEach(lf -> {
                        addPFGEdge(
                                csManager.getInstanceField(obj, lf.getFieldRef().resolve()),
                                csManager.getCSVar(ePtr.getContext(), lf.getLValue())
                        );
                    });
                    ePtr.getVar().getStoreArrays().forEach(sa -> {
                        addPFGEdge(
                                csManager.getCSVar(ePtr.getContext(), sa.getRValue()),
                                csManager.getArrayIndex(obj)
                        );
                    });
                    ePtr.getVar().getLoadArrays().forEach(la -> {
                        addPFGEdge(
                                csManager.getArrayIndex(obj),
                                csManager.getCSVar(ePtr.getContext(), la.getLValue())
                        );
                    });
                    processCall(ePtr, obj);
                });
            }
        }
    }

    /**
     * Propagates pointsToSet to pt(pointer) and its PFG successors,
     * returns the difference set of pointsToSet and pt(pointer).
     */
    private PointsToSet propagate(Pointer pointer, PointsToSet pointsToSet) {
        PointsToSet res = PointsToSetFactory.make();
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
     * @param recv    the receiver variable
     * @param recvObj set of new discovered objects pointed by the variable.
     */
    private void processCall(CSVar recv, CSObj recvObj) {
        recv.getVar().getInvokes().forEach(invokeStmt -> {
            if (invokeStmt.isStatic()) {
                return;
            }
            JMethod callee = resolveCallee(recvObj, invokeStmt);
            Context c = recv.getContext();
            Context ct = contextSelector.selectContext(csManager.getCSCallSite(c, invokeStmt), recvObj, callee);
            workList.addEntry(
                    csManager.getCSVar(ct, callee.getIR().getThis()),
                    PointsToSetFactory.make(recvObj)
            );
            if (callGraph.addEdge(new Edge<>(CallGraphs.getCallKind(invokeStmt), csManager.getCSCallSite(c, invokeStmt), csManager.getCSMethod(ct, callee)))) {
                addReachable(csManager.getCSMethod(ct, callee));
                for (int i = 0; i < invokeStmt.getInvokeExp().getArgCount(); i++) {
                    addPFGEdge(
                            csManager.getCSVar(c, invokeStmt.getInvokeExp().getArg(i)),
                            csManager.getCSVar(ct, callee.getIR().getParam(i))
                    );
                }
                callee.getIR().getReturnVars().forEach(r -> {
                    if (invokeStmt.getResult() != null) {
                        addPFGEdge(
                                csManager.getCSVar(ct, r),
                                csManager.getCSVar(c, invokeStmt.getResult())
                        );
                    }
                });
            }
        });
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
