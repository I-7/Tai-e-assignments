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

package pascal.taie.analysis.graph.callgraph;

import pascal.taie.World;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.language.classes.ClassHierarchy;
import pascal.taie.language.classes.JClass;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.classes.Subsignature;

import java.util.*;

/**
 * Implementation of the CHA algorithm.
 */
class CHABuilder implements CGBuilder<Invoke, JMethod> {

    private ClassHierarchy hierarchy;

    @Override
    public CallGraph<Invoke, JMethod> build() {
        hierarchy = World.get().getClassHierarchy();
        return buildCallGraph(World.get().getMainMethod());
    }

    private CallGraph<Invoke, JMethod> buildCallGraph(JMethod entry) {
        DefaultCallGraph callGraph = new DefaultCallGraph();
        callGraph.addEntryMethod(entry);
        LinkedList<JMethod> waitlist = new LinkedList<>();
        waitlist.add(entry);
        HashSet<JMethod> reachable = new HashSet<>();


        while (!waitlist.isEmpty()) {
            JMethod m = waitlist.pop();
            if (reachable.add(m)) {
                m.getIR().forEach(cs -> {
                    if (cs instanceof Invoke) {
                        resolve((Invoke) cs).forEach(m2 -> {
                            if (!m2.isAbstract()) {
                                waitlist.add(m2);
                                callGraph.addEdge(new Edge<>(CallGraphs.getCallKind((Invoke) cs), (Invoke) cs, m2));
                            }
                        });
                    }
                });
            }
        }

        return callGraph;
    }

    /**
     * Resolves call targets (callees) of a call site via CHA.
     */
    private Set<JMethod> resolve(Invoke callSite) {
        Set<JMethod> res = new HashSet<>();
        if (callSite.isStatic()) {
            res.add(callSite.getMethodRef().getDeclaringClass().getDeclaredMethod(callSite.getMethodRef().getSubsignature()));
        }
        if (callSite.isSpecial()) {
            res.add(dispatch(callSite.getMethodRef().getDeclaringClass(), callSite.getMethodRef().getSubsignature()));
        }
        if (callSite.isVirtual() || callSite.isInterface()) {
            LinkedList<JClass> q = new LinkedList<>();
            HashSet<JClass> seen = new HashSet<>();
            q.push(callSite.getMethodRef().getDeclaringClass());
            seen.add(callSite.getMethodRef().getDeclaringClass());
            while (!q.isEmpty()) {
                JClass t = q.pop();
                JMethod m = dispatch(t, callSite.getMethodRef().getSubsignature());
                res.add(m);
                for (JClass c : hierarchy.getDirectSubclassesOf(t)) {
                    if (seen.add(c)) {
                        q.add(c);
                    }
                }
                for (JClass c : hierarchy.getDirectImplementorsOf(t)) {
                    if (seen.add(c)) {
                        q.add(c);
                    }
                }
                for (JClass c : hierarchy.getDirectSubinterfacesOf(t)) {
                    if (seen.add(c)) {
                        q.add(c);
                    }
                }
            }
        }
        return res;
    }

    /**
     * Looks up the target method based on given class and method subsignature.
     *
     * @return the dispatched target method, or null if no satisfying method
     * can be found.
     */
    private JMethod dispatch(JClass jclass, Subsignature subsignature) {
        if (jclass.getDeclaredMethod(subsignature) != null) {
            return jclass.getDeclaredMethod(subsignature);
        }
        if (jclass.getSuperClass() != null) {
            return dispatch(jclass.getSuperClass(), subsignature);
        }
        return null;
    }
}
