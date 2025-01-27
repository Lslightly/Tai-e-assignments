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
import pascal.taie.ir.proginfo.MethodRef;
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

        var workList = new LinkedList<JMethod>();
        workList.addLast(entry);
        while (!workList.isEmpty()) {
            var m = workList.removeFirst();
            if (!callGraph.contains(m)) {
                callGraph.addReachableMethod(m);
                var css = callGraph.getCallSitesIn(m);
                for (var cs: css) {
//                    System.out.println("\n"+m.getName() + " -> " + cs);
                    var T = resolve(cs);
                    for (var tm: T) {
                        callGraph.addEdge(new Edge<>(CallGraphs.getCallKind(cs), cs, tm));
                        workList.addLast(tm);
                    }
                }
            }
        }
        return callGraph;
    }

    /**
     * Resolves call targets (callees) of a call site via CHA.
     */
    private Set<JMethod> resolve(Invoke callSite) {
        var T = new HashSet<JMethod>();
        var mref = callSite.getMethodRef();
        var subsignature = mref.getSubsignature();
        var cm = mref.getDeclaringClass();
        switch (CallGraphs.getCallKind(callSite)) {
            case STATIC:
                T.add(cm.getDeclaredMethod(subsignature));
                break;
            case SPECIAL: {
                var m = dispatch(cm, subsignature);
                if (m == null) {
                    System.out.println("dispatch does not find method for special call"+callSite);
                    System.exit(2);
                }
                T.add(m);
                break;
            }
            case INTERFACE:
            case VIRTUAL: {
                var subclasses = getSubClasses(cm);
                for (var c: subclasses) {
                    var m = dispatch(c, subsignature);
                    if (m != null) {
                        T.add(m);
                    }
                }
                break;
            }
            default: {
                System.out.println("unknown dynamic invoke");
                System.exit(1);
            }
        }
//        System.out.println("resolve result is "+T);
        return T;
    }

    /**
     * @param c the class to get sub class
     * @return get subclasses of `c` including `c` itself
     */
    private Set<JClass> getSubClasses(JClass c) {
        var subclasses = new HashSet<JClass>();
        var workList = new LinkedList<JClass>();
        workList.addLast(c);
        while (!workList.isEmpty()) {
            var top = workList.removeFirst();
            subclasses.add(top);
            if (top.isInterface()) {
                workList.addAll(hierarchy.getDirectImplementorsOf(top));
                workList.addAll(hierarchy.getDirectSubinterfacesOf(top));
            } else {
                workList.addAll(hierarchy.getDirectSubclassesOf(top));
            }
        }
//        System.out.println("subclasses of " + c.getName() + " is " + subclasses);
        return subclasses;
    }

    /**
     * Looks up the target method based on given class and method subsignature.
     *
     * @return the dispatched target method, or null if no satisfying method
     * can be found.
     */
    private JMethod dispatch(JClass jclass, Subsignature subsignature) {
        var m = jclass.getDeclaredMethod(subsignature);
        if (m == null || m.isAbstract()) {
            if (jclass.getSuperClass() == null) {
                return null;
            } else {
                return dispatch(jclass.getSuperClass(), subsignature);
            }
        }
//        System.out.println("the actual method for " + jclass.getName() + ":" + subsignature + " is " + m);
        return m;
    }
}
