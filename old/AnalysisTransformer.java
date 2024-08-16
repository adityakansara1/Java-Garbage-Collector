import java.util.*;

import fj.Hash;
import soot.*;
import soot.JastAddJ.ReturnStmt;
import soot.jimple.DefinitionStmt;
import soot.jimple.FieldRef;
import soot.jimple.InvokeExpr;
import soot.jimple.InvokeStmt;
import soot.jimple.Jimple;
import soot.jimple.NullConstant;
import soot.jimple.ParameterRef;
import soot.jimple.StaticInvokeExpr;
import soot.jimple.ThisRef;
import soot.jimple.VirtualInvokeExpr;
import soot.jimple.internal.JArrayRef;
import soot.jimple.internal.JAssignStmt;
import soot.jimple.internal.JCastExpr;
import soot.jimple.internal.JIdentityStmt;
import soot.jimple.internal.JInstanceFieldRef;
import soot.jimple.internal.JInterfaceInvokeExpr;
import soot.jimple.internal.JInvokeStmt;
import soot.jimple.internal.JNewArrayExpr;
import soot.jimple.internal.JNewExpr;
import soot.jimple.internal.JReturnStmt;
import soot.jimple.internal.JVirtualInvokeExpr;
import soot.jimple.internal.JimpleLocal;
import soot.jimple.toolkits.callgraph.CallGraph;
import soot.jimple.toolkits.callgraph.Edge;
import soot.toolkits.graph.*;
import soot.toolkits.scalar.SimpleLiveLocals;
import soot.util.Chain;
import soot.toolkits.scalar.LiveLocals;

public class AnalysisTransformer extends SceneTransformer {
    static CallGraph cg;
    static HashMap<String, PointsToGraph> ptgs = new HashMap<>();
    static int count = 0;

    @Override
    protected void internalTransform(String arg0, Map<String, String> arg1) {
        // Set<SootMethod> methods = new HashSet<>();
        cg = Scene.v().getCallGraph();
        // Get the main method
        SootMethod mainMethod = Scene.v().getMainMethod();
        // Get the list of methods reachable from the main method
        // Note: This can be done bottom up manner as well. Might be easier to model.
        // getlistofMethods(mainMethod, methods);

        // for (SootMethod m : methods) {
        processCFG(mainMethod);
        // }
    }

    protected static void processCFG(SootMethod method) {
        if (method.toString().contains("init")) {
            return;
        }

        Iterator<Edge> edges = cg.edgesOutOf(method);
        while (edges.hasNext()) {
            Edge edge = edges.next();
            SootMethod targetMethod = edge.tgt();
            if (!targetMethod.isJavaLibraryMethod()) {
                processCFG(targetMethod);
            }
        }

        Body body = method.getActiveBody();
        System.out.println("\n-----" + body.getMethod().getName() + "-----");

        PointsToGraph ptg = doAnalysis(method);
        ptgs.put(body.getMethod().getName(), ptg);

        // Get the callgraph
        // UnitGraph cfg = new BriefUnitGraph(body);
        // Get live local using Soot's exiting analysis
        // LiveLocals liveLocals = new SimpleLiveLocals(cfg);

        // Units for the body
        PatchingChain<Unit> units = body.getUnits();

        for (Unit u : units) {
            System.out.println("Unit: " + u);
            // if (u instanceof StaticInvokeExpr) {
            // System.out.println("StaticInvokeExpr: " + u);
            // }
            // List<Local> before = liveLocals.getLiveLocalsBefore(u);
            // List<Local> after = liveLocals.getLiveLocalsAfter(u);
            // System.out.println("Live locals before: " + before);
            // System.out.println("Live locals after: " + after);
            // System.out.println();
        }
    }

    static PointsToGraph doAnalysis(SootMethod m) {
        count = 0;
        List<Unit> workList = new ArrayList<>();
        HashMap<Unit, PointsToGraph> out = new HashMap<>();
        PatchingChain<Unit> units = m.getActiveBody().getUnits();
        UnitGraph cfg = new BriefUnitGraph(m.getActiveBody());

        for (Unit u : units) {
            out.put(u, new PointsToGraph());
        }

        for (Unit u : units) {
            PointsToGraph newPtg = new PointsToGraph();
            PointsToGraph oldPtg = out.get(u);

            for (Unit pred : cfg.getPredsOf(u)) {
                PointsToGraph predPtg = out.get(pred);
                newPtg = merge(newPtg, predPtg);
            }

            computeUnit(u, newPtg);

            if (!oldPtg.equals(newPtg)) {
                out.put(u, newPtg);
                workList.addAll(cfg.getSuccsOf(u));
            }
        }

        while (!workList.isEmpty()) {
            Unit u = workList.remove(0);

            PointsToGraph newPtg = new PointsToGraph();
            PointsToGraph oldPtg = out.get(u);

            for (Unit pred : cfg.getPredsOf(u)) {
                PointsToGraph predPtg = out.get(pred);
                newPtg = merge(newPtg, predPtg);
            }

            computeUnit(u, newPtg);

            if (!oldPtg.equals(newPtg)) {
                out.put(u, newPtg);
                workList.addAll(cfg.getSuccsOf(u));
            }
        }

        return new PointsToGraph();
    }

    static PointsToGraph merge(PointsToGraph ptg1, PointsToGraph ptg2) {
        return new PointsToGraph();
    }

    static void computeUnit(Unit u, PointsToGraph ptg) {

        if (u instanceof JIdentityStmt) {
            JIdentityStmt stmt = (JIdentityStmt) u;
            Value left = stmt.leftBox.getValue();
            Value right = stmt.rightBox.getValue();

            if (left instanceof JimpleLocal && right instanceof ThisRef) {
                JimpleLocal local = (JimpleLocal) left;
                String local_name = local.getName();

                if (ptg.stack.containsKey(local_name)) {
                    ptg.stack.get(local_name).clear();
                } else {
                    ptg.stack.put(local_name, new HashSet<>());
                }

                ptg.stack.get(local_name).add("this");
                ptg.heap.put("this", new HashMap<>());

            } else if (left instanceof JimpleLocal && right instanceof ParameterRef) {
                JimpleLocal local = (JimpleLocal) left;
                String local_name = local.getName();

                if (ptg.stack.containsKey(local_name)) {
                    ptg.stack.get(local_name).clear();
                } else {
                    ptg.stack.put(local_name, new HashSet<>());
                }

                count += 1;
                String param = "param_" + count;
                ptg.stack.get(local_name).add(param);
                ptg.heap.put(param, new HashMap<>());

            } else {
                System.out.println("Unknown IdentityStmt: " + u);
                System.exit(1);
            }

        } else if (u instanceof JAssignStmt) {
            JAssignStmt stmt = (JAssignStmt) u;
            Value left = stmt.leftBox.getValue();
            Value right = stmt.rightBox.getValue();
            if (left instanceof JimpleLocal && right instanceof JNewExpr) {

                // NOTE: Strong Update
                String object = Integer.toString(u.getJavaSourceStartLineNumber());
                String local = left.toString();

                if (ptg.stack.containsKey(local)) {
                    ptg.stack.get(local).clear();
                    ptg.stack.get(local).add(object);
                } else {
                    Set<String> objects = new HashSet<>();
                    objects.add(object);
                    ptg.stack.put(local, objects);
                }

                ptg.heap.put(object, new HashMap<>());

            } else if (left instanceof JimpleLocal && right instanceof JInstanceFieldRef) {
                JimpleLocal local = (JimpleLocal) left;
                JInstanceFieldRef field = (JInstanceFieldRef) right;
                String local1_name = local.getName();
                String local2_name = field.getBase().toString();
                String field_name = field.getField().getName();

                // NOTE: Strong Update
                if (ptg.stack.containsKey(local1_name)) {
                    ptg.stack.get(local1_name).clear();

                    for (String object : ptg.stack.get(local2_name)) {
                        if (ptg.heap.containsKey(object)) {
                            if (ptg.heap.get(object).containsKey(field_name)) {
                                ptg.stack.get(local1_name).addAll(ptg.heap.get(object).get(field_name));
                            }
                        }
                    }

                } else {
                    Set<String> objects = new HashSet<>();
                    for (String object : ptg.stack.get(local2_name)) {
                        if (ptg.heap.containsKey(object)) {
                            if (ptg.heap.get(object).containsKey(field_name)) {
                                objects.addAll(ptg.heap.get(object).get(field_name));
                            }
                        }
                    }
                    ptg.stack.put(local1_name, objects);
                }

            } else if (left instanceof JimpleLocal && right instanceof NullConstant) {
                JimpleLocal local = (JimpleLocal) left;
                String local_name = local.getName();

                if (ptg.stack.containsKey(local_name)) {
                    ptg.stack.get(local_name).clear();
                } else {
                    ptg.stack.put(local_name, new HashSet<>());
                }

            } else if (left instanceof JInstanceFieldRef && right instanceof JimpleLocal) {
                JInstanceFieldRef field = (JInstanceFieldRef) left;
                JimpleLocal local = (JimpleLocal) right;
                String local1_name = field.getBase().toString();
                String field_name = field.getField().getName();
                String local2_name = local.getName();

                // NOTE: Weak Update
                if (ptg.stack.containsKey(local1_name)) {
                    if (ptg.stack.containsKey(local2_name)) {
                        for (String object : ptg.stack.get(local1_name)) {
                            if (ptg.heap.containsKey(object)) {
                                if (ptg.heap.get(object).containsKey(field_name)) {
                                    ptg.heap.get(object).get(field_name).addAll(ptg.stack.get(local2_name));
                                } else {
                                    ptg.heap.get(object).put(field_name, ptg.stack.get(local2_name));
                                }
                            }
                        }
                    } else {
                        ptg.stack.put(local2_name, new HashSet<>());
                        for (String object : ptg.stack.get(local1_name)) {
                            if (ptg.heap.containsKey(object)) {
                                if (ptg.heap.get(object).containsKey(field_name)) {
                                    ptg.heap.get(object).get(field_name).addAll(ptg.stack.get(local2_name));
                                } else {
                                    ptg.heap.get(object).put(field_name, ptg.stack.get(local2_name));
                                }
                            }
                        }
                    }
                } else {
                    System.out.println("Error: " + local1_name + " not found in stack");
                }

            } else if (left instanceof JInstanceFieldRef && right instanceof NullConstant) {
                JInstanceFieldRef field = (JInstanceFieldRef) left;
                String local_name = field.getBase().toString();
                String field_name = field.getField().getName();

                if (ptg.stack.containsKey(local_name)) {
                    for (String object : ptg.stack.get(local_name)) {
                        if (ptg.heap.containsKey(object)) {
                            if (ptg.heap.get(object).containsKey(field_name)) {
                                ptg.heap.get(object).get(field_name).clear();
                            }
                        }
                    }
                } else {
                    System.out.println("Error: " + local_name + " not found in stack");
                }

            } else if (left instanceof JimpleLocal && right instanceof StaticInvokeExpr) {
                JimpleLocal local = (JimpleLocal) left;
                StaticInvokeExpr expr = (StaticInvokeExpr) right;
                String local_name = local.getName();
                PointsToGraph methodPtg = ptgs.get(expr.getMethod().getName());
                int argCount = expr.getArgCount();

                if (ptg.stack.containsKey(local_name)) {
                    ptg.stack.get(local_name).clear();
                } else {
                    ptg.stack.put(local_name, new HashSet<>());
                }

                // Update Stack
                ptg.stack.get(local_name).addAll(methodPtg.stack.get("ret"));
                
                // Update Heap
                
                




            } else if (left instanceof JimpleLocal && right instanceof JVirtualInvokeExpr) {

            } else if (left instanceof JimpleLocal && right instanceof JInterfaceInvokeExpr) {

            } else if (left instanceof JimpleLocal && right instanceof JimpleLocal) {
                JimpleLocal local1 = (JimpleLocal) left;
                JimpleLocal local2 = (JimpleLocal) right;
                String local1_name = local1.getName();
                String local2_name = local2.getName();

                if (ptg.stack.containsKey(local1_name)) {
                    ptg.stack.get(local1_name).clear();
                    ptg.stack.get(local1_name).addAll(ptg.stack.get(local2_name));
                } else {
                    ptg.stack.put(local1_name, new HashSet<>());
                    ptg.stack.get(local1_name).addAll(ptg.stack.get(local2_name));
                }

            } else if (left instanceof JimpleLocal && right instanceof JNewArrayExpr) {
                JimpleLocal local = (JimpleLocal) left;
                JNewArrayExpr expr = (JNewArrayExpr) right;

                String local_name = local.getName();
                String object = Integer.toString(u.getJavaSourceStartLineNumber());
                String arrayObject = "Array_" + object;

                if (ptg.stack.containsKey(local_name)) {
                    ptg.stack.get(local_name).clear();
                    ptg.stack.get(local_name).add(object);
                } else {
                    Set<String> objects = new HashSet<>();
                    objects.add(object);
                    ptg.stack.put(local_name, objects);
                }

                ptg.heap.put(object, new HashMap<>());
                ptg.heap.get(object).put(arrayObject, new HashSet<>());

            } else if (left instanceof JArrayRef && right instanceof JimpleLocal) {
                JArrayRef local1 = (JArrayRef) left;
                JimpleLocal local2 = (JimpleLocal) right;
                String local1_name = local1.getBase().toString();
                String local2_name = local2.getName();

                if (ptg.stack.containsKey(local1_name)) {
                    if (ptg.stack.containsKey(local2_name)) {
                        for (String object : ptg.stack.get(local1_name)) {
                            if (ptg.heap.containsKey(object)) {
                                if (ptg.heap.get(object).containsKey("Array_" + object)) {
                                    ptg.heap.get(object).get("Array_" + object).addAll(ptg.stack.get(local2_name));
                                } else {
                                    ptg.heap.get(object).put("Array_" + object, ptg.stack.get(local2_name));
                                }
                            }
                        }
                    } else {
                        ptg.stack.put(local2_name, new HashSet<>());
                        for (String object : ptg.stack.get(local1_name)) {
                            if (ptg.heap.containsKey(object)) {
                                if (ptg.heap.get(object).containsKey("Array_" + object)) {
                                    ptg.heap.get(object).get("Array_" + object).addAll(ptg.stack.get(local2_name));
                                } else {
                                    ptg.heap.get(object).put("Array_" + object, ptg.stack.get(local2_name));
                                }
                            }
                        }
                    }
                } else {
                    System.out.println("Error: " + local1_name + " not found in stack");
                }

            } else if (left instanceof JimpleLocal && right instanceof JArrayRef) {

            } else if (left instanceof JimpleLocal && right instanceof JCastExpr) {
                JimpleLocal local = (JimpleLocal) left;
                JCastExpr expr = (JCastExpr) right;
                String local_name = local.getName();
                String local2_name = expr.getOp().toString();

                if (ptg.stack.containsKey(local_name)) {
                    ptg.stack.get(local_name).clear();
                    ptg.stack.get(local_name).addAll(ptg.stack.get(local2_name));
                } else {
                    ptg.stack.put(local_name, new HashSet<>());
                    ptg.stack.get(local_name).addAll(ptg.stack.get(local2_name));
                }

            } else {
                System.out.println("Unknown AssignStmt: " + u);
                // exit with error
                System.exit(1);
            }
        } else if (u instanceof InvokeStmt) {
            JInvokeStmt stmt = (JInvokeStmt) u;
            InvokeExpr expr = stmt.getInvokeExpr();

            if (expr instanceof StaticInvokeExpr) {

            } else if (expr instanceof VirtualInvokeExpr) {

            } else if (expr instanceof JInterfaceInvokeExpr) {

            }

        } else if (u instanceof JReturnStmt) {
            JReturnStmt stmt = (JReturnStmt) u;
            String local_name = "ret";
            String local2_name = stmt.getOp().toString();

            if (ptg.stack.containsKey(local_name)) {
                ptg.stack.get(local_name).addAll(ptg.stack.get(local2_name));
            } else {
                ptg.stack.put(local_name, new HashSet<>());
                ptg.stack.get(local_name).addAll(ptg.stack.get(local2_name));
            }
        } else {
            System.out.println("Unknown unit type: " + u);
        }
    }
    
}

class PointsToGraph {
    HashMap<String, HashMap<String, Set<String>>> heap;
    HashMap<String, Set<String>> stack;

    public PointsToGraph() {
        heap = new HashMap<>();
        stack = new HashMap<>();
    }

    boolean equals(PointsToGraph oldPtg) {
        if (heap.keySet().equals(oldPtg.heap.keySet())
                && stack.keySet().equals(oldPtg.stack.keySet())) {
            for (String key : heap.keySet()) {
                if (!heap.get(key).equals(oldPtg.heap.get(key))) {
                    return false;
                }
            }
            for (String key : stack.keySet()) {
                if (!stack.get(key).equals(oldPtg.stack.get(key))) {
                    return false;
                }
            }
            return true;
        }
        return false;
    }
}