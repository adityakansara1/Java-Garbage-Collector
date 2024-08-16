import java.util.*;

import soot.*;
import soot.jimple.InvokeExpr;
import soot.jimple.InvokeStmt;
import soot.jimple.NullConstant;
import soot.jimple.ParameterRef;
import soot.jimple.StaticInvokeExpr;
import soot.jimple.ThisRef;
import soot.jimple.internal.JArrayRef;
import soot.jimple.internal.JAssignStmt;
import soot.jimple.internal.JCastExpr;
import soot.jimple.internal.JGotoStmt;
import soot.jimple.internal.JIdentityStmt;
import soot.jimple.internal.JIfStmt;
import soot.jimple.internal.JInstanceFieldRef;
import soot.jimple.internal.JInterfaceInvokeExpr;
import soot.jimple.internal.JInvokeStmt;
import soot.jimple.internal.JNewArrayExpr;
import soot.jimple.internal.JNewExpr;
import soot.jimple.internal.JReturnStmt;
import soot.jimple.internal.JReturnVoidStmt;
import soot.jimple.internal.JSpecialInvokeExpr;
import soot.jimple.internal.JStaticInvokeExpr;
import soot.jimple.internal.JVirtualInvokeExpr;
import soot.jimple.internal.JimpleLocal;
import soot.jimple.toolkits.callgraph.CallGraph;
import soot.jimple.toolkits.callgraph.Edge;
import soot.toolkits.graph.*;
import soot.toolkits.scalar.SimpleLiveLocals;
import soot.toolkits.scalar.LiveLocals;

class Field {
    private String name;
    private Object pointsTo;

    public Field(String name) {
        this.name = name;
        this.pointsTo = null;
    }

    public void setPointsTo(Object object) {
        this.pointsTo = object;
    }

    public Object getPointsTo() {
        return this.pointsTo;
    }

    public void setName(String name) {
        this.name = name;
    }

    public String getName() {
        return this.name;
    }
}

class Object {
    private String info;
    private String name;
    private ArrayList<Field> fields;
    private Object pointsTo;

    public Object(String name, String info) {
        this.name = name;
        this.info = info;
        this.fields = new ArrayList<>();
        this.pointsTo = null;
    }

    public void addField(Field n) {
        fields.add(n);
    }

    public void removeField(Field n) {
        fields.remove(n);
    }

    public void removeAllFields() {
        this.fields = null;
    }

    public void addPointsTo(Object n) {
        this.pointsTo = n;
    }

    public String getInfo() {
        return info;
    }

    public String getName() {
        return name;
    }

    public ArrayList<Field> getFields() {
        return fields;
    }

    public Object getPointsTo() {
        return pointsTo;
    }

    @Override
    public String toString() {
        return "info: " + info + ", fields: " + fields + ", pointsTo: " + pointsTo;
    }
}

public class AnalysisTransformer extends SceneTransformer {
    static CallGraph cg;
    static HashMap<String, HashMap<String, Set<Object>>> stack = new HashMap<>();
    static HashMap<String, Set<Object>> heap = new HashMap<>();
    // Maintains line number at which object last referenced directly or indirectly
    static HashMap<String, HashMap<String, String>> lastAccessPointOfObjectMap = new HashMap<>();
    static Set<SootMethod> methods = new HashSet<>();
    static Map<String, String> objectType = new HashMap<>();
    static Map<String, List<String>> methodToGcLines = new HashMap<>();

    @Override
    protected void internalTransform(String arg0, Map<String, String> arg1) {
        cg = Scene.v().getCallGraph();
        SootMethod mainMethod = Scene.v().getMainMethod();
        processCFG(mainMethod);
        printAnswer();
    }

    protected static void processCFG(SootMethod method) {
        if (method.toString().contains("init") || methods.contains(method)) {
            return;
        }
        methods.add(method);
        Iterator<Edge> edges = cg.edgesOutOf(method);
        while (edges.hasNext()) {
            Edge edge = edges.next();
            SootMethod targetMethod = edge.tgt();
            if (!targetMethod.isJavaLibraryMethod()) {
                processCFG(targetMethod);
            }
        }

        Body body = method.getActiveBody();
        // Get the callgraph
        UnitGraph cfg = new BriefUnitGraph(body);
        // Get live local using Soot's exiting analysis
        LiveLocals liveLocals = new SimpleLiveLocals(cfg);
        // Units for the body

        // Stack Map: StackVar -> Object
        HashMap<String, Set<Object>> stackVarToObjMap = new HashMap<>();
        // Heap Map: Object ---field---> Object
        Set<Object> heapMap = new HashSet<>();
        String currMethodSign = body.getMethod().getName() + body.getMethod().getDeclaringClass().getName()
                + body.getMethod().getReturnType().toString();

        // Helps to decide weak update or strong
        HashMap<String, Integer> branchStack = new HashMap<>();
        HashMap<String, String> lastAccessPointOfObject = new HashMap<>();
        lastAccessPointOfObjectMap.put(currMethodSign, lastAccessPointOfObject);

        int currentBranchStack = 0;
        int paramCount = 0;

        PatchingChain<Unit> units = body.getUnits();
        for (Unit u : units) {
            List<Local> before = liveLocals.getLiveLocalsBefore(u);
            List<Local> after = liveLocals.getLiveLocalsAfter(u);
            List<String> killed = findKilledVariables(before, after);

            if (u instanceof JIdentityStmt) {
                JIdentityStmt stmt = (JIdentityStmt) u;
                Value left = stmt.leftBox.getValue();
                Value right = stmt.rightBox.getValue();

                if (left instanceof JimpleLocal && right instanceof ThisRef) {
                    /* IGNORING THIS CASE */
                } else if (left instanceof JimpleLocal && right instanceof ParameterRef) {
                    /* a = @parameter0 */
                    JimpleLocal local = (JimpleLocal) left;
                    String stackVar = local.getName();
                    String dummyObjectName = "param_" + paramCount;
                    paramCount++;

                    Object dummyObject = new Object(dummyObjectName, "dummy");
                    Set<Object> objects = new HashSet<>();
                    objects.add(dummyObject);
                    stackVarToObjMap.put(stackVar, objects);
                    heapMap.add(dummyObject);
                } else {
                }
            } else if (u instanceof JAssignStmt) {
                JAssignStmt stmt = (JAssignStmt) u;
                Value left = stmt.leftBox.getValue();
                Value right = stmt.rightBox.getValue();
                if (left instanceof JimpleLocal && right instanceof JNewExpr) {
                    /* a = new() */
                    JimpleLocal local = (JimpleLocal) left;
                    String stackVar = local.getName();
                    String objectName = Integer.toString(u.getJavaSourceStartLineNumber());
                    Object object = new Object(objectName, "concrete");

                    JNewExpr newExpr = (JNewExpr) right;
                    String type = newExpr.getType().toString();
                    objectType.put(objectName, type);

                    Set<Object> objects = new HashSet<>();
                    objects.add(object);
                    // Update Stack: Always unique varible
                    stackVarToObjMap.put(stackVar, objects);
                    // Update Heap
                    heapMap.add(object);
                    // Update killedLast with new object, last accessed at object creation site
                    lastAccessPointOfObject.put(objectName, objectName);

                } else if (left instanceof JimpleLocal && right instanceof JInstanceFieldRef) {
                    /* a = b.f */
                    JimpleLocal local = (JimpleLocal) left;
                    JInstanceFieldRef ref = (JInstanceFieldRef) right;
                    String stackVar1 = local.getName();
                    String stackVar2 = ref.getBase().toString();
                    String field = ref.getField().getName();

                    // Get objects pointed by stackVar2
                    Set<Object> objects2 = stackVarToObjMap.get(stackVar2);
                    Set<Object> objects = new HashSet<>();

                    // Get objects pointed by "objects" (retrieved above) via "field"
                    for (Object o2 : objects2) {
                        for (Field f : o2.getFields()) {
                            if (f.getName().equals(field)) {
                                if (f.getPointsTo() != null) {
                                    objects.add(f.getPointsTo());
                                }
                            }
                        }
                    }

                    // Update Stack
                    // No Heap Update
                    stackVarToObjMap.put(stackVar1, objects);

                } else if (left instanceof JInstanceFieldRef && right instanceof JimpleLocal) {
                    /* a.f = b */
                    JimpleLocal local = (JimpleLocal) right;
                    JInstanceFieldRef ref = (JInstanceFieldRef) left;
                    String stackVar1 = ref.getBase().toString();
                    String field = ref.getField().getName();
                    String stackVar2 = local.getName();

                    // Get object pointed by stackVar1 and stackVar2
                    Set<Object> objects1 = stackVarToObjMap.get(stackVar1);
                    Set<Object> objects2 = stackVarToObjMap.get(stackVar2);

                    if (branchStack.containsKey(stackVar1 + field)) {
                        if (branchStack.get(stackVar1 + field).equals(currentBranchStack)) {
                            /* STRONG UPDATE */
                            for (Object o1 : objects1) {
                                Iterator<Object> iter = objects2.iterator();
                                for (Field f : o1.getFields()) {
                                    if (f.getName().equals(field)) {
                                        if (iter.hasNext()) {
                                            f.setPointsTo(iter.next());
                                        } else {
                                            o1.removeField(f);
                                        }
                                    }
                                }
                                if (iter.hasNext()) {
                                    Field f = new Field(field);
                                    f.setPointsTo(iter.next());
                                    o1.addField(f);
                                }
                            }
                        } else {
                            /* WEAK UPDATE */
                            for (Object o1 : objects1) {
                                Iterator<Object> iter = objects2.iterator();
                                if (iter.hasNext()) {
                                    Field f = new Field(field);
                                    f.setPointsTo(iter.next());
                                    o1.addField(f);
                                }
                            }
                        }
                    } else {
                        /* STRONG UPDATE */
                        for (Object o1 : objects1) {
                            Iterator<Object> iter = objects2.iterator();
                            for (Field f : o1.getFields()) {
                                if (f.getName().equals(field)) {
                                    if (iter.hasNext()) {
                                        f.setPointsTo(iter.next());
                                    } else {
                                        o1.removeField(f);
                                    }
                                }
                            }
                            if (iter.hasNext()) {
                                Field f = new Field(field);
                                f.setPointsTo(iter.next());
                                o1.addField(f);
                            }
                        }
                    }
                    branchStack.put(stackVar1 + field, currentBranchStack);

                } else if (left instanceof JimpleLocal && right instanceof NullConstant) {
                    /* a = null */

                } else if (left instanceof JInstanceFieldRef && right instanceof NullConstant) {
                    /* a.f = null */

                } else if (left instanceof JimpleLocal && right instanceof StaticInvokeExpr) {
                    /* a = foo() */
                    JimpleLocal local = (JimpleLocal) left;
                    String stackVar = local.getName();

                    JStaticInvokeExpr jStaticInvokeExpr = (JStaticInvokeExpr) right;
                    String methodSign = jStaticInvokeExpr.getMethod().getName()
                            + jStaticInvokeExpr.getMethodRef().getDeclaringClass().getName()
                            + jStaticInvokeExpr.getMethodRef().getReturnType().toString();
                    if (jStaticInvokeExpr.getMethodRef().getDeclaringClass().getName().contains("java")) {
                        for (String k : killed) {
                            updateLastAccessPointOfObject(k, stackVarToObjMap,
                                    Integer.toString(u.getJavaSourceStartLineNumber()), lastAccessPointOfObject);
                        }

                        updatedLastAccessObjects.clear();
                        continue;
                    }
                    // HashMap<String, Set<Object>> methodStack = stack.get(methodSign);
                    HashMap<String, Set<Object>> methodStack = getCopyOfStack(methodSign);

                    Set<Object> retObjects = methodStack.get("ret");

                    updateLineNumbers(methodSign,
                            Integer.toString(u.getJavaSourceStartLineNumber()),
                            currMethodSign);

                    // Merge Parameters
                    for (int i = 0; i < jStaticInvokeExpr.getArgCount(); i++) {
                        // Get ith argument name
                        String arg = jStaticInvokeExpr.getArg(i).toString();
                        // Get objects pointed by arg
                        Set<Object> objects1 = stackVarToObjMap.get(arg);

                        // Make param_* name
                        String paramName = "param_" + i;
                        // Get params from methodStack
                        for (String var : methodStack.keySet()) {
                            Set<Object> objects2 = methodStack.get(var);
                            for (Object o1 : objects2) {
                                if (o1.getName().equals(paramName)) {
                                    for (Field f : o1.getFields()) {
                                        for (Object o2 : objects1) {
                                            o2.addField(f);
                                        }
                                    }
                                }
                            }
                        }
                    }

                    // Merge ret to stackVar
                    stackVarToObjMap.put(stackVar, retObjects);

                    // System.out.println("ASSIGN " + u + " " + u.getJavaSourceStartLineNumber());

                } else if (left instanceof JimpleLocal && right instanceof JVirtualInvokeExpr) {
                    /* a = b.foo() */
                    JimpleLocal local = (JimpleLocal) left;
                    String stackVar = local.getName();
                    JVirtualInvokeExpr jVirtualInvokeExpr = (JVirtualInvokeExpr) right;
                    String stackVar2 = jVirtualInvokeExpr.getBase().toString();
                    Set<Object> objects = stackVarToObjMap.get(stackVar2);
                    String type = jVirtualInvokeExpr.getMethodRef().getDeclaringClass().getName();
                    for (Object o : objects) {
                        type = objectType.get(o.getName());
                    }
                    String methodSign = jVirtualInvokeExpr.getMethod().getName()
                            + type
                            + jVirtualInvokeExpr.getMethodRef().getReturnType().toString();
                    if (jVirtualInvokeExpr.getMethodRef().getDeclaringClass().getName().contains("java")) {
                        for (String k : killed) {
                            updateLastAccessPointOfObject(k, stackVarToObjMap,
                                    Integer.toString(u.getJavaSourceStartLineNumber()), lastAccessPointOfObject);
                        }

                        updatedLastAccessObjects.clear();
                        continue;
                    }
                    HashMap<String, Set<Object>> methodStack = getCopyOfStack(methodSign);

                    // HashMap<String, Set<Object>> methodStack = stack.get(methodSign);
                    Set<Object> retObjects = methodStack.get("ret");

                    updateLineNumbers(methodSign,
                            Integer.toString(u.getJavaSourceStartLineNumber()),
                            currMethodSign);

                    for (int i = 0; i < jVirtualInvokeExpr.getArgCount(); i++) {
                        // Get ith argument name
                        String arg = jVirtualInvokeExpr.getArg(i).toString();
                        // Get objects pointed by arg
                        Set<Object> objects1 = stackVarToObjMap.get(arg);

                        // Make param_* name
                        String paramName = "param_" + i;
                        // Get params from methodStack
                        for (String var : methodStack.keySet()) {
                            Set<Object> objects2 = methodStack.get(var);
                            for (Object o1 : objects2) {
                                if (o1.getName().equals(paramName)) {
                                    for (Field f : o1.getFields()) {
                                        for (Object o2 : objects1) {
                                            o2.addField(f);
                                        }
                                    }
                                }
                            }
                        }
                    }

                    // Merge Return
                    stackVarToObjMap.put(stackVar, retObjects);

                } else if (left instanceof JimpleLocal && right instanceof JInterfaceInvokeExpr) {
                    /* a = b.foo() */
                    JimpleLocal local = (JimpleLocal) left;
                    String stackVar = local.getName();

                    JInterfaceInvokeExpr jInterfaceInvokeExpr = (JInterfaceInvokeExpr) right;
                    String methodSign = jInterfaceInvokeExpr.getMethod().getName()
                            + jInterfaceInvokeExpr.getMethodRef().getDeclaringClass().getName()
                            + jInterfaceInvokeExpr.getMethodRef().getReturnType().toString();
                    if (jInterfaceInvokeExpr.getMethodRef().getDeclaringClass().getName().contains("java")) {
                        for (String k : killed) {
                            updateLastAccessPointOfObject(k, stackVarToObjMap,
                                    Integer.toString(u.getJavaSourceStartLineNumber()), lastAccessPointOfObject);
                        }

                        updatedLastAccessObjects.clear();
                        continue;
                    }
                    HashMap<String, Set<Object>> methodStack = getCopyOfStack(methodSign);

                    // HashMap<String, Set<Object>> methodStack = stack.get(methodSign);
                    Set<Object> retObjects = methodStack.get("ret");

                    updateLineNumbers(methodSign,
                            Integer.toString(u.getJavaSourceStartLineNumber()),
                            currMethodSign);

                    for (int i = 0; i < jInterfaceInvokeExpr.getArgCount(); i++) {
                        // Get ith argument name
                        String arg = jInterfaceInvokeExpr.getArg(i).toString();
                        // Get objects pointed by arg
                        Set<Object> objects1 = stackVarToObjMap.get(arg);

                        // Make param_* name
                        String paramName = "param_" + i;
                        // Get params from methodStack
                        for (String var : methodStack.keySet()) {
                            Set<Object> objects2 = methodStack.get(var);
                            for (Object o1 : objects2) {
                                if (o1.getName().equals(paramName)) {
                                    for (Field f : o1.getFields()) {
                                        for (Object o2 : objects1) {
                                            o2.addField(f);
                                        }
                                    }
                                }
                            }
                        }
                    }

                    // Merge Return
                    stackVarToObjMap.put(stackVar, retObjects);

                } else if (left instanceof JimpleLocal && right instanceof JimpleLocal) {
                    JimpleLocal local1 = (JimpleLocal) left;
                    JimpleLocal local2 = (JimpleLocal) right;
                    String stackVar1 = local1.getName();
                    String stackVar2 = local2.getName();
                    if (stackVarToObjMap.containsKey(stackVar2)) {
                        stackVarToObjMap.put(stackVar1, stackVarToObjMap.get(stackVar2));
                    }
                } else if (left instanceof JimpleLocal && right instanceof JNewArrayExpr) {

                } else if (left instanceof JArrayRef && right instanceof JimpleLocal) {

                } else if (left instanceof JimpleLocal && right instanceof JArrayRef) {

                } else if (left instanceof JimpleLocal && right instanceof JCastExpr) {
                    JimpleLocal local = (JimpleLocal) left;
                    JCastExpr castExpr = (JCastExpr) right;
                    String stackVar1 = local.getName();
                    String stackVar2 = castExpr.getOp().toString();

                } else {
                }
            } else if (u instanceof InvokeStmt) {
                JInvokeStmt stmt = (JInvokeStmt) u;
                InvokeExpr expr = stmt.getInvokeExpr();

                if (expr instanceof JStaticInvokeExpr) {
                    JStaticInvokeExpr jStaticInvokeExpr = (JStaticInvokeExpr) expr;
                    String methodSign = jStaticInvokeExpr.getMethod().getName()
                            + jStaticInvokeExpr.getMethodRef().getDeclaringClass().getName()
                            + jStaticInvokeExpr.getMethodRef().getReturnType().toString();
                    if (jStaticInvokeExpr.getMethodRef().getDeclaringClass().getName().contains("java")) {
                        for (String k : killed) {
                            updateLastAccessPointOfObject(k, stackVarToObjMap,
                                    Integer.toString(u.getJavaSourceStartLineNumber()), lastAccessPointOfObject);
                        }

                        updatedLastAccessObjects.clear();
                        continue;
                    }
                    // HashMap<String, Set<Object>> methodStack = stack.get(methodSign);
                    HashMap<String, Set<Object>> methodStack = getCopyOfStack(methodSign);

                    updateLineNumbers(methodSign,
                            Integer.toString(u.getJavaSourceStartLineNumber()),
                            currMethodSign);

                    for (int i = 0; i < jStaticInvokeExpr.getArgCount(); i++) {
                        // Get ith argument name
                        String arg = jStaticInvokeExpr.getArg(i).toString();
                        // Get objects pointed by arg
                        Set<Object> objects1 = stackVarToObjMap.get(arg);

                        // Make param_* name
                        String paramName = "param_" + i;
                        // Get params from methodStack
                        for (String var : methodStack.keySet()) {
                            Set<Object> objects2 = methodStack.get(var);
                            for (Object o1 : objects2) {
                                if (o1.getName().equals(paramName)) {
                                    for (Field f : o1.getFields()) {
                                        for (Object o2 : objects1) {
                                            o2.addField(f);
                                        }
                                    }
                                }
                            }
                        }
                    }

                } else if (expr instanceof JVirtualInvokeExpr) {
                    JVirtualInvokeExpr jVirtualInvokeExpr = (JVirtualInvokeExpr) expr;

                    if (jVirtualInvokeExpr.getMethodRef().getDeclaringClass().getName().contains("java")) {
                        for (String k : killed) {
                            updateLastAccessPointOfObject(k, stackVarToObjMap,
                                    Integer.toString(u.getJavaSourceStartLineNumber()), lastAccessPointOfObject);
                        }

                        updatedLastAccessObjects.clear();
                        continue;
                    }
                    String stackVar2 = jVirtualInvokeExpr.getBase().toString();
                    Set<Object> objects = stackVarToObjMap.get(stackVar2);
                    String type = jVirtualInvokeExpr.getMethodRef().getDeclaringClass().getName();
                    for (Object o : objects) {
                        type = objectType.get(o.getName());
                    }
                    String methodSign = jVirtualInvokeExpr.getMethod().getName()
                            + type
                            + jVirtualInvokeExpr.getMethodRef().getReturnType().toString();

                    // HashMap<String, Set<Object>> methodStack = stack.get(methodSign);
                    HashMap<String, Set<Object>> methodStack = getCopyOfStack(methodSign);

                    updateLineNumbers(methodSign,
                            Integer.toString(u.getJavaSourceStartLineNumber()),
                            currMethodSign);

                    for (int i = 0; i < jVirtualInvokeExpr.getArgCount(); i++) {
                        // Get ith argument name
                        String arg = jVirtualInvokeExpr.getArg(i).toString();
                        // Get objects pointed by arg
                        Set<Object> objects1 = stackVarToObjMap.get(arg);

                        // Make param_* name
                        String paramName = "param_" + i;
                        // Get params from methodStack
                        for (String var : methodStack.keySet()) {
                            Set<Object> objects2 = methodStack.get(var);
                            for (Object o1 : objects2) {
                                if (o1.getName().equals(paramName)) {
                                    for (Field f : o1.getFields()) {
                                        for (Object o2 : objects1) {
                                            o2.addField(f);
                                        }
                                    }
                                }
                            }
                        }
                    }

                } else if (expr instanceof JInterfaceInvokeExpr) {
                    JInterfaceInvokeExpr jInterfaceInvokeExpr = (JInterfaceInvokeExpr) expr;
                    String methodSign = jInterfaceInvokeExpr.getMethod().getName()
                            + jInterfaceInvokeExpr.getMethodRef().getDeclaringClass().getName()
                            + jInterfaceInvokeExpr.getMethodRef().getReturnType().toString();
                    if (jInterfaceInvokeExpr.getMethodRef().getDeclaringClass().getName().contains("java")) {
                        for (String k : killed) {
                            updateLastAccessPointOfObject(k, stackVarToObjMap,
                                    Integer.toString(u.getJavaSourceStartLineNumber()), lastAccessPointOfObject);
                        }

                        updatedLastAccessObjects.clear();
                        continue;
                    }
                    // HashMap<String, Set<Object>> methodStack = stack.get(methodSign);
                    HashMap<String, Set<Object>> methodStack = getCopyOfStack(methodSign);

                    updateLineNumbers(methodSign,
                            Integer.toString(u.getJavaSourceStartLineNumber()),
                            currMethodSign);

                    for (int i = 0; i < jInterfaceInvokeExpr.getArgCount(); i++) {
                        // Get ith argument name
                        String arg = jInterfaceInvokeExpr.getArg(i).toString();
                        // Get objects pointed by arg
                        Set<Object> objects1 = stackVarToObjMap.get(arg);

                        // Make param_* name
                        String paramName = "param_" + i;
                        // Get params from methodStack
                        for (String var : methodStack.keySet()) {
                            Set<Object> objects2 = methodStack.get(var);
                            for (Object o1 : objects2) {
                                if (o1.getName().equals(paramName)) {
                                    for (Field f : o1.getFields()) {
                                        for (Object o2 : objects1) {
                                            o2.addField(f);
                                        }
                                    }
                                }
                            }
                        }
                    }

                } else if (expr instanceof JSpecialInvokeExpr) {
                    /* IGNORING THIS CASE */
                } else {
                }
            } else if (u instanceof JReturnStmt) {
                JReturnStmt returnStmt = (JReturnStmt) u;
                String returnVar = returnStmt.getOp().toString();

                // Get objects pointed by returnVar
                Set<Object> objects1 = stackVarToObjMap.get(returnVar);
                if (stackVarToObjMap.containsKey("ret")) {
                    // Get objects pointed by "ret"
                    Set<Object> objects2 = stackVarToObjMap.get("ret");
                    objects2.addAll(objects1);

                } else {
                    stackVarToObjMap.put("ret", objects1);
                }

            } else if (u instanceof JReturnVoidStmt) {

            } else if (u instanceof JIfStmt) {
                currentBranchStack++;
            } else if (u instanceof JGotoStmt) {
                currentBranchStack--;
            } else {
            }

            // Update lastAccessPointOfObject
            for (String k : killed) {
                updateLastAccessPointOfObject(k, stackVarToObjMap, Integer.toString(u.getJavaSourceStartLineNumber()),
                        lastAccessPointOfObject);
            }
            updatedLastAccessObjects.clear();
        }

        Set<String> objectsPointedByParams = getObjectPointedByParams(stackVarToObjMap);
        Set<String> objectsPointedByRet = getObjectPointedByRet(stackVarToObjMap);
        Set<String> printedObjects = new HashSet<>();
        List<String> gcedObjectsWithLineNumber = new ArrayList<>();
        lastAccessPointOfObject.forEach((k, v) -> {
            if (body.getMethod().getName() == "main"
                    || (!objectsPointedByParams.contains(k) && !objectsPointedByRet.contains(k))) {
                if (!k.contains("_")) {
                    gcedObjectsWithLineNumber.add(k + ":" + v);
                }
                printedObjects.add(k);
            }
        });
        methodToGcLines.put(body.getMethod().getDeclaringClass() + ":" + body.getMethod().getName(),
                gcedObjectsWithLineNumber);

        for (String p : printedObjects) {
            if (lastAccessPointOfObject.containsKey(p)) {
                lastAccessPointOfObject.remove(p);
            }
        }

        stack.put(currMethodSign, stackVarToObjMap);
        heap.put(currMethodSign, heapMap);

        // System.out.println("-----------Original-------------\n");
        // printPTG(stackVarToObjMap);
        // HashMap<String, Set<Object>> copy = getCopyOfStack(currMethodSign);
        // System.out.println("-----------Copy-------------\n");
        // printPTG(copy);

        // TODO: Do not overwrite it, just update with additional values
        lastAccessPointOfObjectMap.put(currMethodSign, lastAccessPointOfObject);
    }

    // Update escape objects' lastAccessPoint to caller's callsight line number for
    // that method
    static void updateLineNumbers(String methodSign, String lineNumber, String currentMethodSign) {
        HashMap<String, String> lastAccessPointOfObject1 = lastAccessPointOfObjectMap.get(methodSign);
        for (String obj : lastAccessPointOfObject1.keySet()) {
            lastAccessPointOfObject1.put(obj, lineNumber);
        }

        if (lastAccessPointOfObjectMap.containsKey(currentMethodSign)) {
            HashMap<String, String> lastAccessPointOfObject2 = lastAccessPointOfObjectMap.get(currentMethodSign);
            lastAccessPointOfObject2.putAll(lastAccessPointOfObject1);
        }
    }

    static Set<String> getObjectPointedByParams(HashMap<String, Set<Object>> stack) {
        Set<Object> paramObjects = new HashSet<>();
        for (String var : stack.keySet()) {
            for (Object o : stack.get(var)) {
                if (o.getName().contains("param_")) {
                    getObjectPointedByHelper(o, paramObjects);
                }
            }
        }

        Set<String> po = new HashSet<>();
        for (Object o : paramObjects) {
            po.add(o.getName());
        }
        return po;
    }

    static Set<String> getObjectPointedByRet(HashMap<String, Set<Object>> stack) {
        Set<Object> retObjects = new HashSet<>();
        if (stack.containsKey("ret")) {
            Set<Object> ret = stack.get("ret");
            for (Object o : ret) {
                getObjectPointedByHelper(o, retObjects);
            }
            Set<String> ro = new HashSet<>();
            for (Object o : retObjects) {
                ro.add(o.getName());
            }
            return ro;
        }
        return new HashSet<>();
    }

    static void getObjectPointedByHelper(Object o, Set<Object> objects) {
        objects.add(o);
        for (Field f : o.getFields()) {
            if (f.getPointsTo() != null) {
                if (!objects.contains(f.getPointsTo())) {
                    getObjectPointedByHelper(f.getPointsTo(), objects);
                }
            }
        }
    }

    static Set<Object> updatedLastAccessObjects = new HashSet<>();

    static void updateLastAccessPointOfObject(String k, HashMap<String, Set<Object>> stack,
            String lineNumber, HashMap<String, String> lastAccessPointOfObject) {
        if (stack.containsKey(k)) {
            Set<Object> objects = stack.get(k);

            for (Object o : objects) {
                updateLastAccessPointOfObjectHelper(o);
            }

            for (Object o : updatedLastAccessObjects) {
                lastAccessPointOfObject.put(o.getName(), lineNumber);
            }
        }
    }

    static void updateLastAccessPointOfObjectHelper(Object o) {
        updatedLastAccessObjects.add(o);
        for (Field f : o.getFields()) {
            if (f.getPointsTo() != null) {
                if (!updatedLastAccessObjects.contains(f.getPointsTo())) {
                    updateLastAccessPointOfObjectHelper(f.getPointsTo());
                }
            }
        }
    }

    static Set<Object> visited = new HashSet<>();

    static void printPTG(HashMap<String, Set<Object>> stackVarToObjMap) {
        for (String stackVar : stackVarToObjMap.keySet()) {
            if (stackVarToObjMap.containsKey(stackVar)) {
                for (Object o : stackVarToObjMap.get(stackVar)) {
                    System.out.println(stackVar + "\t" + " --> " + "\t" + o.getName());
                    if (!visited.contains(o)) {
                        printHeap(o);
                    }
                }
            }
        }
    }

    static void printHeap(Object o1) {
        visited.add(o1);
        for (Field f : o1.getFields()) {
            Object o = f.getPointsTo();
            System.out.println(o1.getName() + "\t" + "-" + f.getName() + "->" + "\t" + o.getName());
            printHeap(o);
        }
    }

    static List<String> findKilledVariables(List<Local> before, List<Local> after) {
        List<String> killed = new ArrayList<>();
        for (Local l : before) {
            if (!after.contains(l)) {
                killed.add(l.getName());
            }
        }
        return killed;
    }

    static void printAnswer() {
        Set<String> methods = new TreeSet<>();

        for (String method : methodToGcLines.keySet()) {
            methods.add(method);
            List<String> objects = methodToGcLines.get(method);
            Collections.sort(objects);
            methodToGcLines.put(method, objects);
        }

        for (String method : methods) {
            List<String> objects = methodToGcLines.get(method);
            System.out.print(method + " ");
            for (String object : objects) {
                System.out.print(object + " ");
            }
            System.out.println();
        }

    }

    static HashMap<String, Set<Object>> getCopyOfStack(String methodSign) {
        Map<String, Set<Object>> originalStack = stack.get(methodSign);
        HashMap<String, Set<Object>> copyOfStack = new HashMap<>();

        for (String var : originalStack.keySet()) {
            Set<Object> newObjects = new HashSet<>();
            for (Object object : originalStack.get(var)) {
                getCopyOfStackHelper(object, newObjects);
            }
            copyOfStack.put(var, newObjects);
        }
        return copyOfStack;
    }

    static void getCopyOfStackHelper(Object object, Set<Object> newObjects) {
        Object newObject1 = new Object(object.getName(), object.getInfo());
        if (!containsObject(newObjects, newObject1)) {
            newObjects.add(newObject1);
        }
        for (Field f : object.getFields()) {
            Field newField = new Field(f.getName());
            newObject1.addField(newField);
            if (f.getPointsTo() != null) {
                Object newObject2 = new Object(f.getPointsTo().getName(), f.getPointsTo().getInfo());
                newField.setPointsTo(newObject2);
                getCopyOfStackHelper2(newObject2, f.getPointsTo().getFields(), newObjects);
            }
        }
    }

    static void getCopyOfStackHelper2(Object object1, ArrayList<Field> fields, Set<Object> newObjects) {
        for (Field f : fields) {
            Field newF = new Field(f.getName());
            object1.addField(newF);
            if (f.getPointsTo() != null) {
                Object newObject = new Object(f.getPointsTo().getName(), f.getPointsTo().getInfo());
                newF.setPointsTo(newObject);
                getCopyOfStackHelper2(newObject, f.getPointsTo().getFields(), newObjects);
            }
        }
    }

    static boolean containsObject(Set<Object> objects, Object object) {
        for (Object o : objects) {
            if (isObjectSame(o, object)) {
                return true;
            }
        }
        return false;
    }

    static boolean isObjectSame(Object o1, Object o2) {
        if (o1 != null && o2 != null) {
            if (o1.getName().equals(o2.getName())) {
                return true;
            }
        }
        return false;
    }

}
