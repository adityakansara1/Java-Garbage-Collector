class Node {
    Node f;
    Node g;

    Node() {
    }
}

public class Abc {
    public static Node global;

    public static void main(String[] args) {
        Node a = new Node();
        Node b = new Node();
        Node c = new Node();
        Node ab = null;
        Abc abc = new Abc();
        Node abcd = abc.foo3(); // VirtualInvoke AssignExpr
        if (global.equals(new Node())) {
            a.f = b;
            ab = foo1(); // staticinvoke AssignExpr
            foo2(); // StaticInvoke InvokeExpr
        } else {
            a.f = c;

            foo4();
            a.f = null;
        }
        a.f = null;
        a = (Node) ab;
        a = (Node) abcd;
    }

    static int get() {
        return 1 + 5;
    }

    public static Node foo1() {
        bar1();
        bar2();
        return new Node();
    }

    public static void foo2() {
        bar3();
        bar4();
    }

    public Node foo3() {
        bar5();
        bar6();
        bar7();
        return new Node();
    }

    public static Node foo4() {
        bar8();
        return new Node();
    }

    public static void bar1() {
        System.out.println("Hello");
    }

    public static void bar2() {
        System.out.println("Hello");

    }

    public static void bar3() {
        System.out.println("Hello");

    }

    public static void bar4() {
        System.out.println("Hello");

    }

    public static void bar5() {
        System.out.println("Hello");

    }

    public static void bar6() {
        System.out.println("Hello");

    }

    public static void bar7() {
        System.out.println("Hello");

    }

    public static void bar8() {
        System.out.println("Hello");

    }
}
