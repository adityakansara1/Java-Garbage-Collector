class Test2Node {
	Test2Node f;
	Test2Node g;
	Test2Node() {}
}

public class Pqr {
	public static Test2Node global;
	public static void main(String[] args) {
		foo();
	}
	public static Test2Node foo(){
		Test2Node x = new Test2Node();
		Test2Node y = new Test2Node();
		Test1A a = new Test1A();
		Test1A b = new Test1B();
		x.f = new Test2Node();
		bar(x, y);
		a.baz(x, y);
		b.baz(x, y);
		return x;
	}
	public static void bar(Test2Node p1, Test2Node p2){
		Test2Node v = new Test2Node();
		p1.f = v;	
	}
}

class Test1A {
	public void baz(Test2Node n, Test2Node m) {
		m.f = new Test2Node();
	}
}

class Test1B extends Test1A {
	public void baz(Test2Node n, Test2Node m) {
		Test1A a = new Test1A();
		n.f = new Test2Node();
		System.out.println(a);
	}
}