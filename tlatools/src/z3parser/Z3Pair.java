package z3parser;

public class Z3Pair implements Z3Constants {
	public boolean hasDef;
	public Z3Node def;
	public int depth;
	
	public Z3Pair() {
		this.hasDef = false;
		this.def = new Z3Node(NoName, NoCode, null, null, NoKind, NoSet);
		this.depth = -1;
	}
	
	public void reset() {
		this.hasDef = false;
		this.def = new Z3Node(NoName, NoCode, null, null, NoKind, NoSet);
		this.depth = -1;
	}
	
	public Z3Pair(Z3Node var, Z3Node def, int depth) {
		this.hasDef = true;
		this.def = def;
		this.depth = depth;
	}	
}
