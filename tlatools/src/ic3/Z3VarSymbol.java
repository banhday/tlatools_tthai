package ic3;

import com.microsoft.z3.*;

public class Z3VarSymbol {
	private String name;
	private FuncDecl var;
	private Symbol symbol;
	
	public Z3VarSymbol(String name, FuncDecl expr, Symbol symbol) {
		this.name = name;
		this.var = expr;
		this.symbol = symbol;
	}
	
	public String getName() {
		return this.name;
	}

	public FuncDecl getVar() {
		return this.var;
	}
	
	public Symbol getSymbol() {
		return this.symbol;
	}
}
