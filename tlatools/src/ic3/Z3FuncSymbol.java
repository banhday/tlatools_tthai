package ic3;

import com.microsoft.z3.*;
import z3parser.Z3Constants;

public class Z3FuncSymbol implements Z3Constants {
	private String name;
	private FuncDecl func;
	private Symbol symbol;
	
	public Z3FuncSymbol(String name, FuncDecl func, Symbol symbol) {
		this.name = name;
		this.func = func;
		this.symbol = symbol;
	}
					
	public String getName() {
		return this.name;
	}
	
	public FuncDecl getFunc() {
		return this.func;
	}
	
	public Symbol getSymbol() {
		return this.symbol;
	}
}
