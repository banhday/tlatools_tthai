package ic3;

import com.microsoft.z3.*;
import z3parser.Z3Constants;

public class Z3SortSymbol implements Z3Constants {
	private String name;	
	private Sort sort;
	private Symbol symbol;
	
	public Z3SortSymbol(String name, Sort sort, Symbol symbol) {
		this.name = name;
		this.sort = sort;
		this.symbol = symbol;
	}			
	
	public String getName() {
		return this.name;
	}
	
	public Sort getSort() {
		return this.sort;
	}
	
	public Symbol getSymbol() {
		return this.symbol;
	}
}
