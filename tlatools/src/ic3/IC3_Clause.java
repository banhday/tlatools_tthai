package ic3;

import java.util.*;
import com.microsoft.z3.*;

public class IC3_Clause {
	public int id;
	public BoolExpr formula;
	private static int counter = 1;
	
	public IC3_Clause() {
		this.id = this.counter++;
		this.formula = null;
	}
	
	public IC3_Clause(BoolExpr c) {
		this.id = this.counter++;
		this.formula = c;
	}
}
