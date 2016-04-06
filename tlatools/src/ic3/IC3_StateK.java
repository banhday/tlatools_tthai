package ic3;

import java.util.*;
import com.microsoft.z3.*;

public class IC3_StateK {
	public BoolExpr formula;
	public BoolExpr p_formula; 
	public int k;
	public IC3_StateK next;
	
	public IC3_StateK() {
		this.formula = null;
		this.p_formula = null;
		this.k = -1;
		this.next = null;
	}
	
	public IC3_StateK(BoolExpr s, BoolExpr p_s, int pos) {
		this.formula = s;
		this.p_formula = p_s;
		this.k = pos;
		this.next = null;
	}
}
