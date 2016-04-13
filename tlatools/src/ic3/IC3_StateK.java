package ic3;

import java.util.*;
import com.microsoft.z3.*;

public class IC3_StateK {
	// A state is a conjunction of preds p_1, ..., p_n.
	// Shifted predicates are p'_1, ..., p'_n.
	public BoolExpr[] preds;
	public BoolExpr[] shifted_preds; 
	public int k;
	public IC3_StateK next;
	public Expr[] vars;
	
	public IC3_StateK() {
		this.preds = null;
		this.shifted_preds = null;
		this.k = -1;
		this.next = null;
	}
	
	public IC3_StateK(BoolExpr[] s, BoolExpr[] p_s, int pos) {
		this.preds = s;
		this.shifted_preds = p_s;
		this.k = pos;
		this.next = null;
	}
}
