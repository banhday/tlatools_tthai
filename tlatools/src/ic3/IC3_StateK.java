package ic3;

import java.util.*;
import com.microsoft.z3.*;

public class IC3_StateK {
	public BoolExpr[] preds;
	public BoolExpr[] p_preds; 
	public int k;
	public IC3_StateK next;
	
	public IC3_StateK() {
		this.preds = null;
		this.p_preds = null;
		this.k = -1;
		this.next = null;
	}
	
	public IC3_StateK(BoolExpr[] s, BoolExpr[] p_s, int pos) {
		this.preds = s;
		this.p_preds = p_s;
		this.k = pos;
		this.next = null;
	}
}
