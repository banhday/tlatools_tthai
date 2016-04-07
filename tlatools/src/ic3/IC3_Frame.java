package ic3;

import java.util.*;
import com.microsoft.z3.*;

public class IC3_Frame {
	// Formula is always P.
	// A clause is always c which is an inductive generalization. 
	// A p_clause is a primed clause.
	public BoolExpr formula;
	public ArrayList<IC3_Clause> clauses;
	public ArrayList<IC3_Clause> p_clauses;
	
	public IC3_Frame() {
		this.formula = null;
		this.clauses = new ArrayList<IC3_Clause>();
		this.p_clauses = new ArrayList<IC3_Clause>();
	}
	
	public boolean hasClause(IC3_Clause c) {
		int alen = this.clauses.size(),
				id = c.id;
		for (int i = 0; i < alen; i++) {
			if (id == this.clauses.get(i).id) {
				return true;
			}
		}
		return false;
	}
}
