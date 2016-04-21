package z3parser;

import java.util.ArrayList;

import tlc2.tool.ToolGlobals;
import tlc2.value.ValueConstants;
import util.Assert;

public class Rewriter implements ValueConstants, ToolGlobals, Z3Constants, Z3ErrorCode {
	
	private Z3Encoder z3Encoder;
	private ConstraintChecker constraintChecker;
	private Z3Tool z3Tool;
	private ArrayList<Z3Node> bVars;
	private int depth;

	public Rewriter() {
		// TODO Auto-generated constructor stub
	}
	
	public Rewriter(Z3Encoder z3Encoder, ConstraintChecker checker, Z3Tool z3Tool) {
		this.z3Encoder = z3Encoder;
		this.constraintChecker = checker;
		this.bVars = new ArrayList<Z3Node>();
		this.depth = 0;		
		this.z3Tool = z3Tool;
	}

	// \A x \in {e1, ..., en} : p(x)
	// --> p(e1) iff n = 1
	// --> p(e1) \land ... \land p(en)
	private final Z3Node rewrite_bf_se(Z3Node node) {
		Z3Node set = node.getDomain(0);
		// If n = 0, i.e. the set is empty, replace with TRUE
		if (set.getOperandSize() == 0) {
			return new Z3Node("true", OPCODE_true, this.z3Encoder.boolSort, null, tla_atom, NoSet);			 
		}
		// If n = 1, replace with p(e1)
		else if (set.getOperandSize() == 1) {
			Z3Node x = node.getBoundedVar(0),
					e1 = set.getOperand(0),
					result = node.getExpr(0);
			this.constraintChecker.unifySort_equivSort(x, e1);
			this.z3Tool.replaceNode(x.name, result, e1);
			result = this.rewrite(result);
			result.setSort(this.z3Encoder.boolSort);
			return result;
		}
		// If n > 1, replace with p(e1) \land ... \land p(en)
		else {
			String name = node.getBoundedVar(0).name;
			Z3Node x = node.getBoundedVar(0),
					node1 = node.getExpr(0);
			node1.setSort(this.z3Encoder.boolSort);
			Z3Node result = new Z3Node("and", OPCODE_land, this.z3Encoder.boolSort, null, tla_atom, NoSet);			
			for (int i = 0; i < set.getOperandSize(); i++) {				
				// node1 := p(ei)
				// p(ei) --> rewrite
				Z3Node ei = set.getOperand(i),
						expr = node1.clone();
				this.constraintChecker.unifySort_equivSort(x, ei);
				this.z3Tool.replaceNode(x.name, expr, ei);			
				expr = this.rewrite(expr);
				expr.setSort(this.z3Encoder.boolSort);
				result.addOperand(expr);					
			}	
			return result;
		}					
	}

	// \E x \in {e1, ..., en} : p(x)
	// --> p(e1) iff n = 1
	// --> p(e1) \lor ... \lor p(en)
	private final Z3Node rewrite_be_se(Z3Node node) {		
		Z3Node set = node.getDomain(0);
		// If n = 0, i.e. the set is empty, replace with TRUE
		if (set.getOperandSize() == 0) {
			Z3Node result = new Z3Node("false", OPCODE_false, this.z3Encoder.boolSort, null, tla_atom, NoSet);
			return result;
		}
		// If n = 1, replace with p(e1)
		else if (set.getOperandSize() == 1) {			
			Z3Node x = node.getBoundedVar(0),
					e1 = set.getOperand(0),
					result = node.getExpr(0);
			this.constraintChecker.unifySort_equivSort(x, e1);
			this.z3Tool.replaceNode(x.name, result, e1);
			result = this.rewrite(result);
			result.setSort(this.z3Encoder.boolSort);
			return result;
		}
		// If n > 1, replace with p(e1) \lor ... \lor p(en)
		else {
			String name = node.getBoundedVar(0).name;
			Z3Node x = node.getBoundedVar(0),
					node1 = node.getExpr(0);
			node1.setSort(this.z3Encoder.boolSort);
			Z3Node result = new Z3Node("or", OPCODE_lor, this.z3Encoder.boolSort, null, tla_atom, NoSet);			
			for (int i = 0; i < set.getOperandSize(); i++) {				
				// node1 := p(ei)
				// rewrite p(ei)				
				Z3Node ei = set.getOperand(i),
						expr = node1.clone();
				this.constraintChecker.unifySort_equivSort(x, ei);
				this.z3Tool.replaceNode(x.name, expr, ei);			
				expr = this.rewrite(expr);
				expr.setSort(this.z3Encoder.boolSort);
				result.addOperand(expr);
			}						
			return result;
		}								
	}

	// \A x \in {y \in S : q(y)} : p(x)
	// --> \A x \in S : q(x) => p(x)  
	private final Z3Node rewrite_bf_sso(Z3Node node) {
		Z3Node x = node.getBoundedVar(0),  
				set = node.getDomain(0),
				p = node.getExpr(0),
				y = set.getBoundedVar(0),
				S = set.getDomain(0),
				q = set.getExpr(0),
				result = new Z3Node("forall", OPCODE_bf, this.z3Encoder.boolSort, null, tla_atom, NoSet), 
				newBody = null;		
		this.constraintChecker.unifySort_in(x, S);
		p.setSort(this.z3Encoder.boolSort);
		q.setSort(this.z3Encoder.boolSort);
		this.z3Tool.replaceNode(y.name, q, x);
		q = this.rewrite(q);
		p = this.rewrite(p);		
		result.addBoundedVar(x);							
		//			if (this.z3Encoder.isSort(S)) {
		// newBody := q(x) => p(x)
		newBody = new Z3Node("=>", OPCODE_implies, this.z3Encoder.boolSort, null, q, p, tla_atom, NoSet);		
		//				newBody = this.rewrite(newBody);
		result.addDomain(S);
		result.addExpr(newBody);
		result = this.rewrite(result);
		//			}
		//			else {			
		//				S = this.z3Encoder.getDef(S);
		//				Z3Node sort = this.z3Encoder.getSort(S.getElemSort());
		//				x.setSort(sort.getElemSort());
		//				// con := x \in S
		//				Z3Node con = new Z3Node("in_" + S.getSort().name, OPCODE_in, this.z3Encoder.boolSort, null, x, S, tla_atom, NoSet);												
		//				result.addDomain(sort);
		//				con = this.rewrite(con);			
		//				Z3Node lhsBody = new Z3Node("and", OPCODE_land, this.z3Encoder.boolSort, null, con, q, tla_atom, NoSet);	
		//				// newBody := ((x \in S) \land q(x)) => p(x)		
		//				newBody = new Z3Node("=>", OPCODE_implies, this.z3Encoder.boolSort, null, lhsBody, p, tla_atom, NoSet);			
		//				result.addExpr(newBody);
		//			}		
		return result;								
	}

	// \E x \in {y \in S : q(y)} : p(x)
	// --> \E x \in S : q(x) \land p(x) 
	private final Z3Node rewrite_be_sso(Z3Node node) {
		Z3Node x = node.getBoundedVar(0),  
				set = node.getDomain(0),
				p = node.getExpr(0),
				y = set.getBoundedVar(0),
				S = set.getDomain(0),
				q = set.getExpr(0),
				result = new Z3Node("exists", OPCODE_be, this.z3Encoder.boolSort, null, tla_atom, NoSet), 
				newBody = null;		
		this.constraintChecker.unifySort_in(x, S);
		p.setSort(this.z3Encoder.boolSort);
		q.setSort(this.z3Encoder.boolSort);
		this.z3Tool.replaceNode(y.name, q, x);
		q = this.rewrite(q);
		p = this.rewrite(p);	
		result.addBoundedVar(x);							
		//			if (this.z3Encoder.isSort(S)) {
		// newBody := q(x) \land p(x)
		newBody = new Z3Node("and", OPCODE_land, this.z3Encoder.boolSort, null, q, p, tla_atom, NoSet);		
		//				newBody = this.rewrite(newBody);
		result.addDomain(S);
		result.addExpr(newBody);
		result = this.rewrite(result);
		//			}
		//			else {			
		//				S = this.z3Encoder.getDef(S);
		//				Z3Node sort = this.z3Encoder.getSort(S.getElemSort());
		//				x.setSort(sort.getElemSort());
		//				// con := x \in S
		//				Z3Node con = new Z3Node("in_" + S.getSort().name, OPCODE_in, this.z3Encoder.boolSort, null, x, S, tla_atom, NoSet);			
		//				result.addDomain(sort);
		//				con = this.rewrite(con);			
		//				Z3Node lhsBody = new Z3Node("and", OPCODE_land, this.z3Encoder.boolSort, null, con, q, tla_atom, NoSet);	
		//				// newBody := (x \in S) \land q(x) \land p(x)			
		//				newBody = new Z3Node("and", OPCODE_land, this.z3Encoder.boolSort, null, lhsBody, p, tla_atom, NoSet);			
		//				result.addExpr(newBody);
		//			}				
		return result;											
	}

	// \A x \in {e(y) : y \in S} : p(x)
	// --> \A x \in S : (\E y \in SortY : x = e(y)) => p(x) 
	private final Z3Node rewrite_bf_soa(Z3Node node) {
		Z3Node x = node.getBoundedVar(0),  
				set = node.getDomain(0),
				p = node.getExpr(0),
				y = set.getBoundedVar(0),
				S = set.getDomain(0),
				e = set.getExpr(0),
				eCon 	 	= new Z3Node("exists", OPCODE_be, this.z3Encoder.boolSort, null, tla_atom, NoSet),
				result 	= new Z3Node("forall", OPCODE_bf, this.z3Encoder.boolSort, null, tla_atom, NoSet),
				sortX		= this.z3Encoder.getSort(e.getSort());								
		p.setSort(this.z3Encoder.boolSort);
		p = this.rewrite(p);
		e = this.rewrite(e);
		Z3Node xEey = this.z3Tool.createZ3EqNode(x, e);
		this.constraintChecker.eq_check(xEey);
		xEey = this.rewrite(xEey);				
		//			if (this.z3Encoder.isSort(S)) {	
		eCon.addBoundedVar(y);
		eCon.addDomain(S);
		eCon.addExpr(xEey);
		//			}
		//			else {			
		//				S = this.z3Encoder.getDef(S);
		//				Z3Node sortY = this.z3Encoder.getSort(S.getElemSort());
		//				y.setSort(sortY.getElemSort());
		//				// con := x \in S
		//				Z3Node con = new Z3Node("in_" + S.getSort().name, OPCODE_in, this.z3Encoder.boolSort, null, y, S, tla_atom, NoSet);
		//				con = this.rewrite(con);
		//				Z3Node eBody = new Z3Node("and", OPCODE_land, this.z3Encoder.boolSort, null, con, xEey, tla_atom, NoSet);
		//				eCon.addBoundedVar(y);
		//				eCon.addDomain(sortY);
		//				eCon.addExpr(eBody);					
		//			}				
		Z3Node newBody = new Z3Node("=>", OPCODE_implies, this.z3Encoder.boolSort, null, eCon, p, tla_atom, NoSet);
		result.addBoundedVar(x);
		result.addDomain(S);
		//			newBody = this.rewrite(newBody);
		result.addExpr(newBody);
		result = this.rewrite(result);
		return result;								
	}

	// \E x \in {e(y) : y \in S} : p(x)
	// --> \E x \in S : (\E y \in SortY : x = e(y)) \land p(x)
	private final Z3Node rewrite_be_soa(Z3Node node) {
		Z3Node x = node.getBoundedVar(0),  
				set = node.getDomain(0),
				p = node.getExpr(0),
				y = set.getBoundedVar(0),
				S = set.getDomain(0),
				e = set.getExpr(0),
				eCon 	 	= new Z3Node("exists", OPCODE_be, this.z3Encoder.boolSort, null, tla_atom, NoSet),
				result 	= new Z3Node("exists", OPCODE_be, this.z3Encoder.boolSort, null, tla_atom, NoSet),
				sortX		= this.z3Encoder.getSort(e.getSort());						
		p.setSort(this.z3Encoder.boolSort);
		p = this.rewrite(p);
		e = this.rewrite(e);
		Z3Node xEey = this.z3Tool.createZ3EqNode(x, e);
		this.constraintChecker.eq_check(xEey);
		xEey = this.rewrite(xEey);				
		//			if (this.z3Encoder.isSort(S)) {	
		eCon.addBoundedVar(y);
		eCon.addDomain(S);
		eCon.addExpr(xEey);
		//			}
		//			else {			
		//				S = this.z3Encoder.getDef(S);
		//				Z3Node sortY = this.z3Encoder.getSort(S.getElemSort());
		//				y.setSort(sortY.getElemSort());
		//				// con := x \in S
		//				Z3Node con = new Z3Node("in_" + S.getSort().name, OPCODE_in, this.z3Encoder.boolSort, null, y, S, tla_atom, NoSet);
		//				con = this.rewrite(con);
		//				Z3Node eBody = new Z3Node("and", OPCODE_land, this.z3Encoder.boolSort, null, con, xEey, tla_atom, NoSet);
		//				eCon.addBoundedVar(y);
		//				eCon.addDomain(sortY);
		//				eCon.addExpr(eBody);					
		//			}				
		Z3Node newBody = new Z3Node("and", OPCODE_land, this.z3Encoder.boolSort, null, eCon, p, tla_atom, NoSet);
		result.addBoundedVar(x);
		result.addDomain(sortX);
		//			newBody = this.rewrite(newBody);
		result.addExpr(newBody);
		result = this.rewrite(result);
		return result;							
	}

	private final Z3Node rewrite_be_sor(Z3Node node) {
		Z3Node sor = node.getDomain(0), Si = null, res = null;
		int alen = sor.getFieldSize();
		for (int i = 0; i < alen; i++) {
			Si = sor.getRange(i);
			if (Si.opCode != OPCODE_se) {
				return this.rewrite_be_default(node);
			}
		}
		res = new Z3Node("or", OPCODE_lor, this.z3Encoder.boolSort, null, tla_atom, NoSet);
		int[] pos = new int[alen];
		this.quantified_sor_gen(pos, 0, node, res);
		return res;				
	}

	private final Z3Node rewrite_be_cp(Z3Node node) {
		Z3Node cp = node.getDomain(0), Si = null, res = null;
		int alen = cp.getFieldSize();
		for (int i = 0; i < alen; i++) {
			Si = cp.getOperand(i);
			if (Si.opCode != OPCODE_se) {
				return this.rewrite_bf_default(node);
			}
		}
		res = new Z3Node("or", OPCODE_land, this.z3Encoder.boolSort, null, tla_atom, NoSet);
		int[] pos = new int[alen];
		this.quantified_cp_gen(pos, 0, node, res);
		return res;				
	}

	private final Z3Node rewrite_be_default(Z3Node node) {
		Z3Node result = node,
				set = node.getDomain(0);
		set = this.z3Encoder.getDef(set);
		node.setDomain(0, set);	
		if (!this.z3Encoder.isSort(set)) {
			Z3Node sort = this.z3Encoder.getSort(set.getElemSort()),
					x = result.getBoundedVar(0);
			Z3Node setElemSort = set.getElemSort();						
			x.setSort(setElemSort);				
			Z3Node inSet = new Z3Node("in_" + set.getElemSort().name, OPCODE_in, this.z3Encoder.boolSort, null, x, set, tla_atom, NoSet),
					expr = result.getExpr(0);
			expr.setSort(this.z3Encoder.boolSort);
			inSet = this.rewrite(inSet);
			expr = this.rewrite(expr);				
			Z3Node body = new Z3Node("and", OPCODE_land, this.z3Encoder.boolSort, null, inSet, expr, tla_atom, NoSet);
			body = this.rewrite(body);
			result.setExpr(0, body);
			result.setDomain(0, sort);
		}
		else {
			Z3Node body = result.getExpr(0);
			body = this.rewrite(body);
			result.setExpr(0, body);
		}
		return result;
	}

	// rewriting rules for bounded existential quantifier, \E
	private final Z3Node rewrite_be(Z3Node node) {
		Z3Node result = node,
				set = node.getDomain(0);
		set = this.z3Encoder.getDef(set);
		set = this.rewrite(set);
		node.setDomain(0, set);		
		switch (set.opCode) {
		case OPCODE_se: {
			result = this.rewrite_be_se(node);
			break;
		}
		case OPCODE_sso: {
			result = this.rewrite_be_sso(node);
			break;
		}
		case OPCODE_soa: {
			result = this.rewrite_be_soa(node);
			break;
		}
		case OPCODE_cp: {
			result = this.rewrite_be_cp(node);
			break;
		}
		case OPCODE_sor: {
			result = this.rewrite_be_sor(node);
			break;
		}
		default: {
			result = this.rewrite_be_default(node);
			break;
		}
		}												
		return result;
	}

	private final void quantified_sor_gen(int[] pos, int cur, Z3Node node, Z3Node newNode) {		
		if (cur == pos.length) {
			Z3Node sor = node.getDomain(0),
					bvar = node.getBoundedVar(0),
					body = node.getExpr(0).clone(),
					res = new Z3Node("and", OPCODE_land, this.z3Encoder.boolSort, null, tla_atom, NoSet),
					rcd = this.z3Tool.createBoundedVar(),
					lval = null, rval = null, field = null, cod = null, eq = null;
			this.constraintChecker.unifySort_equivSort(bvar, rcd);
			int alen = pos.length;
			this.z3Encoder.addFreshVar(rcd);
			for (int i = 0; i < alen; i++) {
				field = sor.getField(i);
				cod = sor.getRange(i);
				lval = new Z3Node(NoName, OPCODE_trsl, cod.getSort(), null, rcd, field, cod.kind, cod.setLevel);
				rval = cod.getOperand(pos[i]);
				eq = new Z3Node("=", OPCODE_eq, this.z3Encoder.boolSort, null, lval, rval, tla_atom, NoSet);
				eq = this.rewrite(eq);
				res.addOperand(eq);
			}
			body = this.z3Tool.replaceNode(bvar.name, body, rcd);
			res.addOperand(body);
			newNode.addOperand(res);
		}
		else {
			Z3Node sor = node.getDomain(0),
					S = sor.getRange(cur);
			for (int i = 0; i < S.getOperandSize(); i++) {
				pos[cur] = i;
				this.quantified_sor_gen(pos, cur + 1, node, newNode);
				pos[cur] = -1;
			}
		}
	}

	private final Z3Node rewrite_bf_sor(Z3Node node) {
		Z3Node sor = node.getDomain(0), Si = null, res = null;
		int alen = sor.getFieldSize();
		for (int i = 0; i < alen; i++) {
			Si = sor.getRange(i);
			if (Si.opCode != OPCODE_se) {
				return this.rewrite_bf_default(node);
			}
		}
		res = new Z3Node("and", OPCODE_land, this.z3Encoder.boolSort, null, tla_atom, NoSet);
		int[] pos = new int[alen];
		this.quantified_sor_gen(pos, 0, node, res);
		return res;				
	}			

	private final void quantified_cp_gen(int[] pos, int cur, Z3Node node, Z3Node newNode) {		
		if (cur == pos.length) {
			Z3Node cp = node.getDomain(0),
					bvar = node.getBoundedVar(0),
					body = node.getExpr(0).clone(),
					res = new Z3Node("and", OPCODE_land, this.z3Encoder.boolSort, null, tla_atom, NoSet),
					rcd = this.z3Tool.createBoundedVar(),
					lval = null, rval = null, field = null, cod = null, eq = null;
			this.constraintChecker.unifySort_equivSort(bvar, rcd);
			int alen = pos.length;
			this.z3Encoder.addFreshVar(rcd);
			for (int i = 0; i < alen; i++) {
				field = cp.getField(i);
				cod = cp.getOperand(i);
				lval = new Z3Node(NoName, OPCODE_trsl, cod.getSort(), null, rcd, field, cod.kind, cod.setLevel);
				rval = cod.getOperand(pos[i]);
				eq = new Z3Node("=", OPCODE_eq, this.z3Encoder.boolSort, null, lval, rval, tla_atom, NoSet);
				eq = this.rewrite(eq);
				res.addOperand(eq);
			}
			body = this.z3Tool.replaceNode(bvar.name, body, rcd);
			res.addOperand(body);
			newNode.addOperand(res);
		}
		else {
			Z3Node sor = node.getDomain(0),
					S = sor.getOperand(cur);
			for (int i = 0; i < S.getOperandSize(); i++) {
				pos[cur] = i;
				this.quantified_cp_gen(pos, cur + 1, node, newNode);
				pos[cur] = -1;
			}
		}
	}

	private final Z3Node rewrite_bf_cp(Z3Node node) {
		Z3Node cp = node.getDomain(0), Si = null, res = null;
		int alen = cp.getFieldSize();
		for (int i = 0; i < alen; i++) {
			Si = cp.getOperand(i);
			if (Si.opCode != OPCODE_se) {
				return this.rewrite_bf_default(node);
			}
		}
		res = new Z3Node("and", OPCODE_land, this.z3Encoder.boolSort, null, tla_atom, NoSet);
		int[] pos = new int[alen];
		this.quantified_cp_gen(pos, 0, node, res);
		return res;				
	}

	private final Z3Node rewrite_bf_default(Z3Node node) {
		Z3Node result = node,
				set = node.getDomain(0);
		set = this.z3Encoder.getDef(set);
		node.setDomain(0, set);			
		if (!this.z3Encoder.isSort(set)) {
			Z3Node sort = this.z3Encoder.getSort(set.getElemSort()),
					x = result.getBoundedVar(0);
			this.constraintChecker.unifySort_in(x, set);							
			Z3Node inSet = new Z3Node("in_" + set.getSort().name, OPCODE_in, this.z3Encoder.boolSort, null, x, set, tla_atom, NoSet),
					expr = result.getExpr(0);
			expr.setSort(this.z3Encoder.boolSort);
			inSet = this.rewrite(inSet);
			expr = this.rewrite(expr);				
			Z3Node body = new Z3Node("=>", OPCODE_implies, this.z3Encoder.boolSort, null, inSet, expr, tla_atom, NoSet);
			result.setExpr(0, body);
			result.setDomain(0, sort);
		}
		else {
			Z3Node elemSort = set.getSort().getElemSort(),
					setSort = set.getSort(),
					xSort = node.getBoundedVar(0).getSort(),
					body = result.getExpr(0);
			body = this.rewrite(body);
			if (xSort != setSort && !xSort.name.equals(setSort.name)) {
				result.setDomain(0, elemSort);	
			}			
			result.setExpr(0, body);			
		}
		return result;
	}

	// rewriting rules for bounded universal quantifier, \A
	private final Z3Node rewrite_bf(Z3Node node) {
		Z3Node result = node,
				set = node.getDomain(0);
		set = this.z3Encoder.getDef(set);
		set = this.rewrite(set);
		node.setDomain(0, set);		
		switch (set.opCode) {
		case OPCODE_se: {
			result = this.rewrite_bf_se(node);
			break;
		}
		case OPCODE_sso: {
			result = this.rewrite_bf_sso(node);
			break;
		}
		case OPCODE_soa: {
			result = this.rewrite_bf_soa(node);
			break;
		}
		case OPCODE_cp: {
			result = this.rewrite_bf_cp(node);
			break;
		}
		case OPCODE_sor: {
			result = this.rewrite_bf_sor(node);
			break;
		}
		default: {
			result = this.rewrite_bf_default(node);
			break;
		}
		}										
		return result;
	}

	// x \in {e1, ..., en}
	// --> x = e1 \lor ... \lor x = en iff n > 1
	// --> x = e1 iff n = 1
	// --> FALSE iff n = 0
	private final Z3Node rewrite_in_se(Z3Node node) {
		Z3Node set = node.getOperand(1);
		int alen = set.getOperandSize();
		if (alen == 0) {	// x \in {}
			return new Z3Node("false", OPCODE_false, this.z3Encoder.boolSort, null, tla_atom, NoSet);
		}
		else {
			Z3Node x = node.getOperand(0), 
					result = null;												
			this.constraintChecker.unifySort_in(x, set);
			// --> x = e1 iff n = 1
			if (alen == 1) { // x \in {e1}
				Z3Node e1 = set.getOperand(0);
				this.constraintChecker.unifySort_eq(x, e1);							
				result = this.z3Tool.createZ3EqNode(x, e1);
				result = this.rewrite(result);
				return result;
			}
			// --> x = e1 \lor ... \lor x = en iff n > 1
			else if (alen > 1) {	// x \in {e1, ..., en}
				result = new Z3Node("or", OPCODE_lor, this.z3Encoder.boolSort, null, tla_atom, NoSet);			
				for (int i = 0; i < set.getOperandSize(); i++) {
					Z3Node ei = set.getOperand(i);	
					this.constraintChecker.unifySort_eq(x, ei);
					Z3Node expr = this.z3Tool.createZ3EqNode(x, ei);
					expr = this.rewrite(expr);
					result.addOperand(expr);
				}							
			}
			return result;
		}
	}

	// x \in {y \in S: p(y)}
	// --> x \in S \land p(x)
	private final Z3Node rewrite_in_sso(Z3Node node) {
		Z3Node x 	= node.getOperand(0),
				set = node.getOperand(1),
				y	  = set.getBoundedVar(0),
				S		= set.getDomain(0),
				p	  = set.getExpr(0);		
		S = this.z3Encoder.getDef(S);
		this.constraintChecker.unifySort_in(x, S);
		Z3Node inS = new Z3Node("in_" + S.getSort().name, OPCODE_in, this.z3Encoder.boolSort, null, x, S, tla_atom, NoSet);		
		p = this.z3Tool.replaceNode(y.name, p, x);
		p.setSort(this.z3Encoder.boolSort);
		p	= this.rewrite(p);
		inS = this.rewrite(inS);		
		Z3Node result = new Z3Node("and", OPCODE_land, this.z3Encoder.boolSort, null, inS, p, tla_atom, NoSet);		
		return result;
	}

	// x \in { e(y) : y \in S }
	// --> \E y \in S : x = e(y)
	private final Z3Node rewrite_in_soa(Z3Node node) {
		Z3Node x 	= node.getOperand(0),
				set = node.getOperand(1),
				y	  = set.getBoundedVar(0),
				S		= set.getDomain(0),
				ey  = set.getExpr(0);				
		S = this.z3Encoder.getDef(S);
		this.constraintChecker.unifySort_in(y, S);
		ey = this.rewrite(ey);					
		Z3Node xEey = this.z3Tool.createZ3EqNode(x, ey);
		this.constraintChecker.eq_check(xEey);		
		Z3Node result = new Z3Node("exists", OPCODE_be, this.z3Encoder.boolSort, null, tla_atom, NoSet);
		result.addBoundedVar(y);
		result.addDomain(S);
		result.addExpr(xEey);
		result = this.rewrite(result);
		return result;
	}

	// S \in SUBSET T
	// --> \A x \in Sort : x \in S => x \in T
	private final Z3Node rewrite_in_subset(Z3Node node) {
		Z3Node S = node.getOperand(0),
				T 	= node.getOperand(1).getOperand(0);
		S = this.z3Encoder.getDef(S);
		T = this.z3Encoder.getDef(T);
		Z3Node sortX = this.z3Encoder.getElemSort(S, T),
				x = this.z3Tool.createBoundedVar();		
		this.constraintChecker.unifySort_in(x, S);
		this.constraintChecker.unifySort_in(x, T);
		Z3Node inS = new Z3Node("in_" + S.getSort().name, OPCODE_in, this.z3Encoder.boolSort, null, x, S, tla_atom, NoSet),		
				inT = new Z3Node(T.getElemSort().name + "_in", OPCODE_in, this.z3Encoder.boolSort, null, x, T, tla_atom, NoSet);
		inS = this.rewrite(inS);
		inT = this.rewrite(inT);
		Z3Node newBody = new Z3Node("=>", OPCODE_implies, this.z3Encoder.boolSort, null, inS, inT, tla_atom, NoSet),				
				result = new Z3Node("forall", OPCODE_bf, this.z3Encoder.boolSort, null, tla_atom, NoSet);				
		result.addBoundedVar(x);
		result.addDomain(sortX);
		result.addExpr(newBody);
		return result;		
	}

	// x \in UNION S
	// --> \E T \in S : x \in T
	private final Z3Node rewrite_in_union(Z3Node node) {
		Z3Node x = node.getOperand(0),
				S = node.getOperand(1).getOperand(0),
				T = this.z3Tool.createBoundedVar();				
		S = this.z3Encoder.getDef(S);
		this.constraintChecker.unifySort_in(T, S);
		this.constraintChecker.unifySort_in(x, T);
		Z3Node inT = new Z3Node(T.getElemSort().name + "_in", OPCODE_in, this.z3Encoder.boolSort, null, x, T, tla_atom, NoSet);		
		//			inT = this.rewrite(inT);
		Z3Node result = new Z3Node("exists", OPCODE_be, this.z3Encoder.boolSort, null, tla_atom, NoSet);		
		result.addBoundedVar(T);
		result.addDomain(S);
		result.addExpr(inT);
		result = this.rewrite(result);
		return result;		
	}

	// x \in e1 \cup e2
	// --> x \in e1 \cup x \in e2
	private final Z3Node rewrite_in_cup(Z3Node node) {
		Z3Node x = node.getOperand(0),				
				expr = node.getOperand(1),
				e1	 = expr.getOperand(0),
				e2	 = expr.getOperand(1),
				sortX= this.z3Encoder.getElemSort(e1, e2);		
		e1 = this.z3Encoder.getDef(e1);
		e2 = this.z3Encoder.getDef(e2);
		this.constraintChecker.unifySort_in(x, e1);
		this.constraintChecker.unifySort_in(x, e2);
		Z3Node	inE1= new Z3Node(e1.getElemSort().name + "_in", OPCODE_in, this.z3Encoder.boolSort, null, x, e1, tla_atom, NoSet),
				inE2= new Z3Node(e2.getElemSort().name + "_in", OPCODE_in, this.z3Encoder.boolSort, null, x, e2, tla_atom, NoSet);
		inE1 = this.rewrite(inE1);
		inE2 = this.rewrite(inE2);
		return new Z3Node("or", OPCODE_lor, this.z3Encoder.boolSort, null, inE1, inE2, tla_atom, NoSet);			
	}

	// x \in e1 \cap e2
	// --> x \in e1 \cap x \in e2
	private final Z3Node rewrite_in_cap(Z3Node node) {
		Z3Node x = node.getOperand(0),				
				expr = node.getOperand(1),
				e1	 = expr.getOperand(0),
				e2	 = expr.getOperand(1);
		e1 = this.z3Encoder.getDef(e1);
		e2 = this.z3Encoder.getDef(e2);		
		this.constraintChecker.unifySort_in(x, e1);
		this.constraintChecker.unifySort_in(x, e2);
		Z3Node inE1= new Z3Node(e1.getElemSort().name + "_in", OPCODE_in, this.z3Encoder.boolSort, null, x, e1, tla_atom, NoSet),
				inE2= new Z3Node(e2.getElemSort().name + "_in", OPCODE_in, this.z3Encoder.boolSort, null, x, e2, tla_atom, NoSet);
		inE1 = this.rewrite(inE1);
		inE2 = this.rewrite(inE2);
		return new Z3Node("and", OPCODE_land, this.z3Encoder.boolSort, null, inE1, inE2, tla_atom, NoSet);		
	}

	// x \in e1 \ e2
	// --> x \in e1 \land \lnot (x \in e2)
	private final Z3Node rewrite_in_setdiff(Z3Node node) {
		Z3Node x = node.getOperand(0),				
				expr = node.getOperand(1),
				e1	 = expr.getOperand(0),
				e2	 = expr.getOperand(1);		
		e1 = this.z3Encoder.getDef(e1);
		e2 = this.z3Encoder.getDef(e2);		
		this.constraintChecker.unifySort_in(x, e1);
		this.constraintChecker.unifySort_in(x, e2);
		Z3Node	inE1= new Z3Node(e1.getElemSort().name + "_in", OPCODE_in, this.z3Encoder.boolSort, null, x, e1, tla_atom, NoSet),
				inE2= new Z3Node(e2.getElemSort().name + "_in", OPCODE_in, this.z3Encoder.boolSort, null, x, e2, tla_atom, NoSet);
		inE1 = this.rewrite(inE1);
		inE2 = this.rewrite(inE2);	
		Z3Node notInE2 = new Z3Node("not", OPCODE_lnot, this.z3Encoder.boolSort, null, inE2, tla_atom, NoSet);
		return new Z3Node("and", OPCODE_land, this.z3Encoder.boolSort, null, inE1, notInE2, tla_atom, NoSet);
	}

	// x \notin S
	// --> \lnot ( x \in S )
	private final Z3Node rewrite_notin(Z3Node node) {
		Z3Node x = node.getOperand(0),
				S = node.getOperand(1);			
		S = this.z3Encoder.getDef(S);
		this.constraintChecker.unifySort_in(x, S);
		Z3Node inS = new Z3Node("in_" + S.getSort().name, OPCODE_in, this.z3Encoder.boolSort, null, x, S, tla_atom, NoSet);
		inS = this.rewrite(inS);
		return new Z3Node("not", OPCODE_lnot, this.z3Encoder.boolSort, null, inS, tla_atom, NoSet);							
	}		

	// S \subseteq T
	// --> \A x \in Sort : x \in S => x \in T
	private final Z3Node rewrite_subseteq(Z3Node node) {
		Z3Node S = node.getOperand(0),
				T = node.getOperand(1);
		S = this.z3Encoder.getDef(S);		
		T = this.z3Encoder.getDef(T);		
		Z3Node sortX = this.z3Encoder.getElemSort(S, T),
				x 	= this.z3Tool.createBoundedVar();
		this.constraintChecker.unifySort_in(x, S);
		this.constraintChecker.unifySort_in(x, T);
		Z3Node	inS	 = new Z3Node("in_" + S.getSort().name, OPCODE_in, this.z3Encoder.boolSort, null, x, S, tla_atom, NoSet),
				inT	 = new Z3Node(T.getElemSort().name + "_in", OPCODE_in, this.z3Encoder.boolSort, null, x, T, tla_atom, NoSet);
		inS = this.rewrite(inS);
		inT = this.rewrite(inT);
		Z3Node	newBody = new Z3Node("=>", OPCODE_implies, this.z3Encoder.boolSort, null, inS, inT, tla_atom, NoSet),
				result = new Z3Node("forall", OPCODE_bf, this.z3Encoder.boolSort, null, tla_atom, NoSet);		
		result.addBoundedVar(x);
		result.addDomain(sortX);
		result.addExpr(newBody);	
		return result;		
	}

	// S = {}
	// --> \A x \in Sort : \lnot (x \in S)
	//		private final Z3Node rewrite_eq_ept(Z3Node node) {
	//			Z3Node S = node.getOperand(0),
	//					sort = this.z3Encoder.getElemSort(S),				
	//					x = this.z3Tool.createBoundedVar();		
	//			S = this.z3Encoder.getDef(S);
	//			this.constraintChecker.unifySort_in(x, S);
	//			Z3Node	inS	= new Z3Node("in_" + S.getSort().name, OPCODE_in, this.z3Encoder.boolSort, null, x, S, tla_atom, NoSet);
	//			inS = this.rewrite(inS);
	//			Z3Node newBody = new Z3Node("not", OPCODE_lnot, this.z3Encoder.boolSort, null, inS, tla_atom, NoSet),
	//					result = new Z3Node("forall", OPCODE_bf, this.z3Encoder.boolSort, null, tla_atom, NoSet);
	//			result.addBoundedVar(x);
	//			result.addDomain(sort);
	//			result.addExpr(newBody);
	//			return result;		
	//		}
	// S = empty 
	private final Z3Node rewrite_eq_ept(Z3Node node) {
		Z3Node S = node.getOperand(0),
				sort = S.getSort(),
				emptySet = new Z3Node("empty_" + sort.name, OPCODE_se, sort, null, tla_set, sort.setLevel),
				res = new Z3Node("=", OPCODE_eq, this.z3Encoder.boolSort, null, S, emptySet, tla_atom, 0);		
		return res;
	}

	// S = {e1, ..., en}
	// --> \A x \in Sort : x \in S \equiv (x = e1) \lor ... \lor (x = en) iff n > 1
	// --> \A x \in Sort : x \in S \equiv (x = e1) iff n = 1
	// --> \A x \in Sort : not (x \in S) iff n = 0
	private final Z3Node rewrite_eq_se(Z3Node node) {
		Z3Node set = node.getOperand(1);				
		int alen = set.getOperandSize();
		if (alen == 0) {
			return this.rewrite_eq_ept(node); 	// --> \A x \in Sort : not (x \in S) iff n = 0
		}
		else {			
			Z3Node S = node.getOperand(0),
					sort = this.z3Encoder.getElemSort(S, set),
					x 	 = this.z3Tool.createBoundedVar();
			this.constraintChecker.unifySort_in(x, S);
			S = this.z3Encoder.getDef(S);			
			Z3Node	inS	  = new Z3Node("in_" + S.getSort().name, OPCODE_in, this.z3Encoder.boolSort, null, x, S, tla_atom, NoSet),
					newBody= new Z3Node("=", OPCODE_eq, this.z3Encoder.boolSort, null, tla_atom, NoSet);
			inS = this.rewrite(inS);
			newBody.addOperand(inS);
			if (alen == 1) {
				// --> \A x \in Sort : x \in S \equiv (x = e1) iff n = 1
				//					Z3Node eq1 = this.z3Tool.createZ3EqNode(x, set.getOperand(0));
				Z3Node e1 = set.getOperand(0);
				Z3Node xSort = x.getSort(), 
						e1Sort = e1.getSort();
				x.setSort(e1Sort);				
				e1.setSort(xSort);				
				this.constraintChecker.unifySort_eq(x, e1);
				Z3Node eq1 = this.z3Tool.createZ3EqNode(x, e1);				
				eq1 = this.rewrite(eq1);
				newBody.addOperand(eq1);
			}
			else if (alen > 1) {
				// --> \A x \in Sort : x \in S \equiv (x = e1) \lor ... \lor (x = en) iff n > 1
				Z3Node or_op = new Z3Node("or", OPCODE_lor, this.z3Encoder.boolSort, null, tla_atom, NoSet);
				for (int i = 0; i < alen; i++) {
					Z3Node ei = set.getOperand(i);
					Z3Node xSort = x.getSort(), 							
							eiSort = ei.getSort();
					x.setSort(eiSort);					
					ei.setSort(xSort);
					this.constraintChecker.unifySort_eq(x, ei);
					Z3Node eqi = this.z3Tool.createZ3EqNode(x, ei);
					eqi = this.rewrite(eqi);
					or_op.addOperand(eqi);
				}
				newBody.addOperand(or_op);
			}
			Z3Node	result = new Z3Node("forall", OPCODE_bf, this.z3Encoder.boolSort, null, tla_atom, NoSet);										
			result.addDomain(sort);
			result.addBoundedVar(x);				
			result.addExpr(newBody);
			return result;
		}					
	}

	// S = SUBSET T
	// --> \A x \in SrtX : x \in S <=> (\A y \in SortY : y \in x => y \in T)
	private final Z3Node rewrite_eq_subset(Z3Node node) {
		Z3Node S = node.getOperand(0),
				T = node.getOperand(1).getOperand(0),
				sortX = this.z3Encoder.getElemSort(S),
				x = this.z3Tool.createBoundedVar();		
		x.setSort(sortX);				
		Z3Node y = this.z3Tool.createBoundedVar(),
				sortY = this.z3Encoder.getElemSort(T, x);
		y.setSort(sortY);
		S = this.z3Encoder.getDef(S);
		T = this.z3Encoder.getDef(T);
		this.constraintChecker.unifySort_in(x, S);
		this.constraintChecker.unifySort_in(y, x);
		this.constraintChecker.unifySort_in(y, T);
		Z3Node inS = new Z3Node("in_" + S.getSort().name, OPCODE_in, this.z3Encoder.boolSort, null, x, S, tla_atom, NoSet),
				inT = new Z3Node(T.getElemSort().name + "_in", OPCODE_in, this.z3Encoder.boolSort, null, y, T, tla_atom, NoSet),
				inX	= new Z3Node(x.getElemSort().name + "_in", OPCODE_in, this.z3Encoder.boolSort, null, y, x, tla_atom, NoSet);
		inS = this.rewrite(inS);
		inT = this.rewrite(inT);
		inX = this.rewrite(inX);
		Z3Node bfBody = new Z3Node("=>", OPCODE_implies, this.z3Encoder.boolSort, null, inX, inT, tla_atom, NoSet), //  y \in x => y \in T				
				bfFrm	= new Z3Node("forall", OPCODE_bf, this.z3Encoder.boolSort, null, tla_atom, NoSet);				 // (\A y \in SortY : y \in x => y \in T)
		bfFrm.addBoundedVar(y);
		bfFrm.addDomain(sortY);
		bfFrm.addExpr(bfBody);
		bfFrm = this.rewrite(bfFrm);
		Z3Node	newBody = this.z3Tool.createZ3EqNode(inS, bfFrm),		 // x \in S <=> (\A y \in SortY : y \in x => y \in T)				
				result = new Z3Node("forall", OPCODE_bf, this.z3Encoder.boolSort, null, tla_atom, NoSet);
		result.addBoundedVar(x);
		result.addDomain(sortX);
		result.addExpr(newBody);		
		return result;
	}

	// S = UNION T
	// --> \A x \in SortX : x \in S <=> (\E y \in SortY : y \in T /\ x \in y)
	private final Z3Node rewrite_eq_union(Z3Node node) {
		Z3Node S = node.getOperand(0),
				T = node.getOperand(1).getOperand(0),
				x = this.z3Tool.createBoundedVar(),
				y = this.z3Tool.createBoundedVar(),
				sortX = this.z3Encoder.getElemSort(S, y),
				sortY = this.z3Encoder.getElemSort(T);
		x.setSort(sortX);
		y.setSort(sortY);				
		S = this.z3Encoder.getDef(S);
		T = this.z3Encoder.getDef(T);
		S.setSort(sortX);
		T.setSort(sortY);
		this.constraintChecker.unifySort_in(x, S);
		this.constraintChecker.unifySort_in(y, T);
		this.constraintChecker.unifySort_in(x, y);
		Z3Node inS = new Z3Node("in_" + S.getSort().name, OPCODE_in, this.z3Encoder.boolSort, null, x, S, tla_atom, NoSet),
				inT = new Z3Node(T.getElemSort().name + "_in", OPCODE_in, this.z3Encoder.boolSort, null, y, T, tla_atom, NoSet),
				inY	= new Z3Node(y.getElemSort().name + "_in", OPCODE_in, this.z3Encoder.boolSort, null, x, y, tla_atom, NoSet);
		inS = this.rewrite(inS);
		inT = this.rewrite(inT);
		inY = this.rewrite(inY);
		Z3Node beBody = new Z3Node("and", OPCODE_land, this.z3Encoder.boolSort, null, inT, inY, tla_atom, NoSet), 	// y \in T \land x \in y				
				beFrm	= new Z3Node("exists", OPCODE_be, this.z3Encoder.boolSort, null, tla_atom, NoSet);				// (\E y \in SortY : y \in T \land x \in y)
		beFrm.addBoundedVar(y);
		beFrm.addDomain(sortY);
		beFrm.addExpr(beBody);
		beFrm = this.rewrite(beFrm);
		Z3Node	newBody = this.z3Tool.createZ3EqNode(inS, beFrm),		// x \in S <=> (\E y \in SortY : y \in T \land x \in y)				
				result = new Z3Node("forall", OPCODE_bf, this.z3Encoder.boolSort, null, tla_atom, NoSet);
		result.addBoundedVar(x);
		result.addDomain(sortX);
		result.addExpr(newBody);
		result = this.rewrite(result);
		return result;
	}

	// S = { x \in T : p(x) }
	// --> \A x \in Sort : x \in S <=> x \in T /\ p(x)
	private final Z3Node rewrite_eq_sso(Z3Node node) {
		Z3Node S = node.getOperand(0),
				set	= node.getOperand(1),
				T = set.getDomain(0),
				x = set.getBoundedVar(0),
				sortX = this.z3Encoder.getElemSort(S, T);
		x.setSort(sortX);
		S = this.z3Encoder.getDef(S);
		T = this.z3Encoder.getDef(T);		
		this.constraintChecker.unifySort_in(x, S);
		this.constraintChecker.unifySort_in(x, T);		
		Z3Node p = set.getExpr(0),
				inS	= new Z3Node("in_" + S.getSort().name, OPCODE_in, this.z3Encoder.boolSort, null, x, S, tla_atom, NoSet),
				inT = new Z3Node(T.getElemSort().name + "_in", OPCODE_in, this.z3Encoder.boolSort, null, x, T, tla_atom, NoSet);		
		inS = this.rewrite(inS);
		inT = this.rewrite(inT);
		p =  this.rewrite(p);
		Z3Node rhs	= new Z3Node("and", OPCODE_land, this.z3Encoder.boolSort, null, inT, p, tla_atom, NoSet), 
				newBody	= this.z3Tool.createZ3EqNode(inS, rhs),				
				result 	= new Z3Node("forall", OPCODE_bf, this.z3Encoder.boolSort, null, tla_atom, NoSet);																				
		result.addBoundedVar(x);		
		result.addDomain(sortX);
		result.addExpr(newBody);						
		return result;
	}

	// S = { e(y) : y \in T }
	// --> \A x \in SortX : x \in S <=> (\E y \in SortY : y \in T \land x = e(y))
	private final Z3Node rewrite_eq_soa(Z3Node node) {
		Z3Node S = node.getOperand(0),
				set	= node.getOperand(1),
				T 	= set.getDomain(0),
				y 	= set.getBoundedVar(0),				
				ey	= set.getExpr(0),
				x		= this.z3Tool.createBoundedVar(),
				sortX = this.z3Encoder.getElemSort(S, ey), 
				sortY = this.z3Encoder.getElemSort(T);		
		x.setSort(sortX);		
		ey.setSort(sortX);
		y.setSort(sortY);
		S = this.z3Encoder.getDef(S);
		T = this.z3Encoder.getDef(T);
		this.constraintChecker.unifySort_in(x, S);
		this.constraintChecker.unifySort_in(y, T);
		this.constraintChecker.unifySort_eq(x, ey);
		Z3Node inS = new Z3Node("in_" + S.getSort().name, OPCODE_in, this.z3Encoder.boolSort, null, x, S, tla_atom, NoSet),
				inT = new Z3Node(T.getElemSort().name + "_in", OPCODE_in, this.z3Encoder.boolSort, null, y, T, tla_atom, NoSet),
				xEey = this.z3Tool.createZ3EqNode(x, ey);			// x = e(y)
		inS = this.rewrite(inS);
		inT = this.rewrite(inT);
		xEey	= this.rewrite(xEey);
		Z3Node eBody = new Z3Node("and", OPCODE_land, this.z3Encoder.boolSort, null, inT, xEey, tla_atom, NoSet),  // y \in T \land x = e(y)				
				eFrm		= new Z3Node("exists", OPCODE_be, this.z3Encoder.boolSort, null, tla_atom, NoSet);  		// (\E y \in SortY : y \in T \land x = e(y)
		eFrm.addBoundedVar(y);
		eFrm.addDomain(sortY);
		eFrm.addExpr(eBody);		
		Z3Node newBody = this.z3Tool.createZ3EqNode(inS, eFrm),																	
				result= new Z3Node("forall", OPCODE_bf, this.z3Encoder.boolSort, null, tla_atom, NoSet);																				
		result.addBoundedVar(x);
		result.addDomain(sortX);
		result.addExpr(newBody);		
		return result;
	}

	// S = T \cup U
	// --> \A x \in Sort : x \in S <=> x \in T \land x \in U
	private final Z3Node rewrite_eq_cup(Z3Node node) {
		Z3Node S = node.getOperand(0),
				set		= node.getOperand(1),
				T 		= set.getOperand(0),
				U 		= set.getOperand(1),				
				x			= this.z3Tool.createBoundedVar(),
				sort	= this.z3Encoder.getElemSort(S, T, U);
		x.setSort(sort);
		S = this.z3Encoder.getDef(S);
		T = this.z3Encoder.getDef(T);
		U = this.z3Encoder.getDef(U);		
		this.constraintChecker.unifySort_in(x, S);
		this.constraintChecker.unifySort_in(x, T);
		this.constraintChecker.unifySort_in(x, U);		
		Z3Node inS = new Z3Node("in_" + S.getSort().name, OPCODE_in, this.z3Encoder.boolSort, null, x, S, tla_atom, NoSet),
				inT	= new Z3Node(T.getElemSort().name + "_in", OPCODE_in, this.z3Encoder.boolSort, null, x, T, tla_atom, NoSet),
				inU = new Z3Node(U.getElemSort().name + "_in", OPCODE_in, this.z3Encoder.boolSort, null, x, U, tla_atom, NoSet);
		inS = this.rewrite(inS);
		inT = this.rewrite(inT);
		inU = this.rewrite(inU);
		Z3Node	inTU = new Z3Node("or", OPCODE_lor, this.z3Encoder.boolSort, null, inT, inU, tla_atom, NoSet), 						
				newBody	= this.z3Tool.createZ3EqNode(inS, inTU),				
				result	= new Z3Node("forall", OPCODE_bf, this.z3Encoder.boolSort, null, tla_atom, NoSet);																						
		result.addBoundedVar(x);		
		result.addDomain(sort);
		result.addExpr(newBody);				
		result = this.rewrite(result);
		return result;
	}

	// S = T \cap U
	// --> \A x \in Sort : x \in S <=> x \in T \land x \in U
	private final Z3Node rewrite_eq_cap(Z3Node node) {
		Z3Node S = node.getOperand(0),
				set	 = node.getOperand(1),
				T 	 = set.getOperand(0),
				U 	 = set.getOperand(1),				
				x		 = this.z3Tool.createBoundedVar(),
				sort = this.z3Encoder.getElemSort(S, T, U);
		x.setSort(sort);		
		S = this.z3Encoder.getDef(S);
		T = this.z3Encoder.getDef(T);
		U = this.z3Encoder.getDef(U);
		this.constraintChecker.unifySort_in(x, S);
		this.constraintChecker.unifySort_in(x, T);
		this.constraintChecker.unifySort_in(x, U);
		Z3Node inS = new Z3Node("in_" + S.getSort().name, OPCODE_in, this.z3Encoder.boolSort, null, x, S, tla_atom, NoSet),
				inT	= new Z3Node(T.getElemSort().name + "_in", OPCODE_in, this.z3Encoder.boolSort, null, x, T, tla_atom, NoSet),
				inU = new Z3Node(U.getElemSort().name + "_in", OPCODE_in, this.z3Encoder.boolSort, null, x, U, tla_atom, NoSet);
		inS = this.rewrite(inS);
		inT = this.rewrite(inT);
		inU = this.rewrite(inU);
		Z3Node	inTU = new Z3Node("and", OPCODE_land, this.z3Encoder.boolSort, null, inT, inU, tla_atom, NoSet), 						
				newBody	= this.z3Tool.createZ3EqNode(inS, inTU),				
				result	= new Z3Node("forall", OPCODE_bf, this.z3Encoder.boolSort, null, tla_atom, NoSet);																						
		result.addBoundedVar(x);		
		result.addDomain(sort);
		result.addExpr(newBody);				
		result = this.rewrite(result);
		return result;
	}

	// S = T \ U
	// --> \A x \in Sort : x \in S <=> x \in T \land \lnot (x \in U)
	private final Z3Node rewrite_eq_setdiff(Z3Node node) {
		Z3Node S = node.getOperand(0),
				set	 = node.getOperand(1),
				T 	 = set.getOperand(0),
				U 	 = set.getOperand(1),				
				x		 = this.z3Tool.createBoundedVar(),
				sort = this.z3Encoder.getElemSort(S, T, U);
		x.setSort(sort);
		S = this.z3Encoder.getDef(S);
		T = this.z3Encoder.getDef(T);
		U = this.z3Encoder.getDef(U);		
		this.constraintChecker.unifySort_in(x, S);
		this.constraintChecker.unifySort_in(x, T);
		this.constraintChecker.unifySort_in(x, U);
		Z3Node inS = new Z3Node("in_" + S.getSort().name, OPCODE_in, this.z3Encoder.boolSort, null, x, S, tla_atom, NoSet),
				inT		= new Z3Node(T.getElemSort().name + "_in", OPCODE_in, this.z3Encoder.boolSort, null, x, T, tla_atom, NoSet),
				inU  	= new Z3Node(U.getElemSort().name + "_in", OPCODE_in, this.z3Encoder.boolSort, null, x, U, tla_atom, NoSet);				
		inS = this.rewrite(inS);
		inT = this.rewrite(inT);
		inU = this.rewrite(inU);
		Z3Node	notInU = new Z3Node("not", OPCODE_lnot, this.z3Encoder.boolSort, null, inU, tla_atom, NoSet),
				inTnotInU	= new Z3Node("and", OPCODE_land, this.z3Encoder.boolSort, null, inT, notInU, tla_atom, NoSet), 						
				newBody	= this.z3Tool.createZ3EqNode(inS, inTnotInU),				
				result	= new Z3Node("forall", OPCODE_bf, this.z3Encoder.boolSort, null, tla_atom, NoSet);																						
		result.addBoundedVar(x);		
		result.addDomain(sort);
		result.addExpr(newBody);						
		return result;
	}

	// \A x : x \in S <=> x \in T
	// --> S = T
	private final Z3Node rewrite_bf_in_in(Z3Node node) {
		Z3Node e	= node.getExpr(0),
				inS	= e.getOperand(0),
				inT	= e.getOperand(1),
				S 	= inS.getOperand(1),
				T 	= inT.getOperand(1);	
		Z3Node result= this.z3Tool.createZ3EqNode(S, T);							
		result = this.rewrite(result);
		return result;
	}

	// f[a] ~ [ x \in S |-> e(x) ][ a ] 
	// --> e(a)
	private final Z3Node rewrite_fa_fc(Z3Node node) {
		Z3Node f = node.getOperand(0),				
				a  = node.getOperand(1),
				fc = this.z3Encoder.getDef(f),	
				x	 = fc.getBoundedVar(0),
				S  = fc.getDomain(0),
				e	 = fc.getExpr(0),
				sortA = this.z3Encoder.getSort(S.getElemSort()); 		
		a.setSort(sortA);
		S = this.z3Encoder.getDef(S);
		this.constraintChecker.unifySort_in(a, S);
		//			Z3Node inS = new Z3Node("in_" + S.getSort().name, OPCODE_in, this.z3Encoder.boolSort, null, a, S, tla_atom, NoSet),
		//					iap = new Z3Node("iapply", OPCODE_iapply, null, null, tla_atom, NoSet);
		//			if (a.getSort().name.equals("Int")) {
		//				iap.addOperand(f);
		//				iap.addOperand(a);
		//			}
		//			else {
		//				Z3Node m2i	= new Z3Node(a.getSort().name + "2int", OPCODE_2int, this.z3Encoder.intSort, null, a, tla_atom, NoSet);
		//				iap.addOperand(f);
		//				iap.addOperand(m2i);
		//			}		
		e = this.z3Tool.replaceNode(x.name, e, a);
		e = this.rewrite(e);
		return e;
		//			inS = this.rewrite(inS);
		//			Z3Node result= new Z3Node("ite", OPCODE_ite, null, null, NoKind, iNull);
		//			result.addOperand(inS);
		//			result.addOperand(e);
		//			result.addOperand(iap);
		//			return result;
	}

	// fc[a]  ~ [ f EXCEPT ![x] = y ][ a ]
	// --> IF x = a THEN y ELSE alpha(f, a)) 
	// In this translation, we assume that a is always in DOMAIN f
	private final Z3Node rewrite_fa_exc(Z3Node node) {
		Z3Node fc = node.getOperand(0),
				a   = node.getOperand(1),
				exc = this.z3Encoder.getDef(fc),	
				f 	= exc.getOperand(0),
				x		= exc.getOperand(1),
				y 	= exc.getOperand(2);				
		f = this.z3Encoder.getDef(f);
		this.constraintChecker.unifySort_equivSort(a, x);
		this.constraintChecker.unifySort_equivSort(y, f.cod);
		String nodeName = f.getSort().name + "_" + x.getSort().name + "_apply_" + y.getSort().name;
		Z3Node xEa	= this.z3Tool.createZ3EqNode(x, a),
				app	= new Z3Node(nodeName, OPCODE_alpha, y.getSort(), null, f, a, f.cod.kind, f.cod.setLevel);		
		xEa = this.rewrite(xEa);
		app = this.rewrite(app);
		y 	= this.rewrite(y);
		Z3Node	result = new Z3Node("ite", OPCODE_ite, null, null, xEa, y, app, NoKind, iNull);
		this.constraintChecker.ite_check(result);
		return result;
	}

	// f[a]
	// --> f[a]
	// In this translation, we assume that a is always in DOMAIN f
	private final Z3Node rewrite_fa_default(Z3Node node) {
		Z3Node f = node.getOperand(0),
				a   = node.getOperand(1);
		if (f.getRangeSize() == 0) {
			Assert.fail(NoSortErr, "We don't know the codomain (range) of " + f.name);
		}
		String nodeName = f.getSort().name + "_" + a.getSort().name + "_apply_" + f.getRange(0).name;
		node.name = nodeName;
		return node;
	}

	// fcn[a]
	private final Z3Node rewrite_fa(Z3Node node) {
		Z3Node result = node, 
				lhs = node.getOperand(0),
				dlhs = this.z3Encoder.getDef(lhs),
				rhs = node.getOperand(1),
				drhs = this.z3Encoder.getDef(rhs);			
		dlhs = this.rewrite(dlhs);		
		drhs = this.rewrite(drhs);
		if (drhs.opCode != OPCODE_tup && drhs.opCode != OPCODE_rc) {
			node.setOperand(1, drhs);		
		}		
		if (result.getOperand(1).opCode == OPCODE_ite) {
			result = this.rewrite_binary_ite(node);
		}
		if (result.opCode == OPCODE_fa) {
			switch (dlhs.opCode) {
			case OPCODE_fc:
			case OPCODE_nrfs: {		// [ x \in S |-> e(x) ][ a ]
				result = this.rewrite_fa_fc(node);
				break;
			}					
			case OPCODE_exc: {		// [ f EXCEPT ![x] =y ][ a ]
				result = this.rewrite_fa_exc(node);
				break;
			}
			case OPCODE_tup: {		// < e1, ..., en >[i]
				result = this.rewrite_fa_tuple(node);			
				break;
			}			
			default: {			
				result = this.rewrite_fa_default(node);
				break;
			}
			}
		}					
		return result;
	}

	// DOMAIN [ x \in S |-> e ]
	// --> S
	private final Z3Node rewrite_domain_fc(Z3Node node) {
		Z3Node f = node.getOperand(0),
				result = f.getDomain(0);
		result = this.rewrite(result);
		return result;
	}

	// DOMAIN [ f EXCEPT ![x] = y ]
	// --> DOMAIN f
	private final Z3Node rewrite_domain_exc(Z3Node node) {
		Z3Node exc = node.getOperand(0),
				f = exc.getOperand(0),
				result = node.clone();
		this.constraintChecker.unifySort_equivSort(exc, f);
		result.setOperand(0, f);
		result = this.rewrite(result);
		return result;
	}	

	// DOMAIN <> 
	// --> {}
	// DOMAIN < e1, ... , en >
	// --> { 1, ..., n }
	private final Z3Node rewrite_domain_tuple(Z3Node node) {
		Z3Node tuple	= node.getOperand(0);		
		return tuple.getDomain(0);		
	}

	// DOMAIN [ hi |-> ei ] 
	// --> { h1 , ... , hn }
	private final Z3Node rewrite_domain_rc(Z3Node node) {
		Z3Node rc	= node.getOperand(0);				
		return rc.getDomain(0);
	}

	// DOMAIN f
	private final Z3Node rewrite_domain(Z3Node node) {
		Z3Node op = node.getOperand(0);
		if (op.opCode == OPCODE_bv) {
			return node;
		}
		op = this.z3Encoder.getDef(op);
		op = this.rewrite(op);
		node.setOperand(0, op);		
		switch (op.opCode) {
		case OPCODE_fc: {
			return this.rewrite_domain_fc(node);
		}
		case OPCODE_exc: {
			return this.rewrite_domain_exc(node);
		}
		case OPCODE_tup: {
			return this.rewrite_domain_tuple(node);
		}
		case OPCODE_rc: {
			return this.rewrite_domain_rc(node);
		}		
		case OPCODE_ite: {
			return this.rewrite_unary_ite(node);			
		}
		default: {
			if (this.z3Encoder.taskID == typeOKTask) {
				return node;					
			}
			else if ((this.z3Encoder.taskID == initTask || this.z3Encoder.taskID == nextTask)
					&& op.opCode  != OPCODE_bv && op.getDomainSize() > 0) {				
				Z3Node domain = op.getDomain(0);
				return domain;
			}
			else {
				return node;
			}
		}
		}				
	}

	// f \in [ S -> T ]
	// -> isFcn(f) \land DOMAIN f = S \land \A x \in S : apply(f, x) \in T
	private final Z3Node rewrite_in_sof(Z3Node node) {
		Z3Node f = node.getOperand(0),
				set = node.getOperand(1),
				S 	= set.getDomain(0),
				T 	= set.getRange(0),
				isFcn	 = new Z3Node("IsAFcn", OPCODE_IsAFcn, this.z3Encoder.boolSort, null, f, tla_atom, NoSet), 				
				domain = new Z3Node("domain", OPCODE_domain, f.getDomain(0).getSort(), null, f, f.getDomain(0).kind, f.getDomain(0).setLevel);
		S = this.z3Encoder.getDef(S);
		Z3Node eqDo	= this.z3Tool.createZ3EqNode(domain, S),
				x = this.z3Tool.createBoundedVar(),
				sort = this.z3Encoder.getElemSort(S);		
		x.setSort(sort);
		this.constraintChecker.unifySort_in(x, S);
		eqDo = this.rewrite(eqDo);
		Z3Node fa = new Z3Node(S.getElemSort().name + "_apply_" + T.getElemSort().name, OPCODE_alpha, f.cod.getSort(), null, f, x, f.cod.kind, f.cod.setLevel);
		Z3Node sortFA = this.z3Encoder.getElemSort(T, f.getRange(0));
		fa.setSort(sortFA);
		this.constraintChecker.unifySort_in(fa, T);
		Z3Node inT = new Z3Node(T.getElemSort().name + "_in", OPCODE_in, this.z3Encoder.boolSort, null, fa, T, tla_atom, NoSet),
				e3 = new Z3Node("forall", OPCODE_bf, this.z3Encoder.boolSort, null, tla_atom, NoSet),
				result = new Z3Node("and", OPCODE_land, this.z3Encoder.boolSort, null, tla_atom, NoSet);
		inT = this.rewrite(inT);
		e3.addBoundedVar(x);
		//			if (this.z3Encoder.isSort(S)) {
		e3.addDomain(S);
		e3.addExpr(inT);
		e3 = this.rewrite(e3);
		//			}
		//			else {
		//				Z3Node con = new Z3Node("in_" + S.getSort().name, OPCODE_in, this.z3Encoder.boolSort, null, x, S, tla_atom, NoSet);
		//				con = this.rewrite(con);
		//				Z3Node	body = new Z3Node("=>", OPCODE_implies, this.z3Encoder.boolSort, null, con, inT, tla_atom, NoSet);
		//				e3.addDomain(sort);
		//				e3.addExpr(body);
		//			}
		isFcn = this.rewrite(isFcn);
		result.addOperand(isFcn);						
		result.addOperand(eqDo);
		result.addOperand(e3);				
		return result;
	}

	// [ g EXCEPT ![a] = b ] \in [ S -> T ]
	// -> isFcn(g) \land DOMAIN g = S \land a \in S \land b \in T \land \A x \in S : x # a => apply(f, x) \in T
	private final Z3Node rewrite_in_exc_sof(Z3Node node) {
		Z3Node exc = node.getOperand(0),
				set	= node.getOperand(1),
				S = set.getDomain(0),
				T = set.getRange(0),
				g	= exc.getOperand(0),
				a	= exc.getOperand(1),
				b	= exc.getOperand(2),
				x	= this.z3Tool.createBoundedVar(),
				isFcn	= new Z3Node("IsAFcn", OPCODE_IsAFcn, this.z3Encoder.boolSort, null, g, tla_atom, NoSet),				
				domain= new Z3Node("domain", OPCODE_domain, g.getDomain(0).getSort(), null, g, g.getDomain(0).kind, g.getDomain(0).setLevel);
		isFcn = this.rewrite(isFcn);
		domain = this.rewrite(domain);
		Z3Node eqDo = this.z3Tool.createZ3EqNode(domain, S),											
				aInS = new Z3Node("in_" + S.getSort().name, OPCODE_in, this.z3Encoder.boolSort, null, a, S, tla_atom, NoSet), 																							
				bInT = new Z3Node(T.getElemSort().name + "_in", OPCODE_in, this.z3Encoder.boolSort, null, b, T, tla_atom, NoSet),												
				sortAX = this.z3Encoder.getElemSort(S),				
				sortB = this.z3Encoder.getElemSort(T);
		x.setSort(sortAX);
		a.setSort(sortAX);
		b.setSort(sortB);
		S = this.z3Encoder.getDef(S);
		T = this.z3Encoder.getDef(T);
		this.constraintChecker.unifySort_in(a, S);
		this.constraintChecker.unifySort_in(b, T);
		eqDo = this.rewrite(eqDo);
		aInS = this.rewrite(aInS);
		bInT = this.rewrite(bInT);
		Z3Node fa = new Z3Node(g.getSort().name + "_" + S.getElemSort().name + "_apply_" + T.getElemSort().name, OPCODE_alpha, 
				sortB, null, g, x, g.cod.kind, g.cod.setLevel),
				inT = new Z3Node(T.getElemSort().name + "_in", OPCODE_in, this.z3Encoder.boolSort, null, fa, T, tla_atom, NoSet),				
				xEa	= this.z3Tool.createZ3EqNode(x, a);
		this.constraintChecker.unifySort_in(fa, T);
		inT = this.rewrite(inT);
		xEa = this.rewrite(xEa);
		Z3Node nxEa= new Z3Node("not", OPCODE_lnot, this.z3Encoder.boolSort, null, xEa, tla_atom, NoSet),
				//					inS = new Z3Node("in_" + S.getSort().name, OPCODE_in, this.z3Encoder.boolSort, null, x, S, tla_atom, NoSet);
				//			inS = this.rewrite(inS);
				//			Z3Node con = new Z3Node("and",  OPCODE_land, this.z3Encoder.boolSort, null, inS, nxEa, tla_atom, NoSet),
				//					eBody = new Z3Node("=>",  OPCODE_implies, this.z3Encoder.boolSort, null, con, inT, tla_atom, NoSet),
				//					e	= new Z3Node("forall", OPCODE_bf, this.z3Encoder.boolSort, null, tla_atom, NoSet);
				//			e.addBoundedVar(x);
				//			e.addDomain(sortAX);
				eBody = new Z3Node("=>",  OPCODE_implies, this.z3Encoder.boolSort, null, nxEa, inT, tla_atom, NoSet),
				e	= new Z3Node("forall", OPCODE_bf, this.z3Encoder.boolSort, null, tla_atom, NoSet);
		e.addBoundedVar(x);
		e.addDomain(S);
		e.addExpr(eBody);
		e = this.rewrite(e);
		Z3Node result	= new Z3Node("and", OPCODE_land, this.z3Encoder.boolSort, null, tla_atom, NoSet);		
		result.addOperand(isFcn);						
		result.addOperand(eqDo);
		result.addOperand(aInS);
		result.addOperand(bInT);
		result.addOperand(e);				
		return result;
	}

	// [ x \in SS |-> e(x) ] \in [ S -> T ]
	// S = Sort, SS is not a Sort --> FALSE
	// S = Sort1, SS = Sort2, Sort1 # Sort2 --> FALSE
	// S = Sort = SS --> \A x \in Sort : e(x) \in t
	// --> SS = S \land \A x \in S : e(x) \in T
	private final Z3Node rewrite_in_fc_sof(Z3Node node) {
		Z3Node f = node.getOperand(0),
				SS	= f.getDomain(0),
				x		= f.getBoundedVar(0),
				e		= f.getExpr(0),
				set = node.getOperand(1),
				S 	= set.getDomain(0),
				T 	= set.getRange(0);
		if (this.z3Encoder.isSort(S)) {
			if (!this.z3Encoder.isSort(SS)) {
				return new Z3Node("false", OPCODE_false, this.z3Encoder.boolSort, null, tla_atom, NoSet);
			}
			else {
				if (S.name.equals(SS.name)) {
					Z3Node inT = new Z3Node(T.getElemSort().name + "_in", OPCODE_in, this.z3Encoder.boolSort, null, e, T, tla_atom, NoSet),
							res = new Z3Node("forall", OPCODE_bf, this.z3Encoder.boolSort, null, tla_atom, NoSet);					
					inT = this.rewrite(inT);
					res.addBoundedVar(x);
					res.addDomain(S);
					res.addExpr(inT);
					return res;
				}
				else {
					return new Z3Node("false", OPCODE_false, this.z3Encoder.boolSort, null, tla_atom, NoSet);
				}
			}
		}
		Z3Node eq	= this.z3Tool.createZ3EqNode(SS, S),
				inT = new Z3Node(T.getElemSort().name + "_in", OPCODE_in, this.z3Encoder.boolSort, null, e, T, tla_atom, NoSet),
				e2 	= new Z3Node("forall", OPCODE_bf, this.z3Encoder.boolSort, null, tla_atom, NoSet);
		this.constraintChecker.eq_check(eq);	
		this.constraintChecker.unifySort_in(e, T);
		eq = this.rewrite(eq);
		inT = this.rewrite(inT);
		//			if (this.z3Encoder.isSort(S)) {
		e2.addBoundedVar(x);
		e2.addDomain(S);			
		e2.addExpr(inT);
		//			}
		//			else {
		//				Z3Node sort = this.z3Encoder.getElemSort(S),
		//						inS	= new Z3Node("in_" + S.getSort().name, OPCODE_in, this.z3Encoder.boolSort, null, x, S, tla_atom, NoSet);
		//				inS = this.rewrite(inS);
		//				Z3Node e2Body = new Z3Node("=>", OPCODE_implies, this.z3Encoder.boolSort, null, inS, inT, tla_atom, NoSet);
		//				e2.addBoundedVar(x);
		//				e2.addDomain(sort);			
		//				e2.addExpr(e2Body);
		//			}
		Z3Node result	= new Z3Node("and", OPCODE_land, this.z3Encoder.boolSort, null, eq, e2, tla_atom, NoSet);
		result = this.rewrite(result);
		return result;
	}

	// f = [ x \in S |-> e(x) ] 
	// --> isFcn(f) \land DOMAIN f = S \land \A x \in S : apply(f, x) = e(x) 
	private final Z3Node rewrite_eq_fc(Z3Node node) {
		Z3Node f = node.getOperand(0), 
				fc = node.getOperand(1),
				S	 = fc.getDomain(0),
				x	 = fc.getBoundedVar(0),
				e	 = fc.getExpr(0),
				isFcn	= new Z3Node("IsAFcn", OPCODE_IsAFcn, this.z3Encoder.boolSort, null, f, tla_atom, NoSet),
				dom	= new Z3Node("domain", OPCODE_domain, f.getDomain(0).getSort(), null, f, f.getDomain(0).kind, f.getDomain(0).setLevel);
		isFcn = this.rewrite(isFcn);
		dom = this.rewrite(dom);
		S = this.z3Encoder.getDef(S);
		this.constraintChecker.unifySort_equivSort(dom, S);
		Z3Node eqS = this.z3Tool.createZ3EqNode(dom, S),
				//					fa = new Z3Node(S.getElemSort().name + "_apply_" + e.getSort().name, OPCODE_alpha, e.getSort(), null, f, x, e.getSort().kind, e.getSort().setLevel);
				fa = new Z3Node(S.getElemSort().name + "_apply_" + e.getSort().name, OPCODE_alpha, e.getSort(), null, f, x,  e.getSort().kind,  e.getSort().setLevel);
		fa.setSort(e.getSort());
		if (f.getRangeSize() > 0) {
			fa.setSort(f.getRange(0).getElemSort());
		}		
		Z3Node eqE = this.z3Tool.createZ3EqNode(fa, e),
				e3	= new Z3Node("forall", OPCODE_bf, this.z3Encoder.boolSort, null, tla_atom, NoSet);		
		eqS = this.rewrite(eqS);
		eqE = this.rewrite(eqE);
		e3.addBoundedVar(x);
		//			if (this.z3Encoder.isSort(S)) {
		e3.addDomain(S);
		e3.addExpr(eqE);
		//			}
		//			else {
		//				Z3Node sort = this.z3Encoder.getElemSort(S),
		//						inS	= new Z3Node("in_" + S.getSort().name, OPCODE_in, this.z3Encoder.boolSort, null, x, S, tla_atom, NoSet);
		//				inS = this.rewrite(inS);
		//				Z3Node	newBody	= new Z3Node("=>", OPCODE_implies, this.z3Encoder.boolSort, null, inS, eqE, tla_atom, NoSet);										
		//				e3.addDomain(sort);
		//				e3.addExpr(newBody);
		//			}
		Z3Node result	= new Z3Node("and", OPCODE_land, this.z3Encoder.boolSort, null, isFcn, eqS, e3, tla_atom, NoSet);
		result = this.rewrite(result);
		return result;
	}

	// g = [ f EXCEPT ![a] = b ] 
	// --> isFcn(f) \land DOMAIN f = DOMAIN g  
	//							\land a \in DOMAIN g => apply(g, a) = b
	//							\land \A x \in DOMAIN f : x # a => apply(g, x) = apply(f, x)
	private final Z3Node rewrite_eq_exc_fcn(Z3Node node) {
		Z3Node g = node.getOperand(0),
				exc		= node.getOperand(1),
				f 		= exc.getOperand(0),
				a 		= exc.getOperand(1),
				b 		= exc.getOperand(2),
				x			= this.z3Tool.createBoundedVar(),				
				isFcn	= new Z3Node("IsAFcn", OPCODE_IsAFcn, this.z3Encoder.boolSort, null, g, tla_atom, NoSet),
				domF	= new Z3Node("domain", OPCODE_domain, f.getDomain(0).getSort(), null, f, f.getDomain(0).kind, f.getDomain(0).setLevel),
				domG	= new Z3Node("domain", OPCODE_domain, g.getDomain(0).getSort(), null, g, g.getDomain(0).kind, g.getDomain(0).setLevel);
		domF = this.rewrite(domF);
		domG = this.rewrite(domG);
		Z3Node eqDo	= this.z3Tool.createZ3EqNode(domF, domG),
				aInDomF = new Z3Node(a.getSort().name + "_in", OPCODE_in, this.z3Encoder.boolSort, null, a, domF, tla_atom, NoSet),
				//					faGA	= new Z3Node(a.getSort().name + "_apply_" + b.getSort().name, OPCODE_alpha, b.getSort(), null, g, a, b.getSort().kind, b.getSort().setLevel);
				faGA	= new Z3Node(a.getSort().name + "_apply_" + b.getSort().name, OPCODE_alpha, null, null, g, a, b.getSort().kind, b.getSort().setLevel);
		faGA.setSort(b.getSort());		
		Z3Node eqB = this.z3Tool.createZ3EqNode(faGA, b);
		this.constraintChecker.eq_check(eqDo);
		this.constraintChecker.in_check(aInDomF);
		this.constraintChecker.eq_check(eqB);
		eqDo = this.rewrite(eqDo);		
		aInDomF = this.rewrite(aInDomF);
		eqB = this.rewrite(eqB);
		Z3Node e3 = new Z3Node("=>", OPCODE_implies, this.z3Encoder.boolSort, null, aInDomF, eqB, tla_atom, NoSet),
				e4 		= new Z3Node("forall", OPCODE_bf, this.z3Encoder.boolSort, null, tla_atom, NoSet),
				//					sort	= this.z3Encoder.getElemSort(f.getDomain(0), f.getRange(0)),
				//					xInDomF= new Z3Node(a.getSort().name + "_in", OPCODE_in, this.z3Encoder.boolSort, null, a, domF, tla_atom, NoSet),
				xEa		= this.z3Tool.createZ3EqNode(x, a);
		//			xInDomF = this.rewrite(xInDomF);
		xEa = this.rewrite(xEa);
		Z3Node	nxEa	= new Z3Node("not", OPCODE_lnot, this.z3Encoder.boolSort, null, xEa, tla_atom, NoSet),
				//					con		= new Z3Node("and", OPCODE_land, this.z3Encoder.boolSort, null, xInDomF, nxEa, tla_atom, NoSet),
				//					faFX	= new Z3Node(a.getSort().name + "_apply_" + b.getSort().name, OPCODE_alpha, f.getRange(0).getElemSort(), null, f, x, f.getRange(0).getElemSort().kind, f.getRange(0).getElemSort().setLevel),
				//					faGX  = new Z3Node(a.getSort().name + "_apply_" + b.getSort().name, OPCODE_alpha, g.getRange(0).getElemSort(), null, g, x, g.getRange(0).getElemSort().kind, g.getRange(0).getElemSort().setLevel),
				faFX	= new Z3Node(a.getSort().name + "_apply_" + b.getSort().name, OPCODE_alpha, null, null, f, x, b.getSort().kind, b.getSort().setLevel),
				faGX  = new Z3Node(a.getSort().name + "_apply_" + b.getSort().name, OPCODE_alpha, null, null, g, x, b.getSort().kind, b.getSort().setLevel);
		faFX.setSort(f.getRange(0).getElemSort());
		faGX.setSort(g.getRange(0).getElemSort());
		Z3Node eq_fa	= this.z3Tool.createZ3EqNode(faFX, faGX);
		eq_fa = this.rewrite(eq_fa);
		Z3Node body = new Z3Node("=>", OPCODE_implies, this.z3Encoder.boolSort, null, nxEa, eq_fa, tla_atom, NoSet),
				result	= new Z3Node("and", OPCODE_land, this.z3Encoder.boolSort, null, tla_atom, NoSet);
		e4.addBoundedVar(x);
		e4.addDomain(domF);
		e4.addExpr(body);
		e4 = this.rewrite(e4);
		isFcn = this.rewrite(isFcn);
		result.addOperand(isFcn);
		result.addOperand(eqDo);
		result.addOperand(e3);
		result.addOperand(e4);
		return result;
	}

	// x = [ y EXCEPT !.h = e ] 
	// --> isFcn(x) \land DOMAIN x = DOMAIN y 
	//							\land h \in DOMAIN y => apply(x, h) = e
	//							\land \A k \in DOMAIN y : k # h => apply(x, k) = apply(y, k)
	private final Z3Node rewrite_eq_exc_rcd(Z3Node node) {
		Z3Node x = node.getOperand(0),
				exc		= node.getOperand(1),
				y 		= exc.getOperand(0),
				h 		= exc.getOperand(1),
				e 		= exc.getOperand(2),
				//					domX	= new Z3Node("domain", OPCODE_domain, x.getDomain(0).getSort(), null, x, x.getDomain(0).kind, x.getDomain(0).setLevel),
				domY	= new Z3Node("domain", OPCODE_domain, y.getDomain(0).getSort(), null, y, y.getDomain(0).kind, y.getDomain(0).setLevel),
				isFcn	= new Z3Node("IsAFcn", OPCODE_IsAFcn, this.z3Encoder.boolSort, null, x, tla_atom, NoSet);				
		//			domX = this.rewrite(domX);
		//			domY = this.rewrite(domY);
		Z3Node faXH	= new Z3Node(NoName, OPCODE_trsl, null, null, x, h, NoKind, iNull), 
				//					eqDo	= this.z3Tool.createZ3EqNode(domX, domY),
				hInDomY = new Z3Node(Str + "_in", OPCODE_in, this.z3Encoder.boolSort, null, h, domY, tla_atom, NoSet),				
				eqE		= this.z3Tool.createZ3EqNode(faXH, e);
		//			eqDo = this.rewrite(eqDo);		
		hInDomY = this.rewrite(hInDomY);
		eqE = this.rewrite(eqE);
		Z3Node e3 = new Z3Node("=>", OPCODE_implies, this.z3Encoder.boolSort, null, hInDomY, eqE, tla_atom, NoSet);					
		Z3Node result	= new Z3Node("and", OPCODE_land, this.z3Encoder.boolSort, null, tla_atom, NoSet);
		isFcn = this.rewrite(isFcn);
		result.addOperand(isFcn);
		//			result.addOperand(eqDo);
		result.addOperand(e3);
		int alen = x.getFieldSize();
		for (int i = 0; i < alen; i++) {
			Z3Node field = x.getField(i),
					range = x.getRange(i),
					sort = range.getSort();
			if (!field.name.equals(h.name)) {
				Z3Node faXK = new Z3Node(NoName, OPCODE_trsl, sort, null, x, field, sort.kind, sort.setLevel),
						faYK = new Z3Node(NoName, OPCODE_trsl, sort, null, y, field, sort.kind, sort.setLevel),
						eqFA = this.z3Tool.createZ3EqNode(faXK, faYK);
				eqFA = this.rewrite(eqFA);
				result.addOperand(eqFA);
			}
		}
		return result;
	}

	// [ x \in S |-> e(x) ] = [ x \in T |-> d(x) ]
	// --> S = T \land \A x \in S : e(x) = d(x) 
	private final Z3Node rewrite_eq_fc_fc(Z3Node node) {
		Z3Node fc1	= node.getOperand(0),
				fc2	= node.getOperand(1),
				x 	= fc1.getBoundedVar(0),
				S 	= fc1.getDomain(0),
				e 	= fc1.getExpr(0),
				y		= fc2.getBoundedVar(0),
				T 	= fc2.getDomain(0),
				d 	= fc2.getExpr(0),
				eqST= this.z3Tool.createZ3EqNode(S, T);	
		eqST = this.rewrite(eqST);
		d	= this.z3Tool.replaceNode(y.name, d, x);
		Z3Node eqED= this.z3Tool.createZ3EqNode(e, d),
				e2 	= new Z3Node("forall", OPCODE_bf, this.z3Encoder.boolSort, null, tla_atom, NoSet);
		eqED = this.rewrite(eqED);
		e2.addBoundedVar(x);
		//			if (this.z3Encoder.isSort(S)) {
		e2.addDomain(S);
		e2.addExpr(eqED);
		e2 = this.rewrite(e2);
		//			}
		//			else {
		//				Z3Node sort = this.z3Encoder.getElemSort(S, T),
		//						con	= new Z3Node("in_" + S.getSort().name, OPCODE_in, this.z3Encoder.boolSort, null, x, S, tla_atom, NoSet);
		//				con = this.rewrite(con);
		//				Z3Node newBody= new Z3Node("=>", OPCODE_implies, this.z3Encoder.boolSort, null, con, eqED, tla_atom, NoSet);
		//				e2.addDomain(sort);
		//				e2.addExpr(newBody);
		//			}
		Z3Node result	= new Z3Node("and", OPCODE_land, this.z3Encoder.boolSort, null, eqST, e2, tla_atom, NoSet);
		return result;
	}

	// x * IF c THEN t ELSE f 
	// --> IF c then x * t ELSE x * f
	private final Z3Node rewrite_binary_ite(Z3Node node) {
		Z3Node x 	= node.getOperand(0),									
				ite	= node.getOperand(1),
				c 	= ite.getOperand(0),
				t 	= ite.getOperand(1),
				f 	= ite.getOperand(2),
				e1  = new Z3Node(node.name, node.opCode, node.getSort(), node.getElemSort(), x, t, node.getSort().kind, node.getSort().setLevel),
				e2  = new Z3Node(node.name, node.opCode, node.getSort(), node.getElemSort(), x, f, node.getSort().kind, node.getSort().setLevel),
				res = new Z3Node("ite", OPCODE_ite, null, null, NoKind, iNull);
		e1 = this.rewrite(e1);
		e2 = this.rewrite(e2);
		res.addOperand(c);
		res.addOperand(e1);						
		res.addOperand(e2);
		res.setSort(e1.getSort());		
		res.setSort(e2.getSort());		
		return res;
	}

	// f [ IF c THEN t ELSE u ] 
	// --> IF c THEN f[t] ELSE f[u]
	private final Z3Node rewrite_fa_ite(Z3Node node) {
		Z3Node f 	= node.getOperand(0),
				ite	= node.getOperand(1),
				c 	= ite.getOperand(0),
				t 	= ite.getOperand(1),
				u 	= ite.getOperand(2),
				e1  = new Z3Node(NoName, OPCODE_fa, null, null, f, t, NoKind, iNull),
				e2  = new Z3Node(NoName, OPCODE_fa, null, null, f, u, NoKind, iNull),
				tmp = new Z3Node("ite", OPCODE_ite, null, null, NoKind, iNull);									
		tmp.addOperand(c);
		tmp.addOperand(e1);						
		tmp.addOperand(e2);
		this.rewrite(tmp);
		return tmp;
	}

	// O [ IF c THEN t ELSE u ] 
	// --> IF c THEN O(t) ELSE O(u)
	private final Z3Node rewrite_unary_ite(Z3Node node) {
		Z3Node ite	= node.getOperand(0),
				c 	= ite.getOperand(0),
				t 	= ite.getOperand(1),
				u 	= ite.getOperand(2),
				e1  = new Z3Node(node.name, node.opCode, node.getSort(), node.getElemSort(), t, node.getSort().kind, node.getSort().setLevel),
				e2  = new Z3Node(node.name, node.opCode, node.getSort(), node.getElemSort(), u, node.getSort().kind, node.getSort().setLevel),
				res = new Z3Node("ite", OPCODE_ite, null, null, NoKind, iNull);
		e1 = this.rewrite(e1);
		e2 = this.rewrite(e2);
		res.addOperand(c);
		res.addOperand(e1);								
		res.addOperand(e2);
		res.setSort(e1.getSort());		
		res.setSort(e2.getSort());			
		return res;
	}

	// tuple[i]
	// --> <e1, ..., en>[i]
	// ei
	// --> (tuple fi)
	private final Z3Node rewrite_fa_tuple(Z3Node node) {
		Z3Node t = node.getOperand(0),
				i = node.getOperand(1);
		t = this.z3Encoder.getDef(t);
		int index = Integer.valueOf(i.name) - 1;
		Z3Node result = t.getExpr(index); 
		return result;
	}

	// t \in S1 x ... x Sn	// 
	// --> isFcn(t) \land DOMAIN t = { 1, ..., n } \land (t f1) \in S1 \land ... \land (t fn) \in Sn 
	private final Z3Node rewrite_in_cp(Z3Node node) {
		Z3Node t	= node.getOperand(0),
				cp = node.getOperand(1),
				//					dom = new Z3Node("domain", OPCODE_domain, this.z3Encoder.setIntSort, null, t, tla_set, 1),
				isF = new Z3Node("IsAFcn", OPCODE_IsAFcn, this.z3Encoder.boolSort, null, t, tla_atom, NoSet);			
		int alen = cp.getOperandSize();
		Z3Node 
		//						 domT= this.createInterval(1, alen),
		//					eq = this.z3Tool.createZ3EqNode(dom, domT),
		result = new Z3Node("and", OPCODE_land, this.z3Encoder.boolSort, null, tla_atom, NoSet);
		//			eq = this.rewrite(eq);
		isF = this.rewrite(isF);
		result.addOperand(isF);
		//			result.addOperand(eq);
		for (int i = 0; i < alen; i++) {
			String name = Integer.toString(i + 1);
			Z3Node fieldi = new Z3Node(name, OPCODE_const, this.z3Encoder.intSort, null, tla_atom, NoSet),
					slTi = new Z3Node(NoName, OPCODE_trsl, cp.getOperand(i).getElemSort(), null, t, fieldi, cp.getOperand(i).getElemSort().kind, cp.getOperand(i).getElemSort().setLevel),					
					Si 	 = cp.getOperand(i);
			Si = this.z3Encoder.getDef(Si);
			slTi.setSort(Si.getElemSort());						
			Z3Node	inSi = new Z3Node(Si.getElemSort().name + "_in", OPCODE_in, this.z3Encoder.boolSort, null, slTi, Si, tla_atom, NoSet);
			inSi = this.rewrite(inSi);
			result.addOperand(inSi);
		}				
		return result;

	}

	// [ hi |-> ei].hj
	// --> ej
	private final Z3Node rewrite_rs_rc(Z3Node node) {
		Z3Node rc	= node.getOperand(0),
				hj 	= node.getOperand(1);
		int alen = rc.getFieldSize();		
		String field = NoName;
		for (int i = 0; i < alen; i++) {
			field = rc.getField(i).name;
			if (field.equals(hj.name)) {
				return rc.getExpr(i);
			}
		}
		return null;

	}

	// rcd.hj
	// --> IF hj \in DOM rcd THEN apply(rcd, hj) ELSE iapply(rcd, 2int(hj))
	private final Z3Node rewrite_rs_default(Z3Node node) {
		Z3Node rcd = node.getOperand(0),
				hj   = node.getOperand(1);
		rcd = this.z3Encoder.getDef(rcd);
		Z3Node range = rcd.findRange(hj),
				result = new Z3Node(NoName, OPCODE_trsl, range.getSort(), null, rcd, hj, range.kind, range.setLevel);
		//					domain = new Z3Node("domain", OPCODE_domain, null, this.z3Encoder.strSort, rcd, tla_set, 1), 	
		//					inDom  = new Z3Node(hj.getSort().name + "_in", OPCODE_in, this.z3Encoder.boolSort, null, hj, domain, tla_atom, NoSet),
		//					rs  = new Z3Node(NoName, OPCODE_trsl, null, null, rcd, hj, tla_set, 1);
		//					m2i	= new Z3Node(hj.getSort().name + "2int", OPCODE_2int, this.z3Encoder.intSort, null, hj, tla_atom, NoSet),
		//					iap = new Z3Node("iapply", OPCODE_iapply, null, null, rcd, m2i, NoKind, iNull);
		//			inDom = this.rewrite(inDom);
		//			Z3Node result = new Z3Node("ite", OPCODE_ite, null, null, inDom, rs, iap, NoKind, iNull);
		return result;
	}

	// [ r EXCEPT !.h1 = e].h2
	// --> IF h1 = h2 THEN e ELSE r.h2
	// --> IF h1 = h2 THEN e ELSE (r h2)
	private final Z3Node rewrite_rs_exc(Z3Node node) {
		Z3Node exc	= node.getOperand(0),
				h2 	= node.getOperand(1),
				r		= exc.getOperand(0),
				h1	= exc.getOperand(1),
				e 	= exc.getOperand(2),
				con = this.z3Tool.createZ3EqNode(h1, h2),
				range = r.findRange(h2),
				e2  = new Z3Node(NoName, OPCODE_rs, range.getSort(), null, r, h2, range.kind, range.setLevel);
		e2 = this.rewrite(e2);
		Z3Node result = new Z3Node("ite", OPCODE_ite, null, null, con, e, e2, NoKind, iNull);		
		this.constraintChecker.ite_check(result);
		return result;
	}

	// rcd.h
	private final Z3Node rewrite_rs(Z3Node node) {		
		Z3Node result = node,
				rcd = node.getOperand(0),
				h = node.getOperand(1);
		rcd = this.z3Encoder.getDef(rcd);
		rcd = this.rewrite(rcd);
		node.setOperand(0, rcd);
		h = this.z3Encoder.getDef(h);
		h = this.rewrite(h);
		node.setOperand(1, h);
		switch (rcd.opCode) {
		case OPCODE_tup: {
			result = this.rewrite_fa_tuple(node);
			break;
		}
		case OPCODE_rc: {
			result = this.rewrite_rs_rc(node);
			break;
		}
		case OPCODE_exc: {
			result = this.rewrite_rs_exc(node);
			break;
		}
		default: {
			result = this.rewrite_rs_default(node);
			break;
		}
		}
		if (result.getOperandSize() >= 2 && result.getOperand(1).opCode == OPCODE_ite) {
			result = this.rewrite_binary_ite(node);		
		}
		return result;
	}

	// r \in [ hi : Si ]
	// --> FALSE iff r.getSort() # [ hi : Si ].elementType
	// --> isFcn(r) \land DOMAIN r = { h1, ..., hn } \land (r h1) \in S1 \land ... \land (r hn) \in Sn iff n > 1
	private final Z3Node rewrite_in_sor(Z3Node node) {
		Z3Node r	= node.getOperand(0),				
				sor = node.getOperand(1);
		if (!r.getSort().name.equals(sor.getElemSort().name)) {
			return new Z3Node("false", OPCODE_false, this.z3Encoder.boolSort, null, tla_atom, NoSet);
		}
		else {
			int alen = sor.getFieldSize();
			Z3Node isFcn = new Z3Node("IsAFcn", OPCODE_IsAFcn, this.z3Encoder.boolSort, null, r, tla_atom, NoSet),
					//						dom	 = new Z3Node("domain", OPCODE_domain, this.z3Encoder.setStrSort, null, r, tla_set, 1),
					//						domR = new Z3Node(NoName, OPCODE_se, this.z3Encoder.setStrSort, this.z3Encoder.strSort, tla_set, 1),					
					result = new Z3Node("and", OPCODE_land, this.z3Encoder.boolSort, null, tla_atom, NoSet);		
			isFcn = this.rewrite(isFcn);
			result.addOperand(isFcn);			
			for (int i = 0; i < alen; i++) {					
				Z3Node fieldi = sor.getField(i),
						Si 	 = sor.getRange(i);
				Si = this.z3Encoder.getDef(Si);
				Z3Node sortRSLI = this.z3Encoder.getElemSort(Si);
				Z3Node rsli = new Z3Node(NoName, OPCODE_trsl, sortRSLI, null, r, fieldi, sortRSLI.kind, sortRSLI.setLevel);				
				Z3Node inSi = new Z3Node(Si.getElemSort().name + "_in", OPCODE_in, this.z3Encoder.boolSort, null, rsli, Si, tla_atom, NoSet);
				inSi = this.rewrite(inSi);
				result.addOperand(inSi);
				//					domR.addOperand(fieldi);
			}
			//				Z3Node eq = this.z3Tool.createZ3EqNode(dom, domR);
			//				this.constraintChecker.eq_check(eq);
			//				eq = this.rewrite(eq);
			//				result.addOperand(eq);
			return result;
		}				
	}

	// r.h
	// --> select(r h)
	private final Z3Node rewrite_fa_rcd(Z3Node node) {
		Z3Node r	= node.getOperand(0),
				h 	= node.getOperand(1),			
				result = new Z3Node(NoName, OPCODE_trsl, null, null, r, h, NoKind, iNull);										
		return result;
	}

	// [ hi |-> ei ] \in [ fi : Si ]
	// --> h1 = f1 \land ... \land hn = fn \land e1 \in S1 \land ... \land en \in Sn
	private final Z3Node rewrite_in_rc_sor(Z3Node node) {
		boolean flag = true;
		Z3Node rc	= node.getOperand(0),
				sor = node.getOperand(1);
		Z3Node result = new Z3Node("and", OPCODE_land, this.z3Encoder.boolSort, null, tla_atom, NoSet);
		if (rc.getFieldSize() != sor.getFieldSize()) {
			flag = false;
		}
		else {
			int alen = rc.getFieldSize();
			boolean[] isMarked = new boolean[alen];
			String[] fFields = new String[alen];
			String[] hFields = new String[alen];
			for (int i = 0; i < alen; i++) {
				fFields[i] = sor.getField(i).name;
				hFields[i] = rc.getField(i).name;
			}
			for (int i = 0; i < alen; i++) {		
				for (int j = 0; j < alen; j++) {
					if (hFields[i].equals(fFields[j])) {
						isMarked[i] = true;
						Z3Node ei	= rc.getExpr(i),				
								Si = sor.getRange(j);
						Si = this.z3Encoder.getDef(Si);			
						Z3Node inSi = new Z3Node(Si.getElemSort().name + "_in", OPCODE_in, this.z3Encoder.boolSort, null, ei, Si, tla_atom, NoSet);
						inSi = this.rewrite(inSi);
						result.addOperand(inSi);
						break;
					}
				}
				if (!isMarked[i]) {
					flag = false;
					break;
				}								
			}
		}		
		if (flag) {
			return result;
		}
		else {
			return new Z3Node("false", OPCODE_false, this.z3Encoder.boolSort, null, tla_atom, NoSet);
		}		
	}		

	// t = < e1, ... , en >
	// --> isFcn(t) \land DOMAIN t = { 1, ..., n } \land select(t, 1) = e1 \land ... \land select(t, n) = en
	// assume that n > 0
	private final Z3Node rewrite_eq_tuple(Z3Node node) {
		Z3Node t = node.getOperand(0),
				tuple	 = node.getOperand(1),
				//					dom 	 = new Z3Node("domain", OPCODE_domain, this.z3Encoder.setIntSort, null, t, tla_set, 1),
				isFcn	 = new Z3Node("IsAFcn", OPCODE_IsAFcn, this.z3Encoder.boolSort, null, t, tla_atom, NoSet);				
		int alen = tuple.getFieldSize();		
		//			Z3Node domT = this.createInterval(1, alen),
		//					eqDo = this.z3Tool.createZ3EqNode(dom, domT);
		//			eqDo = this.rewrite(eqDo);
		Z3Node	result = new Z3Node("and", OPCODE_land, this.z3Encoder.boolSort, null, tla_atom, NoSet);
		isFcn = this.rewrite(isFcn);
		result.addOperand(isFcn);
		//			result.addOperand(eqDo);		
		for (int i = 0; i < alen; i++) {			
			Z3Node field = t.getField(i),
					tsli = new Z3Node(NoName, OPCODE_trsl, null, null, t, field, NoKind, iNull),
					ei   = tuple.getExpr(i);
			tsli.setSort(ei.getSort());
			ei = this.z3Encoder.getDef(ei);			
			Z3Node eqi = this.z3Tool.createZ3EqNode(tsli, ei);
			eqi = this.rewrite(eqi);
			result.addOperand(eqi);												
		}		
		return result;
	}

	private final Z3Node createInterval(int left, int right) {
		Z3Node result = new Z3Node(NoName, OPCODE_se, this.z3Encoder.setIntSort, this.z3Encoder.intSort, tla_set, 1);			
		for (int i = left; i <= right; i++) {
			String name = Integer.toString(i);
			Z3Node no = new Z3Node(name, OPCODE_const, this.z3Encoder.intSort, null, tla_atom, NoSet);			
			result.addOperand(no);
		}
		return result;
	}

	// T = S1 x ... x Sn
	// --> \A x \in SortX : x \in T <=> isFcn(x) \land DOMAIN x = { 1, ..., n }
	//							\land select(x, 1) \in S1 \land ... \land select(x, n) \in Sn
	// Since x is always a function, then isFcn(x) = true
	private final Z3Node rewrite_eq_cp(Z3Node node) {
		Z3Node result = new Z3Node("forall", OPCODE_bf, this.z3Encoder.boolSort, null, tla_atom, NoSet),
				T 	= node.getOperand(0),
				set = node.getOperand(1),
				x 	= this.z3Tool.createBoundedVar();
		this.constraintChecker.unifySort_in(x, T);
		Z3Node inT	= new Z3Node(T.getElemSort().name + "_in", OPCODE_in, this.z3Encoder.boolSort, null, x, T, tla_atom, NoSet),
				//					dom = new Z3Node("domain", OPCODE_domain, null, null, x, tla_set, 1),
				isF	= new Z3Node("true", OPCODE_true, this.z3Encoder.boolSort, null, tla_atom, NoSet);				
		int alen = set.getOperandSize();
		inT = this.rewrite(inT);
		Z3Node rhs = new Z3Node("and", OPCODE_land, this.z3Encoder.boolSort, null, tla_atom, NoSet),
				//					domX= this.createInterval(1, alen),
				//					eq  = this.z3Tool.createZ3EqNode(dom, domX),				
				e3 = new Z3Node("and", OPCODE_land, this.z3Encoder.boolSort, null, tla_atom, NoSet);
		//			this.constraintChecker.eq_check(eq);
		//			eq = this.rewrite(eq);
		rhs.addOperand(isF);
		//			rhs.addOperand(eq);		
		for (int i = 0; i < alen; i++) {
			String name = Integer.toString(i + 1);
			Z3Node fieldi = new Z3Node(name, OPCODE_const, this.z3Encoder.strSort, null, tla_atom, NoSet),
					fai = new Z3Node(NoName, OPCODE_trsl, null, null, x, fieldi, NoKind, iNull),
					Si = set.getOperand(i);
			Si = this.z3Encoder.getDef(Si);			
			Z3Node inSi = new Z3Node(Si.getElemSort().name + "_in", OPCODE_in, this.z3Encoder.boolSort, null, fai, Si, tla_atom, NoSet);
			inSi = this.rewrite(inSi);
			e3.addOperand(inSi);
		}
		rhs.addOperand(e3);
		Z3Node newBody = this.z3Tool.createZ3EqNode(inT, rhs),
				sort = this.z3Encoder.getElemSort(T, set);
		result.addBoundedVar(x);
		result.addDomain(sort);
		result.addExpr(newBody);
		return result;
	}

	// r = [ hi |-> ei ]
	// --> isFcn(r) \land DOMAIN r = { h1, ..., hn } \land select(r, hi) = ei
	private final Z3Node rewrite_eq_rc(Z3Node node) {
		Z3Node result = new Z3Node("and", OPCODE_land, this.z3Encoder.boolSort, null, tla_atom, NoSet),
				r 	= node.getOperand(0),
				rc = node.getOperand(1),
				//					dom = new Z3Node("domain", OPCODE_domain, this.z3Encoder.setStrSort, null, r, tla_set, 1),
				//					domR= new Z3Node(NoName, OPCODE_se, this.z3Encoder.setStrSort, this.z3Encoder.strSort, tla_set, 1),
				isF	= new Z3Node("IsAFcn", OPCODE_IsAFcn, this.z3Encoder.boolSort, null, r, tla_atom, NoSet);				
		isF = this.rewrite(isF);
		result.addOperand(isF);		
		int alen = rc.getFieldSize();		
		for (int i = 0; i < alen; i++) {	
			Z3Node fieldi = rc.getField(i),
					fai = new Z3Node(NoName, OPCODE_trsl, null, null, r, fieldi, NoKind, iNull),
					ei = rc.getExpr(i);
			fai.setSort(ei.getSort());
			//				domR.addOperand(fieldi);
			ei = this.z3Encoder.getDef(ei);			
			Z3Node eqi = this.z3Tool.createZ3EqNode(fai, ei);
			eqi = this.rewrite(eqi);
			result.addOperand(eqi);
		}
		//			Z3Node eqDo = this.z3Tool.createZ3EqNode(dom, domR);
		//			this.constraintChecker.eq_check(eqDo);
		//			eqDo = this.rewrite(eqDo);
		//			result.addOperand(eqDo);
		return result;
	}

	//		// x = [ y EXCEPT !.h = e ]
	//		// --> isFcn(x) \land DOMAIN x = DOMAIIN y \land h \in DOMAIN y => apply(x, h) = e
	//		//				\land \A k \in Str: (k \in DOMAIN y \land \lnot (k = h)) => apply(x, k) = apply(y, k)
	//		private final Z3Node rewrite_eq_rcd_exc(Z3Node node) {
	//			Z3Node x = node.getOperand(0),
	//					exc		= node.getOperand(1),
	//					y 		= exc.getOperand(0),
	//					h 		= exc.getOperand(1),
	//					e 		= exc.getOperand(2),
	//					k			= this.z3Tool.createBoundedVar(),				
	//					isFcn	= new Z3Node("IsAFcn", OPCODE_IsAFcn, this.z3Encoder.boolSort, null, x, tla_atom, NoSet),
	//					domX	= new Z3Node("domain", OPCODE_domain, null, null, x, tla_set, 1),
	//					domY	= new Z3Node("domain", OPCODE_domain, null, null, y, tla_set, 1),
	//					eqDo	= this.z3Tool.createZ3EqNode(domX, domY),
	//					inDomY = new Z3Node(h.getSort().name + "_in", OPCODE_in, this.z3Encoder.boolSort, null, h, domY, tla_atom, NoSet),
	//					faXH	= new Z3Node(NoName, OPCODE_trsl, null, null, x, h, NoKind, iNull),
	//					eqE		= this.z3Tool.createZ3EqNode(faXH, e);
	//			this.constraintChecker.eq_check(eqDo);
	//			eqDo = this.rewrite(eqDo);		
	//			inDomY = this.rewrite(inDomY);
	//			eqE = this.rewrite(eqE);
	//			Z3Node e3 = new Z3Node("=>", OPCODE_implies, this.z3Encoder.boolSort, null, inDomY, eqE, tla_atom, NoSet),
	//					e4 			= new Z3Node("forall", OPCODE_bf, this.z3Encoder.boolSort, null, tla_atom, NoSet),
	//					sort	 	= this.z3Encoder.strSort,
	//					kInDomY = new Z3Node(k.getSort().name + "_in", OPCODE_in, this.z3Encoder.boolSort, null, k, domY, tla_atom, NoSet),
	//					kEh			= this.z3Tool.createZ3EqNode(k, h);
	//			kInDomY = this.rewrite(kInDomY);
	//			kEh = this.rewrite(kEh);
	//			Z3Node	nkEh	= new Z3Node("not", OPCODE_lnot, this.z3Encoder.boolSort, null, kEh, tla_atom, NoSet),
	//					con		= new Z3Node("and", OPCODE_land, this.z3Encoder.boolSort, null, kInDomY, nkEh, tla_atom, NoSet),
	//					faXK	= new Z3Node(NoName, OPCODE_trsl, null, null, x, k, NoKind, iNull),
	//					faYK  = new Z3Node(NoName, OPCODE_trsl, null, null, y, k, NoKind, iNull),
	//					eq_fa	= this.z3Tool.createZ3EqNode(faXK, faYK);
	//			eq_fa = this.rewrite(eq_fa);
	//			Z3Node body = new Z3Node("=>", OPCODE_implies, this.z3Encoder.boolSort, null, con, eq_fa, tla_atom, NoSet),
	//					result	= new Z3Node("and", OPCODE_land, this.z3Encoder.boolSort, null, tla_atom, NoSet);
	//			e4.addBoundedVar(x);
	//			e4.addDomain(sort);
	//			e4.addExpr(body);
	//			isFcn = this.rewrite(isFcn);
	//			result.addOperand(isFcn);
	//			result.addOperand(eqDo);
	//			result.addOperand(e3);
	//			result.addOperand(e4);
	//			return result;
	//		}

	// R = [ hi : Si ]
	// --> \A r \in Sort : r \in R <=> 
	//				isFcn(x) \land DOMAIN r = { h1, ..., hn } \land
	//				\land apply(r, h1) \in S1 \land ... \land apply(r, hn) \in Sn 
	// Since r is always a function, then isFcn(r) = true.
	private final Z3Node rewrite_eq_sor(Z3Node node) {
		Z3Node R = node.getOperand(0),
				sor		= node.getOperand(1),
				r			= this.z3Tool.createBoundedVar();
		r.setSort(sor.getElemSort());
		Z3Node inR = new Z3Node(R.getElemSort().name + "_in", OPCODE_in, this.z3Encoder.boolSort, null, r, R, tla_atom, NoSet),
				isFcn	= new Z3Node("true", OPCODE_true, this.z3Encoder.boolSort, null, tla_atom, NoSet),
				//					domr	= new Z3Node("domain", OPCODE_domain, this.z3Encoder.setStrSort, null, r, tla_set, 1),
				setH	= new Z3Node(NoName, OPCODE_se, this.z3Encoder.setStrSort, this.z3Encoder.strSort, tla_set, 1),
				e4		= new Z3Node("and", OPCODE_land, this.z3Encoder.boolSort, null, tla_atom, NoSet);		
		int alen = sor.getFieldSize();
		for (int i = 0; i < alen; i++) {
			Z3Node hi = sor.getField(i),
					Si	= sor.getRange(i),
					fai	= new Z3Node(NoName, OPCODE_trsl, null, null, r, hi, NoKind, iNull),
					inSi= new Z3Node(Si.getElemSort().name + "_in", OPCODE_in, this.z3Encoder.boolSort, null, fai, Si, tla_atom, NoSet);
			setH.addOperand(hi);
			inSi = this.rewrite(inSi);
			e4.addOperand(inSi);					
		}			
		Z3Node rhs = new Z3Node("and", OPCODE_land, this.z3Encoder.boolSort, null, tla_atom, NoSet),
				//					eqDo = this.z3Tool.createZ3EqNode(domr, setH),
				sort = this.z3Encoder.getElemSort(R);
		//			eqDo = this.rewrite(eqDo);
		//			isFcn = this.rewrite(isFcn);
		rhs.addOperand(isFcn);
		//			rhs.addOperand(eqDo);
		rhs.addOperand(e4);
		Z3Node	body = this.z3Tool.createZ3EqNode(inR, rhs),
				result	= new Z3Node("forall", OPCODE_bf, this.z3Encoder.boolSort, null, tla_atom, NoSet);
		result.addBoundedVar(r);
		result.addDomain(sort);
		result.addExpr(body);		
		return result;
	}

	// x \in Sort
	private final Z3Node rewrite_in_Sort(Z3Node node) {
		Z3Node x   = node.getOperand(0),
				sort= node.getOperand(1);
		if (sort.getElemSort() == null) {
			return new Z3Node("false", OPCODE_false, this.z3Encoder.boolSort, null, tla_atom, NoSet);
		}
		if (x.getSort().name.equals(sort.getElemSort().name)) {
			return new Z3Node("true", OPCODE_true, this.z3Encoder.boolSort, null, tla_atom, NoSet);
		}
		else {
			return new Z3Node("false", OPCODE_false, this.z3Encoder.boolSort, null, tla_atom, NoSet);
		}		
	}

	private final Z3Node rewrite_in(Z3Node node) {
		Z3Node result = node,
				lhs = node.getOperand(0),
				set = node.getOperand(1);
		if (this.z3Encoder.taskID != typeOKTask) {
			lhs = this.z3Encoder.getDef(lhs);
			lhs = this.rewrite(lhs);
			node.setOperand(0, lhs);
		}
		set = this.z3Encoder.getDef(set);
		set = this.rewrite(set);
		node.setOperand(1, set);
		if (set.opCode == OPCODE_ssort  || set.opCode == OPCODE_sfsort ||
				set.opCode == OPCODE_srsort || set.opCode == OPCODE_stsort) {
			result = this.rewrite_in_Sort(node);
		}
		else {
			switch (set.opCode) {
			case OPCODE_cap: {			// x \in e1 \cap e2
				result = this.rewrite_in_cap(node);
				break;
			}
			case OPCODE_cup: {			// x \in e1 \cup e2
				result = this.rewrite_in_cup(node);
				break;
			}
			case OPCODE_se: {				// x \in { e1, ..., en}
				result = this.rewrite_in_se(node);
				break;
			}
			case OPCODE_setdiff: {	// x \in e1 \ e2
				result = this.rewrite_in_setdiff(node);
				break;
			}		
			case OPCODE_sof: {			// x \in [ S -> T ]
				switch (lhs.opCode) {	
				case OPCODE_exc: {		// [ g EXCEPT [a] = b ] \in [ S -> T ]
					result = this.rewrite_in_exc_sof(node);
					break;
				}
				case OPCODE_fc:
				case OPCODE_nrfs: {		// [ x \in SS |-> e(x) ] \in [ S -> T ]
					result = this.rewrite_in_fc_sof(node);
					break;
				}				
				case OPCODE_cp: {
					result = this.rewrite_in_cp(node);
					break;
				}
				case OPCODE_ite: {
					result = this.rewrite_binary_ite(node);
					break;
				}					
				default: {						// f \in [ S -> T ]
					if (set.opCode == OPCODE_sof) {
						result = this.rewrite_in_sof(node);
					}
					else {
						lhs = this.rewrite(lhs);
						set = this.rewrite(set);
						result.setOperand(0, lhs);
						result.setOperand(1, set);
					}
					break;
				}
				}			
				break;
			}
			case OPCODE_sso: {	// x \in { y \in S : p(y) }
				result = this.rewrite_in_sso(node);
				break;
			}
			case OPCODE_soa: { 	// x \in { e : y \in S }
				result = this.rewrite_in_soa(node);
				break;
			}
			case OPCODE_cp: {
				result = this.rewrite_in_cp(node);
				break;
			}
			case OPCODE_sor: {
				if (lhs.opCode == OPCODE_rc) {
					result = this.rewrite_in_rc_sor(node);
				}
				else {
					result = this.rewrite_in_sor(node);
				}
				break;
			}			
			case OPCODE_subset: {	// S \in SUBSET T
				result = this.rewrite_in_subset(node);
				break;
			}
			case OPCODE_union: {	// x \in UNION S
				result = this.rewrite_in_union(node);
				break;
			}			
			default: {	
				lhs = this.rewrite(lhs);
				set = this.rewrite(set);
				result.setOperand(0, lhs);
				result.setOperand(1, set);				
			}
			}
		}												
		return result;
	}

	private final Z3Node rewrite_eq_sort(Z3Node node) {
		Z3Node lhs = node.getOperand(0),
				sort = node.getOperand(1),
				x = this.z3Tool.createBoundedVar(),				
				res = new Z3Node("forall", OPCODE_bf, this.z3Encoder.boolSort, null, tla_atom, NoSet);
		this.constraintChecker.unifySort_in(x, lhs);
		this.constraintChecker.unifySort_in(x, sort);
		Z3Node inL = new Z3Node(NoName, OPCODE_in, this.z3Encoder.boolSort, null, x, lhs, tla_atom, NoSet),
				inR = new Z3Node(NoName, OPCODE_in, this.z3Encoder.boolSort, null, x, sort, tla_atom, NoSet);
		inL = this.rewrite(inL);
		inR = this.rewrite(inR);
		Z3Node body = new Z3Node("=", OPCODE_eq, this.z3Encoder.boolSort, null, inL, inR, tla_atom, NoSet);
		res.addBoundedVar(x);
		res.addDomain(sort.getElemSort());
		res.addExpr(body);
		return res;		
	}

	private final Z3Node rewrite_eq_fa(Z3Node node) {
		Z3Node result = node, 				
				rhs = result.getOperand(1);
		rhs = this.rewrite_fa(rhs);
		result.setOperand(1, rhs);
		return result;
	}	

	// lhs = rhs
	private final Z3Node rewrite_eq(Z3Node node) {
		Z3Node result = node, 
				lhs = node.getOperand(0),
				rhs = node.getOperand(1);		
		if (lhs.opCode != OPCODE_var) {
			lhs = this.z3Encoder.getDef(lhs);
			lhs = this.rewrite(lhs);
			node.setOperand(0, lhs);
		}
		rhs = this.z3Encoder.getDef(rhs);
		rhs = this.rewrite(rhs);
		node.setOperand(1, rhs);
		if (lhs.isSyntacticEqual(rhs)) {
			return new Z3Node("true", OPCODE_true, this.z3Encoder.boolSort, null, tla_atom, NoSet);
		}
		switch (rhs.opCode) {
		case OPCODE_exc: {
			if (lhs.kind == tla_fcn) {
				result = this.rewrite_eq_exc_fcn(node);	
			}
			else if (lhs.kind == tla_rcd) {
				result = this.rewrite_eq_exc_rcd(node);
			}
			break;
		}
		case OPCODE_fa: {
			result = this.rewrite_eq_fa(node);
			break;
		}
		case OPCODE_fc:
		case OPCODE_nrfs: {
			if (lhs.opCode == OPCODE_fc || lhs.opCode == OPCODE_nrfs) {
				result = this.rewrite_eq_fc_fc(node);
			}
			else {
				result = this.rewrite_eq_fc(node);
			}			
			break;
		}
		case OPCODE_se: {		// S = { e1, ..., en}
			result = this.rewrite_eq_se(node);
			break;
		}					
		case OPCODE_subset: {	// S = SUBSET T
			result = this.rewrite_eq_subset(node);
			break;
		}		
		case OPCODE_union: {	// S = UNION T
			result = this.rewrite_eq_union(node);
			break;
		}		
		case OPCODE_sso: {	// S = { y \in S : p(y) }
			result = this.rewrite_eq_sso(node);
			break;
		}
		case OPCODE_soa: {	// S = { e(x) : x \in S }
			result = this.rewrite_eq_soa(node);
			break;
		}
		case OPCODE_cup: {	// S = T \cup U
			result = this.rewrite_eq_cup(node);
			break;
		}
		case OPCODE_cap: {	// S = T \cap U
			result = this.rewrite_eq_cap(node);
			break;
		}
		case OPCODE_setdiff: {	// S = T \ U
			result = this.rewrite_eq_setdiff(node);
			break;
		}
		case OPCODE_rc: {
			result = this.rewrite_eq_rc(node);
			break;
		}
		case OPCODE_sor: {
			result = this.rewrite_eq_sor(node);
			break;
		}
		case OPCODE_tup: {
			result = this.rewrite_eq_tuple(node);
			break;
		}
		case OPCODE_cp: {
			result = this.rewrite_eq_cp(node);
			break;
		}
		case OPCODE_ite: {
			result = this.rewrite_binary_ite(node);
			break;
		}
		default: {		
			if (this.z3Encoder.isSort(rhs)) {
				result = this.rewrite_eq_sort(node);
			}
			else {
				lhs = this.rewrite(lhs);
				rhs = this.rewrite(rhs);
				result.setOperand(0, lhs);
				result.setOperand(1, rhs);	
			}					
			break;
		}
		}		
		return result;
	}

	private final Z3Node rewrite_isafcn(Z3Node node) {
		Z3Node op = node.getOperand(0);
		if (op.kind == tla_fcn || op.kind == tla_rcd || op.kind == tla_tup) {
			return new Z3Node("true", OPCODE_true, this.z3Encoder.boolSort, null, tla_atom, NoSet);
		}
		else {
			return new Z3Node("false", OPCODE_false, this.z3Encoder.boolSort, null, tla_atom, NoSet);
		}			
	}

	private final Z3Node rewrite_noteq(Z3Node node) {
		Z3Node lhs = node.getOperand(0),
				rhs = node.getOperand(1),
				//					eq = new Z3Node("=", OPCODE_eqnot, this.z3Encoder.boolSort, null, lhs, rhs, tla_atom, NoSet);
				eq = new Z3Node("=", OPCODE_eq, this.z3Encoder.boolSort, null, lhs, rhs, tla_atom, NoSet);
		eq = this.rewrite(eq);
		Z3Node noteq = new Z3Node("not", OPCODE_lnot, this.z3Encoder.boolSort, null, eq, tla_atom, NoSet);
		return noteq;
	}

	public final Z3Node rewrite(Z3Node node) {
		return this.rewrite(node, false);
	}

	private final boolean isSafeWOBVar(Z3Node node) {
		switch (node.opCode) {
		case OPCODE_bv: {
			int alen = this.bVars.size();						
			for (int i = 0; i < alen; i++) {
				if (this.bVars.get(i).name.equals(node.name)) {
					return true;
				}
			}
			return false;
		}
		case OPCODE_var:
		case OPCODE_const: {
			return true;
		}
		case OPCODE_be: {
			this.bVars.add(node.getBoundedVar(0));
			boolean res = this.isSafeWOBVar(node.getExpr(0));
			this.bVars.remove(this.bVars.size() - 1);
			return res; 			
		}
		case OPCODE_bf: {
			this.bVars.add(node.getBoundedVar(0));
			boolean res = this.isSafeWOBVar(node.getExpr(0));
			this.bVars.remove(this.bVars.size() - 1);
			return res;
		}		
		default: {
			int alen = node.getOperandSize(); 

			if (alen > 0) {
				for (int i = 0; i < alen; i++) {
					if (!this.isSafeWOBVar(node.getOperand(i))) {
						return false;
					}
				}
				return true;
			}
			else {
				return true;
			}							
		}
		}		
	}

	public final Z3Node rewrite(Z3Node node, boolean defFlag) {
		if (node.isRewriten) {
			return node;
		}
		if (node != null) {
			Z3Node result = node;				
			switch (node.opCode) {
			case OPCODE_be: {
				result = this.rewrite_be(node);
				break;
			}
			case OPCODE_bf: {
				result = this.rewrite_bf(node);
				break;
			}
			case OPCODE_domain: {
				result = this.rewrite_domain(node);
				break;
			}
			case OPCODE_eq: {
				result = this.rewrite_eq(node);
				break;
			}
			case OPCODE_fa: {
				result = this.rewrite_fa(node);
				break;
			}
			case OPCODE_in: {
				result = this.rewrite_in(node);
				break;
			}
			case OPCODE_noteq: {
				result = this.rewrite_noteq(node);
				break;
			}
			case OPCODE_notin: {
				result = this.rewrite_notin(node);
				break;
			}			
			case OPCODE_rs: 
			case OPCODE_trsl: {
				result = this.rewrite_rs(node);
				break;
			}								
			case OPCODE_cp: {
				result = this.rewrite_cp(node);
				break;
			}
			case OPCODE_sor: {
				result = this.rewrite_sor(node);
				break;
			}
			case OPCODE_subset: {
				result = this.rewrite_subset(node);
				break;
			}
			case OPCODE_subseteq: {
				result = this.rewrite_subseteq(node);
				break;
			}
			case OPCODE_IsAFcn: {
				result = this.rewrite_isafcn(node);
				break;
			}
			default: {
				int alen = result.getOperandSize();
				if (result.opCode == OPCODE_lor || result.opCode == OPCODE_ite ||
						result.opCode == OPCODE_implies || result.opCode == OPCODE_equiv) {
					this.depth++;
				}
				for (int i = 0; i < alen; i++) {
					Z3Node tmp0 = result.getOperand(i), lhs = null, rhs = null;
					int opCode = tmp0.opCode; 
					if (opCode == OPCODE_eq) {
						lhs = tmp0.getOperand(0).clone();
						rhs = tmp0.getOperand(1).clone();						
					}
					tmp0 = this.rewrite(tmp0);
					if (tmp0.getOperandSize() == 2 && tmp0.getOperand(1).opCode == OPCODE_ite) {
						tmp0 = this.rewrite_binary_ite(tmp0);
					}
					else if (tmp0.getOperandSize() == 1 && tmp0.getOperand(0).opCode == OPCODE_ite) {
						tmp0 = this.rewrite_unary_ite(tmp0);
					}								
					if (opCode == OPCODE_eq) {
						int pos = this.z3Encoder.getVarIndex(lhs.name);
						if (pos >= 0 && !this.z3Encoder.hasDef(pos)) {
							Z3Node lhsSort = lhs.getSort(),
									rhsSort = rhs.getSort();							
							lhs.setSort(rhsSort);							
							rhs.setSort(lhsSort);
							this.bVars.clear();
							if (isSafeWOBVar(rhs)) {
								this.z3Encoder.addDef(pos, rhs, this.depth);	
							}							
						}
					}
					result.setOperand(i, tmp0);				
					if (result.opCode == OPCODE_lor || result.opCode == OPCODE_ite ||
							result.opCode == OPCODE_implies || 
							(result.opCode == OPCODE_equiv   && i == 1)) {
						this.z3Encoder.removeDef(this.depth);
					}
				}
				if (result.opCode == OPCODE_lor || result.opCode == OPCODE_ite ||
						result.opCode == OPCODE_implies || result.opCode == OPCODE_equiv) {
					this.depth--;
				}
				break;
			}
			}						
			if (result.getOperandSize() == 2 && result.getOperand(1).opCode == OPCODE_ite) {
				result = this.rewrite_binary_ite(node);
			}
			else if (result.getOperandSize() == 1 && result.getOperand(0).opCode == OPCODE_ite) {
				result = this.rewrite_unary_ite(node);
			}
			result.isRewriten = true;
			return result;
		}
		else {
			return null;	
		}		
	}

	// After the translation, all nodes must have it's corresponding name in SMT2.
	// There are only three exceptional cases: OPCODE_in, _fa, and _IsAFcn
	public final void rename(Z3Node node) {
		if (node == null) {
			return;
		}
		if (node.getSort() == null) {
			//				Assert.fail(ConstraintErr, node.name + " has no sort.");
			System.out.println(node.name + " has no sort.");
			node.name = node.name + " has no sort.";
		}

		switch (node.opCode) {
		//			case OPCODE_2int: {
		//				Z3Node op = node.getOperand(0);
		//				node.name = op.getSort().name + "2int";
		//				break;
		//			}
		case OPCODE_domain: {
			Z3Node op = node.getOperand(0);
			node.name = "domain_" + op.getSort().name;
			break;
		}
		case OPCODE_in: {
			//				Z3Node type = node.getOperand(1).getElemSort();
			//				if (type.equals(NoSort)) {
			//					type = node.getOperand(0).getSort();
			//				}
			//				node.name = type.name + "_in";
			Z3Node op = node.getOperand(1);
			node.name = "in_" + op.getSort().name;
			break;
		}
		case OPCODE_fa:
		case OPCODE_alpha: {
			//				Z3Node lhs = node.getOperand(0),
			//						domain = lhs.getDomain(0),
			//						range  = lhs.getRange(0);
			//				node.name = domain.getElemSort().name + "_apply_" + range.getElemSort();
			Z3Node lhs = node.getOperand(0),
					sort = lhs.getSort();
			if (sort.opCode == OPCODE_rsort || sort.opCode == OPCODE_tsort) {
				node.opCode = OPCODE_trsl;
				node.name = NoName;
				Z3Node arg = node.getOperand(1).clone();
				if (!arg.isChangedName) {
					arg.name = "z3f_" + arg.name;					
					node.setOperand(1, arg);
					arg.isChangedName = true;	
				}
			}
			else {
				node.name = "alpha_" + lhs.getSort().name;				
			}			
			break;
		}
		//			case OPCODE_iapply: {
		//				Z3Node lhs = node.getOperand(0);				
		//				String dom = lhs.getSort().name;						
		//				node.name = dom + "_iapply";
		//								 
		//				break;
		//			}
		//			case OPCODE_IsAFcn: {
		//				node.name = "IsAFcn";
		//				break;
		//			}
		case OPCODE_rs:
		case OPCODE_trsl: {
			node.name = NoName;				
			Z3Node arg = node.getOperand(1).clone();
			if (!arg.isChangedName) {
				arg.name = "z3f_" + arg.name;					
				node.setOperand(1, arg);
				arg.isChangedName = true;	
			}
			break;
		}
		default: {
			if (node.name.equals(NoName)) {
				//					Assert.fail(NoNameErr, "An Z3Node has no name.\n");	
				System.out.println("An Z3Node has no name." + Integer.toString(node.opCode) + "\n");
				node.name = "An Z3Node has no name." + Integer.toString(node.opCode) + "\n";
			}			
		}
		}

		int i;
		for (i = 0; i < node.getExprSize(); i++) {
			this.rename(node.getExpr(i));
		}
		for (i = 0; i < node.getOperandSize(); i++) {
			this.rename(node.getOperand(i));
		}
		for (i = 0; i < node.getDomainSize(); i++) {
			this.rename(node.getDomain(i));
		}
		for (i = 0; i < node.getRangeSize(); i++) {
			this.rename(node.getRange(i));
		}		
		for (i = 0; i < node.getBoundedVarSize(); i++) {
			this.rename(node.getBoundedVar(i));
		}
		for (i = 0; i < node.getFieldSize(); i++) {
			this.rename(node.getField(i));
		}			
	}		
	
	public final Z3Node simplify(Z3Node node) {
		Z3Node res = node;				
		switch (node.opCode) {
		case OPCODE_be: {
			Z3Node body = node.getExpr(0);
			body = this.simplify(body);
			res.setExpr(0, body);
			return res;
		}
		case OPCODE_bf: {
			Z3Node body = node.getExpr(0);
			body = this.simplify(body);
			res.setExpr(0, body);
			if (body.name.equals("true")) {
				res = new Z3Node("true", OPCODE_true, this.z3Encoder.boolSort, null, tla_atom, NoSet);
			}
			return res;
		}
		case OPCODE_land: {
			res = new Z3Node("and", OPCODE_land, this.z3Encoder.boolSort, null, tla_atom, NoSet);
			int alen = node.getOperandSize();
			for (int i = 0; i < alen; i++) {
				Z3Node op = node.getOperand(i);
				op = this.simplify(op);
				if (op.name.equals("false")) {
					return new Z3Node("false", OPCODE_false, this.z3Encoder.boolSort, null, tla_atom, NoSet);
				}
				if (!op.name.equals("true")) { 					
					if (op.opCode == OPCODE_land) {
						int alen1 = op.getOperandSize();
						for (int j = 0; j < alen1; j++) {
							Z3Node op1 = op.getOperand(j);
							res.addOperand(op1);
						}
					}
					else {
						res.addOperand(op);
					}
				}				
			}
			alen = res.getOperandSize();
			if (alen == 0) {
				res = new Z3Node("true", OPCODE_true, this.z3Encoder.boolSort, null, tla_atom, NoSet);
			}
			return res;
		}
		case OPCODE_lor: {
			res = new Z3Node("or", OPCODE_lor, this.z3Encoder.boolSort, null, tla_atom, NoSet);
			int alen = node.getOperandSize();
			for (int i = 0; i < alen; i++) {
				Z3Node op = node.getOperand(i);
				op = this.simplify(op);
				if (op.name.equals("true")) {
					return new Z3Node("true", OPCODE_true, this.z3Encoder.boolSort, null, tla_atom, NoSet);
				}
				if (!op.name.equals("false")) { 
					if (op.opCode == OPCODE_lor) {
						int alen1 = op.getOperandSize();
						for (int j = 0; j < alen1; j++) {
							Z3Node op1 = op.getOperand(j);
							res.addOperand(op1);
						}
					}
					else {
						res.addOperand(op);
					}
				}				
			}
			alen = res.getOperandSize();
			if (alen == 0) { 
				res = new Z3Node("false", OPCODE_false, this.z3Encoder.boolSort, null, tla_atom, NoSet);
			}
			return res;
		}
		case OPCODE_eq: {
			Z3Node lhs = res.getOperand(0),
					rhs = res.getOperand(1);
			lhs = this.simplify(lhs);
			rhs = this.simplify(rhs);
			if (lhs.isSyntacticEqual(rhs)) {
				res = new Z3Node("true", OPCODE_true, this.z3Encoder.boolSort, null, tla_atom, NoSet);
			}
			else {
				res.setOperand(0, lhs);
				res.setOperand(1, rhs);
			}
			return res;
		}
		case OPCODE_implies: {
			Z3Node lhs = res.getOperand(0),
					notLHS = new Z3Node("not", OPCODE_lnot, this.z3Encoder.boolSort, null, lhs, tla_atom, NoSet),
					rhs = res.getOperand(1);
			notLHS = this.simplify(notLHS);
			rhs = this.simplify(rhs);
			res = new Z3Node("or", OPCODE_lor, this.z3Encoder.boolSort, null, notLHS, rhs, tla_atom, NoSet);
			res = this.simplify(res);
			return res;
		}		
		case OPCODE_lnot: {
			Z3Node op = node.getOperand(0);
			op = this.simplify(op);
			if (op.name.equals("true")) {
				return new Z3Node("false", OPCODE_false, this.z3Encoder.boolSort, null, tla_atom, NoSet);
			}
			else if (op.name.equals("false")) {
				return new Z3Node("true", OPCODE_true, this.z3Encoder.boolSort, null, tla_atom, NoSet);
			}
			else {
				switch (op.opCode) {
				case OPCODE_lnot: {
					return op.getOperand(0);
				}
				case OPCODE_land: {
					res = new Z3Node("or", OPCODE_lor, this.z3Encoder.boolSort, null, tla_atom, NoSet);
					int alen = op.getOperandSize();
					for (int i = 0; i < alen; i++) {
						Z3Node expr = op.getOperand(i),
								notExpr = new Z3Node("not", OPCODE_lnot, this.z3Encoder.boolSort, null, expr, tla_atom, NoSet);
						notExpr = this.simplify(notExpr);
						res.addOperand(notExpr);
					}
					res = this.simplify(res);
					return res;
				}
				case OPCODE_lor: {
					res = new Z3Node("and", OPCODE_land, this.z3Encoder.boolSort, null, tla_atom, NoSet);
					int alen = op.getOperandSize();
					for (int i = 0; i < alen; i++) {
						Z3Node expr = op.getOperand(i),
								notExpr = new Z3Node("not", OPCODE_lnot, this.z3Encoder.boolSort, null, expr, tla_atom, NoSet);
						notExpr = this.simplify(notExpr);
						res.addOperand(notExpr);
					}
					res = this.simplify(res);
					return res;
				}
				case OPCODE_bf: {
					Z3Node x = op.getBoundedVar(0),
							S = op.getDomain(0),
							body = op.getExpr(0),
							notBody = new Z3Node("not", OPCODE_lnot, this.z3Encoder.boolSort, null, body, tla_atom, NoSet);							
					notBody = this.simplify(notBody);
					res = new Z3Node("exists", OPCODE_be, this.z3Encoder.boolSort, null, tla_atom, NoSet);
					res.addBoundedVar(x);
					res.addDomain(S);
					res.addExpr(notBody);
					return res;
				}
				case OPCODE_be: {
					Z3Node x = op.getBoundedVar(0),
							S = op.getDomain(0),
							body = op.getExpr(0),
							notBody = new Z3Node("not", OPCODE_lnot, this.z3Encoder.boolSort, null, body, tla_atom, NoSet);							
					notBody = this.simplify(notBody);
					res = new Z3Node("forall", OPCODE_bf, this.z3Encoder.boolSort, null, tla_atom, NoSet);
					res.addBoundedVar(x);
					res.addDomain(S);
					res.addExpr(notBody);
					return res;
				}
				default: {
					res.setOperand(0, op);
					return res;
				}
				}
			}			
		}
		default: {
			int alen = res.getOperandSize();
			for (int i = 0; i < alen; i++) {
				Z3Node op = res.getOperand(i);
				op = this.simplify(op);
				res.setOperand(i, op);
			}
			return res;
		}
		}		
	}

	private final void sor_gen(int[] pos, int cur, Z3Node sor, Z3Node set) {		
		if (cur == pos.length) {
			Z3Node rcdSort = sor.getSort().getElemSort(),
					rcd = this.z3Tool.createGlobalConst(),
					conj = new Z3Node("and", OPCODE_land, this.z3Encoder.boolSort, null, tla_atom, NoSet),
					lval = null, rval = null, field = null, S = null, eq = null, elemSort = null;			
			rcd.setSort(rcdSort);
			int alen = pos.length;
			this.z3Encoder.addFreshVar(rcd);
			for (int i = 0; i < alen; i++) {
				field = sor.getField(i);
				S = sor.getRange(i);
				elemSort = S.getSort().getElemSort();
				lval = new Z3Node(NoName, OPCODE_trsl, elemSort, null, rcd, field, elemSort.kind, elemSort.setLevel);
				rval = S.getOperand(pos[i]);
				eq = new Z3Node("=", OPCODE_eq, this.z3Encoder.boolSort, null, lval, rval, tla_atom, NoSet);
				eq = this.rewrite(eq);
				conj.addOperand(eq);
			}
			set.addOperand(rcd);
			this.rename(conj);
			Z3Node assertion = new Z3Node("assert", OPCODE_assert, this.z3Encoder.boolSort, null, conj, tla_atom, NoSet);
			this.z3Encoder.addFreshAssertion(assertion);
		}
		else {
			Z3Node S = sor.getRange(cur);
			for (int i = 0; i < S.getOperandSize(); i++) {
				pos[cur] = i;
				this.sor_gen(pos, cur + 1, sor, set);
				pos[cur] = -1;
			}
		}
	}	

	public final Z3Node rewrite_sor(Z3Node node) {
		if (node.name.equals(NoName)) {
			return node;
		}
		int index = this.z3Encoder.getLazyValueIndex(node); 		
		if (index >= 0) {
			return this.z3Encoder.getLazyValue(index);
		}
		int alen = node.getFieldSize();
		for (int i = 0; i < alen; i++) {			
			if (node.getRange(i).opCode != OPCODE_se) {
				return node;
			}
		}		
		Z3Node sort = node.getSort(),		
				res = new Z3Node(node.name, OPCODE_se, sort, null, sort.kind, sort.setLevel);
		int[] pos = new int[alen];
		this.sor_gen(pos, 0, node, res);
		this.z3Encoder.addLazyValue(res);
		return res;
	}

	private final void cp_gen(int[] pos, int cur, Z3Node cp, Z3Node set) {		
		if (cur == pos.length) {
			Z3Node tupSort = cp.getSort().getElemSort(),
					tup = this.z3Tool.createGlobalConst(),
					conj = new Z3Node("and", OPCODE_land, this.z3Encoder.boolSort, null, tla_atom, NoSet),
					lval = null, rval = null, field = null, S = null, eq = null, elemSort = null;			
			tup.setSort(tupSort);
			int alen = pos.length;
			this.z3Encoder.addFreshVar(tup);
			for (int i = 0; i < alen; i++) {
				field = tup.getField(i);
				S = cp.getOperand(i);
				elemSort = S.getSort().getElemSort();
				lval = new Z3Node(NoName, OPCODE_trsl, elemSort, null, tup, field, elemSort.kind, elemSort.setLevel);
				rval = S.getOperand(pos[i]);
				eq = new Z3Node("=", OPCODE_eq, this.z3Encoder.boolSort, null, lval, rval, tla_atom, NoSet);
				eq = this.rewrite(eq);
				conj.addOperand(eq);
			}
			set.addOperand(tup);
			this.rename(conj);
			Z3Node assertion = new Z3Node("assert", OPCODE_assert, this.z3Encoder.boolSort, null, conj, tla_atom, NoSet);
			this.z3Encoder.addFreshAssertion(assertion);
		}
		else {
			Z3Node S = cp.getOperand(cur);
			for (int i = 0; i < S.getOperandSize(); i++) {
				pos[cur] = i;
				this.cp_gen(pos, cur + 1, cp, set);
				pos[cur] = -1;
			}
		}
	}	

	public final Z3Node rewrite_cp(Z3Node node) {
		if (node.name.equals(NoName)) {
			return node;
		}
		int index = this.z3Encoder.getLazyValueIndex(node); 		
		if (index >= 0) {
			return this.z3Encoder.getLazyValue(index);
		}
		int alen = node.getFieldSize();
		for (int i = 0; i < alen; i++) {			
			if (node.getOperand(i).opCode != OPCODE_se) {
				return node;
			}
		}		
		Z3Node sort = node.getSort(),		
				res = new Z3Node(node.name, OPCODE_se, sort, null, sort.kind, sort.setLevel);
		int[] pos = new int[alen];
		this.cp_gen(pos, 0, node, res);
		this.z3Encoder.addLazyValue(res);
		return res;
	}

	private final void subset_gen(int[] pos, int cur, Z3Node S, Z3Node set) {		
		if (cur == pos.length) {
			Z3Node sort = S.getSort();
			if (set.getOperandSize() == 0) {
				Z3Node subset = new Z3Node("empty_" + sort.name, OPCODE_const, sort, null, sort.kind, sort.setLevel);
				set.addOperand(subset);
			}
			else {
				Z3Node subset = this.z3Tool.createGlobalConst(),
						bf = new Z3Node("forall", OPCODE_bf, this.z3Encoder.boolSort, null, tla_atom, NoSet),						
						x  = this.z3Tool.createGlobalConst(),
						sortX = S.getSort().getElemSort(),
						lhs = new Z3Node(NoName, OPCODE_in, this.z3Encoder.boolSort, null, x, subset, tla_atom, NoSet),
						rhs = new Z3Node("or", OPCODE_lor, this.z3Encoder.boolSort, null, tla_atom, NoSet),
						eq = new Z3Node("=", OPCODE_eq, this.z3Encoder.boolSort, null, lhs, rhs, tla_atom, NoSet);
				this.constraintChecker.unifySort_equivSort(subset, S);
				this.constraintChecker.unifySort_in(x, S);
				int alen = pos.length;
				for (int i = 0; i < alen; i++) {
					if (pos[i] == 1) {
						Z3Node tmp = new Z3Node("=", OPCODE_eq, this.z3Encoder.boolSort, null, x, S.getOperand(i), tla_atom, NoSet);
						tmp = this.rewrite(tmp);
						rhs.addOperand(tmp);
					}
				}
				bf.addBoundedVar(x);
				bf.addDomain(sortX);
				bf.addExpr(eq);
				this.rename(bf);
				Z3Node assertion = new Z3Node("assert", OPCODE_assert, this.z3Encoder.boolSort, null, bf, tla_atom, NoSet);
				set.addOperand(subset);
				this.z3Encoder.addFreshVar(subset);
				this.z3Encoder.addFreshAssertion(assertion);
			}			
		}
		else {			
			for (int i = 0; i < 2; i++) {
				pos[cur] = i;
				this.subset_gen(pos, cur + 1, S, set);
				pos[cur] = -1;
			}
		}
	}	

	public final Z3Node rewrite_subset(Z3Node node) {
		if (node.name.equals(NoName)) {
			return node;
		}
		int index = this.z3Encoder.getLazyValueIndex(node); 		
		if (index >= 0) {
			return this.z3Encoder.getLazyValue(index);
		}
		Z3Node S = node.getOperand(0);
		S = this.z3Encoder.getDef(S);
		S = this.rewrite(S);
		if (S.opCode != OPCODE_se) {
			return node;
		}
		Z3Node sort = node.getSort(),		
				res = new Z3Node(node.name, OPCODE_se, sort, null, sort.kind, sort.setLevel);
		int alen = S.getOperandSize();
		int[] pos = new int[alen];
		this.subset_gen(pos, 0, S, res);
		this.z3Encoder.addLazyValue(res);
		return res;
	}

}
