package z3parser;

import util.Assert;

public class ConstraintChecker implements Z3Constants, Z3ErrorCode {
	private Z3Encoder z3encoder;
	
	private ConstraintChecker() { }
	
	public ConstraintChecker(Z3Encoder encoder) {
		this.z3encoder = encoder;
	}
	
	public final void unifySort_equivSort(Z3Node lhs, Z3Node rhs) {
		Z3Node lSort = lhs.getSort(),
				rSort = rhs.getSort();
		if (lSort != null && rSort != null && !lSort.name.equals(rSort.name)) {
			Assert.fail(NoSortErr, "Cannot unify two different ground sorts " + lSort.name + " " + rSort.name);
		}
		else if (lSort == null && rSort != null) {
			lhs.setSort(rSort);			
		}
		else if (lSort != null && rSort == null) {
			rhs.setSort(lSort);			
		}		
	}
	
	private final void unifyInfo(Z3Node var, Z3Node info, Z3Node sort) {
		
	}
	
	public final void unifySort_eq(Z3Node lhs, Z3Node rhs) {
		Z3Node lSort = lhs.getSort(),
				rSort = rhs.getSort();
		if (lSort != null && rSort != null && !lSort.name.equals(rSort.name)) {
			Assert.fail(NoSortErr, "Cannot unify two different ground sorts " + lSort.name + " " + rSort.name);
		}
		else if (lSort == null && rSort != null) {
			lhs.setSort(rSort);					
		}
		else if (lSort != null && rSort == null) {
			rhs.setSort(lSort);			
		}		
	}
	
	public final void unifySort_in(Z3Node lhs, Z3Node rhs) {
		if (lhs.setLevel != iNull && rhs.setLevel != iNull && lhs.setLevel >= rhs.setLevel) {
			Assert.fail(NoSortErr, lhs.name + " cannot be an element of " + rhs.name);
		}
		Z3Node lSort = lhs.getSort(),
				rSort = rhs.getSort(),
				rElemSort = null;
		if (rSort != null) {
			rElemSort = rSort.getElemSort();
		}
		if (lSort == null) {
			lhs.setSort(rElemSort);			
			return;
		}
		else if (rSort == null) {
			Z3Node setSort = this.z3encoder.getSort_ssort_elem(lSort);
			rhs.setSort(setSort);			
			return;
		}				
		else if (rElemSort != null && !lSort.name.equals(rElemSort.name)) {
			Assert.fail(NoSortErr, "Cannot find an appropriate sort for " + lhs.name + " " + rhs.name);			
		}
	}
	
	public final void unifySort_subseteq(Z3Node lhs, Z3Node rhs) {
		if (lhs.setLevel == 0) {
			Assert.fail(NoSortErr, lhs.name + " is not a set.");
		}
		if (rhs.setLevel == 0) {
			Assert.fail(NoSortErr, rhs.name + " is not a set.");
		}
		Z3Node lSort = lhs.getSort(),
				rSort = rhs.getSort();
		if (lSort != null && rSort != null && !lSort.name.equals(rSort.name)) {
			Assert.fail(NoSortErr, "Cannot unify two different ground sorts " + lSort.name + " " + rSort.name);
		}
		else if (lSort == null && rSort != null) {
			lhs.setSort(rSort);			
		}
		else if (lSort != null && rSort == null) {
			rhs.setSort(lSort);			
		}		
	}
	
	public final void dd_check(Z3Node node) {
		Z3Node lhs = node.getOperand(0),
				rhs = node.getOperand(1);
		if (lhs.getSort() != this.z3encoder.intSort) {
			Assert.fail(ConstraintErr, "The lhs of .. is not an integer.");
		}
		if (rhs.getSort() != this.z3encoder.intSort) {
			Assert.fail(ConstraintErr, "The rhs of .. is not an integer.");
		} 
		node.setSort(this.z3encoder.setIntSort);
	}
	
	public final void IntsInt_check(Z3Node node) {
		Z3Node op0 = node.getOperand(0),
				op1 = node.getOperand(1);
		if (op0.getSort() != this.z3encoder.intSort && !op0.getSort().name.equals(Int)) {
			Assert.fail(ConstraintErr, "The first operand of " + node.name + " is not an integer.");
		}
		if (op1.getSort() != this.z3encoder.intSort && !op1.getSort().name.equals(Int)) {
			Assert.fail(ConstraintErr, "The second operand of " + node.name + " is not an integer.");
		} 
		node.setSort(this.z3encoder.intSort);		
	}
	
	public final void IntsBool_check(Z3Node node) {
		Z3Node op0 = node.getOperand(0),
				op1 = node.getOperand(1);
		if (op0.getSort() != this.z3encoder.intSort && !op0.getSort().name.equals(Int)) {
			Assert.fail(ConstraintErr, "The first operand of " + node.name + " is not an integer.");
		}
		if (op1.getSort() != this.z3encoder.intSort && !op0.getSort().name.equals(Int)) {
			Assert.fail(ConstraintErr, "The second operand of " + node.name + " is not an integer.");
		}
		node.setSort(this.z3encoder.boolSort);			
	}
	
	public final void be_check(Z3Node node) {
		Z3Node x = node.getBoundedVar(0),
				S = node.getDomain(0),
				body = node.getExpr(0);
		if (body.getSort() != this.z3encoder.boolSort) {
			Assert.fail(ConstraintErr, "The body of a quantified formula is not a boolean formula.");
		}
		this.unifySort_in(x, S);
		node.setSort(this.z3encoder.boolSort);
	}
	
	public final void bf_check(Z3Node node) {
		Z3Node x = node.getBoundedVar(0),
				S = node.getDomain(0),
				body = node.getExpr(0);
		if (body.getSort() != this.z3encoder.boolSort) {
			Assert.fail(ConstraintErr, "The body of a quantified formula is not a boolean formula.");
		}
		this.unifySort_in(x, S);
		node.setSort(this.z3encoder.boolSort);
	}
	
	public final void ite_check(Z3Node node) {
		Z3Node con = node.getOperand(0),
				action1 = node.getOperand(1),
				action2 = node.getOperand(2);
		if (con.getSort() != this.z3encoder.boolSort) {
			Assert.fail(ConstraintErr, "The condition of an IF THEN ELSE expression is not a boolean formula.");
		}
		this.unifySort_equivSort(action1, action2);		
		node.setSort(action1.getSort());
		node.passSortInfo();
	}
	
	public final void cp_check(Z3Node node) {
		int alen = node.getOperandSize();
		Z3Node op = null;
		for (int i = 0; i < alen; i++) {
			op = node.getOperand(i);
			if (op.getSort() == null) {
				Assert.fail(ConstraintErr, "One set in OPCODE_cp has no sort.");
			}
			if (op.setLevel == 0) {
				Assert.fail(ConstraintErr, "One operand of the Cartesion product is not a set.");
			}
		}		
		node.setSort(this.z3encoder.getSort_cp(node));
	}
	
	public final void boolOperator_check(Z3Node node) {
		int alen = node.getOperandSize();
		Z3Node op = null;
		for (int i = 0; i < alen; i++) {
			op = node.getOperand(i);
			if (op.getSort() != this.z3encoder.boolSort) {
				Assert.fail(ConstraintErr, "A boolean formula with non-boolean child-expression.");
			}
		}		
		node.setSort(this.z3encoder.boolSort);
	}
	
	public final void exc_check(Z3Node node) {
		Z3Node fcn = node.getOperand(0),
				lhs = node.getOperand(1),
				rhs = node.getOperand(2);
		if (fcn.kind != tla_fcn && fcn.kind != tla_rcd && fcn.kind != tla_tup) {
			Assert.fail(ConstraintErr, "The 1st argument of the EXCEPT expression  is not a function: " + fcn.name + ".");
		}		
		this.unifySort_equivSort(node, fcn);
		Z3Node sort = node.getSort();
		if (sort.opCode == OPCODE_fsort) {
			this.unifySort_equivSort(lhs, node.dom);
			this.unifySort_equivSort(rhs, node.cod);
		}
		else if (sort.opCode == OPCODE_rsort) {
			int alen = sort.getFieldSize();
			this.unifySort_equivSort(lhs, this.z3encoder.strSort);
			for (int i = 0; i < alen; i++) {
				if (lhs.name.equals(sort.getField(i).name)) {
					this.unifySort_equivSort(rhs, sort.getRange(i));
					break;
				}
			}
		}
		else if (sort.opCode == OPCODE_tsort) {
			int alen = sort.getFieldSize();
			this.unifySort_equivSort(lhs, this.z3encoder.intSort);
			for (int i = 0; i < alen; i++) {
				this.unifySort_equivSort(rhs, sort.getRange(i));
				break;
			}
		}
	}
	
	public final void fa_check(Z3Node node) {
		Z3Node fcn = node.getOperand(0),
				arg = node.getOperand(1);
		if (fcn.kind != tla_fcn && fcn.kind != tla_rcd && fcn.kind != tla_tup) {
			Assert.fail(ConstraintErr, "The function application applies to a non-function expression " + fcn.name);
		}
		Z3Node sort = fcn.getSort();
		if (sort.opCode == OPCODE_fsort) {
			this.unifySort_equivSort(arg, fcn.dom);
			this.unifySort_equivSort(node, fcn.cod);
		}
		else if (sort.opCode == OPCODE_tsort) {
			this.unifySort_equivSort(arg, this.z3encoder.intSort);
			int alen = sort.getFieldSize();
			for (int i = 0; i < alen; i++) {
				if (sort.getField(i).name.equals(arg.name)) {
					this.unifySort_equivSort(node, sort.getRange(i));
					break;
				}
			}
		}
		else if (sort.opCode == OPCODE_rsort) {
			Assert.fail(ConstraintErr, "The function application is not for records.");
		}
	}
	
	public final void fc_check(Z3Node node) {
		// It seems that we don't need it.
		Z3Node S = node.getDomain(0),
				body = node.getExpr(0);
				
		if (S.setLevel == 0) {
			Assert.fail(ConstraintErr, "The domain, " + S.name + " , of a function is not a set.");
		}
		if (S.getElemSort() != null && body.getSort() != null) {
			node.setSort(this.z3encoder.getSort_fc(node));
			node.dom = S.getElemSort();
			node.cod = body.getSort();
		}
		else {
			
		}
//		if (node.dom != null && node.cod != null) {
//			
//		}
//		else {
//			node.setNullSort();
//		}
		
	}
	
	public final void rc_check(Z3Node node) {
		boolean noNullSort = true;
		int alen = node.getExprSize();
		Z3Node expr = null, field = null;
		for (int i = 0; i < alen; i++) {
			expr = node.getExpr(i);
			field = node.getField(i);
			if (field.getSort() != this.z3encoder.strSort) {
				Assert.fail(ConstraintErr, "One field name of OPCODE_rc is not a string.");
			}
			if (expr.getSort() == null) {
				noNullSort = false;
			}
		}
		if (noNullSort) {
			node.setSort(this.z3encoder.getSort_rc(node));
		}		
	}
	
	public final void rs_check(Z3Node node) {
		Z3Node rcd = node.getOperand(0),
				field = node.getOperand(1);
		if (field.getSort() != this.z3encoder.strSort) {
			Assert.fail(ConstraintErr, "The argument of the record selection is not a string.");
		}
		if (rcd.getSort() == null) {
			Assert.fail(ConstraintErr, "The record of OPCODE_rs has no sort.");
		}
		int alen = rcd.getFieldSize();
		for (int i = 0; i < alen; i++) {
			if (rcd.getField(i).name.equals(field.name)) {
				node.setSort(rcd.getRange(i).getSort());
				return;
			}
		}
		Assert.fail(ConstraintErr, field.name + " is not a field of " + rcd.name);
	}
	
	public final void se_check(Z3Node node) {
		int alen = node.getOperandSize(), i, level = iNull;
		Z3Node elemSort = null, op = null;
		for (i = 0; i < alen; i++) {
			op = node.getOperand(i);
				if (elemSort == null && op.getSort() != null) {
					elemSort = op.getSort();					
				}
				if (level < op.setLevel) {
					level = op.setLevel;
				}
		}
		if (node.setLevel == iNull) {
			if (level != iNull) {
				node.setLevel = level + 1;
			}			
		}
		else if (node.setLevel != level + 1) {
			Assert.fail(ConstraintErr, "Cannot set a set strata to " + node.name + ".");
		}
		if (elemSort != null) {
			for (i = 0; i < alen; i++) {
				op = node.getOperand(i);
				this.unifySort_equivSort(op, elemSort);
			}
			this.unifySort_equivSort(node, this.z3encoder.getSort_ssort_elem(elemSort));			
		}		
	}
	
	public final void soa_check(Z3Node node) {
		Z3Node x = node.getBoundedVar(0),
				S = node.getDomain(0),
				body = node.getExpr(0);
		this.unifySort_in(x, S);
		if (body.getSort() != null) {
			this.unifySort_equivSort(node, this.z3encoder.getSort_ssort_elem(body.getSort()));
			node.setLevel = body.setLevel + 1;
		}
		else {
			node.setSetNullSort(body.setLevel + 1);
		}
	}
	
	public final void sor_check(Z3Node node) {		
		int alen = node.getFieldSize(), i;
		Z3Node field = null, S = null;
		for (i = 0; i < alen; i++) {
			field = node.getField(i);
			S = node.getRange(i);
			if (field.getSort() != this.z3encoder.strSort) {
				Assert.fail(ConstraintErr, "One field of the set of records is not a string.");
			}
			if (S.getSort() == null) {
				Assert.fail(ConstraintErr, "One range of the set of records has no sort.");
			}
			if (S.setLevel == 0) {
				Assert.fail(ConstraintErr, "One range of the set of records is not a set.");
			}
		}
		node.setSort(this.z3encoder.getSort_sor(node));		
	}
	
	public final void sof_check(Z3Node node) {
		Z3Node S = node.getDomain(0),
				T = node.getRange(0);
		if (S.getSort() == null) {
			Assert.fail(ConstraintErr, "One domain of sof has no sort.");
		}
		if (T.getSort() == null) {
			Assert.fail(ConstraintErr, "One range of sof has no sort.");
		}
		node.setSort(this.z3encoder.getSort_sof(node));		
	}
	
	public final void sso_check(Z3Node node) {
		Z3Node x = node.getBoundedVar(0),
				S = node.getDomain(0),
				p = node.getExpr(0);
		if (p.getSort() != this.z3encoder.boolSort) {
			Assert.fail(ConstraintErr, "The body of sso is not a predicate.");
		}
		this.unifySort_in(x, S);
		this.unifySort_equivSort(node, S);
	}
	
	public final void tup_check(Z3Node node) {
		int alen = node.getFieldSize();
		boolean noNullSort = true;
		Z3Node expr = null, field = null;
		for (int i = 0; i < alen; i++) {
			field = node.getField(i);
			expr = node.getExpr(i);
			if (field.getSort() != this.z3encoder.intSort) {
				Assert.fail(ConstraintErr, "One field of the set of records is not an integer.");
			}						
			if (expr.getSort() == null) {
				noNullSort = false;
			}
		}
		if (noNullSort && alen > 0) {
			node.setSort(this.z3encoder.getSort_tup(node));
		}		
	}

	public final void subset_check(Z3Node node) {
		Z3Node op0 = node.getOperand(0);
		if (node.setLevel == iNull) {
			node.setLevel = op0.setLevel + 1;
		}
		else if (node.setLevel != op0.setLevel + 1) {
			Assert.fail(ConstraintErr, "Cannot set a set strata to " + node.name + ".");
		}
		if (op0.getSort() != null) {
			node.setSort(this.z3encoder.getSort_ssort_elem(op0.getSort()));
		}				
		else {
			node.setSetNullSort(op0.setLevel + 1);
		}
	}
	
	public final void union_check(Z3Node node) {
		Z3Node op0 = node.getOperand(0);
		if (op0.getElemSort() != null) {				
			node.setSort(op0.getElemSort());
		}
		else {
			node.setSetNullSort(op0.setLevel - 1);
		}				
	}
	
	public final void domain_check(Z3Node node) {
		Z3Node op0 = node.getOperand(0);
		if (op0.getDomainSize() > 0) {
			if (op0.getDomain(0).getSort() != null) {
				node.setSort(op0.getDomain(0).getSort());
			}
			else {
				node.setSetNullSort(iNull);
			}
		}
		else {
			node.setSetNullSort(iNull);
		}
	}
	
	public final void eq_check(Z3Node node) {
		Z3Node lhs = node.getOperand(0),
				rhs = node.getOperand(1);
		this.unifySort_eq(lhs, rhs);
	}
	
	public final void in_check(Z3Node node) {
		Z3Node x = node.getOperand(0),
				S = node.getOperand(1);
		this.unifySort_in(x, S);
		switch(S.subOpCode) {
		case OPCODE_sof: {
			x.kind = tla_fcn;
			Z3Node domSort = S.getDomain(0).getElemSort(),
				codSort = S.getRange(0).getElemSort(); 
			if (x.dom == null) {
				x.dom = domSort;				
			}
			else {
				if (!x.dom.name.equals(domSort.name)) {
					Assert.fail(NoSortErr, "There is a sort conflict in the domain of " + x.name);
				}
			}
			if (x.cod == null) {
				x.cod = codSort;
			}
			else {
				if (!x.cod.name.equals(codSort.name)) {
					Assert.fail(NoSortErr, "There is a sort conflict in the range of " + x.name);
				}
			}
			break;
		}
		case OPCODE_sor: {
			x.kind = tla_rcd;
			break;
		}
		case OPCODE_cp: {
			x.kind = tla_tup;
			break;
		}
		default: {
			break;
		}
		}
	}
	
	public final void notin_check(Z3Node node) {
		Z3Node x = node.getOperand(0),
				S = node.getOperand(1);
		this.unifySort_in(x, S);
	}
	
	public final void subseteq_check(Z3Node node) {
		Z3Node lhs = node.getOperand(0),
				rhs = node.getOperand(1);
		this.unifySort_equivSort(lhs, rhs);
		lhs.subOpCode = rhs.subOpCode;
	}

	public final void setdiff_check(Z3Node node) {
		Z3Node T = node.getOperand(0),
				U = node.getOperand(1);
		this.unifySort_equivSort(T, U);
		this.unifySort_equivSort(T, node);
		this.unifySort_equivSort(U, node);
	}

	public final void cup_check(Z3Node node) {
		Z3Node T = node.getOperand(0),
				U = node.getOperand(1);
		this.unifySort_equivSort(T, U);
		this.unifySort_equivSort(T, node);
		this.unifySort_equivSort(U, node);
	}
	
	public final void cap_check(Z3Node node) {
		Z3Node T = node.getOperand(0),
				U = node.getOperand(1);
		this.unifySort_equivSort(T, U);
		this.unifySort_equivSort(T, node);
		this.unifySort_equivSort(U, node);
	}
}
