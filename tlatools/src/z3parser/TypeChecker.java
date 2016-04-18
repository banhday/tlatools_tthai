package z3parser;


import util.Assert;

public class TypeChecker implements Z3Constants, Z3ErrorCode {
	
	private Z3Encoder encoder;

	private TypeChecker() {		
	}
	
	public TypeChecker(Z3Encoder encoder) {
		this.encoder = encoder;
	}
	
	private final void check_fa(Z3Node node, boolean beforeTranslation) {
		Z3Node fcn 	= node.getOperand(0),
				fcnSort = fcn.getSort();
		if (beforeTranslation) {
			this.checkBeforeTranslation(fcn);
		}
		else {
			this.checkAfterTranslation(fcn);
		}
		switch (fcnSort.opCode) {
		case OPCODE_fsort: {
			this.check_fa_fcn(node, beforeTranslation);
			return;
		}
		case OPCODE_rsort: {
			this.check_fa_rcd_tup(node, beforeTranslation);
			return;
		}
		case OPCODE_tsort: {
			this.check_fa_rcd_tup(node, beforeTranslation);
			return;
		}
		default: {
			Assert.fail(FcnErr, "Function checking is applied to a non-function.");
			return;
		}
		}
	}
	
	private final void check_fa_rcd_tup(Z3Node node, boolean beforeTranslation)  {
		Z3Node rcd = node.getOperand(0),
				field = node.getOperand(1);
		if (beforeTranslation) {
			this.checkBeforeTranslation(rcd);
			this.checkBeforeTranslation(field);
		}
		else {
			this.checkAfterTranslation(rcd);
			this.checkAfterTranslation(field);
		}		
		if (rcd.getSort().opCode == OPCODE_rsort && !this.compareSort(field.getSort(), this.encoder.strSort)) {
			Assert.fail(RcdFieldErr, "Cannot apply the record selection since " + 
										rcd.name + " is a record but " + field.name + " is not a string.");
		}
		if (rcd.getSort().opCode == OPCODE_tsort && !this.compareSort(field.getSort(), this.encoder.intSort)) {
			Assert.fail(RcdFieldErr, "Cannot apply the function application since " + 
										rcd.name + " is a tuple but " + field.name + " is not an integer.");
		}
		int alen = rcd.getFieldSize();
		for (int i = 0; i < alen; i++) {
			if (field.name.equals("z3f_" + rcd.getField(i).name)) {
				if (!this.compareSort(node.getSort(), rcd.getRange(i).getSort())) {
					Assert.fail(RSErr, "Type inconsistence in record selection with " + rcd.name + " " + field.name);
				}
				else {
					return;
				}					
			}
		}
		Assert.fail(NoFieldErr, field.name + " is not a field in " + rcd.name);		
	}
	
	private final void check_fa_fcn(Z3Node node, boolean beforeTranslation) {
		Z3Node fcn 	= node.getOperand(0),
				arg = node.getOperand(1);						
		Z3Node argSort 	= arg.getSort(),
				domSort	= fcn.dom.getSort(),
				codSort	= fcn.cod.getSort(),
				nodeSort= node.getSort();
		if (beforeTranslation) {
			this.checkBeforeTranslation(fcn);
			this.checkBeforeTranslation(arg);
		}
		else {
			this.checkAfterTranslation(fcn);
			this.checkAfterTranslation(arg);
		}	
		if (!this.compareSort(domSort, argSort)) {
			Assert.fail(DomArgErr, "A function's domain and its argument have different types.");
		}
		if (!this.compareSort(codSort, nodeSort)) {
			Assert.fail(CodErr, "A function's codomain and its returned value have different types.");
		}
	}
	
	private final void check_ints_int(Z3Node node, boolean beforeTranslation) {
		Z3Node x = node.getOperand(0),
				y = node.getOperand(1);
		if (beforeTranslation) {
			this.checkBeforeTranslation(x);
			this.checkBeforeTranslation(y);
		}
		else {
			this.checkAfterTranslation(x);
			this.checkAfterTranslation(y);
		}	
		if (!this.compareSort(node.getSort(), this.encoder.intSort)) {
			Assert.fail(IntOpErr, node.name + "does not have sort Int.");
		}
		if (!this.compareSort(x.getSort(), this.encoder.intSort)) {
			Assert.fail(IntOpErr, node.name + "does not have sort Int.");
		}
		if (!this.compareSort(y.getSort(), this.encoder.intSort)) {
			Assert.fail(IntOpErr, node.name + "does not have sort Int.");
		}
	}
	
	private final void check_ints_bool(Z3Node node, boolean beforeTranslation) {
		Z3Node x = node.getOperand(0),
				y = node.getOperand(1);
		if (beforeTranslation) {
			this.checkBeforeTranslation(x);
			this.checkBeforeTranslation(y);
		}
		else {
			this.checkAfterTranslation(x);
			this.checkAfterTranslation(y);
		}	
		if (!this.compareSort(node.getSort(), this.encoder.boolSort)) {
			Assert.fail(IntOpErr, node.name + "does not have sort Bool.");
		}
		if (!this.compareSort(x.getSort(), this.encoder.intSort)) {
			Assert.fail(IntOpErr, node.name + "does not have sort Int.");
		}
		if (!this.compareSort(y.getSort(), this.encoder.intSort)) {
			Assert.fail(IntOpErr, node.name + "does not have sort Int.");
		}
	}
	
	private final void checks_bools_bool(Z3Node node, boolean beforeTranslation) {
		if (!this.compareSort(node.getSort(), this.encoder.boolSort)) {
			Assert.fail(BoolOpErr, "Node with opcode " + Integer.toString(node.opCode) + " is not a Boolean expression.");
		}
		for (int i = 0; i < node.getOperandSize(); i++) {
			if (beforeTranslation) {
				this.checkBeforeTranslation(node.getOperand(i));
			}
			else {
				this.checkAfterTranslation(node.getOperand(i));
			}
			if (!this.compareSort(node.getOperand(i).getSort(), this.encoder.boolSort)) {
				Assert.fail(BoolOpErr, "Node with op#"
						+ "code " + Integer.toString(node.opCode) + " is not a Boolean expression.");
			}	
		}
	}
	
	private final void checks_ite(Z3Node node, boolean beforeTranslation) {
		Z3Node con = node.getOperand(0),
				act1 = node.getOperand(1),
				act2 = node.getOperand(2);
		if (beforeTranslation) {
			this.checkBeforeTranslation(con);
			this.checkBeforeTranslation(act1);
			this.checkBeforeTranslation(act2);
		}
		else {
			this.checkAfterTranslation(con);
			this.checkAfterTranslation(act1);
			this.checkAfterTranslation(act2);
		}
		if (!this.compareSort(con.getSort(), this.encoder.boolSort)) {
			Assert.fail(ITEConErr, "The condition of ite is not a Boolean expression.");
		}
		if (!this.compareSort(node.getSort(), act1.getSort()) || 
				!this.compareSort(act1.getSort(), act2.getSort())) {
			Assert.fail(ITEActErr, "The actions of ite have different sorts.");
		}
	}
	
	private final void check_domain(Z3Node node, boolean beforeTranslation) {
		Z3Node arg	= node.getOperand(0), 
				argSort = node.getOperand(0).getSort();
		if (beforeTranslation) {
			this.checkBeforeTranslation(arg);
		}
		else {
			this.checkAfterTranslation(arg);
		}
		if (argSort.opCode == OPCODE_rsort && !this.compareSort(node.getSort(), this.encoder.setStrSort)) {
			Assert.fail(DomRcddErr, "The domain of " + arg.name + " is not a set of strings.");
		}
		if (argSort.opCode == OPCODE_tsort && !this.compareSort(node.getSort(), this.encoder.setIntSort)) {
			Assert.fail(DomRcddErr, "The domain of " + arg.name + " is not a set of integers.");
		}
		if (argSort.opCode == OPCODE_fsort && !this.compareSort(node.getSort().getElemSort(), arg.dom.getSort())) {
			Assert.fail(DomFcnErr, "The domain of " + arg.name + "does not have a correct type.");
		}
	}
	
	private final void check_in(Z3Node node, boolean beforeTranslation) {
		Z3Node x = node.getOperand(0),
				S = node.getOperand(1);
		if (beforeTranslation) {
			this.checkBeforeTranslation(x);
			this.checkBeforeTranslation(S);
		}
		else {
			this.checkAfterTranslation(x);
			this.checkAfterTranslation(S);
		}
		if (!this.compareSort(x.getSort(), S.getSort().getElemSort())) {
			Assert.fail(InErr, "There is type inconsistence between " + x.name + " " + S.name);
		}
		if (!this.compareSort(node.getSort(), this.encoder.boolSort)) {
			Assert.fail(InErr, x.name + " in " + S.name + " is not a Boolean expression.");
		}
	}
	
	private final void check_eq(Z3Node node, boolean beforeTranslation) {
		if (!this.compareSort(node.getSort(), this.encoder.boolSort)) {
			Assert.fail(EqBoolErr, "The equation is not a Boolean expression");
		}
		Z3Node lhs = node.getOperand(0),
				rhs = node.getOperand(1);
		if (beforeTranslation) {
			this.checkBeforeTranslation(lhs);
			this.checkBeforeTranslation(rhs);
		}
		else {
			this.checkAfterTranslation(lhs);
			this.checkAfterTranslation(rhs);
		}
		if (!this.compareSort(lhs.getSort(), rhs.getSort())) {
			Assert.fail(EqErr, "Two sides of an equation have different sorts.");
		}
	}
	
	private final void check_be_bf(Z3Node node, boolean beforeTranslation) {
		Z3Node x = node.getBoundedVar(0),
				S = node.getDomain(0),
				p = node.getExpr(0);
		if (beforeTranslation) {
			this.checkBeforeTranslation(x);
			this.checkBeforeTranslation(S);
			this.checkBeforeTranslation(p);
		}
		else {
			this.checkAfterTranslation(x);
			this.checkAfterTranslation(S);
			this.checkAfterTranslation(p);
		}
		if (!this.compareSort(p.getSort(), this.encoder.boolSort)) {
			Assert.fail(BodyBoolErr, "The body of " + node.name + " is not a Boolean expression.");
		}
		if (beforeTranslation) {
			if (!this.compareSort(x.getSort(), S.getSort().getElemSort())) {
				Assert.fail(DomQuanErr, "The domain of " + node.name + " is not consistent.");
			}
		}
		else {
			if (!this.compareSort(x.getSort(), S.getSort())) {
				Assert.fail(DomQuanErr, "The domain of " + node.name + " is not consistent.");
			}	
		}
	}
	
	private void check_IsAFcn(Z3Node node) {
		Z3Node fcn = node.getOperand(0),
				fcnSort = fcn.getSort();
		this.checkBeforeTranslation(fcn);
		switch (fcnSort.opCode) {
		case OPCODE_fsort:
		case OPCODE_rsort:
		case OPCODE_tsort: {
			return;
		}
		default: {
			Assert.fail(IsAFcnErr, "An argument of the operator IsAFcn is not a function.");
		}
		}
	}
	
	private void check_cp(Z3Node node) {
		for (int i = 0; i < node.getOperandSize(); i++) {
			Z3Node op = node.getOperand(i),
					sort = op.getSort();
			this.checkBeforeTranslation(op);
			if (sort == null || sort.opCode != OPCODE_ssort) {
				Assert.fail(CPErr, "One argument of Cartesian product is not a set with type info.");
			}
		}		
	}
	
	private void check_exc(Z3Node node) {
		Z3Node fcn = node.getOperand(0),
				lhs = node.getOperand(1),
				rhs = node.getOperand(2);
		this.checkBeforeTranslation(fcn);
		this.checkBeforeTranslation(lhs);
		this.checkBeforeTranslation(rhs);
		if (fcn.kind != tla_fcn && fcn.kind != tla_rcd && fcn.kind != tla_tup) {
			Assert.fail(ExcErr1, "The 1st argument of the EXCEPT expression  is not a function: " + fcn.name + ".");
		}		
		if (!this.compareSort(node.getSort(), fcn.getSort())) {
			Assert.fail(ExcErr2, node.name + " and " + fcn.name + "do not have the same type.");
		}
		Z3Node sort = node.getSort();
		if (sort.opCode == OPCODE_fsort) {
			if (!this.compareSort(lhs.getSort(), node.dom.getSort())) {
				Assert.fail(ExcErr3, "There is a type conflict in the 1st argument of EXCEPT from " + fcn.name + " and " + lhs.name);
			}
			if (!this.compareSort(rhs.getSort(), node.cod.getSort())) {
				Assert.fail(ExcErr4, "There is a type conflict in the 2st argument of EXCEPT from " + fcn.name + " and " + rhs.name);
			}			
		}
		else if (sort.opCode == OPCODE_rsort) {			
			if (!this.compareSort(lhs.getSort(), this.encoder.strSort)) {
				Assert.fail(ExcErr3, "There is a type conflict in the 1st argument of EXCEPT from " + fcn.name + " and " + lhs.name);
			}
			int alen = sort.getFieldSize();
			for (int i = 0; i < alen; i++) {
				if (lhs.name.equals(sort.getField(i).name)) {
					if (!this.compareSort(rhs.getSort(), sort.getRange(i).getSort())) {
						Assert.fail(ExcErr4, "There is a type conflict in the 2st argument of EXCEPT from " + fcn.name + " and " + rhs.name);
					}
					break;
				}
			}
		}
		else if (sort.opCode == OPCODE_tsort) {			
			if (!this.compareSort(lhs.getSort(), this.encoder.intSort)) {
				Assert.fail(ExcErr3, "There is a type conflict in the 1st argument of EXCEPT from " + fcn.name + " and " + lhs.name);
			}
			int alen = sort.getFieldSize();			
			for (int i = 0; i < alen; i++) {
				if (!this.compareSort(rhs.getSort(), sort.getRange(i).getSort())) {
					Assert.fail(ExcErr4, "There is a type conflict in the 2st argument of EXCEPT from " + fcn.name + " and " + rhs.name);
				}		
				break;
			}
		}
	}
	
	private final void check_fc(Z3Node node) {
		Z3Node x = node.getBoundedVar(0), 
				S = node.getDomain(0),
				body = node.getExpr(0);
		this.checkBeforeTranslation(x);
		this.checkBeforeTranslation(S);
		this.checkBeforeTranslation(body);
		if (!this.compareSort(x.getSort(), S.getSort().getElemSort())) {
			Assert.fail(FcErr1, "The is a type conflict in the domain of the function construction.");
		}
		if (!this.compareSort(S.getSort().getElemSort(), node.dom.getSort())) {
			Assert.fail(FcErr2, "The is a type conflict in the domain of the function construction.");
		}	
		if (!this.compareSort(body.getSort(), node.cod.getSort())) {
			Assert.fail(FcErr3, "The is a type conflict in the codomain of the function construction.");
		}
	}
	
	private final void check_rc(Z3Node node) {	
		Z3Node sort = node.getSort();
		int alen = node.getExprSize();		
		for (int i = 0; i < alen; i++) {
			Z3Node expr = node.getExpr(i),
					field = node.getField(i);
			this.checkBeforeTranslation(expr);
			this.checkBeforeTranslation(field);
			if (!this.compareSort(field.getSort(), this.encoder.strSort)) {
				Assert.fail(RcErr1, "One field name of OPCODE_rc is not a string.");
			}
			if (!this.compareSort(expr.getSort(), sort.getRange(i).getSort())) {
				Assert.fail(RcErr2, "There is a type conflict in the record construction.");
			}
		}				
	}
	
	private final void check_cap_cup_setdiff(Z3Node node) {
		Z3Node S = node.getOperand(0),
				T = node.getOperand(1);
		this.checkBeforeTranslation(S);
		this.checkBeforeTranslation(T);
		if (!this.compareSort(node.getSort(), S.getSort()) ||
				!this.compareSort(S.getSort(), T.getSort())) {
			Assert.fail(SetOpErr, "The set operator with opcode" + Integer.toString(node.opCode) +
						"has a type conflict between " + S.name + " and " + T.name);			
		}
	}
	
	private final void check_subset(Z3Node node) {
		Z3Node op = node.getOperand(0);
		this.checkBeforeTranslation(op);
		if (!this.compareSort(node.getSort().getElemSort(), op.getSort())) {
			Assert.fail(SubsetErr, "The operator SUBSET has a type conflict with " + op.name);
		}
	}
	
	private final void check_subseteq(Z3Node node) {
		Z3Node S = node.getOperand(0),
				T = node.getOperand(1);
		this.checkBeforeTranslation(S);
		this.checkBeforeTranslation(T);
		if (!this.compareSort(S.getSort(), T.getSort()) || 
				!this.compareSort(node.getSort(), this.encoder.boolSort)) {
			Assert.fail(SetOpBoolErr, "The set operator with opcode " + Integer.toString(node.opCode) + 
						"has a type conflict.");
		}		
	}
	private final void check_union(Z3Node node) {
		Z3Node op0 = node.getOperand(0);
		this.checkBeforeTranslation(op0);
		if (!this.compareSort(op0.getSort().getElemSort(), node.getSort())) {
			Assert.fail(UnionErr, "A union operator with a type conflict.");
		}		
	}
	
	private final void check_se(Z3Node node) {
		Z3Node elemSort0 = node.getElemSort();
		int alen = node.getOperandSize();
		for (int i = 0; i < alen; i++) {
			Z3Node elem = node.getOperand(i),
					elemSort = elem.getSort();
			this.checkBeforeTranslation(elem);
			if (!this.compareSort(elemSort0, elemSort)) {
				Assert.fail(SeErr, "Set enumeration with type conflict");
			}
		}
	}

	private final void check_soa(Z3Node node) {
		Z3Node x = node.getBoundedVar(0),
				S = node.getDomain(0),
				body = node.getExpr(0);
		this.checkBeforeTranslation(x);
		this.checkBeforeTranslation(S);
		this.checkBeforeTranslation(body);
		if (!this.compareSort(x.getSort(), S.getSort().getElemSort())) {
			Assert.fail(SoaErr1, "SetOfAll with a type conflict between a bounded variable and its domain.");			
		}
		if (!this.compareSort(node.getSort().getElemSort(), body.getSort())) {
			Assert.fail(SoaErr2, "SetOfAll with a type conflict between a body and a type of a given node.");
		}
	}

	private final void check_sof(Z3Node node) {
		Z3Node S = node.getDomain(0),
				T = node.getRange(0),
				elemSort = node.getSort().getElemSort();
		this.checkBeforeTranslation(S);
		this.checkBeforeTranslation(T);
		if (!this.compareSort(S.getSort().getElemSort(), elemSort.dom.getSort())) {
			Assert.fail(SofErr1, "SetOfFunctions with a type conflict in its domain.");
		}
		if (!this.compareSort(T.getSort().getElemSort(), elemSort.cod.getSort())) {
			Assert.fail(SofErr2, "SetOfFunctions with a type conflict in its codomain.");
		}				
	}

	private final void check_sor(Z3Node node) {
		Z3Node sort = node.getSort();
		int alen = node.getFieldSize(),
				fieldSize = sort.getFieldSize();
		if (fieldSize != node.getFieldSize()) {
			Assert.fail(SorErr1, "A conflict of a number of field in " + node.name);
		}
		for (int i = 0; i < alen; i++) {
			Z3Node field = node.getField(i), 
					S = node.getRange(i);
			this.checkBeforeTranslation(field);
			this.checkBeforeTranslation(S);
			if (!this.compareSort(field.getSort(), this.encoder.strSort)) {
				Assert.fail(SorErr2, "A field " + field.name + " of the set of records is not a string.");
			}
			boolean noRange = true;
			for (int j = 0; j < fieldSize; j++) {
				if (field.name.equals(sort.getField(j).name)) {
					noRange = false;
					if (!this.compareSort(S.getSort(), sort.getRange(j).getSort())) {
						Assert.fail(SorErr3, "Field " + field.name + "with a type conflict.");
					}
					break;
				}
			}
			if (noRange) {
				Assert.fail(SorErr3, "Field " + field.name + " with no type info.");
			}
		}				
	}

	private final void check_sso(Z3Node node) {
		Z3Node x = node.getBoundedVar(0),
				S = node.getDomain(0),
				p = node.getExpr(0);
		this.checkBeforeTranslation(x);
		this.checkBeforeTranslation(S);
		this.checkBeforeTranslation(p);
		if (!this.compareSort(p.getSort(), this.encoder.boolSort)) {
			Assert.fail(SsoErr1, "The body of sso is not a predicate.");
		}
		if (!this.compareSort(x.getSort(), S.getSort().getElemSort())) {
			Assert.fail(SsoErr2, "A type conflict between a bounded variable and its domain in sso.");
		}
		if (!this.compareSort(node.getSort(), S.getSort())) {
			Assert.fail(SsoErr3, "A type conflict in sso.");
		}
	}

	private final void check_tup(Z3Node node) {
		Z3Node sort = node.getSort();
		if (sort.getFieldSize() != node.getFieldSize()) {
			Assert.fail(TupErr2, "A wrong number of field.");
		}
		int alen = node.getFieldSize();			
		for (int i = 0; i < alen; i++) {
			Z3Node field = node.getField(i), 
					expr = node.getExpr(i);
			this.checkBeforeTranslation(field);
			this.checkBeforeTranslation(expr);
			if (!this.compareSort(field.getSort(), this.encoder.intSort)) {
				Assert.fail(TupErr1, "One field of the set of records is not an integer.");
			}						
			if (!this.compareSort(expr.getSort(), sort.getRange(i).getSort())) {
				Assert.fail(TupErr2, "A type conflict of tup in field" + Integer.toString(i));
			}
		}				
	}
	
	public final void checkBeforeTranslation(Z3Node node) {
		boolean beforeTranslation = true;
		if (node == null) {
			return;
		}
		if (node.getSort() == null) {
			Assert.fail(NoSortErr, node.name + " has no sort.");				
		}
		switch (node.opCode) {
		// These cases are checked by the above condition.
		case OPCODE_var: 
		case OPCODE_const: 
		case OPCODE_bv: {
			return;
		}
		case OPCODE_fa: {
			this.check_fa(node, beforeTranslation);
			return;
		}
		case OPCODE_bsort:
		case OPCODE_fsort:
		case OPCODE_rsort:
		case OPCODE_ssort:
		case OPCODE_sfsort:
		case OPCODE_srsort:
		case OPCODE_stsort:
		case OPCODE_tsort: {
			return;
		}
		case OPCODE_add:
		case OPCODE_mul:
		case OPCODE_sub:
		case OPCODE_div:
		case OPCODE_mod: {
			this.check_ints_int(node, beforeTranslation);
			return;
		}
		case OPCODE_lt:
		case OPCODE_le:
		case OPCODE_gt:
		case OPCODE_ge: {
			this.check_ints_bool(node, beforeTranslation);
			return;
		}
		case OPCODE_true:
		case OPCODE_false:
		case OPCODE_pred: {
			if (!this.compareSort(node.getSort(), this.encoder.boolSort)) {
				Assert.fail(BoolOpErr, node.name + "does not have sort Bool.");
			}
			return;
		}
		case OPCODE_be:
		case OPCODE_bf: {
			this.check_be_bf(node, beforeTranslation);
			return;
		}		
		case OPCODE_cl:
		case OPCODE_dl:
		case OPCODE_land:
		case OPCODE_lor:
		case OPCODE_implies:
		case OPCODE_equiv:
		case OPCODE_lnot:
		case OPCODE_neg: {
			this.checks_bools_bool(node, beforeTranslation);
			return;
		}				 
		case OPCODE_cap: 
		case OPCODE_cup: 
		case OPCODE_setdiff: {
			this.check_cap_cup_setdiff(node);
			return;
		}
		case OPCODE_cp: {
			this.check_cp(node);
			return;
		}
		case OPCODE_domain: {
			this.check_domain(node, beforeTranslation);
			return;
		}
		case OPCODE_eq: 
		case OPCODE_noteq: {
			this.check_eq(node, beforeTranslation);
			return;
		}
		case OPCODE_exc: {
			this.check_exc(node);
			return;
		}
		case OPCODE_fc: {
			this.check_fc(node);
			return;
		}
		case OPCODE_in: 
		case OPCODE_notin: {
			this.check_in(node, beforeTranslation);
			return;
		}
		case OPCODE_IsAFcn: {
			this.check_IsAFcn(node);
			return;
		}
		case OPCODE_ite: {
			this.checks_ite(node, beforeTranslation);
			return;
		}	
		case OPCODE_rc: {
			this.check_rc(node);
			return;
		}
		case OPCODE_rs: {
			this.check_fa_rcd_tup(node, beforeTranslation);
			return;	
		}	
		case OPCODE_subset: {
			this.check_subset(node);
			return;
		}
		case OPCODE_subseteq: {
			this.check_subseteq(node);
			return;
		}
		
		case OPCODE_union: {
			this.check_union(node);
			return;
		}
		case OPCODE_se: {
			this.check_se(node);
			return;
		}
		case OPCODE_soa: {
			this.check_soa(node);
			return;
		}
		case OPCODE_sof: {			
			this.check_sof(node);
			return;
		}
		case OPCODE_sor: {
			this.check_sor(node);
			return;
		}
		case OPCODE_sso: {
			this.check_sso(node);
			return;
		}
		case OPCODE_tup: {
			this.check_tup(node);
			return;
		}
//		OPCODE_set 		OPCODE_fcn 		OPCODE_rcd		OPCODE_tuple	OPCODE_ept		OPCODE_iapply 
//		OPCODE_2int		OPCODE_bc 		OPCODE_case		OPCODE_pair		OPCODE_seq				
		default: {					
			Assert.fail(TransErr, "Forget to check a node with opCode " + Integer.toString(node.opCode));			
		}
		}
	}
	
	public final void checkAfterTranslation(Z3Node node) {
		boolean beforeTranslation = false;
		if (node == null) {
			return;
		}
		if (node.getSort() == null) {
			Assert.fail(NoSortErr, node.name + " has no sort.");				
		}
		switch (node.opCode) {
		// These cases are checked by the above condition.
		case OPCODE_var: 
		case OPCODE_const: 
		case OPCODE_bv: {
			return;
		}
//		OPCODE_set 		OPCODE_fcn 		OPCODE_rcd		OPCODE_tuple	OPCODE_ept		OPCODE_iapply 
//		OPCODE_2int		OPCODE_bc 		OPCODE_IsAFcn	OPCODE_eqnot	OPCODE_case 	OPCODE_cp
//		OPCODE_exc		OPCODE_lnot		OPCODE_fc		OPCODE_neg		OPCODE_pair		OPCODE_rc
//		OPCODE_subset	OPCODE_union	OPCODE_seq		OPCODE_se		OPCODE_soa		OPCODE_sor
//		OPCODE_sof		OPCODE_sso		OPCODE_tup
		case OPCODE_alpha: 
		case OPCODE_fa: {
			this.check_fa(node, beforeTranslation);
			return;
		}
		case OPCODE_assert: {
			Z3Node arg = node.getOperand(1),
					argSort = arg.getSort();
			this.checkAfterTranslation(arg);
			if (!this.compareSort(argSort, this.encoder.boolSort)) {
				Assert.fail(AssertErr, "An argument of an assertion is not a Boolean expression.");
			}
			return;
		}		 
		case OPCODE_bsort:
		case OPCODE_fsort:
		case OPCODE_rsort:
		case OPCODE_ssort:
		case OPCODE_sfsort:
		case OPCODE_srsort:
		case OPCODE_stsort:
		case OPCODE_tsort: {			
			return;
		}
		case OPCODE_add:
		case OPCODE_mul:
		case OPCODE_sub:
		case OPCODE_div:
		case OPCODE_mod: {
			this.check_ints_int(node, beforeTranslation);
			return;
		}
		case OPCODE_lt:
		case OPCODE_le:
		case OPCODE_gt:
		case OPCODE_ge: {
			this.check_ints_bool(node, beforeTranslation);
			return;
		}
		case OPCODE_true:
		case OPCODE_false:
		case OPCODE_pred: {
			if (!this.compareSort(node.getSort(), this.encoder.boolSort)) {
				Assert.fail(BoolOpErr, node.name + "does not have sort Bool.");
			}
			return;
		}
		case OPCODE_be:
		case OPCODE_bf: {
			this.check_be_bf(node, beforeTranslation);
			return;
		}		
		case OPCODE_cl:
		case OPCODE_dl:
		case OPCODE_land:
		case OPCODE_lor:
		case OPCODE_implies:
		case OPCODE_equiv:
		case OPCODE_lnot:
		case OPCODE_neg: {
			this.checks_bools_bool(node, beforeTranslation);
			return;
		}
		case OPCODE_domain: {
			this.check_domain(node, beforeTranslation);
			return;
		}
		case OPCODE_eq: {
			this.check_eq(node, beforeTranslation);
			return;
		}
		case OPCODE_in: {
			this.check_in(node, beforeTranslation);
			return;
		}		
		case OPCODE_ite: {
			this.checks_ite(node, beforeTranslation);
			return;
		}				
		case OPCODE_rs:
		case OPCODE_trsl: {
			this.check_fa_rcd_tup(node, beforeTranslation);
			return;	
		}		
		case OPCODE_se: {
			if (node.getOperandSize() == 0) {
				return;
			}	
			Assert.fail(TransErr, "Node with opcode " + Integer.toString(node.opCode) + " cannot be translated.");
		}
		default: {					
			Assert.fail(TransErr, "Node with opcode " + Integer.toString(node.opCode) + " cannot be translated.");			
		}
		}
	}
	
	private boolean compareSort(Z3Node sort1, Z3Node sort2) {
		if (sort1 == sort2 || sort1.name.equals(sort2.name)) {
			return true;
		}
		return false;
	}
	
	
}
