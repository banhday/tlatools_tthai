package z3parser;

import java.util.ArrayList;

import tla2sany.semantic.SemanticNode;
import tlc2.tool.ToolGlobals;
import util.Assert;

public class Z3Node implements ToolGlobals, Z3Constants {
	public String name;											// in z3
	public int opCode;											// in tla2	
	public int subOpCode;										// in tla2, just to check whether or not a variabe is a function, a record or a tuple
	private Z3Node z3Sort;										// in our encoding from tla2 to z3; its sort is Int, Bool, U, Str or record sorts	
	private Z3Node z3ElemSort;							// in our encoding from tla2 to z3; a elements' sort is Int, Bool, U, Str or record (and tuple) sorts		
	private ArrayList<Z3Node> exprs;				// for expressions e in record constructors [ hi |-> e], function constructors [ x \in S |-> e ], ...
	private ArrayList<Z3Node> operands;			// for operands
	private ArrayList<Z3Node> domains;			// for a function's domain or record's domains or quantified formulas	
	private ArrayList<Z3Node> ranges;				// for a function's range or record's ranges	
	private ArrayList<Z3Node> boundedVars; 	// x1, x2, ... in a quantified formula \forall x1 \in S1, x2 \in S2, ...
																					// now we support only 	\forall x \in S : ...
	private ArrayList<Z3Node> fields; 			// for fields in a record
	public boolean isConst;	    						// whether or not this var is primed
	public boolean isFcn;										// whether or not this var is unprimed
	public boolean isVar;			  						// whether or not this var is primed
	public int kind;												// It is just for know whether or not our variable is a function, a record or a tuple
	public int setLevel;										// the level of set strata;
	
	public Z3Node dom;											// for the function's domain
	public Z3Node cod;											// for the function's codomain
	
	public boolean isChangedName;						// for record's fields
	public boolean isRewriten;							// whether this is rewriten
	public boolean isDotDot;								// for M .. N	
	
	private Z3Node() {
		this.name 				= NoName;
		this.opCode 			= NoCode;	
		this.subOpCode		= this.opCode;
		this.z3Sort 			= null;		
		this.z3ElemSort		= null;
		this.exprs		 		= new ArrayList<Z3Node>();
		this.operands 		= new ArrayList<Z3Node>();
		this.domains 			= new ArrayList<Z3Node>();		
		this.ranges				= new ArrayList<Z3Node>();		
		this.boundedVars 	= new ArrayList<Z3Node>();		
		this.fields				= new ArrayList<Z3Node>();						
		this.isConst			= false;
		this.isFcn				= false;
		this.isVar				= false;		
		this.kind					= NoKind;
		this.setLevel 		= 0;
		this.dom					= null;
		this.cod					= null;
		this.isChangedName = false;
		this.isRewriten	  = false;
		this.isDotDot 		= false;		
	}
	
	public Z3Node(String name, int code, Z3Node sort, Z3Node elemSort, 
									int kind, int setLevel) {
		this.name 				= name;
		this.opCode 			= code;	
		this.subOpCode		= this.opCode;
		this.z3Sort 			= sort;		
		this.z3ElemSort		= elemSort;
		this.exprs		 		= new ArrayList<Z3Node>();
		this.operands 		= new ArrayList<Z3Node>();
		this.domains 			= new ArrayList<Z3Node>();		
		this.ranges				= new ArrayList<Z3Node>();		
		this.boundedVars 	= new ArrayList<Z3Node>();		
		this.fields				= new ArrayList<Z3Node>();						
		this.isConst			= false;
		this.isFcn				= false;
		this.isVar				= false;
		this.kind					= kind;
		this.setLevel 		= setLevel;
		this.dom					= null;
		this.cod					= null;
		this.isChangedName = false;
		this.isRewriten	  = false;
		this.isDotDot 		= false;		
		
		if (sort != null) {
			if (sort.kind != kind || sort.setLevel != setLevel) {
				Assert.fail(ConstraintErr, "There is a conflict between kind and sort of " + sort.name);
			}
			if (sort.opCode == OPCODE_fsort) {
				this.dom = sort.dom;
				this.cod = sort.cod;
				if (this.getDomainSize() == 0) {
					this.addDomain(sort.getDomain(0));
				}
				if (this.getRangeSize() == 0) {
					this.addRange(sort.getRange(0));
				}
			}
			else if (sort.opCode == OPCODE_rsort) {
				int alen = sort.getFieldSize();
				if (this.getFieldSize() == 0) {
					for (int i = 0; i < alen; i++) {
						this.addField(sort.getField(i).clone());
						this.addRange(sort.getRange(i));
					}
					this.addDomain(sort.getDomain(0).clone());	
				}					
			}
			else if (sort.opCode == OPCODE_tsort) {
				int alen = sort.getFieldSize();
				if (this.getFieldSize() == 0) {
					for (int i = 0; i < alen; i++) {
						this.addField(sort.getField(i).clone());
						this.addRange(sort.getRange(i));
					}
					this.addDomain(sort.getDomain(0).clone());	
				}					
			}
		}		
	}
	
	public Z3Node(String name, int code, Z3Node sort, Z3Node elemSort, 
									Z3Node op1, int kind, int setLevel) {
		this.name 				= name;
		this.opCode 			= code;	
		this.subOpCode		= this.opCode;
		this.z3Sort 			= sort;		
		this.z3ElemSort		= elemSort;
		this.exprs		 		= new ArrayList<Z3Node>();
		this.operands 		= new ArrayList<Z3Node>();
		this.domains 			= new ArrayList<Z3Node>();		
		this.ranges				= new ArrayList<Z3Node>();		
		this.boundedVars 	= new ArrayList<Z3Node>();		
		this.fields				= new ArrayList<Z3Node>();						
		this.isConst			= false;
		this.isFcn				= false;
		this.isVar				= false;		
		this.kind					= kind;
		this.setLevel 		= setLevel;
		this.dom					= null;
		this.cod					= null;
		
		this.operands.add(op1);
		this.isChangedName = false;
		this.isRewriten	  = false;
		this.isDotDot 		= false;		
		
		if (sort != null) {
			if (sort.kind != kind || sort.setLevel != setLevel) {
				Assert.fail(ConstraintErr, "There is a conflict between kind and sort of " + sort.name);
			}
			if (sort.opCode == OPCODE_fsort) {
				this.dom = sort.dom;
				this.cod = sort.cod;
				if (this.getDomainSize() == 0) {
					this.addDomain(sort.getDomain(0));
				}
				if (this.getRangeSize() == 0) {
					this.addRange(sort.getRange(0));
				}
			}
			else if (sort.opCode == OPCODE_rsort) {
				int alen = sort.getFieldSize();
				if (this.getFieldSize() == 0) {
					for (int i = 0; i < alen; i++) {
						this.addField(sort.getField(i).clone());
						this.addRange(sort.getRange(i));
					}
					this.addDomain(sort.getDomain(0).clone());	
				}					
			}
			else if (sort.opCode == OPCODE_tsort) {
				int alen = sort.getFieldSize();
				if (this.getFieldSize() == 0) {
					for (int i = 0; i < alen; i++) {
						this.addField(sort.getField(i).clone());
						this.addRange(sort.getRange(i));
					}
					this.addDomain(sort.getDomain(0).clone());	
				}					
			}
		}		
	}
	
	public Z3Node(String name, int code, Z3Node sort,	Z3Node elemSort, 
									Z3Node op1, Z3Node op2, int kind, int setLevel) {
		this.name 				= name;
		this.opCode 			= code;	
		this.subOpCode		= this.opCode;
		this.z3Sort 			= sort;		
		this.z3ElemSort		= elemSort;
		this.exprs		 		= new ArrayList<Z3Node>();
		this.operands 		= new ArrayList<Z3Node>();
		this.domains 			= new ArrayList<Z3Node>();		
		this.ranges				= new ArrayList<Z3Node>();		
		this.boundedVars 	= new ArrayList<Z3Node>();		
		this.fields				= new ArrayList<Z3Node>();						
		this.isConst			= false;
		this.isFcn				= false;
		this.isVar				= false;		
		this.kind					= kind;
		this.setLevel 		= setLevel;
		this.dom					= null;
		this.cod					= null;
		
		this.operands.add(op1);
		this.operands.add(op2);
		this.isChangedName = false;
		this.isRewriten	  = false;
		this.isDotDot 		= false;		
		
		if (sort != null) {
			if (sort.kind != kind || sort.setLevel != setLevel) {
				Assert.fail(ConstraintErr, "There is a conflict between kind and sort of " + sort.name);
			}
			if (sort.opCode == OPCODE_fsort) {
				this.dom = sort.dom;
				this.cod = sort.cod;
				if (this.getDomainSize() == 0) {
					this.addDomain(sort.getDomain(0));
				}
				if (this.getRangeSize() == 0) {
					this.addRange(sort.getRange(0));
				}
			}
			else if (sort.opCode == OPCODE_rsort) {
				int alen = sort.getFieldSize();
				if (this.getFieldSize() == 0) {
					for (int i = 0; i < alen; i++) {
						this.addField(sort.getField(i).clone());
						this.addRange(sort.getRange(i));
					}
					this.addDomain(sort.getDomain(0).clone());	
				}					
			}
			else if (sort.opCode == OPCODE_tsort) {
				int alen = sort.getFieldSize();
				if (this.getFieldSize() == 0) {
					for (int i = 0; i < alen; i++) {
						this.addField(sort.getField(i).clone());
						this.addRange(sort.getRange(i));
					}
					this.addDomain(sort.getDomain(0).clone());	
				}					
			}
		}		
	}
	
	public Z3Node(String name, int code, Z3Node sort,	Z3Node elemSort, 
									Z3Node op1, Z3Node op2, Z3Node op3, int kind, int setLevel) {
		this.name 				= name;
		this.opCode 			= code;	
		this.subOpCode		= this.opCode;
		this.z3Sort 			= sort;		
		this.z3ElemSort		= elemSort;
		this.exprs		 		= new ArrayList<Z3Node>();
		this.operands 		= new ArrayList<Z3Node>();
		this.domains 			= new ArrayList<Z3Node>();		
		this.ranges				= new ArrayList<Z3Node>();		
		this.boundedVars 	= new ArrayList<Z3Node>();		
		this.fields				= new ArrayList<Z3Node>();						
		this.isConst			= false;
		this.isFcn				= false;
		this.isVar				= false;		
		this.kind					= kind;
		this.setLevel 		= setLevel;
		this.dom					= null;
		this.cod					= null;
		
		this.operands.add(op1);
		this.operands.add(op2);
		this.operands.add(op3);
		this.isChangedName = false;
		this.isRewriten	  = false;
		this.isDotDot 		= false;		
		
		if (sort != null) {
			if (sort.kind != kind || sort.setLevel != setLevel) {
				Assert.fail(ConstraintErr, "There is a conflict between kind and sort of " + sort.name);
			}
			if (sort.opCode == OPCODE_fsort) {
				this.dom = sort.dom;
				this.cod = sort.cod;
				if (this.getDomainSize() == 0) {
					this.addDomain(sort.getDomain(0));
				}
				if (this.getRangeSize() == 0) {
					this.addRange(sort.getRange(0));
				}
			}
			else if (sort.opCode == OPCODE_rsort) {
				int alen = sort.getFieldSize();
				if (this.getFieldSize() == 0) {
					for (int i = 0; i < alen; i++) {
						this.addField(sort.getField(i).clone());
						this.addRange(sort.getRange(i));
					}
					this.addDomain(sort.getDomain(0).clone());	
				}					
			}
			else if (sort.opCode == OPCODE_tsort) {
				int alen = sort.getFieldSize();
				if (this.getFieldSize() == 0) {
					for (int i = 0; i < alen; i++) {
						this.addField(sort.getField(i).clone());
						this.addRange(sort.getRange(i));
					}
					this.addDomain(sort.getDomain(0).clone());	
				}					
			}
		}		
	}
	
	public Z3Node clone() {		
		Z3Node var 			= new Z3Node();
		var.name	 			= this.name;
		var.opCode	 		= this.opCode;	
		var.subOpCode		= this.opCode;
		var.z3Sort 			= this.z3Sort;			
		var.z3ElemSort	= this.z3ElemSort;
		var.isConst			= this.isConst;
		var.isFcn				= this.isFcn;
		var.isVar				= this.isVar;
		var.kind				= this.kind;
		var.setLevel 		= this.setLevel;
		var.dom					= this.dom;
		var.cod					= this.cod;
		var.isChangedName = this.isChangedName;
		var.isRewriten	= this.isRewriten;
		var.isDotDot		= this.isDotDot;		
		
		int i;
		for (i = 0; i < this.exprs.size(); i++) {
			var.exprs.add(this.exprs.get(i).clone());
		}
		for (i = 0; i < this.operands.size(); i++) {
			var.operands.add(this.operands.get(i).clone());
		}
		for (i = 0; i < this.domains.size(); i++) {
			var.domains.add(this.domains.get(i).clone());
		}			
		for (i = 0; i < this.ranges.size(); i++) {
			var.ranges.add(this.ranges.get(i).clone());
		}			
		for (i = 0; i < this.boundedVars.size(); i++) {
			var.boundedVars.add(this.boundedVars.get(i).clone());
		}				
		for (i = 0; i < this.fields.size(); i++) {
			var.fields.add(this.fields.get(i).clone());
		}						
		return var;
	}

	public void addExpr(Z3Node node) {
		this.exprs.add(node);
	}
		
	public Z3Node getExpr(int i) {
		return this.exprs.get(i);
	}	
	
	public void removeExpr(int i) {
		this.exprs.remove(i);
	}
	
	public void setExpr(int i, Z3Node node) {
		this.exprs.set(i, node);
	}
	
	public void clearExprs() {
		this.exprs.clear();
	}
	
	public int getExprSize() {
		return this.exprs.size();
	}
	
	public void addOperand(Z3Node node) {
		this.operands.add(node);
	}
	public Z3Node getOperand(int i) {
		return this.operands.get(i);
	}
	
	public void removeOperand(int i) {
		this.operands.remove(i);
	}
	
	public void setOperand(int i, Z3Node node) {
		this.operands.set(i, node);
	}
	
	public void clearOperands() {
		this.operands.clear();
	}
	
	public int getOperandSize() {
		return this.operands.size();
	}
	
	public void addDomain(Z3Node node) {
		this.domains.add(node);
	}
			
	public Z3Node getDomain(int i) {
		return this.domains.get(i);
	}
	
	public void removeDomain(int i) {
		this.domains.remove(i);
	}
	
	public void setDomain(int i, Z3Node node) {
		this.domains.set(i, node);
	}
	
	public void clearDomains() {
		this.domains.clear();
	}
	
	public int getDomainSize() {
		return this.domains.size();
	}
	
	public void addRange(Z3Node node) {
		this.ranges.add(node);
	}
	
	public Z3Node getRange(int i) {
		return this.ranges.get(i);
	}
	
	public void removeRange(int i) {
		this.ranges.remove(i);
	}
	
	public Z3Node setRange(int i, Z3Node node) {
		return this.ranges.set(i, node);
	}
	
	public void clearRanges() {
		this.ranges.clear();
	}
	
	public int getRangeSize() {
		return this.ranges.size();
	}
	
	public void addBoundedVar(Z3Node node) {
		this.boundedVars.add(node);
	}
	
	public Z3Node getBoundedVar(int i) {
		return this.boundedVars.get(i);
	}
	
	public void removeBoundedVar(int i) {
		this.boundedVars.remove(i);
	}
	
	public Z3Node setBoundedVar(int i, Z3Node node) {
		return this.boundedVars.set(i, node);
	}
	
	public void clearBoundedVars() {
		this.boundedVars.clear();
	}

	public int getBoundedVarSize() {
		return this.boundedVars.size();
	}
	
	public void addField(Z3Node node) {
		this.fields.add(node);
	}
	
	public Z3Node getField(int i) {
		return this.fields.get(i);
	}
	
	public void removeFields(int i) {
		this.fields.remove(i);
	}
	
	public Z3Node setField(int i, Z3Node node) {
		return this.fields.set(i, node);
	}
	
	public void clearFields() {
		this.fields.clear();
	}
	public int getFieldSize() {
		return this.fields.size();
	}

	public final void setSort(Z3Node sort) {
		if (sort != null) {
			if (this.z3Sort == null) {
				if (this.kind != NoKind && this.kind != sort.kind) {
					Assert.fail("There is a sort confliction in " + this.name + ": " + this.z3Sort.name + " " + sort + ".");
				}
				if (this.setLevel > sort.setLevel) {
					Assert.fail("There is a sort confliction in " + this.name + ": " + this.z3Sort.name + " " + sort + ".");
				}
				this.z3Sort = sort;
				if (sort.opCode == OPCODE_fsort) {
					this.dom = sort.dom;
					this.cod = sort.cod;
					if (this.getDomainSize() == 0) {
						this.addDomain(sort.getDomain(0));
					}
					if (this.getRangeSize() == 0) {
						this.addRange(sort.getRange(0));
					}
				}
				else if (sort.opCode == OPCODE_rsort) {
					int alen = sort.getFieldSize();
					if (this.getFieldSize() == 0) {
						for (int i = 0; i < alen; i++) {
							this.addField(sort.getField(i).clone());
							this.addRange(sort.getRange(i));
						}
						this.addDomain(sort.getDomain(0).clone());	
					}					
				}
				else if (sort.opCode == OPCODE_tsort) {
					int alen = sort.getFieldSize();
					if (this.getFieldSize() == 0) {
						for (int i = 0; i < alen; i++) {
							this.addField(sort.getField(i).clone());
							this.addRange(sort.getRange(i));
						}
						this.addDomain(sort.getDomain(0).clone());	
					}					
				}
				if (this.kind == NoKind) {
					this.kind = sort.kind;	
				}		
				else if  (this.kind != sort.kind) {
					Assert.fail(ConstraintErr, this.name + " does not have the same kind with " + sort.name + ".");
				}
				this.passSortInfo();				
				if (this.setLevel == iNull) {
					this.setLevel = sort.setLevel;
				}
				else if (this.setLevel != sort.setLevel) {
					Assert.fail(ConstraintErr, "Cannot set a set strata to " + this.name + ".");
				}						
			}
			else if (!this.z3Sort.name.equals(sort.name)) {
				Assert.fail("There is a sort confliction in " + this.name + ": " + this.z3Sort.name + " " + sort + ".");			
			}
		}		
	}
	
	public final void setSetNullSort(int setLevel) {
		this.z3Sort = null;
		if (this.setLevel == iNull) {
			this.setLevel = setLevel;	
		}
		else if (this.setLevel != setLevel){
			Assert.fail(ConstraintErr, "Cannot set a set strata to " + this.name + ".");
		}
	}
	
	public final void setNullSort() {
		this.z3Sort = null;
		this.setLevel = 0;
	}
	
	public final Z3Node getElemSort() {
		if (this.z3Sort != null) {
			return this.z3Sort.z3ElemSort;
		}
		if (this.z3ElemSort != null) {
			return this.z3ElemSort;
		}
		return null;
	}
	
	public final Z3Node getSort() {
		if (this.z3Sort != null) {
			return this.z3Sort;
		}
		switch (this.opCode) {
		case OPCODE_bsort:
		case OPCODE_fsort:
		case OPCODE_rsort:
		case OPCODE_tsort:
		case OPCODE_ssort:
		case OPCODE_sfsort:
		case OPCODE_srsort:
		case OPCODE_stsort: {
			return this;
		}			
		default: {
			return null;
		}
		}		
	}
	
	public final Z3Node dom() {
		if (this.getDomainSize() == 0) {
			Assert.fail(ConstraintErr, "No element in the domain of " + this.name);
		}
		return this.getDomain(0).getElemSort();
	}
	
	public final Z3Node cod() {
		if (this.getRangeSize() == 0) {
			Assert.fail(ConstraintErr, "No element in the range of " + this.name);
		}
		return this.getRange(0).getElemSort();
	}
	
	public final void passSortInfo() {
		switch (this.opCode) {
		case OPCODE_fc: {
			Z3Node sort = this.getSort();
			if (this.dom == null) {
				this.dom = sort.dom;
			}
			if (this.cod == null) {
				this.cod = sort.cod;
			}
			if (this.getExpr(0).getSort() == null) {
				this.getExpr(0).setSort(sort.getRange(0).getElemSort());
			}
			if (this.getDomain(0).getSort() == null) {
				this.getDomain(0).setSort(sort.getDomain(0).getSort());
			}
			if (this.getBoundedVar(0).getSort() == null) {
				this.getBoundedVar(0).setSort(sort.getDomain(0).getElemSort());
			}
			break;
		}
		case OPCODE_se: {
			int alen = this.getOperandSize();
			Z3Node elem = null,
					elemSort = this.getElemSort();
			for (int i = 0; i < alen; i++) {
				elem = this.getOperand(i);
				if (elem.getSort() == null) {
					elem.setSort(elemSort);
				}
			}
			break;
		}
		case OPCODE_sso: {
			Z3Node sort = this.getSort(),
					elemSort = this.getElemSort(),
					y = this.getBoundedVar(0),
					S = this.getDomain(0);
			if (y.getSort() == null) {
				y.setSort(elemSort);
			}
			if (S.getSort() == null) {
				S.setSort(sort);
			}
			
			break;
		}
		case OPCODE_soa: {
			Z3Node elemSort = this.getElemSort(),
					e = this.getExpr(0);
			if (e.getSort() == null) {
				e.setSort(elemSort);
			}
			break;
		}
		case OPCODE_subset: {
			Z3Node elemSort = this.getElemSort(),
					op = this.getOperand(0);
			if (op.getSort() == null) {
				op.setSort(elemSort);
			}
			break;
		}
		case OPCODE_union: {
			Z3Node sort = this.getSort(),
					op = this.getOperand(0);
			if (op.getSort() == null) {
				op.setSort(sort);
			}
			break;
		}
		case OPCODE_cap: {
			Z3Node S = this.getOperand(0),
					T = this.getOperand(1),
					sort = this.getSort();
			if (S.getSort() == null) {
				S.setSort(sort);
			}
			if (T.getSort() == null) {
				T.setSort(sort);
			}
			break;
		}
		case OPCODE_cup: {
			Z3Node S = this.getOperand(0),
					T = this.getOperand(1),
					sort = this.getSort();
			if (S.getSort() == null) {
				S.setSort(sort);
			}
			if (T.getSort() == null) {
				T.setSort(sort);
			}
			break;
		}
		case OPCODE_setdiff: {
			Z3Node S = this.getOperand(0),
					T = this.getOperand(1),
					sort = this.getSort();
			if (S.getSort() == null) {
				S.setSort(sort);
			}
			if (T.getSort() == null) {
				T.setSort(sort);
			}
			break;
		}
		}
	}
	
	public final Z3Node findRange(Z3Node field) {
		String fname = field.name;
		int alen = this.getFieldSize();
		for (int i = 0; i < alen; i++) {
			if (fname.equals(this.getField(i).name)) {
				return this.getRange(i);				
			}
		}
		return null;
	}
	
//	public final void setElemSort(Z3Node sort) {
//		if (sort != null) {
//			if (this.z3ElemSort == null) {
//				this.z3ElemSort = sort;
//			}
//			else if (!this.z3ElemSort.name.equals(sort.name)) {
//				Assert.fail("There is a elements' sort confliction in " + this.name + ": " + this.z3Sort + " " + sort + ".");			
//			}
//		}		
//	}

	public final boolean isSyntacticEqual(Z3Node var) {
		if (this == var) {
			return true;
		}
		if (var.opCode != this.opCode 			|| !(var.name.equals(this.name)) 	||
				var.subOpCode != this.subOpCode || this.z3Sort != var.z3Sort 			||
				var.isFcn	!= this.isFcn 				|| var.kind != this.kind 					||
				var.dom	!= this.dom 						|| var.cod != this.cod) {
			return false;
		}				
		
		int i;
		
		if (this.getExprSize() != var.getExprSize()) 
			return false;		
		for (i = 0; i < this.exprs.size(); i++) {
			if (!var.exprs.get(i).isSyntacticEqual(this.exprs.get(i)))
				return false;
		}
		
		if (this.getOperandSize() != var.getOperandSize()) 
			return false;		
		for (i = 0; i < this.operands.size(); i++) {
			if (!var.operands.get(i).isSyntacticEqual(this.operands.get(i))) 
				return false;
		}
		
		if (this.getDomainSize() != var.getDomainSize()) 
			return false;		
		for (i = 0; i < this.domains.size(); i++) {
			if (!var.domains.get(i).isSyntacticEqual(this.domains.get(i)))
				return false;
		}			
		
		if (this.getRangeSize() != var.getRangeSize()) 
			return false;
		for (i = 0; i < this.ranges.size(); i++) {
			if (!var.ranges.get(i).isSyntacticEqual(this.ranges.get(i))) 
				return false;
		}			
		
		if (this.getBoundedVarSize() != var.getBoundedVarSize()) 
			return false;
		for (i = 0; i < this.boundedVars.size(); i++) {
			if (!var.boundedVars.get(i).isSyntacticEqual(this.boundedVars.get(i)))
				return false;
		}				
		
		if (this.getFieldSize() != var.getFieldSize())
			return false;
		for (i = 0; i < this.fields.size(); i++) {
			if (!var.fields.get(i).isSyntacticEqual(this.fields.get(i)))
				return false;
		}						
		
		return true;
	}
	
}