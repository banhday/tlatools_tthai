
package z3parser;

import util.Assert;

import java.util.ArrayList;

public class Z3Tool implements Z3Constants, Z3ErrorCode {
	private Z3Encoder z3Encoder;	
	private int taskID;
	private ConstraintChecker checker;	
	private Rewriter rewriter;
	
	private Z3Tool() {
		this.z3Encoder = null;
	}
	
	public Z3Tool(Z3Encoder encoder)	{
		this.z3Encoder = encoder;		
		this.taskID = NoTask;
		this.checker = new ConstraintChecker(encoder);
		this.rewriter = new Rewriter(this.z3Encoder, this.checker, this);
	}
	
	private static int xIndex = 0;
	
	private static int sortIndex = 1;
	
	// There are five tasks: TypeOK, Init, Next, Inv and Pred
	public void setTaskID(int taskID) {
		this.taskID = taskID;
	}
	
	private String createSortName(String pre) {
		return pre + "_sort_" + Integer.toString(sortIndex++);
	}
	
	public Z3Node createSetSort(Z3Node elemSort, int opCode) {
		String sortName = "Set_" + elemSort.name;
		Z3Node newSort = new Z3Node(sortName, OPCODE_ssort, null, elemSort, 
													tla_set, elemSort.setLevel + 1);
		newSort.opCode = opCode;		
		this.z3Encoder.addSort(newSort);
		return newSort;
	}
	
	public  Z3Node createSort_fc(Z3Node node) {
		if (node.opCode != OPCODE_fc) {
			return null;
		}
		String sortName = this.createSortName("fcn");
		Z3Node sort = new Z3Node(sortName, OPCODE_fsort, null, null, tla_fcn, NoSet),
				domain = node.getDomain(0).getSort(),
				range = this.z3Encoder.getSort_ssort_elem(node.getExpr(0).getSort());
		sort.addDomain(domain);
		sort.addRange(range);		
		sort.dom = domain.getElemSort();
		sort.cod = range.getElemSort();
		this.z3Encoder.addSort(sort);
		return sort;
	}
	
	public  Z3Node createSort_fsort_sof(Z3Node node) {
		if (node.opCode != OPCODE_sof) {
			return null;
		}
		String sortName = this.createSortName("fcn");
		Z3Node sort = new Z3Node(sortName, OPCODE_fsort, null, null, tla_fcn, NoSet);
		sort.addDomain(node.getDomain(0).getSort());		
		sort.addRange(node.getRange(0).getSort());
		sort.dom = node.getDomain(0).getElemSort();
		sort.cod = node.getRange(0).getElemSort();
		this.z3Encoder.addSort(sort);
		return sort;
	}
	
	public  Z3Node createSort_sof(Z3Node node) {
		if (node.opCode != OPCODE_sof) {
			return null;
		}		
		Z3Node elemSort = this.z3Encoder.getSort_fsort_sof(node),
				sort = this.createSetSort(elemSort, OPCODE_sfsort);		
		this.z3Encoder.addSort(sort);
		return sort;
	}			
	
	// node's opCode == OPCODE_tup
	public Z3Node createSort_tup(Z3Node node) {
		if (node.opCode != OPCODE_tup) {
			return null;
		}
		String sortName = this.createSortName("tup");
		Z3Node sort = new Z3Node(sortName, OPCODE_tsort, null, null, tla_tup, NoSet),
				intSort = this.z3Encoder.intSort,
				setIntSort = this.z3Encoder.setIntSort,
				dom = new Z3Node("dom" + sortName, OPCODE_se, setIntSort, intSort, tla_set, 1);
		int alen = node.getOperandSize();
		for (int i = 0; i < alen; i++) {
			String fieldName = Integer.toString(i + 1);
			Z3Node field = new Z3Node(fieldName, OPCODE_const, intSort, null, tla_atom, NoSet),					
					rangeSort = node.getOperand(i).getSort();			
			dom.addOperand(field);
			sort.addField(field);
			sort.addRange(rangeSort);					
		}
		sort.addDomain(dom);			
		this.z3Encoder.addSort(sort);
		return sort;		
	}
	
	public Z3Node createSort_tsort_cp(Z3Node node) {
		String sortName = this.createSortName("tup");
		Z3Node sort = new Z3Node(sortName, OPCODE_tsort, null, null, tla_tup, NoSet),
				intSort = this.z3Encoder.intSort,
				setIntSort = this.z3Encoder.setIntSort,
				dom = new Z3Node("dom" + sortName, OPCODE_se, setIntSort, intSort, tla_set, 1);
		int alen = node.getOperandSize();
		for (int i = 0; i < alen; i++) {
			String fieldName = Integer.toString(i + 1);
			Z3Node field = new Z3Node(fieldName, OPCODE_const, intSort, null, tla_atom, NoSet),
					rangeSort = node.getOperand(i).getElemSort();
			dom.addOperand(field);
			sort.addField(field);
			sort.addRange(rangeSort);					
		}
		sort.addDomain(dom);		
		this.z3Encoder.addSort(sort);
		return sort;
	}
	
	// node's opCode == OPCODE_cp
	public Z3Node createSort_cp(Z3Node node) {
		if (node.opCode != OPCODE_cp) {
			return null;
		}
		Z3Node elemSort = this.z3Encoder.getSort_tsort_cp(node),
		 		sort = this.createSetSort(elemSort, OPCODE_stsort);		 		
		int alen = elemSort.getRangeSize();
		for (int i = 0; i < alen; i++) {	
			sort.addField(elemSort.getField(i));
			sort.addRange(elemSort.getRange(i));
		}
		sort.addDomain(elemSort.getDomain(0));
		return sort;
	}		
	
	// node's opCode == OPCODE_rc
	public Z3Node createSort_rc(Z3Node node) {
		if (node.opCode != OPCODE_rc) {
			return null;
		}
		String sortName = this.createSortName("rcd");
		Z3Node sort = new Z3Node(sortName, OPCODE_rsort, null, null, tla_rcd, NoSet),
				strSort = this.z3Encoder.strSort,
				setStrSort = this.z3Encoder.setStrSort,
				dom = new Z3Node("dom" + sortName, OPCODE_se, setStrSort, strSort, tla_set, 1);
		int alen = node.getFieldSize();
		for (int i = 0; i < alen; i++) {			
			Z3Node field = node.getField(i),
					expr = node.getExpr(i),
					rangeSort = expr.getSort();
			dom.addOperand(field);
			sort.addField(field);
			sort.addRange(rangeSort);					
		}
		sort.addDomain(dom);		
		this.z3Encoder.addSort(sort);
		return sort;
	}		
	
	// node's opCode == OPCODE_rc
	public Z3Node createSort_rsort_sor(Z3Node node) {
		if (node.opCode != OPCODE_sor) {
			return null;
		}
		String sortName = this.createSortName("rcd");
		Z3Node sort = new Z3Node(sortName, OPCODE_rsort, null, null, tla_rcd, NoSet),
				strSort = this.z3Encoder.strSort,
				setStrSort = this.z3Encoder.setStrSort,
				dom = new Z3Node("dom" + sortName, OPCODE_se, setStrSort, strSort, tla_set, 1);
		int alen = node.getFieldSize();
		for (int i = 0; i < alen; i++) {			
			Z3Node field = node.getField(i),					
					rangeSort = node.getRange(i).getElemSort();
			dom.addOperand(field);
			sort.addField(field);
			sort.addRange(rangeSort);					
		}
		sort.addDomain(dom);		
		this.z3Encoder.addSort(sort);
		return sort;
	}		
		
	// node's opCode == OPCODE_sor
	public Z3Node createSort_sor(Z3Node node) {
		if (node.opCode != OPCODE_sor) {
			return null;
		}		
		Z3Node elemSort = this.z3Encoder.getSort_rsort_sor(node),
				sort = this.createSetSort(elemSort, OPCODE_srsort);
		int alen = elemSort.getRangeSize();
		for (int i = 0; i < alen; i++) {			
			sort.addField(elemSort.getField(i));
			sort.addRange(elemSort.getRange(i));
		}
		sort.addDomain(elemSort.getDomain(0));
		return sort;
	}
			
	public final void createDefaultSortList() {
		this.z3Encoder.boolSort = new Z3Node(Bool, OPCODE_bsort, null, null, tla_atom, NoSet);				
		this.z3Encoder.intSort 	= new Z3Node(Int, OPCODE_bsort, null, null, tla_atom, NoSet);				
		this.z3Encoder.strSort 	= new Z3Node(Str, OPCODE_bsort, null, null, tla_atom, NoSet);								
		this.z3Encoder.addSort(this.z3Encoder.boolSort);		
		this.z3Encoder.addSort(this.z3Encoder.intSort);
		this.z3Encoder.addSort(this.z3Encoder.strSort);
		this.z3Encoder.setBoolSort = this.createSetSort(this.z3Encoder.boolSort, OPCODE_ssort);
		this.z3Encoder.setIntSort  = this.createSetSort(this.z3Encoder.intSort, OPCODE_ssort);
		this.z3Encoder.setStrSort	 = this.createSetSort(this.z3Encoder.strSort, OPCODE_ssort);
	}		
		
	public String getSortsDeclartion() {
		String res = "(declare-sort U) \n (declare-sort Str) \n";
		return res;
	}
	
	public static String getVarsDeclaration(Z3Node[] varList) {
		int alen = varList.length;
		String res = "", tmp = "";
		for (int i = 0; i < alen; i++) {
			tmp = " (declare-func " + varList[i].name + " " + varList[i].getSort().name + ")\n";
			res = res + tmp;
		}
		return res;
	}
	
	public final Z3Node makeNextInv(Z3Node curNode) {
		if (curNode != null) {
			if (curNode.opCode == OPCODE_pred) {
				curNode.name = "p_" + curNode.name;
				return curNode;
			}
			else {
				int i;
				for (i = 0; i < curNode.getExprSize(); i++) {
					curNode.setExpr(i, this.makeNextInv(curNode.getExpr(i)));					
				}
				for (i = 0; i < curNode.getOperandSize(); i++) {
					curNode.setOperand(i, this.makeNextInv(curNode.getOperand(i)));					
				}
				for (i = 0; i < curNode.getDomainSize(); i++) {
					curNode.setDomain(i, this.makeNextInv(curNode.getDomain(i)));					
				}
				for (i = 0; i < curNode.getRangeSize(); i++) {
					curNode.setRange(i, this.makeNextInv(curNode.getRange(i)));					
				}				
				for (i = 0; i < curNode.getBoundedVarSize(); i++) {
					curNode.setBoundedVar(i, this.makeNextInv(curNode.getBoundedVar(i)));					
				}
				for (i = 0; i < curNode.getFieldSize(); i++) {
					curNode.setField(i, this.makeNextInv(curNode.getField(i)));					
				}					
				return curNode;
			}
		}
		return null;
	}
	
	public final Z3Node fromZ3toNUSVM(Z3Node curNode) {
		if (curNode != null) {
			if (curNode.opCode == OPCODE_pred && curNode.name.indexOf("p_") == 0) {
				int length = curNode.name.length();
				curNode.name = "next(" + curNode.name.substring(2, length) + ")";
				return curNode;
			}
			else {
				int i;
				for (i = 0; i < curNode.getExprSize(); i++) {
					curNode.setExpr(i, this.fromZ3toNUSVM(curNode.getExpr(i)));					
				}
				for (i = 0; i < curNode.getOperandSize(); i++) {
					curNode.setOperand(i, this.fromZ3toNUSVM(curNode.getOperand(i)));					
				}
				for (i = 0; i < curNode.getDomainSize(); i++) {
					curNode.setDomain(i, this.fromZ3toNUSVM(curNode.getDomain(i)));					
				}
				for (i = 0; i < curNode.getRangeSize(); i++) {
					curNode.setRange(i, this.fromZ3toNUSVM(curNode.getRange(i)));					
				}				
				for (i = 0; i < curNode.getBoundedVarSize(); i++) {
					curNode.setBoundedVar(i, this.fromZ3toNUSVM(curNode.getBoundedVar(i)));					
				}
				for (i = 0; i < curNode.getFieldSize(); i++) {
					curNode.setField(i, this.fromZ3toNUSVM(curNode.getField(i)));					
				}					
				return curNode;
			}
		}
		return null;
	}
	
	public final Z3Node replaceNode(String name, Z3Node curNode, Z3Node newNode) {
		if (curNode != null) {
			if (curNode.name.equals(name)) {
				return newNode.clone();
			}
			else {
				int i;
				for (i = 0; i < curNode.getExprSize(); i++) {
					curNode.setExpr(i, this.replaceNode(name, curNode.getExpr(i), newNode));					
				}
				for (i = 0; i < curNode.getOperandSize(); i++) {
					curNode.setOperand(i, this.replaceNode(name, curNode.getOperand(i), newNode));					
				}
				for (i = 0; i < curNode.getDomainSize(); i++) {
					curNode.setDomain(i, this.replaceNode(name, curNode.getDomain(i), newNode));					
				}
				for (i = 0; i < curNode.getRangeSize(); i++) {
					curNode.setRange(i, this.replaceNode(name, curNode.getRange(i), newNode));					
				}				
				for (i = 0; i < curNode.getBoundedVarSize(); i++) {
					curNode.setBoundedVar(i, this.replaceNode(name, curNode.getBoundedVar(i), newNode));					
				}
				for (i = 0; i < curNode.getFieldSize(); i++) {
					curNode.setField(i, this.replaceNode(name, curNode.getField(i), newNode));					
				}					
				return curNode;
			}
		}
		return null;
	}
	
	public final Z3Node createBoundedVar() {
		String name = "x_" + Integer.toString(xIndex++);		
		return new Z3Node(name, OPCODE_bv, null, null, NoKind, iNull);
	}	
	
	
	private final String makeDomainDeclaration(Z3Node sort) {
		return "(declare-fun domain_" + sort.name + " (" + sort.name + ") " + sort.getDomain(0).getSort().name + ")\n";		
	}
	
	private final String makeAlphaDeclaration(Z3Node sort) {
		return "(declare-fun alpha_" + sort.name + " (" + sort.name + " " + sort.dom.name + ") " + sort.cod.name + ")\n";		
	}
	
	private final String makeInDeclaration(Z3Node sort) {
		return "(declare-fun in_" + sort.name + " (" + sort.getElemSort().name + " " + sort.name + ") Bool)\n";		
	}
	
	public final String makeFunctionsDeclaration(Z3Node sort) {
		String res = "";
		switch (sort.opCode) {
		case OPCODE_fsort: {
			res = res + this.makeDomainDeclaration(sort);
			res = res + this.makeAlphaDeclaration(sort);
			break;
		}
		case OPCODE_rsort:
		case OPCODE_tsort: {
			res = res + this.makeDomainDeclaration(sort);			
			break;
		}
		case OPCODE_ssort:
		case OPCODE_sfsort:
		case OPCODE_srsort: 
		case OPCODE_stsort: {
			res = res + this.makeInDeclaration(sort);
			res = res + this.makeEmptySetDeclaration(sort);
			break;
		}
		default: {
			break;
		}
		}
		return res;
	}
	
	public final String makeSetExtensionality(Z3Node sort) {
		Z3Node set_f = this.createBoundedVar(),
				set_g = this.createBoundedVar(),
				elemSort = sort.getElemSort(),
				id_x = this.createBoundedVar();
		id_x.setSort(elemSort.getSort());
		set_f.setSort(sort);
		set_g.setSort(sort);
		Z3Node inF	= new Z3Node("in_" + sort.name, OPCODE_in, this.z3Encoder.boolSort, null, id_x, set_f, tla_atom, NoSet),
				inG = new Z3Node("in_" + sort.name, OPCODE_in, this.z3Encoder.boolSort, null, id_x, set_g, tla_atom, NoSet),
				eqIn = new Z3Node("=", OPCODE_eq, this.z3Encoder.boolSort, null, inF, inG, tla_atom, NoSet),
				bf0 = new Z3Node("forall", OPCODE_bf, this.z3Encoder.boolSort, null, tla_atom, NoSet),
				eqSet = new Z3Node("=", OPCODE_eq, this.z3Encoder.boolSort, null, set_f, set_g, tla_atom, NoSet),
				body = new Z3Node("=>", OPCODE_implies, this.z3Encoder.boolSort, null, bf0, eqSet, tla_atom, NoSet),
				bf1 = new Z3Node("forall", OPCODE_bf, this.z3Encoder.boolSort, null, tla_atom, NoSet),
				assertion = new Z3Node("assert", OPCODE_assert, this.z3Encoder.boolSort, null, bf1, tla_atom, NoSet);
		bf0.addBoundedVar(id_x);
		bf0.addDomain(elemSort);
		bf0.addExpr(eqIn);
		bf1.addBoundedVar(set_f);
		bf1.addDomain(sort);
		bf1.addBoundedVar(set_g);
		bf1.addDomain(sort);
		bf1.addExpr(body);
		this.rewriter.rename(assertion);
		this.z3Encoder.addAxiom(assertion);
		String res = this.printZ3Node(assertion, "") + "\n";
		return res;
	}
	
	private final String makeFunctionExtensionality(Z3Node sort) {
//		"(assert (forall ((fcn_f " + sort.name + ") (fcn_g " + sort.name + ")) (=> (and "+ 
//				"(forall ((id_x " + sort.dom.name + ")) (= (alpha_" + sort.name + " fcn_f id_x)  (alpha_" + sort.name + " fcn_g id_x))) " +
//				"(= (domain_" + sort.name + " fcn_f) (domain_" + sort.name + " fcn_g))) (= fcn_f fcn_g)))) \n";
		Z3Node fcn_f = this.createBoundedVar(),
				fcn_g = this.createBoundedVar(),				
				dom = sort.dom,
				cod = sort.cod,
				id_x = this.createBoundedVar();
		id_x.setSort(dom.getSort());
		fcn_f.setSort(sort);
		fcn_g.setSort(sort);
		Z3Node alphaF	= new Z3Node("alpha_" + sort.name, OPCODE_alpha, this.z3Encoder.boolSort, null, fcn_f, id_x, tla_atom, NoSet),
				alphaG = new Z3Node("alpha_" + sort.name, OPCODE_alpha, this.z3Encoder.boolSort, null, fcn_g, id_x, tla_atom, NoSet),
				domSort = this.z3Encoder.getSort_ssort_elem(dom),
				domF = new Z3Node("domain_" + sort.name, OPCODE_domain, domSort, null, fcn_f, domSort.kind, domSort.setLevel),
				domG = new Z3Node("domain_" + sort.name, OPCODE_domain, domSort, null, fcn_g, domSort.kind, domSort.setLevel),
				eqDom = new Z3Node("=", OPCODE_eq, this.z3Encoder.boolSort, null, domF, domG, tla_atom, NoSet),								
				inDom = new Z3Node("in_" + domSort.name, OPCODE_in, this.z3Encoder.boolSort, null, id_x, domF, tla_atom, NoSet),
				eqAlpha = new Z3Node("=", OPCODE_eq, this.z3Encoder.boolSort, null, alphaF, alphaG, tla_atom, NoSet),
				body0 = new Z3Node("=>", OPCODE_implies, this.z3Encoder.boolSort, null, inDom, eqAlpha, tla_atom, NoSet),
				bf0 = new Z3Node("forall", OPCODE_bf, this.z3Encoder.boolSort, null, tla_atom, NoSet),
				andNode = new Z3Node("and", OPCODE_land, this.z3Encoder.boolSort, null, eqDom, bf0, tla_atom, NoSet),
				eqFcn = new Z3Node("=", OPCODE_eq, this.z3Encoder.boolSort, null, fcn_f, fcn_g, tla_atom, NoSet),
				body1 = new Z3Node("=>", OPCODE_implies, this.z3Encoder.boolSort, null, andNode, eqFcn, tla_atom, NoSet),
				bf1 = new Z3Node("forall", OPCODE_bf, this.z3Encoder.boolSort, null, tla_atom, NoSet),
				assertion = new Z3Node("assert", OPCODE_assert, this.z3Encoder.boolSort, null, bf1, tla_atom, NoSet);
		bf0.addBoundedVar(id_x);
		bf0.addDomain(dom);
		bf0.addExpr(body0);
		bf1.addBoundedVar(fcn_f);
		bf1.addDomain(sort);
		bf1.addBoundedVar(fcn_g);
		bf1.addDomain(sort);
		bf1.addExpr(body1);
		this.rewriter.rename(assertion);
		this.z3Encoder.addAxiom(assertion);
		String res = this.printZ3Node(assertion, "") + "\n";
		return res;
	}
	
	public final String makeExtensionality(Z3Node sort) {
		String res = "";
		switch (sort.opCode) {
		case OPCODE_fsort: {
			res = this.makeFunctionExtensionality(sort);
			break;
		}		
		case OPCODE_ssort:
		case OPCODE_sfsort:
		case OPCODE_srsort: 
		case OPCODE_stsort: {
			res = this.makeSetExtensionality(sort);
			break;
		}
		default: {
			break;
		}
		}
		return res;
	}
	
	public final String makeStringConstraint(ArrayList<Z3Node> strList) {
		String res = "\n", tmp;
		int alen = strList.size();
		for (int i = 0; i < alen - 1; i++)
			for (int j = i + 1; j < alen; j++) {
					tmp = "(assert (not (= " + strList.get(i).name + " " + strList.get(j).name + ")))\n";
					res = res + tmp;
			}		
		return res + "\n";		
	}
	
	public final String makeEmptySetDeclaration(Z3Node sort) {				
		Z3Node elemSort = sort.getElemSort(),
				x = this.createBoundedVar(),
				bottom = new Z3Node("false", OPCODE_false, this.z3Encoder.boolSort, null, tla_atom, NoSet),
				emptySet = new Z3Node("empty_" + sort.name, OPCODE_const, sort, null, sort.kind, sort.setLevel),
				inEmpty = new Z3Node("in_" + sort.name, OPCODE_in, this.z3Encoder.boolSort, null, x, emptySet, tla_atom, NoSet),				
				body = new Z3Node("=", OPCODE_eq, this.z3Encoder.boolSort, null, inEmpty, bottom, tla_atom, NoSet),
				frm = new Z3Node("forall", OPCODE_bf, this.z3Encoder.boolSort, null, tla_atom, NoSet),
				assertion = new Z3Node("assert", OPCODE_assert, this.z3Encoder.boolSort, null, frm, tla_atom, NoSet);
		x.setSort(elemSort);
		frm.addBoundedVar(x);
		frm.addDomain(elemSort);
		frm.addExpr(body);
		this.rewriter.rename(assertion);
		this.z3Encoder.addFreshVar(emptySet);
		this.z3Encoder.addFreshAssertion(assertion);
		return "";
	}
	
	public final String printZ3Node(Z3Node node, String spaces) {
		String result = "", newspaces = this.getSpaces(node) + spaces;
		if (node != null) {
			switch (node.opCode) {
			case OPCODE_bv:
			case OPCODE_var:
			case OPCODE_const: 
			case OPCODE_true: 
			case OPCODE_false: {
				result = spaces + node.name;
				break;
			}
			case OPCODE_be: {
				String body = this.printZ3Node(node.getExpr(0), newspaces),
						bvars = "(" + node.getBoundedVar(0).name + " " +
								node.getDomain(0).name + ")";
				for (int i = 1; i < node.getBoundedVarSize(); i++) {
					bvars = bvars + " (" + node.getBoundedVar(i).name + " " +
							node.getDomain(i).name + ")";
				}
				result = spaces + "(exists (" + bvars + ")\n" + body + ")";
				break;
			}
			case OPCODE_bf: {
				String body = this.printZ3Node(node.getExpr(0), newspaces),
						bvars = "(" + node.getBoundedVar(0).name + " " +
								node.getDomain(0).name + ")";
				for (int i = 1; i < node.getBoundedVarSize(); i++) {
					bvars = bvars + " (" + node.getBoundedVar(i).name + " " +
							node.getDomain(i).name + ")";
				}
				result = spaces + "(forall (" + bvars + ")\n" + body + ")";
				break;
			}
			case OPCODE_trsl: 
			case OPCODE_rs: {
				String tmp =  this.printZ3Node(node.getOperand(1), newspaces) + "\n" + this.printZ3Node(node.getOperand(0), newspaces);
				tmp = tmp.substring(newspaces.length());
				if (tmp.length() > 1 && tmp.charAt(tmp.length() - 1) == '\n') {
					tmp = tmp.substring(0, tmp.length() - 1);
				}
				result = spaces +  "( " + tmp + ")";
				break;
			}
			default: {
				int alen = node.getOperandSize(); 
				result = spaces + "(" + node.name + " ";
				String tmp = "";
				if (alen > 0 && node.opCode != OPCODE_se) {
					for (int i = 0; i < alen - 1; i++) {
						tmp = tmp + this.printZ3Node(node.getOperand(i), newspaces) + "\n";
					}
					tmp = tmp + this.printZ3Node(node.getOperand(alen - 1), newspaces);
					tmp = tmp.substring(newspaces.length());
					result = result + tmp + ")";
				}
				else if (alen == 0 || node.opCode == OPCODE_se) {
					result = spaces + node.name;
				}				
				break;
			}
			}
		}		
		return result;
	}
	
	private final String getSpaces(Z3Node node) {		
		String res = "";
		for (int i = 0; i < node.name.length() + 2; i++) {
			res += " ";
		}
		return res;
	}	
	
	public final Z3Node createGlobalConst() {
		String name = "x_" + Integer.toString(xIndex++);		
		return new Z3Node(name, OPCODE_const, null, null, NoKind, iNull);
	}	
	
	public String makeVarDeclaration(Z3Node var) {
		if (var != null) {
			String res = "(declare-const " + var.name + " " + var.getSort().name + ")\n";
			return res;
		}
		else {
			return NoCommand;
		}
	}
	
	public String makeFcnDeclaration(Z3Node fcn) {
		if (fcn != null) {
			String argSorts = "( ";
			int alen = fcn.getDomainSize();
			for (int i = 0; i < alen - 1; i++) {
				argSorts = argSorts + fcn.getDomain(i).name + " ";
			}
			argSorts = argSorts + ")";
			String rangeSort = fcn.getDomain(alen - 1).name;
			String res = "(declare-fun " + fcn.name + " " + argSorts + " " + rangeSort + ")\n";
			return res;
		}
		else {
			return NoCommand;
		}		
	}

	public String makeSortDeclaration(Z3Node sort) {
		switch (sort.opCode) {		
		case OPCODE_rsort:
		case OPCODE_tsort: {
			String res = "(declare-datatypes () ((" + sort.name + " (mk-pair",
					tmp;
			int alen = sort.getFieldSize();
			for (int i = 0; i < alen; i++) {
				tmp = " (z3f_" + sort.getField(i).name + " " + sort.getRange(i).name + ")";
				res = res + tmp;
			}
			res = res + "))))\n";
			return res;
		}			
		default: {
			String res = "(declare-sort " + sort.name + ")\n";
			return res;
		}
		}
	}
	
	public String makeAssertion(String assertion) {
		if (!assertion.equals(NoCommand)) {
			String res = "(assert " + assertion + ")\n";
			return res;
		}
		else {
			return NoCommand;
		}
	}
	
	public final Z3Node createZ3EqNode(Z3Node var1, Z3Node var2) {
		Z3Node sort1 = var1.getSort(),  
				sort2 = var2.getSort();
		var1.setSort(sort2);		
		var2.setSort(sort1);		
		return new Z3Node("=", OPCODE_eq, this.z3Encoder.boolSort, null, var1, var2, tla_atom, NoSet);				
	}

	public final Z3Node createZ3InNode(Z3Node var1, Z3Node var2) {
		Z3Node elemSort2 = var2.getElemSort();
		var1.setSort(elemSort2);		
		return new Z3Node(var1.getElemSort().name + "_in", OPCODE_in, this.z3Encoder.boolSort, null, var1, var2, tla_atom, NoSet);						
	}
	
	public final Z3Node makeExtensionality(Z3Node var1, Z3Node var2) {
		if (var1.getElemSort().name.equals(var2.getElemSort().name)) {
			if (var1.kind != var2.kind) {
				Z3Node eq = this.createZ3EqNode(var1, var2),
						neq = new Z3Node("not", OPCODE_lnot, this.z3Encoder.boolSort, null, eq, tla_atom, NoSet);
				return neq;
			}
			else {
				if (var1.kind == NoKind) {
					Z3Node x = this.createBoundedVar(),
							sort = this.z3Encoder.getSort(var1.getElemSort()),
							inVar1 = new Z3Node(var1.getElemSort().name + "_in", OPCODE_in, this.z3Encoder.boolSort, null, x, var1, tla_atom, NoSet),
							inVar2 = new Z3Node(var2.getElemSort().name + "_in", OPCODE_in, this.z3Encoder.boolSort, null, x, var2, tla_atom, NoSet);
					inVar1 = this.rewriter.rewrite(inVar1);
					inVar2 = this.rewriter.rewrite(inVar2);
					Z3Node eqIn = this.createZ3EqNode(inVar1, inVar2),
							bfFrm = new Z3Node("forall", OPCODE_bf, this.z3Encoder.boolSort, null, tla_atom, NoSet),
							eqVar = this.createZ3EqNode(var1, var2);
					bfFrm.addBoundedVar(x);
					bfFrm.addDomain(sort);
					bfFrm.addExpr(eqIn);
					Z3Node res = this.createZ3EqNode(bfFrm, eqVar);
					return res;
				}
				else if (var1.kind == tla_fcn) {
					Z3Node dom1 = var1.getDomain(0), dom2 = var2.getDomain(0),
							range1 = var1.getRange(0), range2 = var2.getRange(0);
					if (dom1.getElemSort().name.equals(dom2.getElemSort().name) && 
							range1.getElemSort().name.equals(range2.getElemSort().name)) {
						Z3Node IsAFcn1 = new Z3Node("IsAFcn", OPCODE_IsAFcn, this.z3Encoder.boolSort, null, var1, tla_atom, NoSet),
								IsAFcn2 = new Z3Node("IsAFcn", OPCODE_IsAFcn, this.z3Encoder.boolSort, null, var2, tla_atom, NoSet),
								domain1 = new Z3Node("domain", OPCODE_domain, null, null, var1, tla_set, 1),
								domVar1	= domain1,
								domain2 = new Z3Node("domain", OPCODE_domain, null, null, var2, tla_set, 1);
						IsAFcn1 = this.rewriter.rewrite(IsAFcn1);
						IsAFcn2 = this.rewriter.rewrite(IsAFcn2);
						domain1 = this.rewriter.rewrite(domain1);
						domain2 = this.rewriter.rewrite(domain2);
						Z3Node eqDo = this.createZ3EqNode(domain1, domain2);
						eqDo = this.rewriter.rewrite(eqDo);
						Z3Node x = this.createBoundedVar(),
								sort = this.z3Encoder.getSort(var1.getDomain(0).getElemSort()),
								inDom1 = new Z3Node(domVar1.getElemSort().name + "_in", OPCODE_in, this.z3Encoder.boolSort, null, x, domVar1, tla_atom, NoSet),
								faVar1 = new Z3Node(dom1.getElemSort().name + "_apply_" + range1.getElemSort(), OPCODE_alpha, null, null, var1, x, range1.getElemSort().kind, range1.getElemSort().setLevel),
								faVar2 = new Z3Node(dom2.getElemSort().name + "_apply_" + range2.getElemSort(), OPCODE_alpha, null, null, var2, x, range1.getElemSort().kind, range1.getElemSort().setLevel),
								eqFA 	 = this.createZ3EqNode(faVar1, faVar2);
						inDom1 = this.rewriter.rewrite(inDom1);
						Z3Node body	 = new Z3Node("=>", OPCODE_implies, this.z3Encoder.boolSort, null, inDom1, eqFA, tla_atom, NoSet),
								bfFrm	 = new Z3Node("forall", OPCODE_bf, this.z3Encoder.boolSort, null, tla_atom, NoSet);
						bfFrm.addBoundedVar(x);
						bfFrm.addDomain(sort);
						bfFrm.addExpr(body);
						Z3Node res = new Z3Node("and", OPCODE_land, this.z3Encoder.boolSort, null, tla_atom, NoSet);
						res.addOperand(IsAFcn1);
						res.addOperand(IsAFcn2);
						res.addOperand(eqDo);
						res.addOperand(bfFrm);
						return res;
					}
					else {
						Z3Node eq = this.createZ3EqNode(var1, var2),
								neq = new Z3Node("not", OPCODE_lnot, this.z3Encoder.boolSort, null, eq, tla_atom, NoSet);
						return neq;
					}					
				}
				else {
					return null;
				}
			}
		}
		else {
			Z3Node eq = this.createZ3EqNode(var1, var2),
					neq = new Z3Node("not", OPCODE_lnot, this.z3Encoder.boolSort, null, eq, tla_atom, NoSet);			
			return neq;
		}
	}
}
