package z3parser;

import java.util.ArrayList;

import tla2sany.drivers.FrontEndException;
import tla2sany.drivers.SANY;
import tla2sany.modanalyzer.SpecObj;
import tla2sany.semantic.ExprNode;
import tla2sany.semantic.ExprOrOpArgNode;
import tla2sany.semantic.FormalParamNode;
import tla2sany.semantic.LabelNode;
import tla2sany.semantic.LetInNode;
import tla2sany.semantic.OpApplNode;
import tla2sany.semantic.OpArgNode;
import tla2sany.semantic.OpDefNode;
import tla2sany.semantic.SemanticNode;
import tla2sany.semantic.Subst;
import tla2sany.semantic.SubstInNode;
import tla2sany.semantic.SymbolNode;
import tlc2.TLCGlobals;
import tlc2.tool.Action;
import tlc2.tool.ActionItemList;
import tlc2.tool.BuiltInOPs;
import tlc2.tool.EvalControl;
import tlc2.tool.Tool;
import tlc2.tool.ToolGlobals;
import tlc2.util.Context;
import tlc2.util.Vect;
import tlc2.value.LazyValue;
import tlc2.value.MethodValue;
import tlc2.value.OpValue;
import tlc2.value.StringValue;
import tlc2.value.Value;
import tlc2.value.ValueConstants;
import tlc2.value.IntValue;
import tlc2.value.BoolValue;
import util.Assert;
import util.FileUtil;
import util.FilenameToStream;
import util.ToolIO;
import util.UniqueString;

import java.io.*;

public class Z3Encoder implements ValueConstants, ToolGlobals, Z3Constants {
	private String specFile;
	private SpecObj spec;
	private FilenameToStream resolver;	
	private ArrayList<String> actionNames;
	public Tool tool;
	private Preprocessor preTool;
	private ArrayList<Z3Node> sortList;
	private ArrayList<Z3Node> stringList;
	private Z3Node[] varList;
	private Z3Pair[] defList;
	private String z3SortDeclarations;
	private String z3VarDeclarations;
	private String z3FcnDeclarations;
	private String strInit;
	private String strNext;
	private Z3Node z3Init;
	private Z3Node z3Next;
	private Z3Node[] z3Actions;	
	private String[] z3StrActions;	
	private Z3Node typeOK;
	private String strTypeOK;
	private ArrayList<Z3Node> preds;
	private ArrayList<Z3Node> negPreds; 
	private ArrayList<String> predNames;
	private ArrayList<String> negPredNames;
	public  Z3Tool z3Tool;
	private ArrayList<String> fcnList;
	
	private ArrayList<Z3Node> tfcn; // It's only for AtNodeKind
	private ArrayList<Z3Node> tlhs; // It's only for AtNodeKind
	
	private ArrayList<Z3Node> z3SpecVars;
	
	private Z3Node z3Extensionality;
	private Z3Node z3IsAFcn;
	private String z3StrExtensionality;
	private String z3StrIsAFcn;
	
	private ArrayList<Z3Node> z3FormalParamNodes;
	
	public static int SortNo = 4;
	
	public Z3Node intSort, boolSort, strSort, setIntSort, setBoolSort, setStrSort;
	
	public ConstraintChecker checker;	
	private int taskID;	
	private ArrayList<Z3Node> freshVars;	
	private ArrayList<Z3Node> typeInfos;
	
	private String dir;
	
	private ArrayList<Z3Node> lazyValues;
	private ArrayList<Z3Node> freshVarAssertions;
	
	private ArrayList<Z3Node> initInvs;
	private ArrayList<Z3Node> nextInvs;
	private ArrayList<Z3Node> axioms;
	private ArrayList<String> files;
	
	private String nusmvInv;
	private String p_nusmvInv;
	public  Z3Node raw_init_inv;
	public  Z3Node raw_next_inv;
	
	private Z3Node z3NusmvInv;
	
	public Z3Encoder(String fileName) {		
		int len = fileName.length();
		if (fileName.startsWith(".tla", len - 4)) {
			specFile = fileName.substring(0, len - 4);
		}
		String configFile = specFile;	
		int lastSep = specFile.lastIndexOf(FileUtil.separatorChar);
		String specDir = (lastSep == -1) ? "" : specFile.substring(0, lastSep + 1);
		specFile = specFile.substring(lastSep + 1);

		resolver = null;
		spec = new SpecObj(fileName, null);
				
		try {
			SANY.frontEndMain(spec, fileName, ToolIO.out);
		}
		catch (FrontEndException fe) {
			// For debugging
			fe.printStackTrace();   
			ToolIO.out.println(fe);			
		}
		
		this.tool = new Tool(specDir, specFile, configFile, resolver);		
		this.actionNames = new ArrayList<String>();		 					
		this.preTool 		= new Preprocessor(this.tool, this.actionNames);
		this.preTool.GetActions(spec);
//		this.preTool.ChangeActionNames();	
		this.sortList		= new ArrayList<Z3Node>();
		this.stringList = new ArrayList<Z3Node>();
		int alen = 2 * this.tool.variablesNodes.length;
		this.varList 		= new Z3Node[ alen ];
		this.defList 		= new Z3Pair[ alen ];
		for (int i = 0; i < alen; i++) {
			this.varList[i] = new Z3Node(NoName, NoCode, null, null, NoKind, iNull);
			this.defList[i] = new Z3Pair();
			this.defList[i].hasDef = false;
		}
		
		this.z3SortDeclarations = "; Sort Declarations\n";
		this.z3VarDeclarations 	= "; Variable Declarations\n";
		this.z3FcnDeclarations  = "; Function Declarations\n";
		this.strInit = NoCommand;
		this.strNext = NoCommand;
		this.z3Actions = new Z3Node[this.actionNames.size()];
		this.z3StrActions = new String[this.actionNames.size()];
				
		this.typeOK = null;
		this.strTypeOK = "; String Declarations\n";
		this.preds = new ArrayList<Z3Node>();
		this.negPreds = new ArrayList<Z3Node>();
		this.predNames = new ArrayList<String>();
		this.negPredNames = new ArrayList<String>();
		this.z3Tool = new Z3Tool(this);
		this.fcnList = new ArrayList<String>();
		
		this.tfcn = new ArrayList<Z3Node>();
		this.tlhs = new ArrayList<Z3Node>();
		this.z3SpecVars = new ArrayList<Z3Node>();
		
		this.z3Extensionality = null;
		this.z3IsAFcn = null;
		this.z3StrExtensionality = "; extensionality\n";
		this.z3StrIsAFcn = "; IsAFcn\n";
		
		this.z3FormalParamNodes = new ArrayList<Z3Node>();
		
		this.boolSort = null;
		this.intSort = null;
		this.strSort = null;
		this.setBoolSort = null;
		this.setIntSort = null;
		this.setStrSort = null;		
		this.checker = new ConstraintChecker(this);		
		this.freshVars = new ArrayList<Z3Node>();		
		this.typeInfos = new ArrayList<Z3Node>();
		this.lazyValues = new ArrayList<Z3Node>();
		this.freshVarAssertions = new ArrayList<Z3Node>();
		
		this.initInvs = new ArrayList<Z3Node>();
		this.nextInvs = new ArrayList<Z3Node>();
		this.axioms 	= new ArrayList<Z3Node>();
		this.files 		= new ArrayList<String>();
	}	
	
	public final void run() throws IOException {
		this.z3Tool.createDefaultSortList();
		this.createVarList();
		this.translateTypeOK();
		this.translateInit();
		this.translateNext();
		this.translateActions();
		this.translateInv();
		this.translateInvariant();
		this.translatePredicates();
		this.translatePredInv();
		this.makeSortDeclarations(); 
		this.makeVarDeclarations();		
		this.printZ3Spec();		
	}
			
	// Get sort info of elements in set1
	public final Z3Node getElemSort(Z3Node set1) {
		return set1.getElemSort();		
	}

	// Get sort info of elements in set1 and set2
	public final Z3Node getElemSort(Z3Node set1, Z3Node set2) {		
		if (set1.getElemSort() != null) {
			return set1.getElemSort();
		}
		else if (set2.getElemSort() != null) {
			return set2.getElemSort();
		}
		else {
			return null;
		}
	}

	// Get sort info of elements in set1, set2, and set3
	public final Z3Node getElemSort(Z3Node set1, Z3Node set2, Z3Node set3) {
		if (set1.getElemSort() != null) {
			return set1.getElemSort();
		}
		else if (set2.getElemSort() != null) {
			return set2.getElemSort();
		}
		else if (set3.getElemSort() != null) {
			return set3.getElemSort();
		}
		else {
			return null;
		}
	}
				
	//The original function lookup(SymbolNode var) is from Context.java.
	// Because we do not need the value of a function, a record, ...
	// We need only its name. Therefore, I decide to create a new function 
	// in NextTool. This function receives two arguments: context and var. 
	// It returns the corresponding name of var.
	// Because cur.next and cur.name are private, I write two new functions
	// getNext() and getName() in Context.java.
	private final String lookup(Context c, SymbolNode var) {
   Context cur;
   for (cur = c; cur.getName() != null; cur = cur.getNext()) {
     if (var == cur.getName()) return cur.getName().getName().toString();
   }
   if (cur == Context.Empty) return NoName;
   return this.lookup(cur.getNext(), var);
 }
		
	public final Object lookup(SymbolNode opNode, Context c, boolean cutoff)
	{
		// Only for params of actions
		boolean isVarDecl = (opNode.getKind() == VariableDeclKind);
		Object result = c.lookup(opNode, cutoff && isVarDecl);
		if (result != null)
			return result;
//
//		result = opNode.getToolObject(TLCGlobals.ToolId);
//		if (result != null)
//			return result;

		if (opNode.getKind() == UserDefinedOpKind)
		{
			// Changed by Thanh Hai
			// just for IsAFcn
			
//			if (opNode.getName().toString().equals("IsAFcn")) {
//				return opNode;
//			}
			
			ExprNode body = ((OpDefNode) opNode).getBody();
			result = body.getToolObject(TLCGlobals.ToolId);
			while ((result == null) && (body.getKind() == SubstInKind)) {
				body = ((SubstInNode) body).getBody();
				result = body.getToolObject(TLCGlobals.ToolId);
			}
			// end change
			if (result != null)
				return result;
		}
		return opNode;
	}
	
	// Remove s0 and TLCState.Empty
	// In Tool.java
	// Change Value to TypedSM2Node
	private final Z3Node eval(SemanticNode expr, Context c) { 
		return this.eval(expr, c, EvalControl.Clear);		
	}
	
	// Remove APSubstInKind, we don't have theorems and assumptions 
	// Remove case DecimalKind, TLC cannot evaluate decimal numbers.	
	// Remove s0 and s1, we don't evaluate any expressions.
	// In Tool.java
	private final Z3Node eval(SemanticNode expr, Context c, int control) {		
		switch (expr.getKind()) {
		/***********************************************************************
		 * LabelKind class added by LL on 13 Jun 2007.                          *
		 ***********************************************************************/
		case LabelKind: {
			LabelNode expr1 = (LabelNode) expr;
			return this.eval(expr1.getBody(), c, control) ;			
		}
		case OpApplKind: {
			OpApplNode expr1 = (OpApplNode)expr;
			return this.evalAppl(expr1, c, control);			
		}
		case LetInKind: {
			LetInNode expr1 = (LetInNode)expr;
			OpDefNode[] letDefs = expr1.getLets();
			int letLen = letDefs.length;
			Context c1 = c;
			for (int i = 0; i < letLen; i++) {
				OpDefNode opDef = letDefs[i];
				if (opDef.getArity() == 0) {
					Value rhs = new LazyValue(opDef.getBody(), c1);
					c1 = c1.cons(opDef, rhs);
				}
			}
			// return this.eval(expr1.getBody(), c1, s0, s1, control);
			return this.eval(expr1.getBody(), c1, control);			
		}
		case SubstInKind: {
			SubstInNode expr1 = (SubstInNode)expr;
			Subst[] subs = expr1.getSubsts();
			int slen = subs.length;
			Context c1 = c;
			for (int i = 0; i < slen; i++) {
				Subst sub = subs[i];
				// There is no value to get here.
				// We just bind sub.getOp() with sub.getExpr().
				c1 = c1.cons(sub.getOp(), sub.getExpr());
			}
			return this.eval(expr1.getBody(), c1, control);			
		}
		case NumeralKind: {	
			String name = (Value.getValue(expr)).toString();
			Z3Node node = new Z3Node(name, OPCODE_const, this.intSort, null, tla_atom, NoSet);
			return node;
		}
		case StringKind: {			
			String name = (Value.getValue(expr)).toString();
			name = name.replace("\"", "");
			Z3Node node = new Z3Node(name, OPCODE_const, this.strSort, null, tla_atom, NoSet);
			this.addStringVar(node);
			return node;
		}		
		case AtNodeKind: {	
			String name = this.lookup(c, EXCEPT_AT);
			int index = this.getVarIndex(name);
			if (index >= 0) {
				Z3Node node = this.varList[index].clone();
				return node;
			}
			else {				
				Z3Node fcn = this.tfcn.get(this.tfcn.size() - 1),
						lhs = this.tlhs.get(this.tlhs.size() - 1),
						node = new Z3Node(NoName, OPCODE_fa, fcn.cod, null, fcn.cod.kind, NoSet);
				node.addOperand(fcn.clone());
				node.addOperand(lhs.clone());
				return node;
			}			
		}
		case OpArgKind:
		{
			OpArgNode expr1 = (OpArgNode)expr;
			SymbolNode opNode = expr1.getOp();
			// We don't evaluate any expression, therefore tool does not know 
			// the value of opNode. We don't need to look up its value.
			// Moreover, we assume that node has no args.
			OpDefNode opDef = (OpDefNode)opNode;
			int opcode = BuiltInOPs.getOpCode(opDef.getName());
			if (opcode == 0) {
				// Remove s0 and s1							
				return this.eval(opDef.getBody(), c, control);
			}	
			return null;
		}		
		default: {			
			// We change it just for params
			if (expr instanceof FormalParamNode) {
				FormalParamNode pNode = (FormalParamNode) expr;
				String name = pNode.getName().toString();
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
				// Can we get more param's info from a corresponding function? 
				Z3Node node = new Z3Node(name, NoCode, null, null, NoKind, iNull);
////////////////////////////////////////////////////////////////////////////////				
				return node;
			}
			return null;
		}
		}
	}
	
	// Remove states s0 and s1
	// In Tool.java
	private final Z3Node evalAppl(OpApplNode expr, Context c, int control) {
		ExprOrOpArgNode[] args = expr.getArgs();
		SymbolNode opNode = expr.getOperator();
		int opcode = BuiltInOPs.getOpCode(opNode.getName());
		Z3Node node = new Z3Node(NoName, NoCode, null, null, NoKind, iNull);
		
		if (opcode == 0) {
			// This is a user-defined operator with one exception: it may
			// be substed by a builtin operator. This special case occurs
			// when the lookup returns an OpDef with opcode # 0.
			// Use tool in tlc2.tool
			if (this.tool.callStack != null) this.tool.callStack.push(expr);
			// Since we don't evaluate states and constants, we don't need to look up 
			// the value in context, states s0 and s1.
			// However, since TLA+ have many "user" defined operators, 
			// we still need to look up their meanings.
			Object val = this.lookup(opNode, c, EvalControl.isPrimed(control));

			// We don't evaluate anything, so lazy values are only for params of actions.
			if (val instanceof LazyValue) {
				LazyValue lv = (LazyValue)val;
				return this.eval(lv.expr, lv.con, control);					
			}
			
			// Instead of res from Value, now we use node from Z3Node.
			if (val instanceof OpDefNode) {
				OpDefNode opDef = (OpDefNode)val;
				opcode = BuiltInOPs.getOpCode(opDef.getName());
				if (opcode == 0) {
					// Use the funciton in tlc2.tool
					Context c1 = this.tool.getOpContext(opDef, args, c, true);				
					if (expr.getOperator().getName().toString().equals("BOOLEAN")) {
						return this.setBoolSort;
					}
					else if (expr.getOperator().getName().toString().equals("FALSE")) {
						return new Z3Node("false", OPCODE_false, this.boolSort, null, tla_atom, NoSet);
					}
					else if (expr.getOperator().getName().toString().equals("TRUE")) {
						return new Z3Node("true", OPCODE_true, this.boolSort, null, tla_atom, NoSet);
					}
					else {						
						node = this.eval(opDef.getBody(), c1, control);
						String name = expr.getOperator().getName().toString();
						if (this.taskID == predTask && !name.equals("Predicates")) {
							this.predNames.add(name);
							this.preds.add(node.clone());
						}
						if (this.taskID == predInvTask && !name.equals("Inv_ToCheck")) {							
							node = new Z3Node(name, OPCODE_pred, this.boolSort, null, tla_atom, NoSet);
						}
					}
				}
			}
			else if (val instanceof Value) {		
				// Instead of assigning val to res, we assign "string" val to node's name.
				// node.name = ((Value)val).toString();
				int alen = args.length;
				if (alen == 0) {
					if (val instanceof MethodValue) {
						// I guess I need to translate this node if MethodValue is Int, 
						// or Boolean.
						node.name = ((MethodValue) val).md.getName();						
						if (node.name.equals("Nat") || node.name.equals("Int")) {							
							node = this.setIntSort;
						}
						else if (node.name.equals("BOOLEAN") || node.name.equals("Bool")) {							
							node = this.setBoolSort;
						}
						return node;
					}
				}
				else if (val instanceof OpValue) {					
					node.name = opNode.getName().toString();
					// Change the sort of argVals from Value to Z3Node
					Z3Node[] argVals = new Z3Node[alen];
					Z3Node elemSort = null;
					// evaluate the actuals:
					// evaluate the arguments of the operator.
					for (int i = 0; i < alen; i++) {
						// Again, remove s0 and s1
						argVals[i] = this.eval(args[i], c, control);						
						if (elemSort == null && argVals[i].getSort() != null) {
							elemSort = argVals[i].getSort();
						}
						node.addOperand(argVals[i]);
					}		
					// If the operator is the integral interval, we need to generate all
					// numbers between n1 and n2.
					if (node.name.equals(OP_dotdot.toString()) || node.name.equals("DotDot")) {
						this.checker.dd_check(node);						
						node = new Z3Node(NoName, OPCODE_se, this.setIntSort, null, tla_set, 1);
						node.isDotDot = true;						
						int n1 = Integer.parseInt(argVals[0].name);
						int n2 = Integer.parseInt(argVals[1].name);
						// Add the current argument to the node's list of arguments.
						for (int i = n1; i <= n2; i++) {
							String name = Integer.toString(i);
							Z3Node node1 = new Z3Node(name, OPCODE_const, this.intSort, null, tla_atom, NoSet);
							node.addOperand(node1);
						}
					}
					else if (node.name.equals("-.")) {
						String name = "-" + argVals[0].name;
						node = new Z3Node(name, OPCODE_const, this.intSort, null, tla_atom, NoSet);
					}
					else {
						// In SMT-LIB, modulo (%) is replaced with "mod" 
						// and integer division "\\div" is replaced with "div".
						if (node.name.equals("%")) {
							node.name = "mod";
							node.opCode = OPCODE_mod;
						}
						else if (node.name.equals("\\div")) {
							node.name = "div";				
							node.opCode = OPCODE_div;
						}
						else if (node.name.equals("\\geq")) {
							node.name = ">=";
							node.opCode = OPCODE_ge;
						}
						else if (node.name.equals("\\leq")) {
							node.name = "<=";
							node.opCode = OPCODE_le;
						}
						//
						// switch (node.name) {
						// case "<": {
						else if (node.name.equals("<")) {
							this.checker.IntsBool_check(node);
							node.opCode = OPCODE_lt;							
						}
						else if (node.name.equals(">")) {							
							this.checker.IntsBool_check(node);
							node.opCode = OPCODE_gt;						
						}
						else if (node.name.equals("<=")) {							
							this.checker.IntsBool_check(node);
							node.opCode = OPCODE_le;						
						}
						else if (node.name.equals(">=")) {							
							this.checker.IntsBool_check(node);
							node.opCode = OPCODE_ge;							
						}
						else if (node.name.equals("mod")) {
							this.checker.IntsInt_check(node);
							node.opCode = OPCODE_mod;					
						}
						else if (node.name.equals("div")) {
							this.checker.IntsInt_check(node);
							node.opCode = OPCODE_div;	
						}
						else if (node.name.equals("+")) {
							this.checker.IntsInt_check(node);
							node.opCode = OPCODE_add;							
						}
						else if (node.name.equals("-")) {
							this.checker.IntsInt_check(node);
							node.opCode = OPCODE_sub;								
						}
						else if (node.name.equals("*")) {
							this.checker.IntsInt_check(node);
							node.opCode = OPCODE_mul;							
						}
						else {							
							node.setSort(elemSort);														
						}												
						// We don't need to apply the operator.											
					}
				}
			}
			// Reomve ThmOrAssumpDefNode and the error information			
			// Use tlc2.tool
			if (this.tool.callStack != null) this.tool.callStack.pop();
			if (opcode == 0) {
				// 
				if (node.name.equals(NoName)) {					
					if (val instanceof IntValue) {
						node = new Z3Node(val.toString(), OPCODE_const, this.intSort, null, tla_atom, NoSet);
					}
					else if (val instanceof BoolValue) {
						node = new Z3Node(val.toString(), OPCODE_const, this.boolSort, null, tla_atom, NoSet);
					}
					else {
						node.name = expr.getOperator().getName().toString();
					}
					if (node.name.equals("Nat") || node.name.equals("Int")) {
						node = this.setIntSort;
					}						
					else if (node.name.equals("BOOLEAN") || node.name.equals("Bool")) {
						node = this.setBoolSort;
					}			
					else if (node.name.equals("TRUE")) {
						node = new Z3Node("true", OPCODE_true, this.boolSort, null, tla_atom, NoSet);
					}
					else if (node.name.equals("FALSE")) {
						node = new Z3Node("false", OPCODE_false, this.boolSort, null, tla_atom, NoSet);
					}
				}
				if (((SymbolNode) opNode).getKind() == VariableDeclKind) {
					int index = this.getVarIndex(node.name);
					if (index >= 0) {
						node = this.varList[index];												
					}			
				}
				if (opNode instanceof FormalParamNode && !(val instanceof IntValue) && !(val instanceof BoolValue) ) {
					node = this.getZ3FormalParamNode(node);
				}
				return node;
			}
		}
		// node's opCode equals expr's opcode in TLA+ code.
		// node's name equals the corresponding name in SMT-LIB.
		// Remove OPCODE_bc, 
		node.opCode = opcode;
		switch (opcode) {
		case OPCODE_be: {    		// BoundedExists		
			node = new Z3Node("exists", OPCODE_be, this.boolSort, null, tla_atom, NoSet);
			// Instead of evaluating possible values of bounded variables,
			// we need to know only their names and domains.
			// Since our formula is \A x \in S. p(x), all formals, isTuples, and   
			// domains have only one element formals[0][0], isTuples[0], and 
			// domains[0]. We will support \A x1 \in S1, x2 \in S2, ... later.
			FormalParamNode[][] formals = expr.getBdedQuantSymbolLists();			
			ExprNode[] domains = expr.getBdedQuantBounds();
			Z3Node x = this.eval(formals[0][0], c, EvalControl.Clear), 
					S = this.eval(domains[0], c, EvalControl.Clear);
			this.checker.unifySort_in(x, S);
			x.opCode = OPCODE_bv;
			this.z3FormalParamNodes.add(x);
			SemanticNode body = args[0];
//			Z3Node z3Body = this.eval(body , c, EvalControl.Clear);
//			node.addBoundedVar(x);
			Z3Node z3Body = this.eval(body, c, EvalControl.Clear),
					bvar = this.z3Tool.createBoundedVar();
			this.checker.unifySort_equivSort(x, bvar);
			this.z3Tool.replaceNode(x.name, z3Body, bvar);
			z3Body.setSort(this.boolSort);
			node.addBoundedVar(bvar);
			node.addDomain(S);			
			node.addExpr(z3Body);
			this.z3FormalParamNodes.remove(this.z3FormalParamNodes.size() - 1);
			// We don't need to show TLC errors.
			this.checker.be_check(node);
			return node;  
		}
		case OPCODE_bf: {    		// BoundedForall		
			node = new Z3Node("forall", OPCODE_bf, this.boolSort, null, tla_atom, NoSet);
			// Instead of evaluating possible values of bounded variables,
			// we need to know only their names and domains.
			// Since our formula is \E x \in S. p(x), all formals, isTuples, and   
			// domains have only one element formals[0][0], isTuples[0], and 
			// domains[0]. We will support \E x1 \in S1, x2 \in S2, ... later.
			FormalParamNode[][] formals = expr.getBdedQuantSymbolLists();			
			ExprNode[] domains = expr.getBdedQuantBounds();
			Z3Node x = this.eval(formals[0][0], c, EvalControl.Clear), 
					S = this.eval(domains[0], c, EvalControl.Clear);
			this.checker.unifySort_in(x, S);
			x.opCode = OPCODE_bv;
			this.z3FormalParamNodes.add(x.clone());
			SemanticNode body = args[0];
//			Z3Node z3Body = this.eval(body , c, EvalControl.Clear);
//			node.addBoundedVar(x);
			Z3Node z3Body = this.eval(body, c, EvalControl.Clear),
					bvar = this.z3Tool.createBoundedVar();
			this.checker.unifySort_equivSort(x, bvar);
			this.z3Tool.replaceNode(x.name, z3Body, bvar);
			z3Body.setSort(this.boolSort);
			node.addBoundedVar(bvar);
			node.addDomain(S);			
			node.addExpr(z3Body);
			this.z3FormalParamNodes.remove(this.z3FormalParamNodes.size() - 1);			
			// We don't need to show TLC errors.
			this.checker.bf_check(node);
			return node;
		}		
		case OPCODE_case: {  		// Case --> IF THEN ELSE		
			// Since there is no corresponding part in SMT-LIB, node's name is empty.			
			node = new Z3Node("ite", OPCODE_ite, null, null, NoKind, iNull);				
			int alen = args.length;			
			Z3Node cur = node;
			OpApplNode pair;
			pair = (OpApplNode)args[alen - 2];
			ExprOrOpArgNode[] pairArgs = pair.getArgs();
			Z3Node con = this.eval(pairArgs[0], c, control),
					action1 = this.eval(pairArgs[1], c, control);			
			// The last one does not have the condition
			pair = (OpApplNode)args[alen - 1];
			pairArgs = pair.getArgs();
			Z3Node action2 = this.eval(pairArgs[1], c, EvalControl.Clear);				
			cur.addOperand(con);
			cur.addOperand(action1);			
			cur.addOperand(action2);
			this.checker.ite_check(node);
			for (int i = alen - 2; i >= 0; i--) {
				pair = (OpApplNode)args[i];
				pairArgs = pair.getArgs();
				con = this.eval(pairArgs[0], c, control);
				action1 = this.eval(pairArgs[1], c, control);
				node = new Z3Node("ite", OPCODE_ite, cur.getSort(), null, action1, cur, NoKind, iNull);
				this.checker.ite_check(node);
				cur = node;
			}
			node.passSortInfo();
			return node;			
		}
		case OPCODE_cp: {    		// CartesianProd		
			// Since there is no corresponding part in SMT-LIB, node's name is empty.
			node = new Z3Node("NoName", OPCODE_cp, null, null, tla_set, 1);
			int alen = args.length;			
			Z3Node dom = new Z3Node("dom_" + this.intSort.name, OPCODE_se, this.setIntSort, null, tla_set, 1);
			for (int i = 0; i < alen; i++) {
				Z3Node field = new Z3Node(Integer.toString(i + 1), OPCODE_const, this.intSort, null, tla_atom, NoSet),
						op = this.eval(args[i], c, control);				
				dom.addOperand(field);
				node.addField(field);
				node.addOperand(op);
			}			
			node.addDomain(dom);
			this.checker.cp_check(node);
			return node;
		}	
		case OPCODE_cl: {    		// ConjList
			node = new Z3Node("and", OPCODE_land, this.boolSort, null, tla_atom, NoSet);
			int alen = args.length;
			Z3Node operand = null;
			for (int i = 0; i < alen; i++) {
				// Use tlc2.tool
				if (this.tool.callStack != null) this.tool.callStack.push(args[i]);
				// Add a new operand
				operand = this.eval(args[i], c, control);				
				node.addOperand(operand);				
				// We don't need to show TLC errors.
				// Use tlc2.tool
				if (this.tool.callStack != null) this.tool.callStack.pop();
			}
			this.checker.boolOperator_check(node);
			return node;
		}
		case OPCODE_dl: {    		// DisjList		
			node = new Z3Node("or", OPCODE_lor, this.boolSort, null, tla_atom, NoSet);			
			int alen = args.length;
			Z3Node operand = null;
			for (int i = 0; i < alen; i++) {
				// Use tlc2.tool
				if (this.tool.callStack != null) this.tool.callStack.push(args[i]);
				// Add a new operand				
				operand = this.eval(args[i], c, control);
				node.addOperand(operand);			
				// We don't need to show TLC errors.
				// Use tlc2.tool
				if (this.tool.callStack != null) this.tool.callStack.pop();				
			}
			this.checker.boolOperator_check(node);
			return node;
		}				
		case OPCODE_exc: {   		// Except			
			node = new Z3Node(NoName, OPCODE_exc, null, null, NoKind, iNull);
			OpApplNode pairNode = (OpApplNode)args[1];
			ExprOrOpArgNode[] pairArgs = pairNode.getArgs();
			SemanticNode[] cmpts = ((OpApplNode)pairArgs[0]).getArgs();			
			Z3Node fcn = this.eval(args[0], c, control), 
					lhs = this.eval(cmpts[0], c, control);
			// for AtNodeKind
			this.tfcn.add(fcn); 
			this.tlhs.add(lhs); 
			// for AtNodeKind
			Z3Node rhs = this.eval(pairArgs[1], c, control);
			// for AtNodeKind
			// What does it mean? @_@
///////////////////////////////////////////////////////////
			int size = this.tfcn.size() - 1;
			if (size >= 2) {
				Z3Node tmp = this.tfcn.get(size - 2);
				if (tmp.name.equals(NoName)) {
					tmp.name = this.tfcn.get(size - 1).name;
				}
			}			
///////////////////////////////////////////////////////////			
			this.tfcn.remove(this.tfcn.size() - 1);
			this.tlhs.remove(this.tlhs.size() - 1);
			// for AtNodeKind			
			node.addOperand(fcn);
			node.addOperand(lhs);
			node.addOperand(rhs);		
			this.checker.exc_check(node);
			return node;			
		}
		case OPCODE_fa: {    // FcnApply
			node = new Z3Node(NoName, OPCODE_fa, null, null, NoKind, iNull);
			Z3Node fcn = this.eval(args[0], c, EvalControl.KeepLazy),
					arg = this.eval(args[1], c, EvalControl.Clear);					
			node.addOperand(fcn);
			node.addOperand(arg);		
			this.checker.fa_check(node);
			return node;
		}
		case OPCODE_fc:     		// FcnConstructor
		case OPCODE_nrfs: {  		// NonRecursiveFcnSpec			
			node = new Z3Node(NoName, OPCODE_fc, null, null, tla_fcn, NoSet);
			// Since there is no corresponding part in SMT-LIB, node's name is empty.			
			// Since our formula is [ x \in S |-> expr(x) ], all formals, isTuples,    
			// and domains have only one element formals[0][0], isTuples[0], and 
			// domains[0]. Note: [ x1 \in S1, ..., xn \in Sn |-> expr(x1, ..., xn) ]
			// is not allowed in our TLA+ specification, the user should rewrite it 
			// as [ x \in S |-> expr(x) ] where x = (x1, ..., xn) and S = S1 x ... x Sn			
			FormalParamNode[][] formals = expr.getBdedQuantSymbolLists();			
			ExprNode[] domains = expr.getBdedQuantBounds();
			// I think isTuples.length = 1, always.
			Z3Node S = this.eval(domains[0], c, control);						
			node.addDomain(S);
			// We need only a variable's name.
			String name = formals[0][0].getName().toString();
			Z3Node x = new Z3Node(name, OPCODE_bv, null, null, NoKind, iNull);
			this.checker.unifySort_in(x, S);
			this.z3FormalParamNodes.add(x.clone());
			SemanticNode fbody = args[0];
			Z3Node z3Body = this.eval(fbody, c, control),
					bvar = this.z3Tool.createBoundedVar();
			this.checker.unifySort_equivSort(x, bvar);
			this.z3Tool.replaceNode(x.name, z3Body, bvar);
			node.addBoundedVar(bvar);
//			Z3Node z3Body = this.eval(fbody, c, control);
//			node.addBoundedVar(x);
			node.addDomain(S);
			node.addExpr(z3Body);
			this.checker.fc_check(node);
			this.z3FormalParamNodes.remove(this.z3FormalParamNodes.size() - 1);
			return node;
		}		
		case OPCODE_ite: {  		// IfThenElse			
			node = new Z3Node("ite", OPCODE_ite, null, null, NoKind, iNull);
			Z3Node con = this.eval(args[0], c, control),
					action1 = this.eval(args[1], c, control),
					action2 = this.eval(args[2], c, control);					
			node.addOperand(con);
			node.addOperand(action1);
			node.addOperand(action2);
			this.checker.ite_check(node);
			return node;
		}
		case OPCODE_rc: {   		// RcdConstructor
			node = new Z3Node(NoName, OPCODE_rc, null, null, tla_rcd, NoSet);			
			int alen = args.length;			
			Z3Node dom = new Z3Node("z3_strSet", OPCODE_se, this.setStrSort, this.strSort, tla_set, 1);			
			for (int i = 0; i < alen; i++) {
				OpApplNode pairNode = (OpApplNode)args[i];
				ExprOrOpArgNode[] pair = pairNode.getArgs();
				String name = (((StringValue)Value.getValue(pair[0])).getVal().toString());
				Z3Node field = new Z3Node(name, OPCODE_const, this.strSort, null, tla_atom, NoSet),
						e = this.eval(pair[1], c, control);				
				dom.addOperand(field);
				node.addField(field);				
				node.addExpr(e);
				node.addRange(e.getSort());				
			}
			node.addDomain(dom);
			this.checker.rc_check(node);
			return node;
		}
		case OPCODE_rs: {   		// RcdSelect
			node = new Z3Node(NoName, OPCODE_rs, null, null, NoKind, iNull);
			Z3Node rcd = this.eval(args[0], c, control),
					field = this.eval(args[1], c, control);			
			node.addOperand(rcd);
			node.addOperand(field);
			this.checker.rs_check(node);
			return node;
		}
		case OPCODE_se: {				// SetEnumerate: { e1, ... , en }
			// Since there is no corresponding part in SMT-LIB, node's name is empty.
			// setLevel can be updated later.
			node = new Z3Node(NoName, OPCODE_se, null, null, tla_set, iNull);			
			int alen = args.length;
			// Reomove vals (ValueVec).
			// We add directly operands into a node.			
			for (int i = 0; i < alen; i++) {				
				Z3Node elem = this.eval(args[i], c, control);								
				node.addOperand(elem);				
			}			
			this.checker.se_check(node);
			// I don't know what isNorm means. I guess it it to check
			// whether duplicated operands exist in a set. 
			// I decide not to add isNorm in my Z3Node.			
			return node;
		}		
		case OPCODE_soa: {  	 	// SetOfAll: {e(x) : x \in S}
			node = new Z3Node(NoName, OPCODE_soa, null, null, tla_set, iNull);
			// Since there is no corresponding part in SMT-LIB, node's name is empty.
			// BoundedVar = x, Expr = e(x), Domain = S			
			FormalParamNode[][] formals = expr.getBdedQuantSymbolLists();			
			ExprNode[] domains = expr.getBdedQuantBounds();			
			Z3Node x = this.eval(formals[0][0], c, control),
					S = this.eval(domains[0], c, control);
			this.checker.unifySort_in(x, S);			
			this.z3FormalParamNodes.add(x.clone());			
			SemanticNode body = args[0];
			Z3Node z3Body = this.eval(body, c, control),
					bvar = this.z3Tool.createBoundedVar();
			this.checker.unifySort_equivSort(x, bvar);
			this.z3Tool.replaceNode(x.name, z3Body, bvar);
			node.addBoundedVar(bvar);
//			Z3Node z3Body = this.eval(body, c, control);
//			node.addBoundedVar(x);
			node.addDomain(S);			
			node.addExpr(z3Body);								
			this.z3FormalParamNodes.remove(this.z3FormalParamNodes.size() - 1);
			this.checker.soa_check(node);			
			return node;
		}
		case OPCODE_sor: {   		// SetOfRcds: [ hi : Si ]
			node = new Z3Node(NoName, OPCODE_sor, null, null, tla_set, 1);
			// Since there is no corresponding part in SMT-LIB, node's name is empty.			
			int alen = args.length;
			UniqueString names[] = new UniqueString[alen];			
			Z3Node dom = new Z3Node("z3_strSet", OPCODE_se, this.setStrSort, this.strSort, tla_set, 1);			
			for (int i = 0; i < alen; i++) {
				OpApplNode pairNode = (OpApplNode)args[i];
				ExprOrOpArgNode[] pair = pairNode.getArgs();
				names[i] = ((StringValue)Value.getValue(pair[0])).getVal();
				String name = names[i].toString();
				Z3Node field = new Z3Node(name , OPCODE_const, this.strSort, null, tla_atom, NoSet),
						S = this.eval(pair[1], c, control);
				this.addStringVar(field);
				dom.addOperand(field);				
				node.addField(field);
				node.addRange(S);
			}
			node.addDomain(dom);
			this.checker.sor_check(node);			
			return node;
		}
		case OPCODE_sof: {   		// SetOfFcns: [ S -> T ]			
			// Since there is no corresponding part in SMT-LIB, node's name is empty.
			node = new Z3Node(NoName, OPCODE_sof, null, null, tla_set, 1);
			Z3Node S = this.eval(args[0], c, control),
					T = this.eval(args[1], c, control);
			node.addDomain(S);
			node.addRange(T);
			this.checker.sof_check(node);
			return node;
		}
		case OPCODE_sso: {	    // SubsetOf: { x \in S : p(x) }					
			// Since there is no corresponding part in SMT-LIB, node's name is empty.
			// BoundedVar = x, Domain = S, Expr = p(x)			
			FormalParamNode[][] formals = expr.getBdedQuantSymbolLists();		
			ExprNode[] domains = expr.getBdedQuantBounds();			
			Z3Node x = this.eval(formals[0][0], c, control),
					S = this.eval(domains[0], c, control);					
			this.checker.unifySort_in(x, S);			
			this.z3FormalParamNodes.add(x.clone());
			SemanticNode pred = args[0];
			node = new Z3Node(NoName, OPCODE_sso, S.getSort(), null, tla_set, S.setLevel);
			Z3Node p = this.eval(pred, c, control),
					bvar = this.z3Tool.createBoundedVar();			
			this.checker.unifySort_equivSort(x, bvar);
			this.z3Tool.replaceNode(x.name, p, bvar);			
			node.addBoundedVar(bvar);
//			Z3Node p = this.eval(pred, c, control);
//			node.addBoundedVar(x);			
			node.addDomain(S);						
			node.addExpr(p);
			this.z3FormalParamNodes.remove(this.z3FormalParamNodes.size() - 1);			
			this.checker.sso_check(node);			
			return node;			
		}			
		case OPCODE_tup: {   // Tuple			
			node = new Z3Node(NoName, OPCODE_tup, null, null, tla_tup, NoSet);
			int alen = args.length;			
			Z3Node dom = new Z3Node("dom", OPCODE_se, this.setIntSort, this.intSort, tla_set, 1);			
			for (int i = 0; i < alen; i++) {
				String fieldName = Integer.toString(i + 1);
				Z3Node field = new Z3Node(fieldName, OPCODE_const, this.intSort, null, tla_atom, NoSet);				
				dom.addOperand(field);
				Z3Node z3Expr = this.eval(args[i], c, control),
						z3ExprSort = this.getSort(z3Expr.getSort());
				node.addExpr(z3Expr);
				node.addField(field);
				node.addRange(z3ExprSort);
			}
			node.addDomain(dom);	
			this.checker.tup_check(node);
			return node;
		}		
		// Remove OPCODE_uc, OPCODE_ue, OPCODE_uf:
		case OPCODE_lnot: {	
			node = new Z3Node("not", OPCODE_lnot, this.boolSort, null, tla_atom, NoSet);
			node.setSort(this.boolSort);
			Z3Node op0 = this.eval(args[0], c, control);
			op0.setSort(this.boolSort);					
			node.addOperand(op0);
			this.checker.boolOperator_check(node);
			return node;
		}
		case OPCODE_subset: {
			node = new Z3Node(NoName, OPCODE_subset, null, null, tla_set, iNull);
			// Since there is no corresponding part in SMT-LIB, node's name is empty.
			// z3Sort and setLevel can be updated later.
			Z3Node op0 = this.eval(args[0], c, control);											
			node.addOperand(op0);		
			this.checker.subset_check(node);
			return node;			
		}
		case OPCODE_union: {				
			node = new Z3Node(NoName, OPCODE_union, null, null, tla_set, iNull);
			// Since there is no corresponding part in SMT-LIB, node's name is empty.
			// z3Sort and setLevel can be updated later.
			Z3Node op0 = this.eval(args[0], c, control);
			node.addOperand(op0);			
			this.checker.union_check(node);	
			return node;
		}		
		case OPCODE_domain: {			
			node = new Z3Node("domain", OPCODE_domain, null, null, tla_set, iNull);			
			// Since there is no corresponding part in SMT-LIB, node's name is empty.
			// z3Sort and setLevel can be updated later.
			Z3Node op0 = this.eval(args[0], c, control);			
			node.addOperand(op0);
			this.checker.domain_check(node);
			return node;
		}
		// Remove OPCODE_enable
		case OPCODE_eq: {	
			node = new Z3Node("=", OPCODE_eq, this.boolSort, null, tla_atom, NoSet);
			Z3Node lhs = this.eval(args[0], c, control),
					rhs = this.eval(args[1], c, control);				
			node.addOperand(lhs);
			node.addOperand(rhs);
			this.checker.eq_check(node);
			return node;
		}
		case OPCODE_land: {
			node = new Z3Node("and", OPCODE_land, this.boolSort, null, tla_atom, NoSet);
			Z3Node op0 = this.eval(args[0], c, control),
					op1 = this.eval(args[1], c, control);			
			node.addOperand(op0);
			node.addOperand(op1);
			this.checker.boolOperator_check(node);
			return node;
		}
		case OPCODE_lor: {		
			node = new Z3Node("or", OPCODE_lor, this.boolSort, null, tla_atom, NoSet);
			Z3Node op0 = this.eval(args[0], c, control),
					op1 = this.eval(args[1], c, control);			
			node.addOperand(op0);
			node.addOperand(op1);
			this.checker.boolOperator_check(node);
			return node;
		}
		case OPCODE_implies: {		
			node = new Z3Node("=>", OPCODE_implies, this.boolSort, null, tla_atom, NoSet);
			Z3Node op0 = this.eval(args[0], c, control),
					op1 = this.eval(args[1], c, control);			
			node.addOperand(op0);
			node.addOperand(op1);
			this.checker.boolOperator_check(node);
			return node;
		}
		case OPCODE_equiv: {	
			node = new Z3Node("=", OPCODE_eq, this.boolSort, null, tla_atom, NoSet);
			Z3Node op0 = this.eval(args[0], c, control),
					op1 = this.eval(args[1], c, control);
			node.addOperand(op0);
			node.addOperand(op1);
			this.checker.boolOperator_check(node);
			return node;			
		}
		case OPCODE_noteq: {
			node = new Z3Node(NoName, OPCODE_noteq, this.boolSort, null, tla_atom, NoSet);
			Z3Node op0 = this.eval(args[0], c, control),
					op1 = this.eval(args[1], c, control);				
			node.addOperand(op0);
			node.addOperand(op1);		
			this.checker.unifySort_equivSort(op0, op1);
			return node;
		}
		case OPCODE_in: {
			node = new Z3Node(NoName, OPCODE_in, this.boolSort, null, tla_atom, NoSet);
			Z3Node x = this.eval(args[0], c, control),
					S = this.eval(args[1], c, control);								
			node.addOperand(x);
			node.addOperand(S);						
			this.checker.in_check(node);			
			return node;
		}
		case OPCODE_notin: {					
			node = new Z3Node(NoName, OPCODE_notin, this.boolSort, null, tla_atom, NoSet);
			Z3Node x = this.eval(args[0], c, control),
					S = this.eval(args[1], c, control);						
			node.addOperand(x);
			node.addOperand(S);
			this.checker.notin_check(node);
			return node;
		}		 				 
		case OPCODE_subseteq: {
			node = new Z3Node(NoName, OPCODE_subseteq, this.boolSort, null, tla_atom, NoSet);
			Z3Node S = this.eval(args[0], c, control),
					T = this.eval(args[1], c, control);
			node.addOperand(S);			
			node.addOperand(T);			
			return node;
		}		 				
		case OPCODE_setdiff: {
			node = new Z3Node(NoName, OPCODE_setdiff, null, null, tla_set, iNull);
			Z3Node T = this.eval(args[0], c, control),
					U = this.eval(args[1], c, control);
			node.addOperand(T);
			node.addOperand(U);	
			this.checker.setdiff_check(node);			
			return node;
		}
		case OPCODE_cap:  {
			node = new Z3Node(NoName, OPCODE_cap, null, null, tla_set, iNull);
			Z3Node T = this.eval(args[0], c, control),
					U = this.eval(args[1], c, control);
			node.addOperand(T);
			node.addOperand(U);	
			this.checker.cap_check(node);			
			return node;
		}
		case OPCODE_cup: {					
			node = new Z3Node(NoName, OPCODE_cup, null, null, tla_set, iNull);
			Z3Node T = this.eval(args[0], c, control),
					U = this.eval(args[1], c, control);
			node.addOperand(T);
			node.addOperand(U);	
			this.checker.setdiff_check(node);			
			return node;
		}
		case OPCODE_prime: {		
			Z3Node tmp = null;
			if (EvalControl.isEnabled(control)) {
				// We are now in primed and enabled.
				tmp = this.eval(args[0], c, EvalControl.setPrimed(control));
			}
			else {
				tmp = this.eval(args[0], c, control);
			}						
			String name = "p_" + tmp.name;
			int index = this.getVarIndex(name);
			if (index >= 0) {
				node = this.varList[index];
			}
			else {
				Assert.fail(NoIdErr, "No a primed variable: " + name);
			}
			return node;
		}
		case OPCODE_unchanged: {
//			node.addOperand(this.eval(args[0], c, EvalControl.setPrimed(control)));
//			node = (this.eval(args[0], c, EvalControl.setPrimed(control)));
//			node.setSort(this.boolSort);
			node = this.processUnchanged(args[0], ActionItemList.Empty, c);
			return node;
		}			
		// Remove OPCODE_aa, OPCODE_sa, OPCODE_cdot, OPCODE_sf, OPCODE_wf, OPCODE_te, OPCODE_tf
		// Remove OPCODE_leadto, OPCODE_arrow, OPCODE_box, OPCODE_diamond
		default:
		{		
			return null;
		}
		}
	}

  // Remove state, s1, nss and change  StateVec to Z3Node
	private final Z3Node getNextStates(Action action) {
		ActionItemList acts = ActionItemList.Empty;
		return this.getNextStates(action.pred, acts, action.con);		
	}

	// Remove s0, s1, nss, APSubstInKind
	// Change TLCState to Z3Node
	private final Z3Node getNextStates(SemanticNode pred, ActionItemList acts, Context c) {
		switch (pred.getKind()) {
		case OpApplKind:
		{
			OpApplNode pred1 = (OpApplNode)pred;
			return this.getNextStatesAppl(pred1, acts, c);
		}
		case LetInKind:
		{
			LetInNode pred1 = (LetInNode)pred;
			return this.getNextStates(pred1.getBody(), acts, c);
		}
		case SubstInKind:
		{
			SubstInNode pred1 = (SubstInNode)pred;
			Subst[] subs = pred1.getSubsts();
			int slen = subs.length;
			Context c1 = c;
			for (int i = 0; i < slen; i++) {
				Subst sub = subs[i];
				// There is no value, we just bind sub.getOp() with sub.getExpr().
				c1 = c1.cons(sub.getOp(), sub.getExpr());
			}
			return this.getNextStates(pred1.getBody(), acts, c1);
		}
		/***********************************************************************
		 * LabelKind class added by LL on 13 Jun 2007.                          *
		 ***********************************************************************/
		case LabelKind:
		{
			LabelNode pred1 = (LabelNode)pred;
			return this.getNextStates(pred1.getBody(), acts, c);
		}
		default:
		{
			Assert.fail(NotBoolErr, "The next state relation is not a boolean expression.\n" + pred);
		}
		}
		return null;
	}
	
	// Remove s0, s1, nss
	// Change TLCState to Z3Value
	private final Z3Node getNextStates(ActionItemList acts) {
		Z3Node node = null;
		if (acts.isEmpty()) {
			return null;
		}
		else {
			int kind = acts.carKind();
			SemanticNode pred = acts.carPred();
			Context c = acts.carContext();
			ActionItemList acts1 = acts.cdr();
			if (kind > 0) {
				if (this.tool.callStack != null) this.tool.callStack.push(pred);
				node = this.getNextStates(pred, acts1, c);
				if (this.tool.callStack != null) this.tool.callStack.pop();       
			}
			else if (kind == -1) {
				node = this.getNextStates(pred, acts1, c);
			}
			else if (kind == -2) {
				node = this.processUnchanged(pred, acts1, c);
			}
			else {
				Z3Node tmp1 = this.eval(pred, c);
				Z3Node tmp2 = this.getNextStates(acts1);
				if (tmp2 != null) {
					node = new Z3Node("and", OPCODE_land, this.boolSort, null, tmp1, tmp2, tla_atom, NoSet);								
				}
				else {
					node = tmp1;
				}
			}
		}
		return node;
	}
	
	// Remove s0, s1, nss, ThmOrAssumpDefNode, cdot, aa, sa
	// Change TLCState to Z3Node
	// Change resState in TLCState to tmp in Z3Node
	private final Z3Node getNextStatesAppl(OpApplNode pred, ActionItemList acts, Context c) {
		ExprOrOpArgNode[] args = pred.getArgs();
		int alen = args.length;
		SymbolNode opNode = pred.getOperator();
		int opcode = BuiltInOPs.getOpCode(opNode.getName());
		Z3Node node = new Z3Node(NoName, NoCode, null, null, NoKind, iNull);
		
		if (opcode == 0) {
			// This is a user-defined operator with one exception: it may
			// be substed by a builtin operator. This special case occurs
			// when the lookup returns an OpDef with opcode # 0.
			// Remove s0 because we do not evaluate any s0.
			// Therefore, lookup(opNode, c, s0, false) becomes lookup(opNode, c, false).
			// Fortuanately, lookup(opNode, c, false) does not have any value because
			// we do not evaluate any expression.
			// However, since TLA+ have many "user" defined operators, 
			// we still need to look up their meanings.
			Object val = this.lookup(opNode, c, false);
			
			if (val instanceof LazyValue) {
				LazyValue lv = (LazyValue)val;
				return this.getNextStates(lv.expr, acts, lv.con);					
			}

			if (val instanceof OpDefNode) {
				OpDefNode opDef = (OpDefNode)val;
				opcode = BuiltInOPs.getOpCode(opDef.getName());
				if (opcode == 0) {
					// Context c1 = this.getOpContext(opDef, args, c, false);
					if (opDef.getName().toString().equals("IsAFcn")) {
						Z3Node var = this.getNextStates(args[0], acts, c);
						node = new Z3Node("IsAFcn", OPCODE_IsAFcn, this.boolSort, null, var, tla_atom, NoSet);
						return node;
						
					}
					else {
						Context c1 = this.tool.getOpContext(opDef, args, c, true);   
						return this.getNextStates(opDef.getBody(), acts, c1);
					}					
				}
			}
					
			if (alen == 0) {
				if (val instanceof MethodValue) {					
					// I guess I need to translate this node if MethodValue is Int, 
					// or Boolean.					
					node.name = ((MethodValue) val).md.getName();						
					if (node.name.equals("Nat") || node.name.equals("Int")) {
						node = this.setIntSort;							
					}
					else if (node.name.equals("BOOLEAN") || node.name.equals("Bool")) {
						node = this.setBoolSort;							
					}
					return node;
				}
			}
			else {
				if (val instanceof OpValue) {
					node.name = opNode.getName().toString();
					// Change the sort of argVals from Value to Z3Node
					Z3Node[] argVals = new Z3Node[alen];
					Z3Node elemSort = null;
					// evaluate the actuals:
					// evaluate the arguments of the operator.
					for (int i = 0; i < alen; i++) {
						// Again, remove s0 and s1
						argVals[i] = this.eval(args[i], c, EvalControl.Clear);						
						if (elemSort == null && argVals[i].getSort() != null) {
							elemSort = argVals[i].getSort();
						}
						node.addOperand(argVals[i]);
					}	
					// If the operator is the integral interval, we need to generate all
					// numbers between n1 and n2.
					if (node.name.equals(OP_dotdot.toString()) || node.name.equals("DotDot")) {
						this.checker.dd_check(node);						
						node = new Z3Node(NoName, OPCODE_se, this.setIntSort, null, tla_set, 1);
						node.isDotDot = true;								
						int n1 = Integer.parseInt(argVals[0].name);
						int n2 = Integer.parseInt(argVals[1].name);
						// Add the current argument to the node's list of arguments.
						for (int i = n1; i <= n2; i++) {
							String name = Integer.toString(i);
							Z3Node node1 = new Z3Node(name, OPCODE_const, this.intSort, null, tla_atom, NoSet);
							node.addOperand(node1);
						}
					}
					else if (node.name.equals("-.")) {
						String name = "-" + argVals[0].name;
						node = new Z3Node(name, OPCODE_const, this.intSort, null, tla_atom, NoSet);
					}
					else {
						// In SMT-LIB, modulo (%) is replaced with "mod" 
						// and integer division "\\div" is replaced with "div".
						if (node.name.equals("%")) {
							node.name = "mod";
							node.opCode = OPCODE_mod;
						}
						else if (node.name.equals("\\div")) {
							node.name = "div";				
							node.opCode = OPCODE_div;
						}
						else if (node.name.equals("\\geq")) {
							node.name = ">=";
							node.opCode = OPCODE_ge;
						}
						else if (node.name.equals("\\leq")) {
							node.name = "<=";
							node.opCode = OPCODE_le;
						}
						else if (node.name.equals("<")) {
							this.checker.IntsBool_check(node);
							node.opCode = OPCODE_lt;							
						}
						else if (node.name.equals(">")) {							
							this.checker.IntsBool_check(node);
							node.opCode = OPCODE_gt;						
						}
						else if (node.name.equals("<=")) {							
							this.checker.IntsBool_check(node);
							node.opCode = OPCODE_le;						
						}
						else if (node.name.equals(">=")) {							
							this.checker.IntsBool_check(node);
							node.opCode = OPCODE_ge;							
						}
						else if (node.name.equals("mod")) {
							this.checker.IntsInt_check(node);
							node.opCode = OPCODE_mod;					
						}
						else if (node.name.equals("div")) {
							this.checker.IntsInt_check(node);
							node.opCode = OPCODE_div;	
						}
						else if (node.name.equals("+")) {
							this.checker.IntsInt_check(node);
							node.opCode = OPCODE_add;							
						}
						else if (node.name.equals("-")) {
							this.checker.IntsInt_check(node);
							node.opCode = OPCODE_sub;								
						}
						else if (node.name.equals("*")) {
							this.checker.IntsInt_check(node);
							node.opCode = OPCODE_mul;							
						}
						else {							
							node.setSort(elemSort);														
						}																		
						// We don't need to apply the operator.											
					}
				}
			}

			if (opcode == 0) {
				// Maybe it is unnecessary or only evalAppl needs it.
				if (node.name.equals(NoName)) {					
					node.name = pred.getOperator().getName().toString();
					if (node.name.equals("Nat") || node.name.equals("Int")) {
						node = this.setIntSort;
					}						
					else if (node.name.equals("BOOLEAN") || node.name.equals("Bool")) {
						node = this.setBoolSort;
					}			
					else if (node.name.equals("TRUE")) {
						node = new Z3Node("true", OPCODE_true, this.boolSort, null, tla_atom, NoSet);
					}
					else if (node.name.equals("FALSE")) {
						node = new Z3Node("false", OPCODE_false, this.boolSort, null, tla_atom, NoSet);
					}				
				}
				if (((SymbolNode) opNode).getKind() == VariableDeclKind) {
					int index = this.getVarIndex(node.name);
					if (index >= 0) {
						node = this.varList[index];												
					}			
				}
				// Maybe it is unnecessary or only evalAppl needs it.
				if (opNode instanceof FormalParamNode && !(val instanceof IntValue) && !(val instanceof BoolValue)) {
					node = this.getZ3FormalParamNode(node).clone();
				}
				Z3Node tmp = this.getNextStates(acts);  
				// Because TLC does not detect any error, it always calls getNextStates(acts)
				if (tmp == null) {
					return node;
				}
				else {
					Z3Node res =  new Z3Node("and", OPCODE_land, this.boolSort, null, node, tmp, tla_atom, NoSet);
					this.checker.boolOperator_check(res);
					return res; 				
				}
			}
		}
		
		node.opCode = opcode;		
		switch (opcode) {
		case OPCODE_cl:     			// ConjList
		case OPCODE_land: {
			// We replace OPCODE_cl with OPCODE_land.
			node = new Z3Node("and", OPCODE_land, this.boolSort, null, tla_atom, NoSet);			
			Z3Node operand = null;
			for (int i = 0; i < alen; i++) {
				// Use tlc2.tool
				if (this.tool.callStack != null) this.tool.callStack.push(args[i]);
				// Add a new operand
				operand = this.getNextStates(args[i], acts, c);				
				node.addOperand(operand);				
				// We don't need to show TLC errors.
				// Use tlc2.tool
				if (this.tool.callStack != null) this.tool.callStack.pop();
			}
			this.checker.boolOperator_check(node);
			Z3Node tmp1 = this.getNextStates(acts);
			if (tmp1 != null) {
				Z3Node tmp2 = new Z3Node("and", OPCODE_land, this.boolSort, null, node, tmp1, tla_atom, NoSet);
				this.checker.boolOperator_check(tmp2);
				return tmp2;
			}
			return node;
		}
		case OPCODE_dl:     			// DisjList
		case OPCODE_lor: {				
			// We replace OPCODE_cl with OPCODE_land.
			node = new Z3Node("or", OPCODE_lor, this.boolSort, null, tla_atom, NoSet);			
			Z3Node operand = null;
			for (int i = 0; i < alen; i++) {
				// Use tlc2.tool
				if (this.tool.callStack != null) this.tool.callStack.push(args[i]);
				// Add a new operand
				operand = this.getNextStates(args[i], acts, c);				
				node.addOperand(operand);				
				// We don't need to show TLC errors.
				// Use tlc2.tool
				if (this.tool.callStack != null) this.tool.callStack.pop();
			}
			this.checker.boolOperator_check(node);
			Z3Node tmp1 = this.getNextStates(acts);
			if (tmp1 != null) {
				Z3Node tmp2 = new Z3Node("and", OPCODE_land, this.boolSort, null, node, tmp1, tla_atom, NoSet);
				this.checker.boolOperator_check(tmp2);
				return tmp2;
			}
			return node;	
		}
		case OPCODE_be: {    // BoundedExists	
			node = new Z3Node("exists", OPCODE_be, this.boolSort, null, tla_atom, NoSet);		
			// Instead of evaluating possible values of bounded variables,
			// we need to know only their names and domains.
			// Since our formula is \A x \in S. p(x), all formals, isTuples, and   
			// domains have only one element formals[0][0], isTuples[0], and 
			// domains[0]. We will support \A x1 \in S1, x2 \in S2, ... later.		
			FormalParamNode[][] formals = pred.getBdedQuantSymbolLists();			
			ExprNode[] domains = pred.getBdedQuantBounds();
			Z3Node x = this.eval(formals[0][0], c, EvalControl.Clear), 
					S = this.eval(domains[0], c, EvalControl.Clear);
			this.checker.unifySort_in(x, S);
			x.opCode = OPCODE_bv;
			this.z3FormalParamNodes.add(x.clone());
			SemanticNode body = args[0];
//			Z3Node z3Body = this.eval(body , c, EvalControl.Clear);
//			z3Body.setSort(this.boolSort);
//			node.addBoundedVar(x);
			Z3Node z3Body = this.eval(body, c, EvalControl.Clear),
					bvar = this.z3Tool.createBoundedVar();
			this.checker.unifySort_equivSort(x, bvar);
			this.z3Tool.replaceNode(x.name, z3Body, bvar);
			z3Body.setSort(this.boolSort);
			node.addBoundedVar(bvar);
			node.addDomain(S);			
			node.addExpr(z3Body);
			this.z3FormalParamNodes.remove(this.z3FormalParamNodes.size() - 1);
			this.checker.be_check(node);
			// Need to check			
			Z3Node tmp1 = this.getNextStates(acts);
			if (tmp1 != null) {
				Z3Node tmp2 = new Z3Node("and", OPCODE_land, this.boolSort, null, node, tmp1, tla_atom, NoSet);
				this.checker.boolOperator_check(tmp2);
				return tmp2;
			}
			return node;
		}
		case OPCODE_bf: {    // BoundedForall	
			node = new Z3Node("forall", OPCODE_bf, this.boolSort, null, tla_atom, NoSet);
			// Instead of evaluating possible values of bounded variables,
			// we need to know only their names and domains.
			// Since our formula is \A x \in S. p(x), all formals, isTuples, and   
			// domains have only one element formals[0][0], isTuples[0], and 
			// domains[0]. We will support \A x1 \in S1, x2 \in S2, ... later.
			FormalParamNode[][] formals = pred.getBdedQuantSymbolLists();			
			ExprNode[] domains = pred.getBdedQuantBounds();
			Z3Node x = this.eval(formals[0][0], c, EvalControl.Clear), 
					S = this.eval(domains[0], c, EvalControl.Clear);
			this.checker.unifySort_in(x, S);
			x.opCode = OPCODE_bv;
			this.z3FormalParamNodes.add(x.clone());
			SemanticNode body = args[0];
//			Z3Node z3Body = this.eval(body , c, EvalControl.Clear);
//			z3Body.setSort(this.boolSort);
//			node.addBoundedVar(x);
			Z3Node z3Body = this.eval(body, c, EvalControl.Clear),
					bvar = this.z3Tool.createBoundedVar();
			this.checker.unifySort_equivSort(x, bvar);
			this.z3Tool.replaceNode(x.name, z3Body, bvar);
			z3Body.setSort(this.boolSort);
			node.addBoundedVar(bvar);
			node.addDomain(S);			
			node.addExpr(z3Body);
			this.z3FormalParamNodes.remove(this.z3FormalParamNodes.size() - 1);
			this.checker.bf_check(node);
			// Need to check			
			Z3Node tmp1 = this.getNextStates(acts);
			if (tmp1 != null) {
				Z3Node tmp2 = new Z3Node("and", OPCODE_land, this.boolSort, null, node, tmp1, tla_atom, NoSet);
				this.checker.boolOperator_check(tmp2);
				return tmp2;
			}
			return node;
		}
		case OPCODE_fa: {    // FcnApply		
			// Since there is no corresponding part in SMT-LIB, node's name is empty.
			node = new Z3Node(NoName, OPCODE_fa, null, null, NoKind, iNull);
			Z3Node fcn = this.eval(args[0], c, EvalControl.KeepLazy),
					arg = this.eval(args[1], c, EvalControl.Clear);
			node.addOperand(fcn);
			node.addOperand(arg);					
			this.checker.fa_check(node);
			// Need to check			
			Z3Node tmp1 = this.getNextStates(acts);
			if (tmp1 != null) {
				Z3Node tmp2 = new Z3Node("and", OPCODE_land, this.boolSort, null, node, tmp1, tla_atom, NoSet);
				this.checker.boolOperator_check(tmp2);
				return tmp2;
			}											
			return node;
		}
		// Remove OPCODE_aa, OPCODE_sa
		case OPCODE_ite: {   // IfThenElse		
			node = new Z3Node("ite", OPCODE_ite, null, null, NoKind, iNull);
			Z3Node con = this.eval(args[0], c,  EvalControl.Clear),
					action1 = this.getNextStates(args[1], ActionItemList.Empty, c),
					action2 = this.getNextStates(args[2], ActionItemList.Empty, c);			
			node.addOperand(con);
			node.addOperand(action1);
			node.addOperand(action2);
			this.checker.ite_check(node);			
			Z3Node tmp1 = this.getNextStates(acts);
			if (tmp1 != null) {
				Z3Node tmp2 = new Z3Node("and", OPCODE_land, this.boolSort, null, node, tmp1, tla_atom, NoSet);
				this.checker.boolOperator_check(tmp2);
				return tmp2;
			}				
			return node;
		}
		case OPCODE_case: {  // Case		
			// Since there is no corresponding part in SMT-LIB, node's name is empty.
			node = new Z3Node("ite", OPCODE_ite, null, null, NoKind, iNull);				
			Z3Node cur = node;
			OpApplNode pair;	
			pair = (OpApplNode)args[alen - 2];
			ExprOrOpArgNode[] pairArgs = pair.getArgs();
			Z3Node con = this.eval(pairArgs[0], c, EvalControl.Clear),
					action1 = this.eval(pairArgs[1], c, EvalControl.Clear);			
			// The last one does not have the condition
			pair = (OpApplNode)args[alen - 1];
			pairArgs = pair.getArgs();
			Z3Node action2 = this.eval(pairArgs[1], c, EvalControl.Clear);				
			cur.addOperand(con);
			cur.addOperand(action1);			
			cur.addOperand(action2);
			this.checker.ite_check(node);
			for (int i = alen - 2; i >= 0; i--) {
				pair = (OpApplNode)args[i];
				pairArgs = pair.getArgs();
				con = this.eval(pairArgs[0], c, EvalControl.Clear);
				action1 = this.eval(pairArgs[1], c, EvalControl.Clear);
				node = new Z3Node("ite", OPCODE_ite, cur.getSort(), null, action1, cur, NoKind, iNull);
				this.checker.ite_check(node);
			}
			node.passSortInfo();	
			Z3Node tmp1 = this.getNextStates(acts);
			if (tmp1 != null) {
				Z3Node tmp2 = new Z3Node("and", OPCODE_land, this.boolSort, null, node, tmp1, tla_atom, NoSet);
				this.checker.boolOperator_check(tmp2);
				return tmp2;
			}
			return node;			
		}
		case OPCODE_eq: {
			node = new Z3Node("=", OPCODE_eq, this.boolSort, null, tla_atom, NoSet);			
			SymbolNode var = this.tool.getPrimedVar(args[0], c, false);
			// The lhs is unprimed
			if (var == null) {
				return this.eval(pred, c, EvalControl.Clear);				
			}
			// The lhs is primed
			else {
				String name = "p_" + var.getName().toString();
				Z3Node lhs = null, rhs = null;
				int index = this.getVarIndex(name);
				if (index >= 0) {
					lhs = this.varList[index];												
				}			
				rhs = this.eval(args[1], c, EvalControl.Clear);				
				node.addOperand(lhs);
				node.addOperand(rhs);
				this.checker.eq_check(node);
				Z3Node tmp1 = this.getNextStates(acts);
				if (tmp1 != null) {
					Z3Node tmp2 = new Z3Node("and", OPCODE_land, this.boolSort, null, node, tmp1, tla_atom, NoSet);
					this.checker.boolOperator_check(tmp2);
					return tmp2;
				}						
				return node;				
			}
		}
		case OPCODE_in: {
			node = new Z3Node(NoName, OPCODE_in, this.boolSort, null, tla_atom, NoSet);
			// Since there is no corresponding part in SMT-LIB, node's name is empty.
			// The lhs is unprimed
			SymbolNode var = this.tool.getPrimedVar(args[0], c, false);			     
			if (var == null) {
				return this.eval(pred, c, EvalControl.Clear);				
			}
			// The lhs is primed
			else {
				String name = "p_" + var.getName().toString();
				Z3Node lhs = null, rhs = null;
				int index = this.getVarIndex(name);
				if (index >= 0) {
					lhs = this.varList[index];												
				}			
				rhs = this.eval(args[1], c, EvalControl.Clear);				
				node.addOperand(lhs);
				node.addOperand(rhs);
				this.checker.in_check(node);			
				Z3Node tmp1 = this.getNextStates(acts);
				if (tmp1 != null) {
					Z3Node tmp2 = new Z3Node("and", OPCODE_land, this.boolSort, null, node, tmp1, tla_atom, NoSet);
					this.checker.boolOperator_check(tmp2);
					return tmp2;
				}						
			}
			return node;
		}
		case OPCODE_implies: {
			node = new Z3Node("=>", OPCODE_implies, this.boolSort, null, tla_atom, NoSet);
			Z3Node lhs = this.eval(args[0], c, EvalControl.Clear),
					rhs = this.eval(args[1], c, EvalControl.Clear);			
			node.addOperand(lhs);
			node.addOperand(rhs);
			this.checker.boolOperator_check(node);
			Z3Node tmp1 = this.getNextStates(acts);
			if (tmp1 != null) {
				Z3Node tmp2 = new Z3Node("and", OPCODE_land, this.boolSort, null, node, tmp1, tla_atom, NoSet);
				this.checker.boolOperator_check(tmp2);
				return tmp2;
			}							
			return node;			
		}
		case OPCODE_unchanged: {
			return this.processUnchanged(args[0], acts, c);
		}
		// Remove OPCODE_cdot
		// The following case added by LL on 13 Nov 2009 to handle subexpression names.
		case OPCODE_nop: {
			return this.getNextStates(args[0], acts, c); 
		}
		default:
		{
			// We handle all the other builtin operators here.
			node = this.eval(pred, c, EvalControl.Clear);
			Z3Node tmp1 = this.getNextStates(acts);
			if (tmp1 != null) {
				Z3Node tmp2 = new Z3Node("and", OPCODE_land, this.boolSort, null, node, tmp1, tla_atom, NoSet);
				this.checker.boolOperator_check(tmp2);
				return tmp2;				
			}		
			return node;
		}
		}	
 }	
	
	// Remove s0, s1, nss, LazyValue
	// Change TLCState to Z3Node
	private final Z3Node processUnchanged(SemanticNode expr, ActionItemList acts, Context c) {
		SymbolNode var = this.tool.getVar(expr, c, false);		
		if (var != null) {
			// expr is a state variable:
			String rhsName = var.getName().toString(),
					lhsName = "p_" + rhsName;
			int lIndex = this.getVarIndex(lhsName),
					rIndex = this.getVarIndex(rhsName);
			if (lIndex < 0 || rIndex < 0) {
				Assert.fail(NoIdErr, rhsName + " " + lhsName + " are not existed.");												
			}			
			Z3Node rhs = this.varList[rIndex],												
					lhs  = this.varList[lIndex],
					node = new Z3Node("=", OPCODE_eq, this.boolSort, null, lhs, rhs, tla_atom, NoSet),
					tmp  = this.getNextStates(acts);			
			if (tmp != null) {
				Z3Node res = new Z3Node("and", OPCODE_land, this.boolSort, null, node, tmp, tla_atom, NoSet);
				this.checker.boolOperator_check(res);
				return res;
			}
			return node;
		}
		if (expr instanceof OpApplNode) {
			OpApplNode expr1 = (OpApplNode)expr;
			ExprOrOpArgNode[] args = expr1.getArgs();
			int alen = args.length;
			SymbolNode opNode = expr1.getOperator();
			UniqueString opName = opNode.getName();
			int opcode = BuiltInOPs.getOpCode(opName);

			if (opcode == OPCODE_tup) {
				// a tuple:
				if (alen != 0) {
					ActionItemList acts1 = acts;
					for (int i = alen-1; i > 0; i--) {
						acts1 = acts1.cons(args[i], c, -2);
					}
					return this.processUnchanged(args[0], acts1, c);
				}
				return this.getNextStates(acts);
			}

			if (opcode == 0 && alen == 0) {
				// a 0-arity operator:
				// Do not look up, just use opNode.
				// However, since TLA+ have many "user" defined operators, 
				// we still need to look up their meanings.
				Object val = this.lookup(opNode, c, false);


				if (val instanceof OpDefNode) {
					return this.processUnchanged(((OpDefNode)val).getBody(), acts, c);
				}
				else {
					Assert.fail(NoIdErr, "In computing next states, we found the identifier\n" +
							opName + " undefined in an UNCHANGED expression at\n" + expr);
				}
				return this.getNextStates(acts);
			}
		}

		Z3Node tmp1 = this.eval(expr, c, EvalControl.Clear);
		Z3Node tmp2 = this.getNextStates(acts);
		if (tmp2 != null) {
			return new Z3Node("and", OPCODE_land, this.boolSort, null, tmp1, tmp2, tla_atom, NoSet);						
		}
		else {
			return tmp1;
		}		
	}
	
	private final Z3Node getInitStates(SemanticNode init, ActionItemList acts, Context c) {
		switch (init.getKind()) {
		case OpApplKind:
		{
			OpApplNode init1 = (OpApplNode)init;
			return this.getInitStatesAppl(init1, acts, c);			
		}
		case LetInKind:
		{
			LetInNode init1 = (LetInNode)init;
			return this.getInitStates(init1.getBody(), acts, c);			
		}
		case SubstInKind:
		{
			SubstInNode init1 = (SubstInNode)init;
			Subst[] subs = init1.getSubsts();
			Context c1 = c;
			for (int i = 0; i < subs.length; i++) {
				Subst sub = subs[i];
				// There is no value to get here.
				// We just bind sub.getOp() with sub.getExpr().
				c1 = c1.cons(sub.getOp(), sub.getExpr());
			}
			return this.getInitStates(init1.getBody(), acts, c1);			
		}

		// Remove APSubstInKind
		
		/***********************************************************************
		 * LabelKind class added by LL on 13 Jun 2007.                          *
		 ***********************************************************************/
		case LabelKind:
		{
			LabelNode init1 = (LabelNode)init;
			return this.getInitStates(init1.getBody(), acts, c);			
		}
		default:
		{
			return null;
		}
		}
	}

	private final Z3Node getInitStates(ActionItemList acts) {
		if (acts.isEmpty()) {
			return null;
		}
		else {
			// Assert.check(act.kind > 0 || act.kind == -1);
			ActionItemList acts1 = acts.cdr();
			return this.getInitStates(acts.carPred(), acts1, acts.carContext());
		}
	}

	private final Z3Node getInitStatesAppl(OpApplNode init, ActionItemList acts, Context c) {
		ExprOrOpArgNode[] args = init.getArgs();
		int alen = args.length;
		SymbolNode opNode = init.getOperator();
		int opcode = BuiltInOPs.getOpCode(opNode.getName());
		Z3Node node = new Z3Node(NoName, NoCode, null, null, NoKind, iNull);

		if (opcode == 0) {
			// This is a user-defined operator with one exception: it may
			// be substed by a builtin operator. This special case occurs
			// when the lookup returns an OpDef with opcode # 0.
			// Since we don't evaluate states and constants, we don't need to look up 
			// the value in context, states s0 and s1.
			// However, since TLA+ have many "user" defined operators, 
			// we still need to look up their meanings.
			Object val = this.lookup(opNode, c, false);
			
			if (val instanceof LazyValue) {
				LazyValue lv = (LazyValue)val;
				return this.getInitStates(lv.expr, acts, lv.con);					
			}

			if (val instanceof OpDefNode) {
				OpDefNode opDef = (OpDefNode)val;
				opcode = BuiltInOPs.getOpCode(opDef.getName());				
				if (opcode == 0) {
					// Context c1 = this.getOpContext(opDef, args, c, false);
					if (opDef.getName().toString().equals("IsAFcn")) {
						Z3Node var = this.getInitStates(args[0], acts, c);
						node = new Z3Node("IsAFcn", OPCODE_IsAFcn, this.boolSort, null, var, tla_atom, NoSet);
						return node;
					}
					else {
						Context c1 = this.tool.getOpContext(opDef, args, c, true);   
						return this.getInitStates(opDef.getBody(), acts, c1);
					}					
				}				
			}
			
			// Remove ThmOrAssumpDefNode since we do not support theoroms and assumptions.
			
			if (alen == 0) {
				if (val instanceof MethodValue) {
				// I guess I need to translate this node if MethodValue is Int, 
					// or Boolean.					
					node.name = ((MethodValue) val).md.getName();						
					if (node.name.equals("Nat") || node.name.equals("Int")) {
						node = this.setIntSort;							
					}
					else if (node.name.equals("BOOLEAN") || node.name.equals("Bool")) {
						node = this.setBoolSort;							
					}
					return node;
				}
			}
			else {
				if (val instanceof OpValue) {
					node.name = opNode.getName().toString();
					// Change the sort of argVals from Value to Z3Node
					Z3Node[] argVals = new Z3Node[alen];
					Z3Node elemSort = null;
					// evaluate the actuals:
					// evaluate the arguments of the operator.
					for (int i = 0; i < alen; i++) {
						// Again, remove s0 and s1
						argVals[i] = this.eval(args[i], c, EvalControl.Clear);						
						if (elemSort == null && argVals[i].getSort() != null) {
							elemSort = argVals[i].getSort();
						}
						node.addOperand(argVals[i]);
					}	
					// If the operator is the integral interval, we need to generate all
					// numbers between n1 and n2.
					if (node.name.equals(OP_dotdot.toString()) || node.name.equals("DotDot")) {
						this.checker.dd_check(node);						
						node = new Z3Node(NoName, OPCODE_se, this.setIntSort, null, tla_set, 1);
						node.isDotDot = true;						
						int n1 = Integer.parseInt(argVals[0].name);
						int n2 = Integer.parseInt(argVals[1].name);
						// Add the current argument to the node's list of arguments.
						for (int i = n1; i <= n2; i++) {
							String name = Integer.toString(i);
							Z3Node node1 = new Z3Node(name, OPCODE_const, this.intSort, null, tla_atom, NoSet);
							node.addOperand(node1);
						}
					}
					else if (node.name.equals("-.")) {
						String name = "-" + argVals[0].name;
						node = new Z3Node(name, OPCODE_const, this.intSort, null, tla_atom, NoSet);
					}
					else {
						// In SMT-LIB, modulo (%) is replaced with "mod" 
						// and integer division "\\div" is replaced with "div".
						if (node.name.equals("%")) {
							node.name = "mod";
							node.opCode = OPCODE_mod;
						}
						else if (node.name.equals("\\div")) {
							node.name = "div";				
							node.opCode = OPCODE_div;
						}
						else if (node.name.equals("\\geq")) {
							node.name = ">=";
							node.opCode = OPCODE_ge;
						}
						else if (node.name.equals("\\leq")) {
							node.name = "<=";
							node.opCode = OPCODE_le;
						}
						else if (node.name.equals("<")) {
							this.checker.IntsBool_check(node);
							node.opCode = OPCODE_lt;							
						}
						else if (node.name.equals(">")) {							
							this.checker.IntsBool_check(node);
							node.opCode = OPCODE_gt;						
						}
						else if (node.name.equals("<=")) {							
							this.checker.IntsBool_check(node);
							node.opCode = OPCODE_le;						
						}
						else if (node.name.equals(">=")) {							
							this.checker.IntsBool_check(node);
							node.opCode = OPCODE_ge;							
						}
						else if (node.name.equals("mod")) {
							this.checker.IntsInt_check(node);
							node.opCode = OPCODE_mod;					
						}
						else if (node.name.equals("div")) {
							this.checker.IntsInt_check(node);
							node.opCode = OPCODE_div;	
						}
						else if (node.name.equals("+")) {
							this.checker.IntsInt_check(node);
							node.opCode = OPCODE_add;							
						}
						else if (node.name.equals("-")) {
							this.checker.IntsInt_check(node);
							node.opCode = OPCODE_sub;								
						}
						else if (node.name.equals("*")) {
							this.checker.IntsInt_check(node);
							node.opCode = OPCODE_mul;							
						}
						else {							
							node.setSort(elemSort);														
						}												
						// We don't need to apply the operator.											
					}
				}
			}

			if (opcode == 0) {
				// Maybe it is unnecessary or only evalAppl needs it.
				if (node.name.equals(NoName)) {					
					node.name = init.getOperator().getName().toString();
					if (node.name.equals("Nat") || node.name.equals("Int")) {
						node = this.setIntSort;
					}						
					else if (node.name.equals("BOOLEAN") || node.name.equals("Bool")) {
						node = this.setBoolSort;
					}							
				}
				if (((SymbolNode) opNode).getKind() == VariableDeclKind) {
					int index = this.getVarIndex(node.name);
					if (index >= 0) {
						node = this.varList[index];												
					}			
				}
				// Maybe it is unnecessary or only evalAppl needs it.
				if (opNode instanceof FormalParamNode && !(val instanceof IntValue) && !(val instanceof BoolValue)) {
					node = this.getZ3FormalParamNode(node).clone();
				}
				Z3Node tmp = this.getInitStates(acts); 
				// Because TLC does not detect any error, it always calls getInitStates(acts) 				
				if (tmp == null) {
					return node;
				}
				else {
					Z3Node res =  new Z3Node("and", OPCODE_land, this.boolSort, null, node, tmp, tla_atom, NoSet);
					this.checker.boolOperator_check(res);
					return res;
				}
			}
		}
		node.opCode = opcode;
		switch (opcode) {
		case OPCODE_dl:     // DisjList
		case OPCODE_lor: {
			// We replace OPCODE_dl with OPCODE_lor.
			node = new Z3Node("or", OPCODE_lor, this.boolSort, null, tla_atom, NoSet);			
			Z3Node operand = null;
			for (int i = 0; i < alen; i++) {
				// Use tlc2.tool
				if (this.tool.callStack != null) this.tool.callStack.push(args[i]);
				// Add a new operand
				operand = this.getInitStates(args[i], acts, c);				
				node.addOperand(operand);				
				// We don't need to show TLC errors.
				// Use tlc2.tool
				if (this.tool.callStack != null) this.tool.callStack.pop();
			}
			this.checker.boolOperator_check(node);
			Z3Node tmp1 = this.getInitStates(acts);
			if (tmp1 != null) {
				Z3Node tmp2 = new Z3Node("and", OPCODE_land, this.boolSort, null, node, tmp1, tla_atom, NoSet);
				this.checker.boolOperator_check(tmp2);
				return tmp2;
			}
			return node;			
		}
		case OPCODE_cl:     // ConjList
		case OPCODE_land: {			
			// We replace OPCODE_cl with OPCODE_land.
			node = new Z3Node("and", OPCODE_land, this.boolSort, null, tla_atom, NoSet);			
			Z3Node operand = null;
			for (int i = 0; i < alen; i++) {
				// Use tlc2.tool
				if (this.tool.callStack != null) this.tool.callStack.push(args[i]);
				// Add a new operand
				operand = this.getInitStates(args[i], acts, c);				
				node.addOperand(operand);				
				// We don't need to show TLC errors.
				// Use tlc2.tool
				if (this.tool.callStack != null) this.tool.callStack.pop();
			}
			this.checker.boolOperator_check(node);
			Z3Node tmp1 = this.getInitStates(acts);
			if (tmp1 != null) {
				Z3Node tmp2 = new Z3Node("and", OPCODE_land, this.boolSort, null, node, tmp1, tla_atom, NoSet);
				this.checker.boolOperator_check(tmp2);
				return tmp2;
			}
			return node;
		}
		case OPCODE_be: {   // BoundedExists		
			node = new Z3Node("exists", OPCODE_be, this.boolSort, null, tla_atom, NoSet);				
			// Instead of evaluating possible values of bounded variables,
			// we need to know only their names and domains.
			// Since our formula is \A x \in S. p(x), all formals, isTuples, and   
			// domains have only one element formals[0][0], isTuples[0], and 
			// domains[0]. We will support \A x1 \in S1, x2 \in S2, ... later.
			FormalParamNode[][] formals = init.getBdedQuantSymbolLists();			
			ExprNode[] domains = init.getBdedQuantBounds();
			Z3Node x = this.eval(formals[0][0], c, EvalControl.Clear), 
					S = this.eval(domains[0], c, EvalControl.Clear);
			this.checker.unifySort_in(x, S);
			x.opCode = OPCODE_bv;
			this.z3FormalParamNodes.add(x.clone());
			SemanticNode body = args[0];
//			Z3Node z3Body = this.eval(body , c, EvalControl.Clear);
//			z3Body.setSort(this.boolSort);
//			node.addBoundedVar(x);
			Z3Node z3Body = this.eval(body, c, EvalControl.Clear),
					bvar = this.z3Tool.createBoundedVar();
			this.checker.unifySort_equivSort(x, bvar);
			this.z3Tool.replaceNode(x.name, z3Body, bvar);
			z3Body.setSort(this.boolSort);
			node.addBoundedVar(bvar);
			node.addDomain(S);			
			node.addExpr(z3Body);
			this.z3FormalParamNodes.remove(this.z3FormalParamNodes.size() - 1);
			this.checker.be_check(node);
			// Need to check			
			Z3Node tmp1 = this.getInitStates(acts);
			if (tmp1 != null) {
				Z3Node tmp2 = new Z3Node("and", OPCODE_land, this.boolSort, null, node, tmp1, tla_atom, NoSet);
				this.checker.boolOperator_check(tmp2);
				return tmp2;
			}
			return node;
		}
		case OPCODE_bf: {    // BoundedForall
			node = new Z3Node("forall", OPCODE_bf, this.boolSort, null, tla_atom, NoSet);			
			// Instead of evaluating possible values of bounded variables,
			// we need to know only their names and domains.
			// Since our formula is \A x \in S. p(x), all formals, isTuples, and   
			// domains have only one element formals[0][0], isTuples[0], and 
			// domains[0]. We will support \A x1 \in S1, x2 \in S2, ... later.
			FormalParamNode[][] formals = init.getBdedQuantSymbolLists();			
			ExprNode[] domains = init.getBdedQuantBounds();
			Z3Node x = this.eval(formals[0][0], c, EvalControl.Clear), 
					S = this.eval(domains[0], c, EvalControl.Clear),
					sort = this.getElemSort(S);
			this.checker.unifySort_in(x, S);
			x.opCode = OPCODE_bv;
			this.z3FormalParamNodes.add(x.clone());
			SemanticNode body = args[0];
//			Z3Node z3Body = this.eval(body , c, EvalControl.Clear);
//			z3Body.setSort(this.boolSort);
//			node.addBoundedVar(x);
			Z3Node z3Body = this.eval(body, c, EvalControl.Clear),
					bvar = this.z3Tool.createBoundedVar();
			this.checker.unifySort_equivSort(x, bvar);
			this.z3Tool.replaceNode(x.name, z3Body, bvar);
			z3Body.setSort(this.boolSort);
			node.addBoundedVar(bvar);
			node.addDomain(S);			
			node.addExpr(z3Body);
			this.z3FormalParamNodes.remove(this.z3FormalParamNodes.size() - 1);
			this.checker.bf_check(node);
			// Need to check			
			Z3Node tmp1 = this.getInitStates(acts);
			if (tmp1 != null) {
				Z3Node tmp2 = new Z3Node("and", OPCODE_land, this.boolSort, null, node, tmp1, tla_atom, NoSet);
				this.checker.boolOperator_check(tmp2);
				return tmp2;
			}
			return node;
		}
		case OPCODE_ite: {   // IfThenElse		
			node = new Z3Node("ite", OPCODE_ite, null, null, NoKind, iNull);
			Z3Node con = this.eval(args[0], c),
					action1 = this.eval(args[1], c),
					action2 = this.eval(args[2], c);			
			node.addOperand(con);
			node.addOperand(action1);
			node.addOperand(action2);
			this.checker.ite_check(node);			
			Z3Node tmp1 = this.getInitStates(acts);
			if (tmp1 != null) {
				Z3Node tmp2 = new Z3Node("and", OPCODE_land, this.boolSort, null, node, tmp1, tla_atom, NoSet);
				this.checker.boolOperator_check(tmp2);
				return tmp2;
			}											
			return node;
		}
		case OPCODE_case: {  // Case		
			// Since there is no corresponding part in SMT-LIB, node's name is empty.			
			node = new Z3Node("ite", OPCODE_ite, null, null, NoKind, iNull);				
			Z3Node cur = node;
			OpApplNode pair;	
			pair = (OpApplNode)args[alen - 2];
			ExprOrOpArgNode[] pairArgs = pair.getArgs();
			Z3Node con = this.eval(pairArgs[0], c, EvalControl.Clear),
					action1 = this.eval(pairArgs[1], c, EvalControl.Clear);			
			// The last one does not have the condition
			pair = (OpApplNode)args[alen - 1];
			pairArgs = pair.getArgs();
			Z3Node action2 = this.eval(pairArgs[1], c, EvalControl.Clear);				
			cur.addOperand(con);
			cur.addOperand(action1);			
			cur.addOperand(action2);
			this.checker.ite_check(node);			
			for (int i = alen - 2; i >= 0; i--) {
				pair = (OpApplNode)args[i];
				pairArgs = pair.getArgs();
				con = this.eval(pairArgs[0], c);
				action1 = this.eval(pairArgs[1], c);
				node = new Z3Node("ite", OPCODE_ite, cur.getSort(), null, action1, cur, NoKind, iNull);
				this.checker.ite_check(node);
			}
			node.passSortInfo();
			Z3Node tmp1 = this.getInitStates(acts);
			if (tmp1 != null) {
				Z3Node tmp2 = new Z3Node("and", OPCODE_land, this.boolSort, null, node, tmp1, tla_atom, NoSet);
				this.checker.boolOperator_check(tmp2);
				return tmp2;
			}							
			return node;		
		}
		case OPCODE_fa: {    // FcnApply		
			// Since there is no corresponding part in SMT-LIB, node's name is empty.
			node = new Z3Node(NoName, OPCODE_fa, null, null, NoKind, iNull);
			Z3Node fcn = this.eval(args[0], c),
					arg = this.eval(args[1], c);
			node.addOperand(fcn);
			node.addOperand(arg);
			this.checker.fa_check(node);
			// Need to check						
			Z3Node tmp1 = this.getInitStates(acts);
			if (tmp1 != null) {
				Z3Node tmp2 = new Z3Node("and", OPCODE_land, this.boolSort, null, node, tmp1, tla_atom, NoSet);
				this.checker.boolOperator_check(tmp2);
				return tmp2;				
			}													
			return node;
		}
		case OPCODE_eq: {		
			node = new Z3Node("=", OPCODE_eq, this.boolSort, null, tla_atom, NoSet);			
			// We don't evaluate any expression; therefore, we don't need
			// to look up any value and check whether or not an expression 
			// is a variable.
			// There is no primed variables in Init.
			Z3Node lhs = this.eval(args[0], c),
					rhs = this.eval(args[1], c);
			node.addOperand(lhs);
			node.addOperand(rhs);
			this.checker.eq_check(node);
			Z3Node tmp1 = this.getInitStates(acts);
			if (tmp1 != null) {
				Z3Node tmp2 = new Z3Node("and", OPCODE_land, this.boolSort, null, node, tmp1, tla_atom, NoSet);
				this.checker.boolOperator_check(tmp2);
				return tmp2;				
			}													
			return node;						
		}
		case OPCODE_in:	{
			node = new Z3Node(NoName, OPCODE_in, this.boolSort, null, tla_atom, NoSet);
			// Since there is no corresponding part in SMT-LIB, node's name is empty.
			// We don't evaluate any expression; therefore, we don't need
			// to look up any value and check whether or not an expression 
			// is a variable.
			// There is no primed variables in Init.
			Z3Node lhs = this.eval(args[0], c),
					rhs = this.eval(args[1], c);
			node.addOperand(lhs);
			node.addOperand(rhs);
			this.checker.in_check(node);			
			Z3Node tmp1 = this.getInitStates(acts);
			if (tmp1 != null) {
				Z3Node tmp2 = new Z3Node("and", OPCODE_land, this.boolSort, null, node, tmp1, tla_atom, NoSet);
				this.checker.boolOperator_check(tmp2);
				return tmp2;				
			}													
			return node;					
		}
		case OPCODE_implies: {		
			node = new Z3Node("=>", OPCODE_implies, this.boolSort, null, tla_atom, NoSet);
			Z3Node lhs = this.eval(args[0], c, EvalControl.Clear),
					rhs = this.eval(args[1], c, EvalControl.Clear);			
			node.addOperand(lhs);
			node.addOperand(rhs);
			this.checker.boolOperator_check(node);
			Z3Node tmp1 = this.getInitStates(acts);
			if (tmp1 != null) {
				Z3Node tmp2 = new Z3Node("and", OPCODE_land, this.boolSort, null, node, tmp1, tla_atom, NoSet);
				this.checker.boolOperator_check(tmp2);
				return tmp2;				
			}							
			return node;	
		}
		// The following case added by LL on 13 Nov 2009 to handle subexpression names.
		case OPCODE_nop: {		
			return this.getInitStates(args[0], acts, c); 			
		}
		default: {
			node = this.eval(init, c);
			Z3Node tmp1 = this.getInitStates(acts);
			if (tmp1 != null) {
				Z3Node tmp2 = new Z3Node("and", OPCODE_land, this.boolSort, null, node, tmp1, tla_atom, NoSet);
				this.checker.boolOperator_check(tmp2);
				return tmp2;				
			}		
			return node;
		}
		}
	}		
	
	private final void createVarList() {
		// create vars
		int alen = this.tool.variablesNodes.length;
		for (int i = 0; i < alen; i++) {
			String varName1 = this.tool.variablesNodes[i].getName().toString(),
					varName2 = "p_" + varName1;
			this.sortVars(2 * i, varName1);
			this.sortVars(2 * i + 1, varName2);			
		}	
		for (int i = 0; i < 2 * alen; i++) {
			this.varList[i].opCode = OPCODE_var;
		}
	}
	
	private final void sortVars(int index, String name) {
		int pos = index;
		while (pos > 0) {
			if (this.varList[pos - 1].name.compareTo(name) > 0) {
				this.varList[pos].name  = this.varList[pos - 1].name;
				pos -= 1;
			}
			else {
				break;
			}
		}
		this.varList[pos].name = name;		
	}
	
	public final int getVarIndex(String name) {
		int left = 0, right = 2 * this.tool.variablesNodes.length - 1, middle, res;
		while (left <= right) {
			middle = (left + right) / 2;
			res = this.varList[middle].name.compareTo(name);
			if (res == 0)
				return middle;
			else if (res < 0) {
				left = middle + 1;
			}
			else {
				right = middle - 1;
			}	
		}		
		return -1;
	}
	
	private final Z3Node getVar(Z3Node node, String name) {
		if (!name.equals(NoName)) {
			int index = this.getVarIndex(name);
			if (index >= 0) {
				return this.varList[index];
			}
		}		
		return node;
	}
	
	private final void createTypeInfo_PrimedVars(Z3Node sortInfo) {
		Z3Node z3Node, z3LHS, z3dLHS, z3pLHS, z3RHS;
		int exprNo = sortInfo.getOperandSize();
		String name = "", pname = "";
		for (int i = 0; i < exprNo; i++) {
			z3Node  = sortInfo.getOperand(i).clone();
			if (z3Node.getOperandSize() == 2) {
				z3LHS = z3Node.getOperand(0);
				name = z3LHS.name;
				pname = "p_" + z3LHS.name;
				z3pLHS = this.getVar(z3LHS, pname);
				this.z3Tool.replaceNode(name, z3Node, z3pLHS);
				sortInfo.addOperand(z3Node);
			}						
		}
	}
	
	private final void getPrimitiveTypeInfo(Z3Node sortInfo) {
		Z3Node z3Node, z3LHS, z3dLHS, z3pLHS, z3RHS;		
		int exprNo = sortInfo.getOperandSize();
		for (int i = exprNo - 1; i >= 0; i--) {
			z3Node  = sortInfo.getOperand(i);
			z3LHS = z3Node.getOperand(0);
			z3dLHS = this.getVar(z3LHS, z3LHS.name);
			z3dLHS.setSort(z3LHS.getSort());											
			z3RHS = z3Node.getOperand(1);			
			z3RHS = this.getVar(z3RHS, z3RHS.name);
			switch (z3Node.opCode) {
			case OPCODE_in: {					
				// A primitive variable
				if (z3RHS.name.equals("Int") || z3RHS.name.equals("Bool")) {					
					z3dLHS.setSort(z3RHS.getElemSort());												
					// This sort info is contained in the declartion.
					sortInfo.removeOperand(i);
				}
				else {
					switch (z3RHS.opCode) {
					case OPCODE_se: {
						if (z3RHS.getOperandSize() > 0) {
							Z3Node op = z3RHS.getOperand(0);
							z3dLHS.setSort(op.getSort());													
						}
						break;
					}
					case OPCODE_sso: {
						Z3Node S = z3RHS.getDomain(0);
						z3dLHS.setSort(S.getElemSort());						
						break;
					}
					case OPCODE_soa: {
						Z3Node e = z3RHS.getExpr(0);
						z3dLHS.setSort(e.getSort());						
						break;
					}
					case OPCODE_subset: {
						Z3Node T = z3RHS.getOperand(0);						
						z3dLHS.setSort(T.getSort());												
						break;
					}
					case OPCODE_union: {
						Z3Node S = z3RHS.getOperand(0),
								T = S.getOperand(0);
						z3dLHS.setSort(T.getElemSort());												
						break;
					}
					case OPCODE_sof: {
						Z3Node S = z3RHS.getDomain(0),
								T = z3RHS.getRange(0);											
						if (S.getSort() != z3dLHS.getDomain(0).getSort() &&
								!S.getSort().name.equals(z3dLHS.getDomain(0).getSort().name)) {
							Assert.fail(ConstraintErr, "There is a sort confliction in the domain of " + z3dLHS.name + ".");
						}
						else {
							z3dLHS.setDomain(0, S);
						}
						if (T.getSort() != z3dLHS.getRange(0).getSort()) {
							Assert.fail(ConstraintErr, "There is a sort confliction in the range of " + z3dLHS.name + ".");
						}
						else {
							z3dLHS.setRange(0, T);
						}				
						z3dLHS.kind = tla_fcn;												
						break;
					}
					case OPCODE_sor: {
						z3dLHS.setSort(z3RHS.getElemSort());
						z3dLHS.kind = tla_rcd;						
						int alen = z3RHS.getFieldSize();
						if (z3dLHS.getDomain(0).getSort() != this.setStrSort) {
							Assert.fail(ConstraintErr, "The domain of" + z3dLHS.name + " is not a set of strings.");
						}
						for (int k = 0; k < alen; k++) {
							Z3Node field = z3RHS.getField(k),
									S = z3RHS.getRange(k);
							if (!field.name.equals(z3dLHS.getField(k).name)) {
								Assert.fail(ConstraintErr, "There is a confliction in the " + Integer.toString(k) + "-th field of" + z3dLHS.name + ".");
							}							
							if (S.getElemSort() != z3dLHS.getRange(k).getSort()) {
								Assert.fail(ConstraintErr, "There is a confliction in the " + Integer.toString(k) + "-th range of" + z3dLHS.name + ".");
							}
						}																	
						this.addStringVars(z3RHS);
						break;
					}
					case OPCODE_cp: {
						z3dLHS.setSort(z3RHS.getElemSort());
						z3dLHS.kind = tla_tup;												
						int alen = z3RHS.getOperandSize();
						if (z3dLHS.getDomain(0).getSort() != this.setIntSort) {
							Assert.fail(ConstraintErr, "The domain of" + z3dLHS.name + " is not a set of integers.");
						}
						for (int k = 0; k < alen; k++) {
							Z3Node field = new Z3Node(Integer.toString(k + 1), OPCODE_const, this.intSort, null, tla_atom, NoSet), 
									S = z3RHS.getOperand(k);							
							if (!field.name.equals(z3dLHS.getField(k).name)) {
								Assert.fail(ConstraintErr, "There is a confliction in the " + Integer.toString(k) + "-th field of" + z3dLHS.name + ".");
							}	
							if (S.getElemSort() != z3dLHS.getRange(k).getSort()) {
								Assert.fail(ConstraintErr, "There is a confliction in the " + Integer.toString(k) + "-th range of" + z3dLHS.name + ".");
							}																												
						}										
						break;
					}
					}
				}
				break;
			}
			case OPCODE_eq: {							
				// create new String variables
				if (z3LHS.name.equals("Str") && z3RHS.opCode == OPCODE_se) {
					int size = z3RHS.getOperandSize();					
					for (int pos = 0; pos < size; pos++) {
						this.addStringVar(z3RHS.getOperand(pos));
					}
					sortInfo.removeOperand(i);
				}							
				break;
			}
			default: {
				break;
			}
			}
			int pIndex = this.getVarIndex("p_" + z3dLHS.name);
			z3pLHS = z3dLHS.clone();
			z3pLHS.name = "p_" + z3dLHS.name;
			this.varList[pIndex] = z3pLHS;
		}				
	}
	
	private final Z3Node bindZ3Node(Z3Node node, boolean flag) {
		if (node != null) {
			int index = this.getVarIndex(node.name);
			if (index >= 0 && flag) {
				node = this.varList[index];
				// We don't want to bind a node with its original node twice.
				// Therefore, we call bindZ3Node with flag = false.
				if (flag) {
					this.bindZ3Node(node, false);
				}
				// We need to a cloned node, not an original node because we need to boolify later.
				return node.clone();
			}			
			int i;
			for (i = 0; i < node.getExprSize(); i++) {
				node.setExpr(i, this.bindZ3Node(node.getExpr(i), true));
			}
			for (i = 0; i < node.getOperandSize(); i++) {
				node.setOperand(i, this.bindZ3Node(node.getOperand(i), true));
			}
			for (i = 0; i < node.getDomainSize(); i++) {
				node.setDomain(i, this.bindZ3Node(node.getDomain(i), true));
			}			
			for (i = 0; i < node.getRangeSize(); i++) {
				node.setRange(i, this.bindZ3Node(node.getRange(i), true));
			}			
			for (i = 0; i < node.getBoundedVarSize(); i++) {
				node.setBoundedVar(i, this.bindZ3Node(node.getBoundedVar(i), true));
			}
			for (i = 0; i < node.getFieldSize(); i++) {
				node.setField(i, this.bindZ3Node(node.getField(i), true));
			}
			return node;
		}				
		return null;		
	}
	
	public final boolean isSort(Z3Node node) {
		int alen = this.sortList.size();
		Z3Node sort = null;
		String name = node.name;
		for (int i = 0; i < alen; i++) {
			sort = this.sortList.get(i);
			if (sort.name.equals(name)) {
				return true;
			}
		}		
		return false;		
	}
	
	private final Z3Node createTypeOK_PrimedVars(Z3Node sortInfo) {
		Z3Node res = new Z3Node("and", OPCODE_land, this.boolSort, null, tla_atom, NoSet),
				z3Node, z3LHS, z3RHS, z3Node1, z3pLHS;
		int alen = sortInfo.getOperandSize();
		for (int i = 0; i < alen; i++) {
			z3Node  = sortInfo.getOperand(i);
			z3LHS = z3Node.getOperand(0);
			z3LHS = this.getVar(z3LHS, z3LHS.name);
			z3RHS = z3Node.getOperand(1);			
			z3RHS = this.getVar(z3RHS, z3RHS.name);
			res.addOperand(z3Node);
			if (this.getVarIndex(z3LHS.name) >= 0) {
				z3pLHS	= z3LHS.clone();
				z3pLHS.name = "p_" + z3LHS.name;
				z3Node1 = z3Node.clone();
				z3Node1.setOperand(0, z3pLHS);				
				res.addOperand(z3Node1);
			}			
		}
		return res;
	}		
	
	public final Z3Node getDef(Z3Node node) {
		int index = this.getVarIndex(node.name);
		if (index >= 0 && this.defList[index].hasDef) {
			return this.defList[index].def;
		}
		return node;
	}
	
	private final void resetDefList() {
		int alen = 2 * this.tool.variablesNodes.length;
		for (int i = 0; i < alen; i++) {
			this.defList[i].hasDef = false;
		}
	}
	
	public final boolean hasDef(int i) {
		return this.defList[i].hasDef;
	}
	
	public final void addDef(int i, Z3Node def, int depth) {
		this.defList[i].def = def.clone();
		this.defList[i].hasDef = true;
		this.defList[i].depth = depth;
	}
	
	public final void removeDef(int depth) {
		int alen = this.defList.length;
		for (int i = 0; i < alen; i++) {
			if (this.defList[i].depth >= depth) {
				this.defList[i].reset();
			}
		}
	}
	
	private final void addStringVar(Z3Node newStr) {
		boolean flag = true;
		int stringSize = this.stringList.size();
		for (int j = 0; j < stringSize; j++) {
			Z3Node str = this.stringList.get(j);
			if (str.name.equals(newStr.name)) {
				flag = false;
				break;
			}
		}
		if (flag)	{
			this.stringList.add(newStr.clone());
		}
	}
	
	private final void addStringVars(Z3Node node) {
		int fieldSize = node.getFieldSize();
		for (int i = 0; i < fieldSize; i++) {
			Z3Node field = node.getField(i);
			this.addStringVar(field);
		}
	}
	
	private final Z3Node rewriteTypeOK(Z3Node node) {
		Z3Node res = node;
		if (res.getOperandSize() == 0) {
			return null;
		}
		else if (res.getOperandSize() == 1) {
			return res.getOperand(0);
		}		
		return res;
	}
	
	private final void translateTypeOK() {
		this.taskID = typeOKTask;
		Action[] inv = this.tool.getInvariants();		
		int alen = inv.length;
		String name = "";		
		Z3Node rhs = null;
		for (int j = 0; j < alen; j++) {
			OpApplNode node = (OpApplNode) inv[j].pred;
			OpDefNode node1 = (OpDefNode) node.getOperator();
			name = node1.getName().toString();
			if (name.equals("TypeOK")) {
				rhs = this.eval(inv[j].pred, inv[j].con, EvalControl.Clear);
				if (rhs.opCode == OPCODE_cl || rhs.opCode == OPCODE_land) {
					this.getPrimitiveTypeInfo(rhs);
//					rhs = this.bindZ3Node(rhs, true);
//					rhs = this.createTypeOK_PrimedVars(rhs);
					this.createTypeInfo_PrimedVars(rhs);
					this.z3Tool.setTaskID(typeOKTask);
					rhs = this.z3Tool.rewrite(rhs, true);
					rhs = this.rewriteTypeOK(rhs);
					this.z3Tool.checkNamesTypes(rhs);
					if (rhs != null) {
						rhs = this.z3Tool.simplify(rhs);
						this.typeOK = new Z3Node("assert", OPCODE_assert, this.boolSort, null, rhs, tla_atom, NoSet);					
						this.strTypeOK = "\n" + this.z3Tool.printZ3Node(this.typeOK, "") + "\n\n";														
					}
					else {
						this.strTypeOK = "";
					}
					int no = rhs.getOperandSize();
					for (int k = 0; k < no; k++) {
						this.typeInfos.add(rhs.getOperand(k));
					}
				}
			}
		}
//		System.out.println(this.strTypeOK);
	}
		
	private final void translateActions() {	
		this.taskID = nextTask;
		Action[] actions = this.tool.getActions();
		int alen = actions.length;
		Z3Node lhs = null, rhs = null;				
		for (int i = 0; i < alen; i++) {
			this.resetDefList();
			rhs = this.getNextStates(actions[i]);
			rhs = this.bindZ3Node(rhs, true);
			this.z3Tool.setTaskID(nextTask);
			rhs = this.z3Tool.rewrite(rhs, true);
			this.z3Tool.checkNamesTypes(rhs);
			rhs = this.z3Tool.simplify(rhs);
			lhs = new Z3Node(this.actionNames.get(i), OPCODE_const, this.strSort, null, tla_atom, NoSet);
			Z3Node eqAction = new Z3Node("=", OPCODE_eq, this.boolSort, null, lhs, rhs, tla_atom, NoSet);
			this.z3Actions[i] = new Z3Node("assert", OPCODE_assert, this.boolSort, null, eqAction, tla_atom, NoSet); 
			this.z3Tool.checkNamesTypes(this.z3Actions[i]);
			this.z3StrActions[i] = "\n" + this.z3Tool.printZ3Node(this.z3Actions[i], "") + "\n\n";
//			this.z3StrActions[i] = this.z3Tool.makeAssertion(this.z3StrActions[i]);
		}               		
	}
	
	private final void translateNext() {
		this.taskID = nextTask;
		int alen = this.actionNames.size();
		Z3Node lhs = null, rhs = null, tmp = null;
		// Translate Next formula.
		if (alen >= 2) {
			// tmp = action1 \lor ... \lor action n
			rhs = new Z3Node("or", OPCODE_lor, this.boolSort, null, tla_atom, NoSet);
			for (int i = 0; i < alen; i++) {
				tmp = new Z3Node(this.actionNames.get(i), OPCODE_const, this.boolSort, null, tla_atom, NoSet);
				this.z3SpecVars.add(tmp.clone());
				rhs.addOperand(tmp);
			}			
		}		
		else if (alen == 1) {
			tmp = new Z3Node(this.actionNames.get(0), OPCODE_const, this.boolSort, null, tla_atom, NoSet);
			this.z3SpecVars.add(tmp.clone());
			rhs = new Z3Node(this.actionNames.get(0), OPCODE_const, this.boolSort, null, tla_atom, NoSet);
		}
		else {
			rhs = new Z3Node("Next", OPCODE_const, this.boolSort, null, tla_atom, NoSet);
		}
		lhs = new Z3Node("Next", OPCODE_const, this.boolSort, null, tla_atom, NoSet);
		Z3Node eqNext = new Z3Node("=", OPCODE_eq, this.boolSort, null, lhs, rhs, tla_atom, NoSet);
		this.z3Next = new Z3Node("assert", OPCODE_assert, this.boolSort, null, eqNext, tla_atom, NoSet);
		this.z3SpecVars.add(lhs.clone());		
		this.z3Tool.checkNamesTypes(this.z3Next);
		this.strNext = "\n" + this.z3Tool.printZ3Node(this.z3Next, "") + "\n\n";
		this.strNext = this.strNext + "\n (assert Next) \n\n";	
//		this.strNext = this.z3Tool.makeAssertion(this.strNext);
	}
	
	private final void translateInit() {
		this.taskID = initTask;
		Vect init = this.tool.getInitStateSpec();
		ActionItemList acts = ActionItemList.Empty;	    
		for (int i = 1; i < init.size(); i++) {
			Action elem = (Action)init.elementAt(i);
			acts = acts.cons(elem.pred, elem.con, -1);
		}
		Z3Node lhs = null, rhs = null, eqInit = null;
		if (init.size() != 0) {
			Action elem = (Action)init.elementAt(0);	      			
			rhs = this.getInitStates(elem.pred, acts, elem.con);
			rhs = this.bindZ3Node(rhs, true);
			this.z3Tool.setTaskID(initTask);
			rhs = this.z3Tool.rewrite(rhs, true);			
			this.z3Tool.checkNamesTypes(rhs);
			rhs = this.z3Tool.simplify(rhs);
			lhs = new Z3Node("Init", OPCODE_const, this.boolSort, null, tla_atom, NoSet);			
			eqInit = new Z3Node("=", OPCODE_eq, this.boolSort, null, lhs, rhs, tla_atom, NoSet);
			this.z3Init = new Z3Node("assert", OPCODE_assert, this.boolSort, null, eqInit, tla_atom, NoSet);
			this.z3SpecVars.add(lhs.clone());
			this.strInit = "\n" + this.z3Tool.printZ3Node(this.z3Init, "") + "\n\n";			
		}				
//		this.strInit = this.z3Tool.makeAssertion(this.strInit);
	}     		
	
	private void makeVarDeclarations() {
		int alen, i;
		String tmp = NoCommand;
		
		alen = this.varList.length;
		for (i = 0; i < alen; i++) {
			tmp = this.z3Tool.makeVarDeclaration(this.varList[i]);
			this.z3VarDeclarations = this.z3VarDeclarations + tmp;
		}
		
		alen = this.stringList.size();
		for (i = 0; i < alen; i++) {
			tmp = this.z3Tool.makeVarDeclaration(this.stringList.get(i));
			this.z3VarDeclarations = this.z3VarDeclarations + tmp;
		}
		
		alen = this.z3SpecVars.size();
		for (i = 0; i < alen; i++) {
			tmp = this.z3Tool.makeVarDeclaration(this.z3SpecVars.get(i));
			this.z3VarDeclarations = this.z3VarDeclarations + tmp;
		}
		
		alen = this.predNames.size() / 2;
		for (i = 0; i < alen; i++) {
			Z3Node pred = new Z3Node(this.predNames.get(i), OPCODE_const, this.boolSort, null, tla_atom, NoSet),
					eq = new Z3Node("=", OPCODE_eq, this.boolSort, null, pred, this.preds.get(i).getOperand(0), tla_atom, NoSet),
					assertion = new Z3Node("assert", OPCODE_assert, this.boolSort, null, eq, tla_atom, NoSet);
			this.freshVars.add(pred);
			this.freshVarAssertions.add(assertion);
		}
		
		alen = this.predNames.size() / 2;
		for (i = alen; i < this.predNames.size(); i++) {
			Z3Node pred = new Z3Node("p_" + this.predNames.get(i - alen), OPCODE_const, this.boolSort, null, tla_atom, NoSet),
					eq = new Z3Node("=", OPCODE_eq, this.boolSort, null, pred, this.preds.get(i).getOperand(0), tla_atom, NoSet),
					assertion = new Z3Node("assert", OPCODE_assert, this.boolSort, null, eq, tla_atom, NoSet);
			this.freshVars.add(pred);
			this.freshVarAssertions.add(assertion);
		}
		
		alen = this.freshVars.size();
		for (i = 0; i < alen; i++) {
			tmp = this.z3Tool.makeVarDeclaration(this.freshVars.get(i));
			this.z3VarDeclarations = this.z3VarDeclarations + tmp;
		}
		alen = this.freshVarAssertions.size();
		for (i = 0; i < alen; i++) {
			this.z3VarDeclarations = this.z3VarDeclarations + "\n" + this.z3Tool.printZ3Node(this.freshVarAssertions.get(i), "") + "\n";			
		}				
	}
	
	private void makeSortDeclarations() {
		int alen = this.sortList.size();
		String cmd = "";
		for (int i = 0; i < alen; i++) {
			Z3Node sort = this.sortList.get(i);
			if (!sort.name.equals(Bool) && !sort.name.equals(Int)) {
				cmd = this.z3Tool.makeSortDeclaration(sort);
				this.z3SortDeclarations = this.z3SortDeclarations + cmd;
				if (sort.opCode != OPCODE_bsort) {
					cmd = this.z3Tool.makeFunctionsDeclaration(sort);
					this.z3SortDeclarations = this.z3SortDeclarations + cmd;
					cmd = this.z3Tool.makeExtensionality(sort);
					this.z3SortDeclarations = this.z3SortDeclarations + cmd;
				}
				this.z3SortDeclarations = this.z3SortDeclarations + "\n";
			}						
		}		
	}

	private void makeFcnDeclarations() {
		int alen = this.sortList.size();
		Z3Node tmp, uSort = this.sortList.get(UIndex), 
				intSort = this.sortList.get(IntIndex);
		String name, cmd;
		for (int i = 0; i < alen; i++) {
			// Sort_in
			name = this.sortList.get(i).name + "_in";
			tmp = new Z3Node(name, OPCODE_const, null, null, tla_atom, NoSet);
			tmp.addDomain(uSort);
			tmp.addDomain(this.sortList.get(i));
			tmp.addDomain(this.sortList.get(BoolIndex));
			cmd = this.z3Tool.makeFcnDeclaration(tmp);
			this.z3FcnDeclarations = this.z3FcnDeclarations + cmd;												
		}	
	}
	
	private final void printRawZ3SpecToStdout() throws IOException {
		System.out.println(this.z3SortDeclarations);
		System.out.println(this.z3VarDeclarations);
		System.out.println(this.strTypeOK);
		System.out.println(this.strInit);
		for (int i = 0; i < this.actionNames.size(); i++) {
			System.out.println(this.z3StrActions[i]);
		}
		System.out.println(this.strNext);
		if (this.stringList.size() > 1) {
			System.out.println(this.z3Tool.makeStringConstraint(this.stringList));
		}
	}
	
	private final void printRawZ3SpecToFile() throws IOException {
		FileWriter file = new FileWriter(this.dir + this.specFile + ".txt");
		file.write(this.z3SortDeclarations);
		file.flush();
		file.write(this.z3VarDeclarations);
		file.flush();
		file.write(this.strTypeOK);
		file.flush();
		file.write(this.strInit);
		file.flush();
		for (int i = 0; i < this.actionNames.size(); i++) {
			file.flush();
			file.write(this.z3StrActions[i]);
		}		
		file.flush();
		file.write(this.strNext);
		file.flush();
		if (this.stringList.size() > 1) {
			file.write(this.z3Tool.makeStringConstraint(this.stringList));
		}
		file.flush();
		file.write("(check-sat)");
		file.flush();
		file.close();
	}
	
	private final void printRefinedZ3SpecToFile() throws IOException {
		FileWriter file = new FileWriter(this.dir + "refinedspec_" + this.specFile + ".txt");
		file.write(this.z3SortDeclarations);
		file.flush();
		file.write(this.z3VarDeclarations);
		file.write("\n");
		file.flush();
		file.write(this.strInit);
		file.flush();
		for (int i = 0; i < this.actionNames.size(); i++) {
			file.flush();
			file.write(this.z3StrActions[i]);
		}		
		file.flush();
		file.write(this.strNext);
		file.flush();
		if (this.stringList.size() > 1) {
			file.write(this.z3Tool.makeStringConstraint(this.stringList));
		}
		file.flush();
		for (int i = 0; i < this.typeInfos.size(); i++) {
			Z3Node info = this.typeInfos.get(i);
			if (info.opCode == OPCODE_land) {
				int alen1 = info.getOperandSize();
				for (int j = 0; j < alen1; j++) {
					Z3Node info1 = info.getOperand(j);
					if (info1.opCode == OPCODE_land) {
						int alen2 = info1.getOperandSize();
						for (int k = 0; k < alen2; k++) {
							Z3Node info2 = info1.getOperand(k);
							Z3Node assertion = new Z3Node("assert", OPCODE_assert, this.boolSort, null, info2, tla_atom, NoSet);
							String str = "\n" + this.z3Tool.printZ3Node(assertion, "") + "\n\n";
							file.write(str);
							file.flush();
						}
					}
					else {
						Z3Node assertion = new Z3Node("assert", OPCODE_assert, this.boolSort, null, info1, tla_atom, NoSet);
						String str = "\n" + this.z3Tool.printZ3Node(assertion, "") + "\n\n";
						file.write(str);
						file.flush();
					}
				}
			}
			else {
				Z3Node assertion = new Z3Node("assert", OPCODE_assert, this.boolSort, null, info, tla_atom, NoSet);
				String str = "\n" + this.z3Tool.printZ3Node(assertion, "") + "\n\n";
				file.write(str);
				file.flush();
			}
		}
		file.write("(check-sat)");
		file.flush();
		file.close();
	}
	
	private final void makeAssertsion(ArrayList<Z3Node> list, Z3Node node) {		
		if (node.opCode == OPCODE_land) {
			int alen = node.getOperandSize();
			for (int i = 0; i < alen; i++) {
				Z3Node node1 = node.getOperand(i);
				this.makeAssertsion(list, node1);
			}
		}
		else {
			Z3Node assertion = new Z3Node("assert", OPCODE_assert, this.boolSort, null, node, tla_atom, NoSet);
			list.add(assertion);
		}
	}
	
	private final void printInitInvToFile(FileWriter file) throws IOException {
		for (int i = 0; i < this.initInvs.size(); i++) {
			Z3Node assertion = new Z3Node("assert", OPCODE_assert, this.boolSort, null, this.initInvs.get(i), tla_atom, NoSet);
			String str = "\n" + this.z3Tool.printZ3Node(assertion, "") + "\n\n";
			file.write(str);
			file.flush();	
		}		
	}
	
	private final void printNextInvToFile(FileWriter file) throws IOException {
		for (int i = 0; i < this.nextInvs.size(); i++) {
			Z3Node assertion = new Z3Node("assert", OPCODE_assert, this.boolSort, null, this.nextInvs.get(i), tla_atom, NoSet);
			String str = "\n" + this.z3Tool.printZ3Node(assertion, "") + "\n\n";
			file.write(str);
			file.flush();	
		}		
	}
	
	private final void printRefinedInitToFile() throws IOException {
		ArrayList<Z3Node> list = new ArrayList<Z3Node>();
		String fileName = this.dir + "init_" + this.specFile + ".txt";
		this.files.add(fileName);
		FileWriter file = new FileWriter(fileName);
//		file.write("(set-option :produce-unsat-cores true)\n\n");
		file.flush();
		file.write(this.z3SortDeclarations);
		file.flush();
		file.write(this.z3VarDeclarations);
		file.write("\n");
		file.flush();
		if (this.z3Init.opCode == OPCODE_assert) {
			Z3Node eq = this.z3Init.getOperand(0);
			if (eq.opCode == OPCODE_eq) {
				Z3Node andNode = eq.getOperand(1);
				andNode = this.z3Tool.simplify(andNode);
				this.z3Init.setOperand(0, andNode);
				list.clear();
				this.makeAssertsion(list, andNode);
				int alen = list.size();
				for (int i = 0; i < alen; i++) {
					String str = "\n" + this.z3Tool.printZ3Node(list.get(i), "") + "\n\n";
					file.write(str);
					file.flush();	
				}
			}
		}			
		for (int i = 0; i < this.typeInfos.size(); i++) {
			Z3Node info = this.typeInfos.get(i);
			list.clear();
			info = this.z3Tool.simplify(info);
			this.typeInfos.set(i, info);
			this.makeAssertsion(list, info);
			int alen = list.size();
			for (int j = 0; j < alen; j++) {
				String str = "\n" + this.z3Tool.printZ3Node(list.get(j), "") + "\n\n";
				file.write(str);
				file.flush();	
			}		
		}		
		if (this.stringList.size() > 1) {
			file.write(this.z3Tool.makeStringConstraint(this.stringList));
			file.flush();
		}
//		for (int i = 0; i < this.predNames.size() / 2; i++) {
//			String str = "\n(assert (! " + this.predNames.get(i) + " :named lbl_" + this.predNames.get(i) + "))\n\n";
//			file.write(str);
//			file.flush();
//		}
//		this.printInitInvToFile(file);		
//		file.flush();
//		file.write("(check-sat)\n");
//		file.flush(); 
		file.close();
	}
	
	private final void printRefinedActionToFile(Z3Node node, String str) throws IOException {
		if (node.opCode == OPCODE_assert) {
			ArrayList<Z3Node> list = new ArrayList<Z3Node>();
			Z3Node eq = node.getOperand(0);
			if (eq.opCode == OPCODE_eq) {
				String actionName = eq.getOperand(0).name;
				Z3Node action = eq.getOperand(1);
				String fileName = this.dir + "action_" + actionName + ".txt";
				this.files.add(fileName);
				FileWriter file = new FileWriter(fileName);
				file.write(this.z3SortDeclarations);
				file.flush();
				file.write(this.z3VarDeclarations);
				file.write("\n");
				file.flush();				
				action = this.z3Tool.simplify(action);
				eq.setOperand(1, action);
				list.clear();
				this.makeAssertsion(list, action);
				int alen = list.size();
				for (int i = 0; i < alen; i++) {
					String str0 = "\n" + this.z3Tool.printZ3Node(list.get(i), "") + "\n\n";
					file.write(str0);
					file.flush();	
				}
				for (int i = 0; i < this.typeInfos.size(); i++) {
					Z3Node info = this.typeInfos.get(i);
					list.clear();
					info = this.z3Tool.simplify(info);
					this.typeInfos.set(i, info);
					this.makeAssertsion(list, info);
					int alen1 = list.size();
					for (int j = 0; j < alen1; j++) {
						String str0 = "\n" + this.z3Tool.printZ3Node(list.get(j), "") + "\n\n";
						file.write(str0);
						file.flush();	
					}		
				}
				if (this.stringList.size() > 1) {
					file.write(this.z3Tool.makeStringConstraint(this.stringList));
					file.flush();
				}
//				this.printNextInvToFile(file);				
//				file.flush();
//				file.write("(check-sat)\n");
//				file.flush(); 
				file.close();
			}
		}					
	}
	
	private final void printRefinedNextToFile() throws IOException {
		String fileName = this.dir + "next_" + this.specFile + ".txt";
		this.files.add(fileName);
		FileWriter file = new FileWriter(fileName);
//		file.write("(set-option :produce-unsat-cores true)");
		file.flush();
		file.write(this.z3SortDeclarations);
		file.flush();
		file.write(this.z3VarDeclarations);
		file.flush();		
		for (int i = 0; i < this.actionNames.size(); i++) {
			String action = "\n" + this.z3Tool.printZ3Node(this.z3Actions[i], "") + "\n\n";
			file.write(action);
			file.flush();
		}
		file.write(this.strNext);
		file.flush();		
		ArrayList<Z3Node> list = new ArrayList<Z3Node>();
		for (int i = 0; i < this.typeInfos.size(); i++) {
			Z3Node info = this.typeInfos.get(i);
			list.clear();
			info = this.z3Tool.simplify(info);
			this.typeInfos.set(i, info);
			this.makeAssertsion(list, info);
			int alen1 = list.size();
			for (int j = 0; j < alen1; j++) {
				String str0 = "\n" + this.z3Tool.printZ3Node(list.get(j), "") + "\n\n";
				file.write(str0);
				file.flush();	
			}		
		}
		if (this.stringList.size() > 1) {
			file.write(this.z3Tool.makeStringConstraint(this.stringList));
			file.flush();	
		}			
//		this.printNextInvToFile(file);
//		file.flush(); 
//		file.write("(check-sat)\n");
//		file.flush();
//		int tmp = this.predNames.size() / 2;
//		for (int i = 0; i < tmp; i++) {
//			String str = "\n(assert (! " + this.predNames.get(i) + " :named lbl_" + this.predNames.get(i) + "))\n\n";
//			file.write(str);
//			file.flush();
//		}		
//		for (int i = tmp; i < this.predNames.size(); i++) {
//			String str = "\n(assert (! p_" + this.predNames.get(i - tmp) + " :named lbl_p_" + this.predNames.get(i - tmp) + "))\n\n";
//			file.write(str);
//			file.flush();
//		}
		file.close();
	}
	
	private final void printRefinedthPredidatesToFile() throws IOException {
		String fileName = this.dir + "next_predicates_" + this.specFile + ".txt";
		this.files.add(fileName);
		FileWriter file = new FileWriter(fileName);
//		file.write("(set-option :produce-unsat-cores true)");
		file.flush();
		file.write(this.z3SortDeclarations);
		file.flush();
		file.write(this.z3VarDeclarations);
		file.flush();		
		for (int i = 0; i < this.actionNames.size(); i++) {
			String action = "\n" + this.z3Tool.printZ3Node(this.z3Actions[i], "") + "\n\n";
			file.write(action);
			file.flush();
		}
		file.write(this.strNext);
		file.flush();		
		ArrayList<Z3Node> list = new ArrayList<Z3Node>();
		for (int i = 0; i < this.typeInfos.size(); i++) {
			Z3Node info = this.typeInfos.get(i);
			list.clear();
			info = this.z3Tool.simplify(info);
			this.typeInfos.set(i, info);
			this.makeAssertsion(list, info);
			int alen1 = list.size();
			for (int j = 0; j < alen1; j++) {
				String str0 = "\n" + this.z3Tool.printZ3Node(list.get(j), "") + "\n\n";
				file.write(str0);
				file.flush();	
			}		
		}
		if (this.stringList.size() > 1) {
			file.write(this.z3Tool.makeStringConstraint(this.stringList));
			file.flush();	
		}			
		file.close();
	}

	
	private final void printZ3Spec() throws IOException {
		this.dir = "D:\\EMCL\\TUW\\Thesis\\Z3API\\z3-master\\build\\test_ToyExample\\";
		this.printRawZ3SpecToFile();
		this.printRawZ3SpecToStdout();
		this.printRefinedZ3SpecToFile();
		this.printRefinedInitToFile();
		int alen = this.z3Actions.length;
		for (int i = 0; i < alen; i++) {
			this.printRefinedActionToFile(this.z3Actions[i], this.z3StrActions[i]);
		}
		this.printRefinedNextToFile();
		this.printRefinedthPredidatesToFile();
	}
	
	private final void makeIsAFcn() {
		int alen = this.varList.length;
		int count = 0, i;
		for (i = 0; i < alen; i++) {
			if (this.varList[i].getSort().name.equals(U)) {
				count++;
			}
		}
		if (count == 0) {
			this.z3StrIsAFcn = "; IsAFcn\n";
		}
		else if (count == 1) {
			for (i = 0; i < alen; i++) {
				if (this.varList[i].getSort().name.equals(U)) {
					if (this.varList[i].kind == tla_fcn || this.varList[i].kind == tla_rcd ||
							this.varList[i].kind == tla_tup) {
						Z3Node op = new Z3Node("IsAFcn", OPCODE_IsAFcn, this.boolSort, null, this.varList[i], tla_atom, NoSet);
						this.z3StrIsAFcn = this.z3Tool.printZ3Node(op, "");
						this.z3StrIsAFcn = "; IsAFcn\n" + this.z3Tool.makeAssertion(this.z3StrIsAFcn);
					}
					else {
						Z3Node op = new Z3Node("IsAFcn", OPCODE_IsAFcn, this.boolSort, null, this.varList[i], tla_atom, NoSet),
								op1 = new Z3Node("not", OPCODE_lnot, this.boolSort, null, op, tla_atom, NoSet);						
						this.z3StrIsAFcn = this.z3Tool.printZ3Node(op1, "");
						this.z3StrIsAFcn = "; IsAFcn\n" + this.z3Tool.makeAssertion(this.z3StrIsAFcn);
					}
				}
			}
		}
		else if (count > 1) {
			Z3Node node = new Z3Node("and", OPCODE_land, this.boolSort, null, tla_atom, NoSet);
			for (i = 0; i < alen; i++) {
				if (this.varList[i].getSort().name.equals(U)) {
					if (this.varList[i].kind == tla_fcn || this.varList[i].kind == tla_rcd ||
							this.varList[i].kind == tla_tup) {
						Z3Node op = new Z3Node("IsAFcn", OPCODE_IsAFcn, this.boolSort, null, this.varList[i], tla_atom, NoSet);
						node.addOperand(op);
					}
					else {
						Z3Node op = new Z3Node("IsAFcn", OPCODE_IsAFcn, this.boolSort, null, this.varList[i], tla_atom, NoSet),
								op1 = new Z3Node("not", OPCODE_lnot, this.boolSort, null, op, tla_atom, NoSet);
						node.addOperand(op1);					
					}				
				}
			}	
			this.z3StrIsAFcn = this.z3Tool.printZ3Node(node, "");
			this.z3StrIsAFcn = "; IsAFcn\n" + this.z3Tool.makeAssertion(this.z3StrIsAFcn);			
		}			
	}
			
	private final void makeExtensionality() {
		int alen = this.varList.length;
		String tmpStr;
		Z3Node var1 = null, var2 = null, tmp = null,
				res1 = new Z3Node("and", OPCODE_land, this.boolSort, null, tla_atom, NoSet);		
		for (int i = 0; i < alen; i++) {
			var1 = this.varList[i];
			if (var1.getSort().name.equals(U)) {
				for (int j = i + 1; j < alen; j++) {
					var2 = this.varList[j];
					if (var2.getSort().name.equals(U)) {
						tmp = this.z3Tool.makeExtensionality(var1, var2);						
						if (tmp != null) {
							tmpStr = this.z3Tool.printZ3Node(tmp, "");
							tmpStr = this.z3Tool.makeAssertion(tmpStr);
							this.z3StrExtensionality = this.z3StrExtensionality + tmpStr;
							res1.addOperand(tmp);	
						}						
					}
				}
			}
		}
		if (res1.getOperandSize() == 1) {
			this.z3Extensionality = res1.getOperand(0);
		}
		else if (res1.getOperandSize() > 1) {
			this.z3Extensionality = res1;
		}
	}
	
	private final Z3Node getZ3FormalParamNode(Z3Node node) {
		Z3Node res = node;
		String name = res.name;
		int alen = this.z3FormalParamNodes.size();
		for(int i = alen - 1; i >= 0; i--) {
			if (name.equals(this.z3FormalParamNodes.get(i).name)) {
				return this.z3FormalParamNodes.get(i);
			}
		}		
		return res;
	}
	
	public final void addSort(Z3Node newSort) {
		if (newSort.name.equals(NoName)) {
			return;
		}			
		boolean flag = true;
		int alen = this.sortList.size();
		for (int j = 0; j < alen; j++) {
			Z3Node sort = this.sortList.get(j);
			if (sort.name.equals(newSort.name)) {
				flag = false;
				break;
			}
		}
		if (flag)	{
			this.sortList.add(newSort);
		}
	}
		
	public final Z3Node getSort(int index) {
		if (index < 0 || index >= this.sortList.size()) {
			return null;
		}
		else {
			return this.sortList.get(index);
		}
	}
	
	public final Z3Node getSort(String name) {
		if (name.equals(NoName)) {
			return null;
		}
		int alen = this.sortList.size();
		for (int i = 0; i < alen; i++) {
			if (name.equals(this.sortList.get(i).name)) {
				return this.sortList.get(i);
			}
		}
		return null;
	}
	
	public final Z3Node getSort(Z3Node node) {
		String name = node.name;
		if (name.equals("NoName")) {
			switch (node.opCode) {
			case OPCODE_fc: {
				return this.getSort_fc(node);
			}
			case OPCODE_sof: {
				return this.getSort_sof(node);
			}
			case OPCODE_tup: {
				return this.getSort_tup(node);
			}
			case OPCODE_cp: {
				return this.getSort_cp(node);
			}
			case OPCODE_rc: {
				return this.getSort_rc(node);
			}
			case OPCODE_sor: {
				return this.getSort_sor(node);
			}
			default: {
				Assert.fail(NoSortErr, "No appropriate sort.");
			}				
			}
		}
		else {
//			switch (name) {
//			case Bool: {
//				return this.sortList.get(BoolIndex);		
//			}
//			case SetBool: {
//				return this.sortList.get(SetBoolIndex);
//			}
//			case Int: {
//				return this.sortList.get(IntIndex);			
//			}
//			case SetInt: {
//				return this.sortList.get(SetIntIndex);
//			}
//			case Str: {
//				return this.sortList.get(StrIndex);
//			}
//			case SetStr: {
//				return this.sortList.get(SetStrIndex);
//			}
//			case U: {
//				return this.sortList.get(UIndex);
//			}
//			default: {
//				int alen = this.sortList.size();
//				for (int i = alen - 1; i >= 0; i--) {
//					Z3Node sort = this.sortList.get(i);
//					if (node.name.equals(sort.name)) {
//						return sort;
//					}
//				}
//				Assert.fail(NoSortErr, "No existing sort" + name);			
//			}
//			}
			if (name.equals(Bool)) {
				return this.sortList.get(BoolIndex);		
			}
			else if (name.equals(SetBool)) {
				return this.sortList.get(SetBoolIndex);
			}
			else if (name.equals(Int)) {
				return this.sortList.get(IntIndex);			
			}
			else if (name.equals(SetInt)) {
				return this.sortList.get(SetIntIndex);
			}
			else if (name.equals(Str)) {
				return this.sortList.get(StrIndex);
			}
			else if (name.equals(SetStr)) {
				return this.sortList.get(SetStrIndex);
			}
			else if (name.equals(U)) {
				return this.sortList.get(UIndex);
			}
			else {
				int alen = this.sortList.size();
				for (int i = alen - 1; i >= 0; i--) {
					Z3Node sort = this.sortList.get(i);
					if (node.name.equals(sort.name)) {
						return sort;
					}
				}
				Assert.fail(NoSortErr, "No existing sort" + name);			
			}
			
		}
		return null;
	}		
	
	public final Z3Node getSort_ssort_elem(Z3Node elemSort) {
		int alen = this.sortList.size();										
		Z3Node sort = null;
		for (int i = alen - 1; i >= 0; i--) {
			sort = this.sortList.get(i);
			if ((sort.opCode == OPCODE_ssort  || sort.opCode == OPCODE_sfsort ||
					 sort.opCode == OPCODE_srsort || sort.opCode == OPCODE_stsort) &&
					sort.getElemSort().name.equals(elemSort.name)) {
				return sort;
			}
		}
		switch (elemSort.opCode) {
		case OPCODE_fc: {
			return this.z3Tool.createSetSort(elemSort, OPCODE_sfsort);
		}
		case OPCODE_rc: {
			return this.z3Tool.createSetSort(elemSort, OPCODE_srsort);
		}
		case OPCODE_tup: {
			return this.z3Tool.createSetSort(elemSort, OPCODE_stsort);
		}
		default: {
			return this.z3Tool.createSetSort(elemSort, OPCODE_ssort);
		}
		}
		
	}
	
	public final Z3Node getSort_fc(Z3Node node) {
		if (node.opCode != OPCODE_fc) {
			Assert.fail(OPCODEErr, "Get FSORT of a node whose OPCODE is not _fc.");
		}
		int alen = this.sortList.size();								
		Z3Node domain = node.getDomain(0).getSort(),
				range = this.getSort_ssort_elem(node.getExpr(0).getSort()),
				sort = null;		
		for (int i = alen - 1; i >= 0; i--) {
			sort = this.sortList.get(i);
			if (sort.opCode == OPCODE_fsort) {
				Z3Node domain1 = sort.getDomain(0).getSort(),
						range1 = sort.getRange(0).getSort();
				if (domain.name.equals(domain1.name) &&
						range.name.equals(range1.name)) {					
					return sort;
				}
			}
		}
		return this.z3Tool.createSort_fc(node);
	}
	
	// node.opCode == OPCODE_sof
	public final Z3Node getSort_fsort_sof(Z3Node node) {
		if (node.opCode != OPCODE_sof) {
			Assert.fail(OPCODEErr, "Get FSORT from a node whose OPCODE is not _sof.");
		}
		int alen = this.sortList.size();								
		Z3Node domain = node.getDomain(0).getSort(),
				range = node.getRange(0).getSort(),
				sort = null;		
		for (int i = alen - 1; i >= 0; i--) {
			sort = this.sortList.get(i);
			if (sort.opCode == OPCODE_fsort) {
				Z3Node domain1 = sort.getDomain(0).getSort(),
						range1 = sort.getRange(0).getSort();
				if (domain.name.equals(domain1.name) &&
						range.name.equals(range1.name)) {					
					return sort;
				}
			}
		}
		return this.z3Tool.createSort_fsort_sof(node);
	}
	
	public final Z3Node getSort_sof(Z3Node node) {
		if (node.opCode != OPCODE_sof) {
			Assert.fail(OPCODEErr, "Get SFSORT of a node whose OPCODE is not _sof.");
		}
		int alen = this.sortList.size();								
		Z3Node domain = node.getDomain(0).getElemSort(),
				range = node.getRange(0).getElemSort(),
				sort = null;		
		for (int i = alen - 1; i >= 0; i--) {
			sort = this.sortList.get(i);
			if (sort.opCode == OPCODE_sfsort) {
				Z3Node fcnSort1 = sort.getElemSort(), 
						domain1 = fcnSort1.dom,
						range1 = fcnSort1.cod;
				if (domain.name.equals(domain1.name) &&
						range.name.equals(range1.name)) {					
					return sort;
				}
			}
		}
		return this.z3Tool.createSort_sof(node);
	}
	
	public final Z3Node getSort_tup(Z3Node node) {
		if (node.opCode != OPCODE_tup) {
			Assert.fail(OPCODEErr, "Get TSORT of a node whose OPCODE is not _tup.");
		}
		int alen = this.sortList.size(),
				fieldSize = node.getFieldSize(),
				i, j;
		Z3Node sort = null;
		boolean flag;
		for (i = alen - 1; i >= 0; i--) {
			sort = this.sortList.get(i);
			if (sort.opCode == OPCODE_tsort && fieldSize == sort.getFieldSize()) {
				flag = true;
				for (j = 0; j < fieldSize; j++) {
					if (!node.getField(j).name.equals(sort.getField(j).name) || 
							!node.getExpr(j).getSort().name.equals(sort.getRange(j).getSort().name)) {
						flag = false;
						break;
					}						
				}
				if (flag) {
					return sort;
				}
			}
		}
		return this.z3Tool.createSort_tup(node);
	}
	
	public final Z3Node getSort_tsort_cp(Z3Node node) {
		if (node.opCode != OPCODE_cp) {
			Assert.fail(OPCODEErr, "Get TSORT from a node whose OPCODE is not _cp.");
		}
		int alen = this.sortList.size(),
				fieldSize = node.getOperandSize(),
				i, j;
		Z3Node sort = null;
		boolean flag;
		for (i = alen - 1; i >= 0; i--) {
			sort = this.sortList.get(i);
			if (sort.opCode == OPCODE_tsort && fieldSize == sort.getFieldSize()) {
				flag = true;
				for (j = 0; j < fieldSize; j++) {
					if (!node.getOperand(j).getElemSort().name.equals(sort.getRange(j).getSort().name)) {
						flag = false;
						break;
					}						
				}
				if (flag) {
					return sort;
				}
			}
		}
		return this.z3Tool.createSort_tsort_cp(node);
	}
	
	public final Z3Node getSort_cp(Z3Node node) {
		if (node.opCode != OPCODE_cp) {
			Assert.fail(OPCODEErr, "Get STSORT of a node whose OPCODE is not _cp.");
		}
		int alen = this.sortList.size(),
				fieldSize = node.getOperandSize(),
				i, j;
		Z3Node sort = null;
		boolean flag;
		for (i = alen - 1; i >= 0; i--) {
			sort = this.sortList.get(i);
			if (sort.opCode == OPCODE_stsort && fieldSize == sort.getFieldSize()) {
				flag = true;
				for (j = 0; j < fieldSize; j++) {
					if (!node.getOperand(j).getSort().name.equals(sort.getRange(j).getSort().name)) {
						flag = false;
						break;
					}						
				}
				if (flag) {
					return sort;
				}
			}
		}
		return this.z3Tool.createSort_cp(node);
	}
	
	public final Z3Node getSort_rc(Z3Node node) {
		if (node.opCode != OPCODE_rc) {
			Assert.fail(OPCODEErr, "Get RSORT of a node whose OPCODE is not _rc.");
		}
		int alen = this.sortList.size(),
				fieldSize = node.getFieldSize(),
				i, j, k, count;
		Z3Node sort = null;	
		for (i = alen - 1; i >= 0; i--) {
			sort = this.sortList.get(i);
			if (sort.opCode == OPCODE_rsort && fieldSize == sort.getFieldSize()) {
				count = 0;
				for (j = 0; j < fieldSize; j++) {
					for (k = 0; k < fieldSize; k++) {
						if (sort.getField(j).name.equals(node.getField(k).name) &&
								sort.getRange(j).name.equals(node.getExpr(k).getSort().name)) {
							count++;
							break;
						}
					}
				}
				if (count == fieldSize) {
					return sort;
				}
			}
		}
		return this.z3Tool.createSort_rc(node);
	}
	
	public final Z3Node getSort_rsort_sor(Z3Node node) {
		if (node.opCode != OPCODE_sor) {
			Assert.fail(OPCODEErr, "Get RSORT from a node whose OPCODE is not _sor.");
		}
		int alen = this.sortList.size(),
				fieldSize = node.getFieldSize(),
				i, j, k, count;
		Z3Node sort = null;	
		for (i = alen - 1; i >= 0; i--) {
			sort = this.sortList.get(i);
			if (sort.opCode == OPCODE_srsort && fieldSize == sort.getFieldSize()) {
				count = 0;
				for (j = 0; j < fieldSize; j++) {
					for (k = 0; k < fieldSize; k++) {
						if (sort.getField(j).name.equals(node.getField(k).name) &&
								sort.getRange(j).name.equals(node.getRange(k).getElemSort().name)) {
							count++;
							break;
						}
					}
				}
				if (count == fieldSize) {
					return sort;
				}
			}
		}
		return this.z3Tool.createSort_rsort_sor(node);
	}
	
	public final Z3Node getSort_sor(Z3Node node) {
		if (node.opCode != OPCODE_sor) {
			Assert.fail(OPCODEErr, "Get SRSORT of a node whose OPCODE is not _spr.");
		}
		int alen = this.sortList.size(),
				fieldSize = node.getFieldSize(),
				i, j, k, count;
		Z3Node sort = null;	
		for (i = alen - 1; i >= 0; i--) {
			sort = this.sortList.get(i);
			if (sort.opCode == OPCODE_srsort && 
					fieldSize == sort.getFieldSize()) {
				count = 0;
				for (j = 0; j < fieldSize; j++) {
					for (k = 0; k < fieldSize; k++) {
						if (sort.getField(j).name.equals(node.getField(k).name) &&
								sort.getRange(j).name.equals(node.getRange(k).getElemSort().name)) {
							count++;
							break;
						}
					}
				}
				if (count == fieldSize) {
					return sort;
				}
			}
		}
		return this.z3Tool.createSort_sor(node);
	}
	
	private final Z3Node rewriteInv(Z3Node node) {
		Z3Node res = node;
		if (res.getOperandSize() == 0) {
			return null;
		}
		else if (res.getOperandSize() == 1) {
			return res.getOperand(0);
		}		
		return res;
	}
		
	private void translateInvariant() {
		this.taskID = invTask;
		Action[] inv = this.tool.getInvariants();		
		int alen = inv.length;
		String name = "";		
		Z3Node rhs = null;
		for (int j = 0; j < alen; j++) {
			OpApplNode node = (OpApplNode) inv[j].pred;
			OpDefNode node1 = (OpDefNode) node.getOperator();
			name = node1.getName().toString();
			if (name.equals("Inv_ToCheck")) {
				rhs = this.eval(inv[j].pred, inv[j].con, EvalControl.Clear);
				if (rhs.opCode == OPCODE_cl || rhs.opCode == OPCODE_land) {
					this.z3Tool.setTaskID(invTask);
					rhs = this.z3Tool.rewrite(rhs, true);
					rhs = this.rewriteInv(rhs);
					this.z3Tool.checkNamesTypes(rhs);
					this.typeOK = rhs;
					String sortInv = this.z3Tool.printZ3Node(rhs, "");					
					this.strTypeOK = this.z3Tool.makeAssertion(sortInv);					
				}
			}
		}
	}
	
	public void addFreshVar(Z3Node var) {
		int alen = this.freshVars.size();
		Z3Node var1;
		for (int i = 0; i < alen; i++) {
			var1 = this.freshVars.get(i);
			if (var1.name.equals(var.name)) {
				Assert.fail(ConstraintErr, "Duplicated variables: " + var.name + " " + var1.name);
			}
		}
		this.freshVars.add(var);
	}
	
	public final int getLazyValueIndex(Z3Node node) {
		int alen = this.lazyValues.size();
		for (int i = 0; i < alen; i++) {
			if (this.lazyValues.get(i).name.equals(node.name)) {
				return i;
			}
		}
		return -1;
	}
	
	public final Z3Node getLazyValue(int index) {
		return this.lazyValues.get(index);
	}
	
	public final void addFreshAssertion(Z3Node assertion) {
		this.freshVarAssertions.add(assertion);
	}
	
	public final void addLazyValue(Z3Node val) {
		this.lazyValues.add(val);
	}
	
	private final void addInvs(ArrayList<Z3Node> list, Z3Node inv) {
		if (inv.opCode == OPCODE_land) {
			int alen = inv.getOperandSize();
			for (int i = 0; i < alen; i++) {
				list.add(inv.getOperand(i));
			}
		}
		else {			
			list.add(inv);
		}
	}
	
	private final void translateInv() {
		this.taskID = invTask;
		Action[] inv = this.tool.getInvariants();		
		int alen = inv.length;
		String name = "";		
		Z3Node rhs = null;
		for (int j = 0; j < alen; j++) {
			OpApplNode node = (OpApplNode) inv[j].pred;
			OpDefNode node1 = (OpDefNode) node.getOperator();
			name = node1.getName().toString();
			if (name.equals("Inv_ToCheck")) {
				rhs = this.eval(inv[j].pred, inv[j].con, EvalControl.Clear);			
				this.z3Tool.setTaskID(invTask);
				rhs = this.z3Tool.rewrite(rhs, true);				
				this.z3Tool.checkNamesTypes(rhs);
				this.z3NusmvInv = rhs.clone();
				this.z3NusmvInv = this.z3Tool.simplify(this.z3NusmvInv);
				Z3Node notInv = new Z3Node("not", OPCODE_lnot, this.boolSort, null, rhs, tla_atom, NoSet), 
						notInitInv = notInv.clone(),
						nextInv = rhs.clone(),
						notNextInv = notInv.clone();
				notInitInv = this.z3Tool.simplify(notInitInv);
				nextInv		 = this.z3Tool.simplify(nextInv);
				notNextInv = this.z3Tool.simplify(notNextInv);
				for (int i = 0; i < this.varList.length; i++) {
					if (this.varList[i].name.indexOf("p_") == 0) {
						String varName = this.varList[i].name.substring(2, this.varList[i].name.length());
						notNextInv = this.z3Tool.replaceNode(varName, notNextInv, this.varList[i]);							
					}
				}
				this.addInvs(this.initInvs, notInitInv);
				this.addInvs(this.nextInvs, nextInv);
				this.addInvs(this.nextInvs, notNextInv);				
			}
		}
	}
	
	public ArrayList<Z3Node> getSortList() {
		return this.sortList;
	}
	
	public Z3Node[] getVarList() {
		return this.varList;
	}
	
	public ArrayList<Z3Node> getFreshVarList() {
		return this.freshVars;
	}
	
	public ArrayList<Z3Node> getAxioms() {
		return this.axioms;
	}
	
	public void addAxiom(Z3Node node) {
		this.axioms.add(node);
	}
	
	public ArrayList<String> getFileNames() {
		return this.files;
	}
	
	private final void getPreds() {
		this.taskID = predTask;
		Action[] inv = this.tool.getInvariants();		
		int alen = inv.length;
		String name = "";		
		Z3Node rhs = null;
		for (int j = 0; j < alen; j++) {
			OpApplNode node = (OpApplNode) inv[j].pred;
			OpDefNode node1 = (OpDefNode) node.getOperator();
			name = node1.getName().toString();
			if (name.equals("Predicates")) {
				rhs = this.eval(inv[j].pred, inv[j].con, EvalControl.Clear);								
			}			
		}
	}
	
	private final void simplifyPreds() {
		int alen = this.preds.size();
		for (int i = 0; i < alen; i++) {
			Z3Node pred = this.preds.get(i);
			pred = this.z3Tool.rewrite(pred, true);
			this.z3Tool.checkNamesTypes(pred);
			pred = this.z3Tool.simplify(pred);
			this.preds.set(i, pred);
		}		
	}
	
	private final void createNextPreds() {
		int alen = this.preds.size();
		for (int i = 0; i < alen; i++) {
			Z3Node nextPred = this.preds.get(i).clone();
			for (int j = 0; j < this.varList.length; j++) {
				if (this.varList[j].name.indexOf("p_") == 0) {
					String varName = this.varList[j].name.substring(2, this.varList[j].name.length());
					nextPred = this.z3Tool.replaceNode(varName, nextPred, this.varList[j]);					
				}
			}
			this.preds.add(nextPred);
			String name = "next(" + this.predNames.get(i) + ")";
			this.predNames.add(name);
		}
	}
	
	private final void createNegPreds() {
		int alen = this.preds.size();
		for (int i = 0; i < alen; i++) {
			Z3Node tmp = this.preds.get(i).clone(),
					negPred = new Z3Node("not", OPCODE_lnot, this.boolSort, null, tmp, tla_atom, NoSet);
			negPred = this.z3Tool.rewrite(negPred, true);
			negPred = this.z3Tool.simplify(negPred);
			this.negPreds.add(negPred);
		}
	}
	
	private final void createPredAssertions() {
		int alen = this.preds.size();
		for (int i = 0; i < alen; i++) {
			Z3Node tmp0 = this.preds.get(i),
					expr0 = new Z3Node("assert", OPCODE_assert, this.boolSort, null, tmp0, tla_atom, NoSet),					
					tmp1 = this.negPreds.get(i),
					expr1 = new Z3Node("assert", OPCODE_assert, this.boolSort, null, tmp1, tla_atom, NoSet);
			this.preds.set(i, expr0);
			this.negPreds.set(i, expr1);
		}
	}
	
	private final void translatePredicates() {
		this.getPreds();
		this.simplifyPreds();
		this.createNextPreds();
		this.createNegPreds();
		this.createPredAssertions();
	}
	
	public String printNUSMV(Z3Node node) {
		String res = "";
		if (node != null) {
			switch (node.opCode) {
			case OPCODE_bv:
			case OPCODE_var:
			case OPCODE_const: 
			case OPCODE_true: 
			case OPCODE_false: 
			case OPCODE_pred: {
				res = node.name;
				break;
			}
			case OPCODE_be: {
				String body = this.printNUSMV(node.getExpr(0)),
						bvars = "(" + node.getBoundedVar(0).name + " " +
								node.getDomain(0).name + ")";
				for (int i = 1; i < node.getBoundedVarSize(); i++) {
					bvars = bvars + " (" + node.getBoundedVar(i).name + " " +
							node.getDomain(i).name + ")";
				}
				res = "(exists (" + bvars + ")\n" + body + ")";
				break;
			}
			case OPCODE_bf: {
				String body = this.printNUSMV(node.getExpr(0)),
						bvars = "(" + node.getBoundedVar(0).name + " " +
								node.getDomain(0).name + ")";
				for (int i = 1; i < node.getBoundedVarSize(); i++) {
					bvars = bvars + " (" + node.getBoundedVar(i).name + " " +
							node.getDomain(i).name + ")";
				}
				res = "(forall (" + bvars + ")\n" + body + ")";
				break;
			}			
			case OPCODE_land: {
				int alen = node.getOperandSize();
				for (int i = 0; i < alen - 1; i++) {
					res = res + this.printNUSMV(node.getOperand(i)) + " & ";
				}
				res = "(" + res + this.printNUSMV(node.getOperand(alen - 1)) + ")";
				break;
			}
			case OPCODE_lor: {
				int alen = node.getOperandSize();
				for (int i = 0; i < alen - 1; i++) {
					res = res + this.printNUSMV(node.getOperand(i)) + " | ";
				}
				res = "(" + res + this.printNUSMV(node.getOperand(alen - 1)) + ")";
				break;				
			}
			case OPCODE_lnot: {
				String op = this.printNUSMV(node.getOperand(0));
				res = "(! " + op + ")";
				break;
			}
			}			
		}		
		return res;
	}
	
	private void translatePredInv() {
		this.taskID = predInvTask;
		Action[] inv = this.tool.getInvariants();		
		int alen = inv.length;
		String name = "";		
		Z3Node rhs = null, p_rhs = null;
		for (int j = 0; j < alen; j++) {
			OpApplNode node = (OpApplNode) inv[j].pred;
			OpDefNode node1 = (OpDefNode) node.getOperator();
			name = node1.getName().toString();
			if (name.equals("Inv_ToCheck")) {
				rhs = this.eval(inv[j].pred, inv[j].con, EvalControl.Clear);
				this.z3Tool.setTaskID(predInvTask);
				rhs = this.z3Tool.rewrite(rhs, true);
				rhs = this.rewriteInv(rhs);
				this.z3Tool.checkNamesTypes(rhs);				
				rhs = this.z3Tool.simplify(rhs);
				p_rhs = rhs.clone();
				this.z3Tool.makeNextInv(p_rhs);
				this.nusmvInv = this.printNUSMV(rhs);
				this.p_nusmvInv = this.printNUSMV(p_rhs);
				this.raw_init_inv = rhs;
				this.raw_next_inv = p_rhs;
			}
		}
	}
	
	public ArrayList<Z3Node> getPredicates() {
		return this.preds;
	}
	
	public ArrayList<Z3Node> getNegPredicates() {
		return this.negPreds;
	}
	
	public ArrayList<String> getPredNames() {
		return this.predNames;
	}
	
	public String getInitFileName() {
		return this.dir + "init_" + this.specFile + ".txt";
	}
	
	public String getNextFileName() {
		return this.dir + "next_" + this.specFile + ".txt";
	}
	
	public ArrayList<Z3Node> getStringList() {
		return this.stringList;
	}
	
	public String getDir() {
		return this.dir;
	}
	
	public String getSpecFileName() {
		return this.specFile;
	}
	
	public String getNuSMVInv() {
		return this.nusmvInv;
	}
	public String getNuSMVpInv() {
		return this.p_nusmvInv;
	}
}