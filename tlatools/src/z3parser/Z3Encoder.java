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
import z3parser.Rewriter;

public class Z3Encoder implements ValueConstants, ToolGlobals, Z3Constants, Z3ErrorCode {
	private String specFile;
	private SpecObj spec;
	private FilenameToStream resolver;	
	private ArrayList<String> actionNames;
	public Tool tool;
	private Preprocessor preTool;
	private ArrayList<Z3Node> sortList;
	private ArrayList<Z3Node> stringList;
	public Z3Node[] varList;
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
	public ArrayList<Z3Node> preds;
	private ArrayList<Z3Node> negPreds; 
	public ArrayList<String> predNames;
	private ArrayList<String> negPredNames;
	public  Z3Tool z3Tool;
	private ArrayList<String> fcnList;

	private ArrayList<Z3Node> z3SpecVars;

	private Z3Node z3Extensionality;
	private Z3Node z3IsAFcn;
	private String z3StrExtensionality;
	private String z3StrIsAFcn;
	
	public static int SortNo = 4;

	public Z3Node intSort, boolSort, strSort, setIntSort, setBoolSort, setStrSort;

	public ConstraintChecker checker;	
	public int taskID;	
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

	private TypeChecker typeChecker;
	private TypeReconstructor typeReconstructor;
	private Rewriter rewriter;
	private ConstraintChecker constraintChecker;

	public Z3Encoder(String fileName) {
		this.dir = System.getProperty("user.dir") + "//";
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

		this.z3SpecVars = new ArrayList<Z3Node>();

		this.z3Extensionality = null;
		this.z3IsAFcn = null;
		this.z3StrExtensionality = "; extensionality\n";
		this.z3StrIsAFcn = "; IsAFcn\n";		

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
		
		this.typeChecker = new TypeChecker(this);
		this.typeReconstructor = new TypeReconstructor(this, this.tool, this.z3Tool);
		this.constraintChecker = new ConstraintChecker(this);
		this.rewriter = new Rewriter(this, this.constraintChecker, this.z3Tool);
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

	public final void addStringVar(Z3Node newStr) {
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
				rhs = this.typeReconstructor.eval(inv[j].pred, inv[j].con, EvalControl.Clear);
				if (rhs.opCode == OPCODE_cl || rhs.opCode == OPCODE_land) {
					this.getPrimitiveTypeInfo(rhs);
					//					rhs = this.bindZ3Node(rhs, true);
					//					rhs = this.createTypeOK_PrimedVars(rhs);
					this.createTypeInfo_PrimedVars(rhs);
					this.z3Tool.setTaskID(typeOKTask);
					this.typeChecker.checkBeforeTranslation(rhs);
					rhs = this.rewriter.rewrite(rhs, true);
					rhs = this.rewriteTypeOK(rhs);
					this.rewriter.rename(rhs);
					this.typeChecker.checkAfterTranslation(rhs);
					if (rhs != null) {
						rhs = this.rewriter.simplify(rhs);
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
	}

	private final void translateActions() {	
		this.taskID = nextTask;
		Action[] actions = this.tool.getActions();
		int alen = actions.length;
		Z3Node lhs = null, rhs = null;				
		for (int i = 0; i < alen; i++) {
			this.resetDefList();
			rhs = this.typeReconstructor.getNextStates(actions[i]);
			rhs = this.bindZ3Node(rhs, true);
			this.z3Tool.setTaskID(nextTask);
			this.typeChecker.checkBeforeTranslation(rhs);
			rhs = this.rewriter.rewrite(rhs, true);
			this.rewriter.rename(rhs);
			rhs = this.rewriter.simplify(rhs);			
			lhs = new Z3Node(this.actionNames.get(i), OPCODE_const, this.strSort, null, tla_atom, NoSet);
			Z3Node eqAction = new Z3Node("=", OPCODE_eq, this.boolSort, null, lhs, rhs, tla_atom, NoSet);
			this.z3Actions[i] = new Z3Node("assert", OPCODE_assert, this.boolSort, null, eqAction, tla_atom, NoSet); 
			this.rewriter.rename(this.z3Actions[i]);
			this.typeChecker.checkAfterTranslation(rhs);
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
		this.rewriter.rename(this.z3Next);
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
			rhs = this.typeReconstructor.getInitStates(elem.pred, acts, elem.con);
			rhs = this.bindZ3Node(rhs, true);
			this.z3Tool.setTaskID(initTask);
			this.typeChecker.checkBeforeTranslation(rhs);
			rhs = this.rewriter.rewrite(rhs, true);			
			this.rewriter.rename(rhs);
			this.typeChecker.checkAfterTranslation(rhs);
			rhs = this.rewriter.simplify(rhs);			
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
				andNode = this.rewriter.simplify(andNode);
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
			info = this.rewriter.simplify(info);
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
				action = this.rewriter.simplify(action);
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
					info = this.rewriter.simplify(info);
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
			info = this.rewriter.simplify(info);
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
			info = this.rewriter.simplify(info);
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
		//		this.dir = System.getProperty("user.dir" + "\\");
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
				rhs = this.typeReconstructor.eval(inv[j].pred, inv[j].con, EvalControl.Clear);
				if (rhs.opCode == OPCODE_cl || rhs.opCode == OPCODE_land) {
					this.z3Tool.setTaskID(invTask);
					rhs = this.rewriter.rewrite(rhs, true);
					rhs = this.rewriteInv(rhs);
					this.rewriter.rename(rhs);
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
				rhs = this.typeReconstructor.eval(inv[j].pred, inv[j].con, EvalControl.Clear);			
				this.z3Tool.setTaskID(invTask);
				rhs = this.rewriter.rewrite(rhs, true);				
				this.rewriter.rename(rhs);
				this.z3NusmvInv = rhs.clone();
				this.z3NusmvInv = this.rewriter.simplify(this.z3NusmvInv);
				Z3Node notInv = new Z3Node("not", OPCODE_lnot, this.boolSort, null, rhs, tla_atom, NoSet), 
						notInitInv = notInv.clone(),
						nextInv = rhs.clone(),
						notNextInv = notInv.clone();
				notInitInv = this.rewriter.simplify(notInitInv);
				nextInv		 = this.rewriter.simplify(nextInv);
				notNextInv = this.rewriter.simplify(notNextInv);
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
				rhs = this.typeReconstructor.eval(inv[j].pred, inv[j].con, EvalControl.Clear);								
			}			
		}
	}

	private final void simplifyPreds() {
		int alen = this.preds.size();
		for (int i = 0; i < alen; i++) {
			Z3Node pred = this.preds.get(i);
			pred = this.rewriter.rewrite(pred, true);
			this.rewriter.rename(pred);
			pred = this.rewriter.simplify(pred);
			this.preds.set(i, pred);
		}		
	}

	// for NuSMV
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
			negPred = this.rewriter.rewrite(negPred, true);
			negPred = this.rewriter.simplify(negPred);
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
		boolean noInv = true;
		for (int j = 0; j < alen; j++) {
			OpApplNode node = (OpApplNode) inv[j].pred;
			OpDefNode node1 = (OpDefNode) node.getOperator();
			name = node1.getName().toString();
			if (name.equals("Inv_ToCheck")) {
				noInv = false;
				rhs = this.typeReconstructor.eval(inv[j].pred, inv[j].con, EvalControl.Clear);
				this.z3Tool.setTaskID(predInvTask);
				rhs = this.rewriter.rewrite(rhs, true);
				rhs = this.rewriteInv(rhs);
				this.rewriter.rename(rhs);				
				rhs = this.rewriter.simplify(rhs);
				p_rhs = rhs.clone();
				this.z3Tool.makeNextInv(p_rhs);
				this.nusmvInv = this.printNUSMV(rhs);
				this.p_nusmvInv = this.printNUSMV(p_rhs);
				this.raw_init_inv = rhs;
				this.raw_next_inv = p_rhs;
			}
		}
		if (noInv) {			
			Assert.fail(invNullErr, "No Invariant to check.");						
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
		if (this.dir != null || !this.dir.equals(NoName)) {
			return this.dir;
		}
		else {
			return "";
		}
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