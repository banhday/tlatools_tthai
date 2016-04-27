package z3parser;

import java.util.ArrayList;

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
import tlc2.value.BoolValue;
import tlc2.value.IntValue;
import tlc2.value.LazyValue;
import tlc2.value.MethodValue;
import tlc2.value.OpValue;
import tlc2.value.StringValue;
import tlc2.value.Value;
import tlc2.value.ValueConstants;
import util.Assert;
import util.UniqueString;

public class TypeReconstructor implements ValueConstants, ToolGlobals, Z3Constants, Z3ErrorCode  {

	private Z3Encoder encoder;
	private ArrayList<Z3Node> tfcn; // It's only for AtNodeKind
	private ArrayList<Z3Node> tlhs; // It's only for AtNodeKind
	private Tool tool;
	private ArrayList<Z3Node> z3FormalParamNodes;
	private Z3Tool z3Tool;
	
	private TypeReconstructor() {
		// TODO Auto-generated constructor stub			
	}

	public TypeReconstructor(Z3Encoder encoder, Tool tool, Z3Tool z3Tool) {
		this.encoder = encoder;
		this.tfcn = new ArrayList<Z3Node>();
		this.tlhs = new ArrayList<Z3Node>();
		this.tool = tool;
		this.z3FormalParamNodes = new ArrayList<Z3Node>();
		this.z3Tool = z3Tool; 
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

	private final Object lookup(SymbolNode opNode, Context c, boolean cutoff)
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
	public final Z3Node eval(SemanticNode expr, Context c, int control) {		
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
			Z3Node node = new Z3Node(name, OPCODE_const, this.encoder.intSort, null, tla_atom, NoSet);
			return node;
		}
		case StringKind: {			
			String name = (Value.getValue(expr)).toString();
			name = name.replace("\"", "");
			Z3Node node = new Z3Node(name, OPCODE_const, this.encoder.strSort, null, tla_atom, NoSet);
			this.encoder.addStringVar(node);
			return node;
		}		
		case AtNodeKind: {	
			String name = this.lookup(c, EXCEPT_AT);
			int index = this.encoder.getVarIndex(name);
			if (index >= 0) {
				Z3Node node = this.encoder.varList[index].clone();
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
						return this.encoder.setBoolSort;
					}
					else if (expr.getOperator().getName().toString().equals("FALSE")) {
						return new Z3Node("false", OPCODE_false, this.encoder.boolSort, null, tla_atom, NoSet);
					}
					else if (expr.getOperator().getName().toString().equals("TRUE")) {
						return new Z3Node("true", OPCODE_true, this.encoder.boolSort, null, tla_atom, NoSet);
					}
					else {						
						node = this.eval(opDef.getBody(), c1, control);
						String name = expr.getOperator().getName().toString();
						if (this.encoder.taskID == predTask && !name.equals("Predicates")) {
							this.encoder.predNames.add(name);
							this.encoder.preds.add(node.clone());
						}
						if (this.encoder.taskID == predInvTask && !name.equals("Inv_ToCheck")) {							
							node = new Z3Node(name, OPCODE_pred, this.encoder.boolSort, null, tla_atom, NoSet);
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
						if (node.name.equals("Int")) {							
							node = this.encoder.setIntSort;
						}
						else if (node.name.equals("Nat")) {
							node = this.encoder.setIntSort.clone();
							node.name = "Nat";
						}
						else if (node.name.equals("BOOLEAN") || node.name.equals("Bool")) {							
							node = this.encoder.setBoolSort;
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
						this.dd_check(node);						
						node = new Z3Node(NoName, OPCODE_se, this.encoder.setIntSort, null, tla_set, 1);
						node.isDotDot = true;						
						int n1 = Integer.parseInt(argVals[0].name);
						int n2 = Integer.parseInt(argVals[1].name);
						// Add the current argument to the node's list of arguments.
						for (int i = n1; i <= n2; i++) {
							String name = Integer.toString(i);
							Z3Node node1 = new Z3Node(name, OPCODE_const, this.encoder.intSort, null, tla_atom, NoSet);
							node.addOperand(node1);
						}
					}
					else if (node.name.equals("-.")) {
						String name = "-" + argVals[0].name;
						node = new Z3Node(name, OPCODE_const, this.encoder.intSort, null, tla_atom, NoSet);
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
						if (node.name.equals("<")) {
							this.IntsBool_check(node);
							node.opCode = OPCODE_lt;							
						}
						else if (node.name.equals(">")) {							
							this.IntsBool_check(node);
							node.opCode = OPCODE_gt;						
						}
						else if (node.name.equals("<=")) {							
							this.IntsBool_check(node);
							node.opCode = OPCODE_le;						
						}
						else if (node.name.equals(">=")) {							
							this.IntsBool_check(node);
							node.opCode = OPCODE_ge;							
						}
						else if (node.name.equals("mod")) {
							this.IntsInt_check(node);
							node.opCode = OPCODE_mod;					
						}
						else if (node.name.equals("div")) {
							this.IntsInt_check(node);
							node.opCode = OPCODE_div;	
						}
						else if (node.name.equals("+")) {
							this.IntsInt_check(node);
							node.opCode = OPCODE_add;							
						}
						else if (node.name.equals("-")) {
							this.IntsInt_check(node);
							node.opCode = OPCODE_sub;								
						}
						else if (node.name.equals("*")) {
							this.IntsInt_check(node);
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
						node = new Z3Node(val.toString(), OPCODE_const, this.encoder.intSort, null, tla_atom, NoSet);
					}
					else if (val instanceof BoolValue) {
						node = new Z3Node(val.toString(), OPCODE_const, this.encoder.boolSort, null, tla_atom, NoSet);
					}
					else {
						node.name = expr.getOperator().getName().toString();
					}
					if (node.name.equals("Int")) {							
						node = this.encoder.setIntSort;
					}
					else if (node.name.equals("Nat")) {
						node = this.encoder.setIntSort.clone();
						node.name = "Nat";
					}						
					else if (node.name.equals("BOOLEAN") || node.name.equals("Bool")) {
						node = this.encoder.setBoolSort;
					}			
					else if (node.name.equals("TRUE")) {
						node = new Z3Node("true", OPCODE_true, this.encoder.boolSort, null, tla_atom, NoSet);
					}
					else if (node.name.equals("FALSE")) {
						node = new Z3Node("false", OPCODE_false, this.encoder.boolSort, null, tla_atom, NoSet);
					}
				}
				if (((SymbolNode) opNode).getKind() == VariableDeclKind) {
					int index = this.encoder.getVarIndex(node.name);
					if (index >= 0) {
						node = this.encoder.varList[index];												
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
			node = new Z3Node("exists", OPCODE_be, this.encoder.boolSort, null, tla_atom, NoSet);
			// Instead of evaluating possible values of bounded variables,
			// we need to know only their names and domains.
			// Since our formula is \A x \in S. p(x), all formals, isTuples, and   
			// domains have only one element formals[0][0], isTuples[0], and 
			// domains[0]. We will support \A x1 \in S1, x2 \in S2, ... later.
			FormalParamNode[][] formals = expr.getBdedQuantSymbolLists();			
			ExprNode[] domains = expr.getBdedQuantBounds();
			Z3Node x = this.eval(formals[0][0], c, EvalControl.Clear), 
					S = this.eval(domains[0], c, EvalControl.Clear);
			this.unifySort_in(x, S);
			x.opCode = OPCODE_bv;
			this.z3FormalParamNodes.add(x);
			SemanticNode body = args[0];
			//			Z3Node z3Body = this.eval(body , c, EvalControl.Clear);
			//			node.addBoundedVar(x);
			Z3Node z3Body = this.eval(body, c, EvalControl.Clear),
					bvar = this.z3Tool.createBoundedVar();
			this.unifySort_equivSort(x, bvar);
			this.z3Tool.replaceNode(x.name, z3Body, bvar);
			z3Body.setSort(this.encoder.boolSort);
			node.addBoundedVar(bvar);
			node.addDomain(S);			
			node.addExpr(z3Body);
			this.z3FormalParamNodes.remove(this.z3FormalParamNodes.size() - 1);
			// We don't need to show TLC errors.
			this.be_check(node);
			return node;  
		}
		case OPCODE_bf: {    		// BoundedForall		
			node = new Z3Node("forall", OPCODE_bf, this.encoder.boolSort, null, tla_atom, NoSet);
			// Instead of evaluating possible values of bounded variables,
			// we need to know only their names and domains.
			// Since our formula is \E x \in S. p(x), all formals, isTuples, and   
			// domains have only one element formals[0][0], isTuples[0], and 
			// domains[0]. We will support \E x1 \in S1, x2 \in S2, ... later.
			FormalParamNode[][] formals = expr.getBdedQuantSymbolLists();			
			ExprNode[] domains = expr.getBdedQuantBounds();
			Z3Node x = this.eval(formals[0][0], c, EvalControl.Clear), 
					S = this.eval(domains[0], c, EvalControl.Clear);
			this.unifySort_in(x, S);
			x.opCode = OPCODE_bv;
			this.z3FormalParamNodes.add(x.clone());
			SemanticNode body = args[0];
			//			Z3Node z3Body = this.eval(body , c, EvalControl.Clear);
			//			node.addBoundedVar(x);
			Z3Node z3Body = this.eval(body, c, EvalControl.Clear),
					bvar = this.z3Tool.createBoundedVar();
			this.unifySort_equivSort(x, bvar);
			this.z3Tool.replaceNode(x.name, z3Body, bvar);
			z3Body.setSort(this.encoder.boolSort);
			node.addBoundedVar(bvar);
			node.addDomain(S);			
			node.addExpr(z3Body);
			this.z3FormalParamNodes.remove(this.z3FormalParamNodes.size() - 1);			
			// We don't need to show TLC errors.
			this.bf_check(node);
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
			this.ite_check(node);
			for (int i = alen - 2; i >= 0; i--) {
				pair = (OpApplNode)args[i];
				pairArgs = pair.getArgs();
				con = this.eval(pairArgs[0], c, control);
				action1 = this.eval(pairArgs[1], c, control);
				node = new Z3Node("ite", OPCODE_ite, cur.getSort(), null, action1, cur, NoKind, iNull);
				this.ite_check(node);
				cur = node;
			}
			node.passSortInfo();
			return node;			
		}
		case OPCODE_cp: {    		// CartesianProd		
			// Since there is no corresponding part in SMT-LIB, node's name is empty.
			node = new Z3Node("NoName", OPCODE_cp, null, null, tla_set, 1);
			int alen = args.length;			
			Z3Node dom = new Z3Node("dom_" + this.encoder.intSort.name, OPCODE_se, this.encoder.setIntSort, null, tla_set, 1);
			for (int i = 0; i < alen; i++) {
				Z3Node field = new Z3Node(Integer.toString(i + 1), OPCODE_const, this.encoder.intSort, null, tla_atom, NoSet),
						op = this.eval(args[i], c, control);				
				dom.addOperand(field);
				node.addField(field);
				node.addOperand(op);
			}			
			node.addDomain(dom);
			this.cp_check(node);
			return node;
		}	
		case OPCODE_cl: {    		// ConjList
			node = new Z3Node("and", OPCODE_land, this.encoder.boolSort, null, tla_atom, NoSet);
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
			this.boolOperator_check(node);
			return node;
		}
		case OPCODE_dl: {    		// DisjList		
			node = new Z3Node("or", OPCODE_lor, this.encoder.boolSort, null, tla_atom, NoSet);			
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
			this.boolOperator_check(node);
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
			this.exc_check(node);
			return node;			
		}
		case OPCODE_fa: {    // FcnApply
			node = new Z3Node(NoName, OPCODE_fa, null, null, NoKind, iNull);
			Z3Node fcn = this.eval(args[0], c, EvalControl.KeepLazy),
					arg = this.eval(args[1], c, EvalControl.Clear);					
			node.addOperand(fcn);
			node.addOperand(arg);		
			this.fa_check(node);
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
			this.unifySort_in(x, S);
			this.z3FormalParamNodes.add(x.clone());
			SemanticNode fbody = args[0];
			Z3Node z3Body = this.eval(fbody, c, control),
					bvar = this.z3Tool.createBoundedVar();
			this.unifySort_equivSort(x, bvar);
			this.z3Tool.replaceNode(x.name, z3Body, bvar);
			node.addBoundedVar(bvar);
			//			Z3Node z3Body = this.eval(fbody, c, control);
			//			node.addBoundedVar(x);
			node.addDomain(S);
			node.addExpr(z3Body);
			this.fc_check(node);
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
			this.ite_check(node);
			return node;
		}
		case OPCODE_rc: {   		// RcdConstructor
			node = new Z3Node(NoName, OPCODE_rc, null, null, tla_rcd, NoSet);			
			int alen = args.length;			
			Z3Node dom = new Z3Node("z3_strSet", OPCODE_se, this.encoder.setStrSort, this.encoder.strSort, tla_set, 1);			
			for (int i = 0; i < alen; i++) {
				OpApplNode pairNode = (OpApplNode)args[i];
				ExprOrOpArgNode[] pair = pairNode.getArgs();
				String name = (((StringValue)Value.getValue(pair[0])).getVal().toString());
				Z3Node field = new Z3Node(name, OPCODE_const, this.encoder.strSort, null, tla_atom, NoSet),
						e = this.eval(pair[1], c, control);				
				dom.addOperand(field);
				node.addField(field);				
				node.addExpr(e);
				node.addRange(e.getSort());				
			}
			node.addDomain(dom);
			this.rc_check(node);
			return node;
		}
		case OPCODE_rs: {   		// RcdSelect
			node = new Z3Node(NoName, OPCODE_rs, null, null, NoKind, iNull);
			Z3Node rcd = this.eval(args[0], c, control),
					field = this.eval(args[1], c, control);			
			node.addOperand(rcd);
			node.addOperand(field);
			this.rs_check(node);
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
			this.se_check(node);
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
			this.unifySort_in(x, S);			
			this.z3FormalParamNodes.add(x.clone());			
			SemanticNode body = args[0];
			Z3Node z3Body = this.eval(body, c, control),
					bvar = this.z3Tool.createBoundedVar();
			this.unifySort_equivSort(x, bvar);
			this.z3Tool.replaceNode(x.name, z3Body, bvar);
			node.addBoundedVar(bvar);
			//			Z3Node z3Body = this.eval(body, c, control);
			//			node.addBoundedVar(x);
			node.addDomain(S);			
			node.addExpr(z3Body);								
			this.z3FormalParamNodes.remove(this.z3FormalParamNodes.size() - 1);
			this.soa_check(node);			
			return node;
		}
		case OPCODE_sor: {   		// SetOfRcds: [ hi : Si ]
			node = new Z3Node(NoName, OPCODE_sor, null, null, tla_set, 1);
			// Since there is no corresponding part in SMT-LIB, node's name is empty.			
			int alen = args.length;
			UniqueString names[] = new UniqueString[alen];			
			Z3Node dom = new Z3Node("z3_strSet", OPCODE_se, this.encoder.setStrSort, this.encoder.strSort, tla_set, 1);			
			for (int i = 0; i < alen; i++) {
				OpApplNode pairNode = (OpApplNode)args[i];
				ExprOrOpArgNode[] pair = pairNode.getArgs();
				names[i] = ((StringValue)Value.getValue(pair[0])).getVal();
				String name = names[i].toString();
				Z3Node field = new Z3Node(name , OPCODE_const, this.encoder.strSort, null, tla_atom, NoSet),
						S = this.eval(pair[1], c, control);
				this.encoder.addStringVar(field);
				dom.addOperand(field);				
				node.addField(field);
				node.addRange(S);
			}
			node.addDomain(dom);
			this.sor_check(node);			
			return node;
		}
		case OPCODE_sof: {   		// SetOfFcns: [ S -> T ]			
			// Since there is no corresponding part in SMT-LIB, node's name is empty.
			node = new Z3Node(NoName, OPCODE_sof, null, null, tla_set, 1);
			Z3Node S = this.eval(args[0], c, control),
					T = this.eval(args[1], c, control);
			node.addDomain(S);
			node.addRange(T);
			this.sof_check(node);
			return node;
		}
		case OPCODE_sso: {	    // SubsetOf: { x \in S : p(x) }					
			// Since there is no corresponding part in SMT-LIB, node's name is empty.
			// BoundedVar = x, Domain = S, Expr = p(x)			
			FormalParamNode[][] formals = expr.getBdedQuantSymbolLists();		
			ExprNode[] domains = expr.getBdedQuantBounds();			
			Z3Node x = this.eval(formals[0][0], c, control),
					S = this.eval(domains[0], c, control);					
			this.unifySort_in(x, S);			
			this.z3FormalParamNodes.add(x.clone());
			SemanticNode pred = args[0];
			node = new Z3Node(NoName, OPCODE_sso, S.getSort(), null, tla_set, S.setLevel);
			Z3Node p = this.eval(pred, c, control),
					bvar = this.z3Tool.createBoundedVar();			
			this.unifySort_equivSort(x, bvar);
			this.z3Tool.replaceNode(x.name, p, bvar);			
			node.addBoundedVar(bvar);
			//			Z3Node p = this.eval(pred, c, control);
			//			node.addBoundedVar(x);			
			node.addDomain(S);						
			node.addExpr(p);
			this.z3FormalParamNodes.remove(this.z3FormalParamNodes.size() - 1);			
			this.sso_check(node);			
			return node;			
		}			
		case OPCODE_tup: {   // Tuple			
			node = new Z3Node(NoName, OPCODE_tup, null, null, tla_tup, NoSet);
			int alen = args.length;			
			Z3Node dom = new Z3Node("dom", OPCODE_se, this.encoder.setIntSort, this.encoder.intSort, tla_set, 1);			
			for (int i = 0; i < alen; i++) {
				String fieldName = Integer.toString(i + 1);
				Z3Node field = new Z3Node(fieldName, OPCODE_const, this.encoder.intSort, null, tla_atom, NoSet);				
				dom.addOperand(field);
				Z3Node z3Expr = this.eval(args[i], c, control),
						z3ExprSort = this.encoder.getSort(z3Expr.getSort());
				node.addExpr(z3Expr);
				node.addField(field);
				node.addRange(z3ExprSort);
			}
			node.addDomain(dom);	
			this.tup_check(node);
			return node;
		}		
		// Remove OPCODE_uc, OPCODE_ue, OPCODE_uf:
		case OPCODE_lnot: {	
			node = new Z3Node("not", OPCODE_lnot, this.encoder.boolSort, null, tla_atom, NoSet);
			node.setSort(this.encoder.boolSort);
			Z3Node op0 = this.eval(args[0], c, control);
			op0.setSort(this.encoder.boolSort);					
			node.addOperand(op0);
			this.boolOperator_check(node);
			return node;
		}
		case OPCODE_subset: {
			node = new Z3Node(NoName, OPCODE_subset, null, null, tla_set, iNull);
			// Since there is no corresponding part in SMT-LIB, node's name is empty.
			// z3Sort and setLevel can be updated later.
			Z3Node op0 = this.eval(args[0], c, control);											
			node.addOperand(op0);		
			this.subset_check(node);
			return node;			
		}
		case OPCODE_union: {				
			node = new Z3Node(NoName, OPCODE_union, null, null, tla_set, iNull);
			// Since there is no corresponding part in SMT-LIB, node's name is empty.
			// z3Sort and setLevel can be updated later.
			Z3Node op0 = this.eval(args[0], c, control);
			node.addOperand(op0);			
			this.union_check(node);	
			return node;
		}		
		case OPCODE_domain: {			
			node = new Z3Node("domain", OPCODE_domain, null, null, tla_set, iNull);			
			// Since there is no corresponding part in SMT-LIB, node's name is empty.
			// z3Sort and setLevel can be updated later.
			Z3Node op0 = this.eval(args[0], c, control);			
			node.addOperand(op0);
			this.domain_check(node);
			return node;
		}
		// Remove OPCODE_enable
		case OPCODE_eq: {	
			node = new Z3Node("=", OPCODE_eq, this.encoder.boolSort, null, tla_atom, NoSet);
			Z3Node lhs = this.eval(args[0], c, control),
					rhs = this.eval(args[1], c, control);				
			node.addOperand(lhs);
			node.addOperand(rhs);
			this.eq_check(node);
			return node;
		}
		case OPCODE_land: {
			node = new Z3Node("and", OPCODE_land, this.encoder.boolSort, null, tla_atom, NoSet);
			Z3Node op0 = this.eval(args[0], c, control),
					op1 = this.eval(args[1], c, control);			
			node.addOperand(op0);
			node.addOperand(op1);
			this.boolOperator_check(node);
			return node;
		}
		case OPCODE_lor: {		
			node = new Z3Node("or", OPCODE_lor, this.encoder.boolSort, null, tla_atom, NoSet);
			Z3Node op0 = this.eval(args[0], c, control),
					op1 = this.eval(args[1], c, control);			
			node.addOperand(op0);
			node.addOperand(op1);
			this.boolOperator_check(node);
			return node;
		}
		case OPCODE_implies: {		
			node = new Z3Node("=>", OPCODE_implies, this.encoder.boolSort, null, tla_atom, NoSet);
			Z3Node op0 = this.eval(args[0], c, control),
					op1 = this.eval(args[1], c, control);			
			node.addOperand(op0);
			node.addOperand(op1);
			this.boolOperator_check(node);
			return node;
		}
		case OPCODE_equiv: {	
			node = new Z3Node("=", OPCODE_eq, this.encoder.boolSort, null, tla_atom, NoSet);
			Z3Node op0 = this.eval(args[0], c, control),
					op1 = this.eval(args[1], c, control);
			node.addOperand(op0);
			node.addOperand(op1);
			this.boolOperator_check(node);
			return node;			
		}
		case OPCODE_noteq: {
			node = new Z3Node(NoName, OPCODE_noteq, this.encoder.boolSort, null, tla_atom, NoSet);
			Z3Node op0 = this.eval(args[0], c, control),
					op1 = this.eval(args[1], c, control);				
			node.addOperand(op0);
			node.addOperand(op1);		
			this.unifySort_equivSort(op0, op1);
			return node;
		}
		case OPCODE_in: {
			node = new Z3Node(NoName, OPCODE_in, this.encoder.boolSort, null, tla_atom, NoSet);
			Z3Node x = this.eval(args[0], c, control),
					S = this.eval(args[1], c, control);								
			node.addOperand(x);
			node.addOperand(S);				
			if (S.name.equals("Nat")) {
				Z3Node zero = new Z3Node("0", OPCODE_const, this.encoder.intSort, null, tla_atom, NoSet),						
						geq0 = new Z3Node(">=", OPCODE_ge, this.encoder.boolSort, null, x, zero, tla_atom, NoSet),
						intNode = new Z3Node(NoName, OPCODE_in, this.encoder.boolSort, null, x, this.encoder.setIntSort, tla_atom, NoSet),
						newNode = new Z3Node("and", OPCODE_land, this.encoder.boolSort, null, geq0, intNode, tla_atom, NoSet);
				this.in_check(intNode);
				node = newNode;
			}
			else {
				this.in_check(node);
			}
			return node;
		}
		case OPCODE_notin: {					
			node = new Z3Node(NoName, OPCODE_notin, this.encoder.boolSort, null, tla_atom, NoSet);
			Z3Node x = this.eval(args[0], c, control),
					S = this.eval(args[1], c, control);						
			node.addOperand(x);
			node.addOperand(S);
			this.notin_check(node);
			return node;
		}		 				 
		case OPCODE_subseteq: {
			node = new Z3Node(NoName, OPCODE_subseteq, this.encoder.boolSort, null, tla_atom, NoSet);
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
			this.setdiff_check(node);			
			return node;
		}
		case OPCODE_cap:  {
			node = new Z3Node(NoName, OPCODE_cap, null, null, tla_set, iNull);
			Z3Node T = this.eval(args[0], c, control),
					U = this.eval(args[1], c, control);
			node.addOperand(T);
			node.addOperand(U);	
			this.cap_check(node);			
			return node;
		}
		case OPCODE_cup: {					
			node = new Z3Node(NoName, OPCODE_cup, null, null, tla_set, iNull);
			Z3Node T = this.eval(args[0], c, control),
					U = this.eval(args[1], c, control);
			node.addOperand(T);
			node.addOperand(U);	
			this.setdiff_check(node);			
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
			int index = this.encoder.getVarIndex(name);
			if (index >= 0) {
				node = this.encoder.varList[index];
			}
			else {
				Assert.fail(NoIdErr, "No a primed variable: " + name);
			}
			return node;
		}
		case OPCODE_unchanged: {
			//			node.addOperand(this.eval(args[0], c, EvalControl.setPrimed(control)));
			//			node = (this.eval(args[0], c, EvalControl.setPrimed(control)));
			//			node.setSort(this.encoder.boolSort);
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
	public final Z3Node getNextStates(Action action) {
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
					node = new Z3Node("and", OPCODE_land, this.encoder.boolSort, null, tmp1, tmp2, tla_atom, NoSet);								
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
						node = new Z3Node("IsAFcn", OPCODE_IsAFcn, this.encoder.boolSort, null, var, tla_atom, NoSet);
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
					if (node.name.equals("Int")) {							
						node = this.encoder.setIntSort;
					}
					else if (node.name.equals("Nat")) {
						node = this.encoder.setIntSort.clone();
						node.name = "Nat";
					}
					else if (node.name.equals("BOOLEAN") || node.name.equals("Bool")) {
						node = this.encoder.setBoolSort;							
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
						this.dd_check(node);						
						node = new Z3Node(NoName, OPCODE_se, this.encoder.setIntSort, null, tla_set, 1);
						node.isDotDot = true;								
						int n1 = Integer.parseInt(argVals[0].name);
						int n2 = Integer.parseInt(argVals[1].name);
						// Add the current argument to the node's list of arguments.
						for (int i = n1; i <= n2; i++) {
							String name = Integer.toString(i);
							Z3Node node1 = new Z3Node(name, OPCODE_const, this.encoder.intSort, null, tla_atom, NoSet);
							node.addOperand(node1);
						}
					}
					else if (node.name.equals("-.")) {
						String name = "-" + argVals[0].name;
						node = new Z3Node(name, OPCODE_const, this.encoder.intSort, null, tla_atom, NoSet);
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
						if (node.name.equals("<")) {
							this.IntsBool_check(node);
							node.opCode = OPCODE_lt;							
						}
						else if (node.name.equals(">")) {							
							this.IntsBool_check(node);
							node.opCode = OPCODE_gt;						
						}
						else if (node.name.equals("<=")) {							
							this.IntsBool_check(node);
							node.opCode = OPCODE_le;						
						}
						else if (node.name.equals(">=")) {							
							this.IntsBool_check(node);
							node.opCode = OPCODE_ge;							
						}
						else if (node.name.equals("mod")) {
							this.IntsInt_check(node);
							node.opCode = OPCODE_mod;					
						}
						else if (node.name.equals("div")) {
							this.IntsInt_check(node);
							node.opCode = OPCODE_div;	
						}
						else if (node.name.equals("+")) {
							this.IntsInt_check(node);
							node.opCode = OPCODE_add;							
						}
						else if (node.name.equals("-")) {
							this.IntsInt_check(node);
							node.opCode = OPCODE_sub;								
						}
						else if (node.name.equals("*")) {
							this.IntsInt_check(node);
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
					if (node.name.equals("Int")) {							
						node = this.encoder.setIntSort;
					}
					else if (node.name.equals("Nat")) {
						node = this.encoder.setIntSort.clone();
						node.name = "Nat";
					}						
					else if (node.name.equals("BOOLEAN") || node.name.equals("Bool")) {
						node = this.encoder.setBoolSort;
					}			
					else if (node.name.equals("TRUE")) {
						node = new Z3Node("true", OPCODE_true, this.encoder.boolSort, null, tla_atom, NoSet);
					}
					else if (node.name.equals("FALSE")) {
						node = new Z3Node("false", OPCODE_false, this.encoder.boolSort, null, tla_atom, NoSet);
					}				
				}
				if (((SymbolNode) opNode).getKind() == VariableDeclKind) {
					int index = this.encoder.getVarIndex(node.name);
					if (index >= 0) {
						node = this.encoder.varList[index];												
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
					Z3Node res =  new Z3Node("and", OPCODE_land, this.encoder.boolSort, null, node, tmp, tla_atom, NoSet);
					this.boolOperator_check(res);
					return res; 				
				}
			}
		}

		node.opCode = opcode;		
		switch (opcode) {
		case OPCODE_cl:     			// ConjList
		case OPCODE_land: {
			// We replace OPCODE_cl with OPCODE_land.
			node = new Z3Node("and", OPCODE_land, this.encoder.boolSort, null, tla_atom, NoSet);			
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
			this.boolOperator_check(node);
			Z3Node tmp1 = this.getNextStates(acts);
			if (tmp1 != null) {
				Z3Node tmp2 = new Z3Node("and", OPCODE_land, this.encoder.boolSort, null, node, tmp1, tla_atom, NoSet);
				this.boolOperator_check(tmp2);
				return tmp2;
			}
			return node;
		}
		case OPCODE_dl:     			// DisjList
		case OPCODE_lor: {				
			// We replace OPCODE_cl with OPCODE_land.
			node = new Z3Node("or", OPCODE_lor, this.encoder.boolSort, null, tla_atom, NoSet);			
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
			this.boolOperator_check(node);
			Z3Node tmp1 = this.getNextStates(acts);
			if (tmp1 != null) {
				Z3Node tmp2 = new Z3Node("and", OPCODE_land, this.encoder.boolSort, null, node, tmp1, tla_atom, NoSet);
				this.boolOperator_check(tmp2);
				return tmp2;
			}
			return node;	
		}
		case OPCODE_be: {    // BoundedExists	
			node = new Z3Node("exists", OPCODE_be, this.encoder.boolSort, null, tla_atom, NoSet);		
			// Instead of evaluating possible values of bounded variables,
			// we need to know only their names and domains.
			// Since our formula is \A x \in S. p(x), all formals, isTuples, and   
			// domains have only one element formals[0][0], isTuples[0], and 
			// domains[0]. We will support \A x1 \in S1, x2 \in S2, ... later.		
			FormalParamNode[][] formals = pred.getBdedQuantSymbolLists();			
			ExprNode[] domains = pred.getBdedQuantBounds();
			Z3Node x = this.eval(formals[0][0], c, EvalControl.Clear), 
					S = this.eval(domains[0], c, EvalControl.Clear);
			this.unifySort_in(x, S);
			x.opCode = OPCODE_bv;
			this.z3FormalParamNodes.add(x.clone());
			SemanticNode body = args[0];
			//			Z3Node z3Body = this.eval(body , c, EvalControl.Clear);
			//			z3Body.setSort(this.encoder.boolSort);
			//			node.addBoundedVar(x);
			Z3Node z3Body = this.eval(body, c, EvalControl.Clear),
					bvar = this.z3Tool.createBoundedVar();
			this.unifySort_equivSort(x, bvar);
			this.z3Tool.replaceNode(x.name, z3Body, bvar);
			z3Body.setSort(this.encoder.boolSort);
			node.addBoundedVar(bvar);
			node.addDomain(S);			
			node.addExpr(z3Body);
			this.z3FormalParamNodes.remove(this.z3FormalParamNodes.size() - 1);
			this.be_check(node);
			// Need to check			
			Z3Node tmp1 = this.getNextStates(acts);
			if (tmp1 != null) {
				Z3Node tmp2 = new Z3Node("and", OPCODE_land, this.encoder.boolSort, null, node, tmp1, tla_atom, NoSet);
				this.boolOperator_check(tmp2);
				return tmp2;
			}
			return node;
		}
		case OPCODE_bf: {    // BoundedForall	
			node = new Z3Node("forall", OPCODE_bf, this.encoder.boolSort, null, tla_atom, NoSet);
			// Instead of evaluating possible values of bounded variables,
			// we need to know only their names and domains.
			// Since our formula is \A x \in S. p(x), all formals, isTuples, and   
			// domains have only one element formals[0][0], isTuples[0], and 
			// domains[0]. We will support \A x1 \in S1, x2 \in S2, ... later.
			FormalParamNode[][] formals = pred.getBdedQuantSymbolLists();			
			ExprNode[] domains = pred.getBdedQuantBounds();
			Z3Node x = this.eval(formals[0][0], c, EvalControl.Clear), 
					S = this.eval(domains[0], c, EvalControl.Clear);
			this.unifySort_in(x, S);
			x.opCode = OPCODE_bv;
			this.z3FormalParamNodes.add(x.clone());
			SemanticNode body = args[0];
			//			Z3Node z3Body = this.eval(body , c, EvalControl.Clear);
			//			z3Body.setSort(this.encoder.boolSort);
			//			node.addBoundedVar(x);
			Z3Node z3Body = this.eval(body, c, EvalControl.Clear),
					bvar = this.z3Tool.createBoundedVar();
			this.unifySort_equivSort(x, bvar);
			this.z3Tool.replaceNode(x.name, z3Body, bvar);
			z3Body.setSort(this.encoder.boolSort);
			node.addBoundedVar(bvar);
			node.addDomain(S);			
			node.addExpr(z3Body);
			this.z3FormalParamNodes.remove(this.z3FormalParamNodes.size() - 1);
			this.bf_check(node);
			// Need to check			
			Z3Node tmp1 = this.getNextStates(acts);
			if (tmp1 != null) {
				Z3Node tmp2 = new Z3Node("and", OPCODE_land, this.encoder.boolSort, null, node, tmp1, tla_atom, NoSet);
				this.boolOperator_check(tmp2);
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
			this.fa_check(node);
			// Need to check			
			Z3Node tmp1 = this.getNextStates(acts);
			if (tmp1 != null) {
				Z3Node tmp2 = new Z3Node("and", OPCODE_land, this.encoder.boolSort, null, node, tmp1, tla_atom, NoSet);
				this.boolOperator_check(tmp2);
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
			this.ite_check(node);			
			Z3Node tmp1 = this.getNextStates(acts);
			if (tmp1 != null) {
				Z3Node tmp2 = new Z3Node("and", OPCODE_land, this.encoder.boolSort, null, node, tmp1, tla_atom, NoSet);
				this.boolOperator_check(tmp2);
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
			this.ite_check(node);
			for (int i = alen - 2; i >= 0; i--) {
				pair = (OpApplNode)args[i];
				pairArgs = pair.getArgs();
				con = this.eval(pairArgs[0], c, EvalControl.Clear);
				action1 = this.eval(pairArgs[1], c, EvalControl.Clear);
				node = new Z3Node("ite", OPCODE_ite, cur.getSort(), null, action1, cur, NoKind, iNull);
				this.ite_check(node);
			}
			node.passSortInfo();	
			Z3Node tmp1 = this.getNextStates(acts);
			if (tmp1 != null) {
				Z3Node tmp2 = new Z3Node("and", OPCODE_land, this.encoder.boolSort, null, node, tmp1, tla_atom, NoSet);
				this.boolOperator_check(tmp2);
				return tmp2;
			}
			return node;			
		}
		case OPCODE_eq: {
			node = new Z3Node("=", OPCODE_eq, this.encoder.boolSort, null, tla_atom, NoSet);			
			SymbolNode var = this.tool.getPrimedVar(args[0], c, false);
			// The lhs is unprimed
			if (var == null) {
				return this.eval(pred, c, EvalControl.Clear);				
			}
			// The lhs is primed
			else {
				String name = "p_" + var.getName().toString();
				Z3Node lhs = null, rhs = null;
				int index = this.encoder.getVarIndex(name);
				if (index >= 0) {
					lhs = this.encoder.varList[index];												
				}			
				rhs = this.eval(args[1], c, EvalControl.Clear);				
				node.addOperand(lhs);
				node.addOperand(rhs);
				this.eq_check(node);
				Z3Node tmp1 = this.getNextStates(acts);
				if (tmp1 != null) {
					Z3Node tmp2 = new Z3Node("and", OPCODE_land, this.encoder.boolSort, null, node, tmp1, tla_atom, NoSet);
					this.boolOperator_check(tmp2);
					return tmp2;
				}						
				return node;				
			}
		}
		case OPCODE_in: {
			node = new Z3Node(NoName, OPCODE_in, this.encoder.boolSort, null, tla_atom, NoSet);
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
				int index = this.encoder.getVarIndex(name);
				if (index >= 0) {
					lhs = this.encoder.varList[index];												
				}			
				rhs = this.eval(args[1], c, EvalControl.Clear);				
				node.addOperand(lhs);
				node.addOperand(rhs);
				if (rhs.name.equals("Nat")) {
					Z3Node zero = new Z3Node("0", OPCODE_const, this.encoder.intSort, null, tla_atom, NoSet),						
							geq0 = new Z3Node(">=", OPCODE_ge, this.encoder.boolSort, null, lhs, zero, tla_atom, NoSet),
							intNode = new Z3Node(NoName, OPCODE_in, this.encoder.boolSort, null, lhs, this.encoder.setIntSort, tla_atom, NoSet),
							newNode = new Z3Node("and", OPCODE_land, this.encoder.boolSort, null, geq0, intNode, tla_atom, NoSet);
					this.in_check(intNode);
					node = newNode;
				}
				else {
					this.in_check(node);
				}						
				Z3Node tmp1 = this.getNextStates(acts);
				if (tmp1 != null) {
					Z3Node tmp2 = new Z3Node("and", OPCODE_land, this.encoder.boolSort, null, node, tmp1, tla_atom, NoSet);
					this.boolOperator_check(tmp2);
					return tmp2;
				}						
			}
			return node;
		}
		case OPCODE_implies: {
			node = new Z3Node("=>", OPCODE_implies, this.encoder.boolSort, null, tla_atom, NoSet);
			Z3Node lhs = this.eval(args[0], c, EvalControl.Clear),
					rhs = this.eval(args[1], c, EvalControl.Clear);			
			node.addOperand(lhs);
			node.addOperand(rhs);
			this.boolOperator_check(node);
			Z3Node tmp1 = this.getNextStates(acts);
			if (tmp1 != null) {
				Z3Node tmp2 = new Z3Node("and", OPCODE_land, this.encoder.boolSort, null, node, tmp1, tla_atom, NoSet);
				this.boolOperator_check(tmp2);
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
				Z3Node tmp2 = new Z3Node("and", OPCODE_land, this.encoder.boolSort, null, node, tmp1, tla_atom, NoSet);
				this.boolOperator_check(tmp2);
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
			int lIndex = this.encoder.getVarIndex(lhsName),
					rIndex = this.encoder.getVarIndex(rhsName);
			if (lIndex < 0 || rIndex < 0) {
				Assert.fail(NoIdErr, rhsName + " " + lhsName + " are not existed.");												
			}			
			Z3Node rhs = this.encoder.varList[rIndex],												
					lhs  = this.encoder.varList[lIndex],
					node = new Z3Node("=", OPCODE_eq, this.encoder.boolSort, null, lhs, rhs, tla_atom, NoSet),
					tmp  = this.getNextStates(acts);			
			if (tmp != null) {
				Z3Node res = new Z3Node("and", OPCODE_land, this.encoder.boolSort, null, node, tmp, tla_atom, NoSet);
				this.boolOperator_check(res);
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
			return new Z3Node("and", OPCODE_land, this.encoder.boolSort, null, tmp1, tmp2, tla_atom, NoSet);						
		}
		else {
			return tmp1;
		}		
	}

	public final Z3Node getInitStates(SemanticNode init, ActionItemList acts, Context c) {
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
						node = new Z3Node("IsAFcn", OPCODE_IsAFcn, this.encoder.boolSort, null, var, tla_atom, NoSet);
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
					if (node.name.equals("Int")) {							
						node = this.encoder.setIntSort;
					}
					else if (node.name.equals("Nat")) {
						node = this.encoder.setIntSort.clone();
						node.name = "Nat";
					}
					else if (node.name.equals("BOOLEAN") || node.name.equals("Bool")) {
						node = this.encoder.setBoolSort;							
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
						this.dd_check(node);						
						node = new Z3Node(NoName, OPCODE_se, this.encoder.setIntSort, null, tla_set, 1);
						node.isDotDot = true;						
						int n1 = Integer.parseInt(argVals[0].name);
						int n2 = Integer.parseInt(argVals[1].name);
						// Add the current argument to the node's list of arguments.
						for (int i = n1; i <= n2; i++) {
							String name = Integer.toString(i);
							Z3Node node1 = new Z3Node(name, OPCODE_const, this.encoder.intSort, null, tla_atom, NoSet);
							node.addOperand(node1);
						}
					}
					else if (node.name.equals("-.")) {
						String name = "-" + argVals[0].name;
						node = new Z3Node(name, OPCODE_const, this.encoder.intSort, null, tla_atom, NoSet);
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
						if (node.name.equals("<")) {
							this.IntsBool_check(node);
							node.opCode = OPCODE_lt;							
						}
						else if (node.name.equals(">")) {							
							this.IntsBool_check(node);
							node.opCode = OPCODE_gt;						
						}
						else if (node.name.equals("<=")) {							
							this.IntsBool_check(node);
							node.opCode = OPCODE_le;						
						}
						else if (node.name.equals(">=")) {							
							this.IntsBool_check(node);
							node.opCode = OPCODE_ge;							
						}
						else if (node.name.equals("mod")) {
							this.IntsInt_check(node);
							node.opCode = OPCODE_mod;					
						}
						else if (node.name.equals("div")) {
							this.IntsInt_check(node);
							node.opCode = OPCODE_div;	
						}
						else if (node.name.equals("+")) {
							this.IntsInt_check(node);
							node.opCode = OPCODE_add;							
						}
						else if (node.name.equals("-")) {
							this.IntsInt_check(node);
							node.opCode = OPCODE_sub;								
						}
						else if (node.name.equals("*")) {
							this.IntsInt_check(node);
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
					if (node.name.equals("Int")) {							
						node = this.encoder.setIntSort;
					}
					else if (node.name.equals("Nat")) {
						node = this.encoder.setIntSort.clone();
						node.name = "Nat";
					}						
					else if (node.name.equals("BOOLEAN") || node.name.equals("Bool")) {
						node = this.encoder.setBoolSort;
					}							
				}
				if (((SymbolNode) opNode).getKind() == VariableDeclKind) {
					int index = this.encoder.getVarIndex(node.name);
					if (index >= 0) {
						node = this.encoder.varList[index];												
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
					Z3Node res =  new Z3Node("and", OPCODE_land, this.encoder.boolSort, null, node, tmp, tla_atom, NoSet);
					this.boolOperator_check(res);
					return res;
				}
			}
		}
		node.opCode = opcode;
		switch (opcode) {
		case OPCODE_dl:     // DisjList
		case OPCODE_lor: {
			// We replace OPCODE_dl with OPCODE_lor.
			node = new Z3Node("or", OPCODE_lor, this.encoder.boolSort, null, tla_atom, NoSet);			
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
			this.boolOperator_check(node);
			Z3Node tmp1 = this.getInitStates(acts);
			if (tmp1 != null) {
				Z3Node tmp2 = new Z3Node("and", OPCODE_land, this.encoder.boolSort, null, node, tmp1, tla_atom, NoSet);
				this.boolOperator_check(tmp2);
				return tmp2;
			}
			return node;			
		}
		case OPCODE_cl:     // ConjList
		case OPCODE_land: {			
			// We replace OPCODE_cl with OPCODE_land.
			node = new Z3Node("and", OPCODE_land, this.encoder.boolSort, null, tla_atom, NoSet);			
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
			this.boolOperator_check(node);
			Z3Node tmp1 = this.getInitStates(acts);
			if (tmp1 != null) {
				Z3Node tmp2 = new Z3Node("and", OPCODE_land, this.encoder.boolSort, null, node, tmp1, tla_atom, NoSet);
				this.boolOperator_check(tmp2);
				return tmp2;
			}
			return node;
		}
		case OPCODE_be: {   // BoundedExists		
			node = new Z3Node("exists", OPCODE_be, this.encoder.boolSort, null, tla_atom, NoSet);				
			// Instead of evaluating possible values of bounded variables,
			// we need to know only their names and domains.
			// Since our formula is \A x \in S. p(x), all formals, isTuples, and   
			// domains have only one element formals[0][0], isTuples[0], and 
			// domains[0]. We will support \A x1 \in S1, x2 \in S2, ... later.
			FormalParamNode[][] formals = init.getBdedQuantSymbolLists();			
			ExprNode[] domains = init.getBdedQuantBounds();
			Z3Node x = this.eval(formals[0][0], c, EvalControl.Clear), 
					S = this.eval(domains[0], c, EvalControl.Clear);
			this.unifySort_in(x, S);
			x.opCode = OPCODE_bv;
			this.z3FormalParamNodes.add(x.clone());
			SemanticNode body = args[0];
			//			Z3Node z3Body = this.eval(body , c, EvalControl.Clear);
			//			z3Body.setSort(this.encoder.boolSort);
			//			node.addBoundedVar(x);
			Z3Node z3Body = this.eval(body, c, EvalControl.Clear),
					bvar = this.z3Tool.createBoundedVar();
			this.unifySort_equivSort(x, bvar);
			this.z3Tool.replaceNode(x.name, z3Body, bvar);
			z3Body.setSort(this.encoder.boolSort);
			node.addBoundedVar(bvar);
			node.addDomain(S);			
			node.addExpr(z3Body);
			this.z3FormalParamNodes.remove(this.z3FormalParamNodes.size() - 1);
			this.be_check(node);
			// Need to check			
			Z3Node tmp1 = this.getInitStates(acts);
			if (tmp1 != null) {
				Z3Node tmp2 = new Z3Node("and", OPCODE_land, this.encoder.boolSort, null, node, tmp1, tla_atom, NoSet);
				this.boolOperator_check(tmp2);
				return tmp2;
			}
			return node;
		}
		case OPCODE_bf: {    // BoundedForall
			node = new Z3Node("forall", OPCODE_bf, this.encoder.boolSort, null, tla_atom, NoSet);			
			// Instead of evaluating possible values of bounded variables,
			// we need to know only their names and domains.
			// Since our formula is \A x \in S. p(x), all formals, isTuples, and   
			// domains have only one element formals[0][0], isTuples[0], and 
			// domains[0]. We will support \A x1 \in S1, x2 \in S2, ... later.
			FormalParamNode[][] formals = init.getBdedQuantSymbolLists();			
			ExprNode[] domains = init.getBdedQuantBounds();
			Z3Node x = this.eval(formals[0][0], c, EvalControl.Clear), 
					S = this.eval(domains[0], c, EvalControl.Clear),
					sort = this.encoder.getElemSort(S);
			this.unifySort_in(x, S);
			x.opCode = OPCODE_bv;
			this.z3FormalParamNodes.add(x.clone());
			SemanticNode body = args[0];
			//			Z3Node z3Body = this.eval(body , c, EvalControl.Clear);
			//			z3Body.setSort(this.encoder.boolSort);
			//			node.addBoundedVar(x);
			Z3Node z3Body = this.eval(body, c, EvalControl.Clear),
					bvar = this.z3Tool.createBoundedVar();
			this.unifySort_equivSort(x, bvar);
			this.z3Tool.replaceNode(x.name, z3Body, bvar);
			z3Body.setSort(this.encoder.boolSort);
			node.addBoundedVar(bvar);
			node.addDomain(S);			
			node.addExpr(z3Body);
			this.z3FormalParamNodes.remove(this.z3FormalParamNodes.size() - 1);
			this.bf_check(node);
			// Need to check			
			Z3Node tmp1 = this.getInitStates(acts);
			if (tmp1 != null) {
				Z3Node tmp2 = new Z3Node("and", OPCODE_land, this.encoder.boolSort, null, node, tmp1, tla_atom, NoSet);
				this.boolOperator_check(tmp2);
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
			this.ite_check(node);			
			Z3Node tmp1 = this.getInitStates(acts);
			if (tmp1 != null) {
				Z3Node tmp2 = new Z3Node("and", OPCODE_land, this.encoder.boolSort, null, node, tmp1, tla_atom, NoSet);
				this.boolOperator_check(tmp2);
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
			this.ite_check(node);			
			for (int i = alen - 2; i >= 0; i--) {
				pair = (OpApplNode)args[i];
				pairArgs = pair.getArgs();
				con = this.eval(pairArgs[0], c);
				action1 = this.eval(pairArgs[1], c);
				node = new Z3Node("ite", OPCODE_ite, cur.getSort(), null, action1, cur, NoKind, iNull);
				this.ite_check(node);
			}
			node.passSortInfo();
			Z3Node tmp1 = this.getInitStates(acts);
			if (tmp1 != null) {
				Z3Node tmp2 = new Z3Node("and", OPCODE_land, this.encoder.boolSort, null, node, tmp1, tla_atom, NoSet);
				this.boolOperator_check(tmp2);
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
			this.fa_check(node);
			// Need to check						
			Z3Node tmp1 = this.getInitStates(acts);
			if (tmp1 != null) {
				Z3Node tmp2 = new Z3Node("and", OPCODE_land, this.encoder.boolSort, null, node, tmp1, tla_atom, NoSet);
				this.boolOperator_check(tmp2);
				return tmp2;				
			}													
			return node;
		}
		case OPCODE_eq: {		
			node = new Z3Node("=", OPCODE_eq, this.encoder.boolSort, null, tla_atom, NoSet);			
			// We don't evaluate any expression; therefore, we don't need
			// to look up any value and check whether or not an expression 
			// is a variable.
			// There is no primed variables in Init.
			Z3Node lhs = this.eval(args[0], c),
					rhs = this.eval(args[1], c);
			node.addOperand(lhs);
			node.addOperand(rhs);
			this.eq_check(node);
			Z3Node tmp1 = this.getInitStates(acts);
			if (tmp1 != null) {
				Z3Node tmp2 = new Z3Node("and", OPCODE_land, this.encoder.boolSort, null, node, tmp1, tla_atom, NoSet);
				this.boolOperator_check(tmp2);
				return tmp2;				
			}													
			return node;						
		}
		case OPCODE_in:	{
			node = new Z3Node(NoName, OPCODE_in, this.encoder.boolSort, null, tla_atom, NoSet);
			// Since there is no corresponding part in SMT-LIB, node's name is empty.
			// We don't evaluate any expression; therefore, we don't need
			// to look up any value and check whether or not an expression 
			// is a variable.
			// There is no primed variables in Init.
			Z3Node lhs = this.eval(args[0], c),
					rhs = this.eval(args[1], c);
			node.addOperand(lhs);
			node.addOperand(rhs);				
			if (rhs.name.equals("Nat")) {
				Z3Node zero = new Z3Node("0", OPCODE_const, this.encoder.intSort, null, tla_atom, NoSet),						
						geq0 = new Z3Node(">=", OPCODE_ge, this.encoder.boolSort, null, lhs, zero, tla_atom, NoSet),
						intNode = new Z3Node(NoName, OPCODE_in, this.encoder.boolSort, null, lhs, this.encoder.setIntSort, tla_atom, NoSet),
						newNode = new Z3Node("and", OPCODE_land, this.encoder.boolSort, null, geq0, intNode, tla_atom, NoSet);
				this.in_check(intNode);
				node = newNode;
			}
			else {
				this.in_check(node);
			}
			Z3Node tmp1 = this.getInitStates(acts);
			if (tmp1 != null) {
				Z3Node tmp2 = new Z3Node("and", OPCODE_land, this.encoder.boolSort, null, node, tmp1, tla_atom, NoSet);
				this.boolOperator_check(tmp2);
				return tmp2;				
			}													
			return node;					
		}
		case OPCODE_implies: {		
			node = new Z3Node("=>", OPCODE_implies, this.encoder.boolSort, null, tla_atom, NoSet);
			Z3Node lhs = this.eval(args[0], c, EvalControl.Clear),
					rhs = this.eval(args[1], c, EvalControl.Clear);			
			node.addOperand(lhs);
			node.addOperand(rhs);
			this.boolOperator_check(node);
			Z3Node tmp1 = this.getInitStates(acts);
			if (tmp1 != null) {
				Z3Node tmp2 = new Z3Node("and", OPCODE_land, this.encoder.boolSort, null, node, tmp1, tla_atom, NoSet);
				this.boolOperator_check(tmp2);
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
				Z3Node tmp2 = new Z3Node("and", OPCODE_land, this.encoder.boolSort, null, node, tmp1, tla_atom, NoSet);
				this.boolOperator_check(tmp2);
				return tmp2;				
			}		
			return node;
		}
		}
	}		

	private final void unifySort_equivSort(Z3Node lhs, Z3Node rhs) {
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

	private final void unifySort_eq(Z3Node lhs, Z3Node rhs) {
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

	private final void unifySort_in(Z3Node lhs, Z3Node rhs) {
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
			Z3Node setSort = this.encoder.getSort_ssort_elem(lSort);
			rhs.setSort(setSort);			
			return;
		}				
		else if (rElemSort != null && !lSort.name.equals(rElemSort.name)) {
			Assert.fail(NoSortErr, "Cannot find an appropriate sort for " + lhs.name + " " + rhs.name);			
		}
	}

	private final void unifySort_subseteq(Z3Node lhs, Z3Node rhs) {
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

	private final void dd_check(Z3Node node) {
		Z3Node lhs = node.getOperand(0),
				rhs = node.getOperand(1);
		if (lhs.getSort() != this.encoder.intSort) {
			Assert.fail(ConstraintErr, "The lhs of .. is not an integer.");
		}
		if (rhs.getSort() != this.encoder.intSort) {
			Assert.fail(ConstraintErr, "The rhs of .. is not an integer.");
		} 
		node.setSort(this.encoder.setIntSort);
	}

	private final void IntsInt_check(Z3Node node) {
		Z3Node op0 = node.getOperand(0),
				op1 = node.getOperand(1);
		if (op0.getSort() != this.encoder.intSort && !op0.getSort().name.equals(Int)) {
			Assert.fail(ConstraintErr, "The first operand of " + node.name + " is not an integer.");
		}
		if (op1.getSort() != this.encoder.intSort && !op1.getSort().name.equals(Int)) {
			Assert.fail(ConstraintErr, "The second operand of " + node.name + " is not an integer.");
		} 
		node.setSort(this.encoder.intSort);		
	}

	private final void IntsBool_check(Z3Node node) {
		Z3Node op0 = node.getOperand(0),
				op1 = node.getOperand(1);
		if (op0.getSort() != this.encoder.intSort && !op0.getSort().name.equals(Int)) {
			Assert.fail(ConstraintErr, "The first operand of " + node.name + " is not an integer.");
		}
		if (op1.getSort() != this.encoder.intSort && !op0.getSort().name.equals(Int)) {
			Assert.fail(ConstraintErr, "The second operand of " + node.name + " is not an integer.");
		}
		node.setSort(this.encoder.boolSort);			
	}

	private final void be_check(Z3Node node) {
		Z3Node x = node.getBoundedVar(0),
				S = node.getDomain(0),
				body = node.getExpr(0);
		if (body.getSort() != this.encoder.boolSort) {
			Assert.fail(ConstraintErr, "The body of a quantified formula is not a boolean formula.");
		}
		this.unifySort_in(x, S);
		node.setSort(this.encoder.boolSort);
	}

	private final void bf_check(Z3Node node) {
		Z3Node x = node.getBoundedVar(0),
				S = node.getDomain(0),
				body = node.getExpr(0);
		if (body.getSort() != this.encoder.boolSort) {
			Assert.fail(ConstraintErr, "The body of a quantified formula is not a boolean formula.");
		}
		this.unifySort_in(x, S);
		node.setSort(this.encoder.boolSort);
	}

	private final void ite_check(Z3Node node) {
		Z3Node con = node.getOperand(0),
				action1 = node.getOperand(1),
				action2 = node.getOperand(2);
		if (con.getSort() != this.encoder.boolSort) {
			Assert.fail(ConstraintErr, "The condition of an IF THEN ELSE expression is not a boolean formula.");
		}
		this.unifySort_equivSort(action1, action2);		
		node.setSort(action1.getSort());
		node.passSortInfo();
	}

	private final void cp_check(Z3Node node) {
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
		node.setSort(this.encoder.getSort_cp(node));
	}

	private final void boolOperator_check(Z3Node node) {
		int alen = node.getOperandSize();
		Z3Node op = null;
		for (int i = 0; i < alen; i++) {
			op = node.getOperand(i);
			if (op.getSort() != this.encoder.boolSort) {
				Assert.fail(ConstraintErr, "A boolean formula with non-boolean child-expression.");
			}
		}		
		node.setSort(this.encoder.boolSort);
	}

	private final void exc_check(Z3Node node) {
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
			this.unifySort_equivSort(lhs, this.encoder.strSort);
			for (int i = 0; i < alen; i++) {
				if (lhs.name.equals(sort.getField(i).name)) {
					this.unifySort_equivSort(rhs, sort.getRange(i));
					break;
				}
			}
		}
		else if (sort.opCode == OPCODE_tsort) {
			int alen = sort.getFieldSize();
			this.unifySort_equivSort(lhs, this.encoder.intSort);
			for (int i = 0; i < alen; i++) {
				this.unifySort_equivSort(rhs, sort.getRange(i));
				break;
			}
		}
	}

	private final void fa_check(Z3Node node) {
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
			this.unifySort_equivSort(arg, this.encoder.intSort);
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

	private final void fc_check(Z3Node node) {
		// It seems that we don't need it.
		Z3Node S = node.getDomain(0),
				body = node.getExpr(0);

		if (S.setLevel == 0) {
			Assert.fail(ConstraintErr, "The domain, " + S.name + " , of a function is not a set.");
		}
		if (S.getElemSort() != null && body.getSort() != null) {
			node.setSort(this.encoder.getSort_fc(node));
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

	private final void rc_check(Z3Node node) {
		boolean noNullSort = true;
		int alen = node.getExprSize();
		Z3Node expr = null, field = null;
		for (int i = 0; i < alen; i++) {
			expr = node.getExpr(i);
			field = node.getField(i);
			if (field.getSort() != this.encoder.strSort) {
				Assert.fail(ConstraintErr, "One field name of OPCODE_rc is not a string.");
			}
			if (expr.getSort() == null) {
				noNullSort = false;
			}
		}
		if (noNullSort) {
			node.setSort(this.encoder.getSort_rc(node));
		}		
	}

	private final void rs_check(Z3Node node) {
		Z3Node rcd = node.getOperand(0),
				field = node.getOperand(1);
		if (field.getSort() != this.encoder.strSort) {
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

	private final void se_check(Z3Node node) {
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
			this.unifySort_equivSort(node, this.encoder.getSort_ssort_elem(elemSort));			
		}		
	}

	private final void soa_check(Z3Node node) {
		Z3Node x = node.getBoundedVar(0),
				S = node.getDomain(0),
				body = node.getExpr(0);
		this.unifySort_in(x, S);
		if (body.getSort() != null) {
			this.unifySort_equivSort(node, this.encoder.getSort_ssort_elem(body.getSort()));
			node.setLevel = body.setLevel + 1;
		}
		else {
			node.setSetNullSort(body.setLevel + 1);
		}
	}

	private final void sor_check(Z3Node node) {		
		int alen = node.getFieldSize(), i;
		Z3Node field = null, S = null;
		for (i = 0; i < alen; i++) {
			field = node.getField(i);
			S = node.getRange(i);
			if (field.getSort() != this.encoder.strSort) {
				Assert.fail(ConstraintErr, "One field of the set of records is not a string.");
			}
			if (S.getSort() == null) {
				Assert.fail(ConstraintErr, "One range of the set of records has no sort.");
			}
			if (S.setLevel == 0) {
				Assert.fail(ConstraintErr, "One range of the set of records is not a set.");
			}
		}
		node.setSort(this.encoder.getSort_sor(node));		
	}

	private final void sof_check(Z3Node node) {
		Z3Node S = node.getDomain(0),
				T = node.getRange(0);
		if (S.getSort() == null) {
			Assert.fail(ConstraintErr, "One domain of sof has no sort.");
		}
		if (T.getSort() == null) {
			Assert.fail(ConstraintErr, "One range of sof has no sort.");
		}
		node.setSort(this.encoder.getSort_sof(node));		
	}

	private final void sso_check(Z3Node node) {
		Z3Node x = node.getBoundedVar(0),
				S = node.getDomain(0),
				p = node.getExpr(0);
		if (p.getSort() != this.encoder.boolSort) {
			Assert.fail(ConstraintErr, "The body of sso is not a predicate.");
		}
		this.unifySort_in(x, S);
		this.unifySort_equivSort(node, S);
	}

	private final void tup_check(Z3Node node) {
		int alen = node.getFieldSize();
		boolean noNullSort = true;
		Z3Node expr = null, field = null;
		for (int i = 0; i < alen; i++) {
			field = node.getField(i);
			expr = node.getExpr(i);
			if (field.getSort() != this.encoder.intSort) {
				Assert.fail(ConstraintErr, "One field of the set of records is not an integer.");
			}						
			if (expr.getSort() == null) {
				noNullSort = false;
			}
		}
		if (noNullSort && alen > 0) {
			node.setSort(this.encoder.getSort_tup(node));
		}		
	}

	private final void subset_check(Z3Node node) {
		Z3Node op0 = node.getOperand(0);
		if (node.setLevel == iNull) {
			node.setLevel = op0.setLevel + 1;
		}
		else if (node.setLevel != op0.setLevel + 1) {
			Assert.fail(ConstraintErr, "Cannot set a set strata to " + node.name + ".");
		}
		if (op0.getSort() != null) {
			node.setSort(this.encoder.getSort_ssort_elem(op0.getSort()));
		}				
		else {
			node.setSetNullSort(op0.setLevel + 1);
		}
	}

	private final void union_check(Z3Node node) {
		Z3Node op0 = node.getOperand(0);
		if (op0.getElemSort() != null) {				
			node.setSort(op0.getElemSort());
		}
		else {
			node.setSetNullSort(op0.setLevel - 1);
		}				
	}

	private final void domain_check(Z3Node node) {
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

	private final void eq_check(Z3Node node) {
		Z3Node lhs = node.getOperand(0),
				rhs = node.getOperand(1);
		this.unifySort_eq(lhs, rhs);
	}

	private final void in_check(Z3Node node) {
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

	private final void notin_check(Z3Node node) {
		Z3Node x = node.getOperand(0),
				S = node.getOperand(1);
		this.unifySort_in(x, S);
	}

	private final void subseteq_check(Z3Node node) {
		Z3Node lhs = node.getOperand(0),
				rhs = node.getOperand(1);
		this.unifySort_equivSort(lhs, rhs);
		lhs.subOpCode = rhs.subOpCode;
	}

	private final void setdiff_check(Z3Node node) {
		Z3Node T = node.getOperand(0),
				U = node.getOperand(1);
		this.unifySort_equivSort(T, U);
		this.unifySort_equivSort(T, node);
		this.unifySort_equivSort(U, node);
	}

	private final void cup_check(Z3Node node) {
		Z3Node T = node.getOperand(0),
				U = node.getOperand(1);
		this.unifySort_equivSort(T, U);
		this.unifySort_equivSort(T, node);
		this.unifySort_equivSort(U, node);
	}

	private final void cap_check(Z3Node node) {
		Z3Node T = node.getOperand(0),
				U = node.getOperand(1);
		this.unifySort_equivSort(T, U);
		this.unifySort_equivSort(T, node);
		this.unifySort_equivSort(U, node);
	}

	//	public Z3Node reconstructTypeForInit(Z3Node node) {
	//		
	//	}
	//	
	//	public Z3Node reconstructTypeForNext(Z3Node node) {
	//		
	//	}
	//	
	//	public Z3Node reconstructTypeForInv(Z3Node node) {
	//	}
}
