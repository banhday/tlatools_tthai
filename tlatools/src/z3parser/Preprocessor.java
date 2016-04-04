package z3parser;

import java.util.ArrayList;

import tla2sany.modanalyzer.SpecObj;
import tla2sany.semantic.APSubstInNode;
import tla2sany.semantic.ExprOrOpArgNode;
import tla2sany.semantic.FormalParamNode;
import tla2sany.semantic.LabelNode;
import tla2sany.semantic.LetInNode;
import tla2sany.semantic.OpApplNode;
import tla2sany.semantic.OpDefNode;
import tla2sany.semantic.SemanticNode;
import tla2sany.semantic.Subst;
import tla2sany.semantic.SubstInNode;
import tla2sany.semantic.SymbolNode;
import tlc2.tool.Action;
import tlc2.tool.BuiltInOPs;
import tlc2.tool.ContextEnumerator;
import tlc2.tool.EvalControl;
import tlc2.tool.TLCState;
import tlc2.tool.Tool;
import tlc2.tool.ToolGlobals;
import tlc2.util.Context;
import tlc2.util.Vect;
import tlc2.value.Value;
import tlc2.value.ValueConstants;
import util.Assert;

public class Preprocessor implements ValueConstants, ToolGlobals {
	private ArrayList<String> actionNames;
	private Tool tool;
	private int index;
	private Vect actionVec = new Vect(10);
	private String actionName;
	
	public Preprocessor(Tool tool, ArrayList<String> actionNames) {
		this.tool = tool;
		this.actionNames = actionNames;
		this.index = 0;
		this.actionName = "";
	}
	
  //Example \exists x \in {1, 2, 3}: Lbl0(x) with a label Lbl0
	// There are three actions Lbl0 in the action list since x has
	// three possible values. Therefore, we need three corresponding 
	// predicates which are Lbl0(1), Lbl0(2) and Lbl0(3).
	// renameActions will change names of actions by combining it 
	// with indices.
	private final void renameActions() {		
		int alen = this.actionNames.size();
		int count;
		String name;
		for (int i = 0; i < alen; i++) {
			// calculate the number of appearances of an action
			count = 0;			
			for (int j = i + 1; j < alen; j++) {
				if (this.actionNames.get(i).endsWith(this.actionNames.get(j))) {
					count++;
				}
			}
			// combine an action name with its index
			name = this.actionNames.get(i) + String.valueOf(count);
			this.actionNames.set(i, name);			
		}			
	}
	
	private final void getAction() {		
		Action next = this.tool.getNextStateSpec();
		if (next != null) {
			this.getActions(next.pred, next.con);
		}			    
		return;
	}
	
	private final void getActions(SemanticNode next, Context con) {
		switch (next.getKind()) {
		case OpApplKind:
		{
			OpApplNode next1 = (OpApplNode)next;
			this.getActionsAppl(next1, con);
			return;
		}
		case LetInKind:
		{
			LetInNode next1 = (LetInNode)next;
			this.getActions(next1.getBody(), con);
			return;
		}
		case SubstInKind:
		{
			SubstInNode next1 = (SubstInNode)next;
			Subst[] substs = next1.getSubsts();
			if (substs.length == 0) {
				this.getActions(next1.getBody(), con);
			}
			else {
				Action action = new Action(next1, con);
				this.actionVec.addElement(action);
				this.actionNames.add(this.actionName + "_id_" + Integer.toString(index++));
			}
			return;
		}

		// Added by LL on 13 Nov 2009 to handle theorem and assumption names.
		case APSubstInKind:
		{
			APSubstInNode next1 = (APSubstInNode)next;
			Subst[] substs = next1.getSubsts();
			if (substs.length == 0) {
				this.getActions(next1.getBody(), con);
			}
			else {
				Action action = new Action(next1, con);
				this.actionVec.addElement(action);
				this.actionNames.add(this.actionName + "_id_" + Integer.toString(index++));
			}
			return;
		}

		/***********************************************************************
		 * LabelKind class added by LL on 13 Jun 2007.                          *
		 ***********************************************************************/
		case LabelKind:
		{
			LabelNode next1 = (LabelNode)next;
			this.getActions(next1.getBody(), con);
			return;
		}
		default:
		{
			Assert.fail("The next state relation is not a boolean expression.\n" + next);
		}
		}
	}

	private final void getActionsAppl(OpApplNode next, Context con) {
		ExprOrOpArgNode[] args = next.getArgs();
		SymbolNode opNode = next.getOperator();
		int opcode = BuiltInOPs.getOpCode(opNode.getName());

		if (opcode == 0) {
			Object val = this.tool.lookup(opNode, con, false);

			if (val instanceof OpDefNode) {
				OpDefNode opDef = (OpDefNode)val;
				opcode = BuiltInOPs.getOpCode(opDef.getName());
				if (opcode == 0) {
					try {
						FormalParamNode[] formals = opDef.getParams();
						int alen = args.length;
						int argLevel = 0;
						for (int i = 0; i < alen; i++) {
							argLevel = args[i].getLevel();
							if (argLevel != 0) break;
						}
						if (argLevel == 0) {
							Context con1 = con;
							for (int i = 0; i < alen; i++) {
								Value aval = this.tool.eval(args[i], con, TLCState.Empty);
								con1 = con1.cons(formals[i], aval);
							}
							this.actionName = opDef.getName().toString();
							this.getActions(opDef.getBody(), con1);
							return;
						}
					}
					catch (Throwable e) { /*SKIP*/ }
				}
			}
			if (opcode == 0) {
				Action action = new Action(next, con);
				this.actionVec.addElement(action);
				this.actionNames.add(this.actionName + "_id_" + Integer.toString(index++));
				return;
			}
		}

		switch (opcode) {
		case OPCODE_be:     // BoundedExists
		{
			int cnt = this.actionVec.size();
			try {
				ContextEnumerator Enum =
						this.tool.contexts(next, con, TLCState.Empty, TLCState.Empty, EvalControl.Clear);
				Context econ;
				while ((econ = Enum.nextElement()) != null) {
					this.getActions(args[0], econ);
				}
			}
			catch (Throwable e) {
				Action action = new Action(next, con);
				this.actionVec.removeAll(cnt);
				this.actionNames.clear();
				this.actionVec.addElement(action);
				this.actionNames.add(this.actionName + "_id_" + Integer.toString(index++));
			}
			return;
		}
		case OPCODE_dl:     // DisjList
		case OPCODE_lor:      
		{
			for (int i = 0; i < args.length; i++) {
				this.getActions(args[i], con);
			}
			return;
		}
		default:
		{
			// We handle all the other builtin operators here.
			Action action = new Action(next, con);
			this.actionVec.addElement(action);
			this.actionNames.add(this.actionName + "_id_" + Integer.toString(index++));
			return;
		}
		}
	}
	
	public final void GetActions(SpecObj spec) {
		this.tool.init(true, spec);     
		this.tool.getImpliedInits(); 		// implied-inits to be checked
		this.tool.getInvariants(); 			// invariants to be checked
		this.tool.getImpliedActions(); 	// implied-actions to be checked
		this.tool.getActions(); 							// the sub-actions --> need for names
		this.getAction();
	}
	
	/**
	 * This method returns the set of all possible actions of the 
	 * spec, and sets the actions field of this object. In fact, we
	 * could simply treat the next predicate as one "giant" action.
	 * But for efficiency, we preprocess the next state predicate by 
	 * splitting it into a set of actions for the maximum prefix
	 * of disjunction and existential quantification.
	 */
	
	public final void ChangeActionNames() {
		Action next = this.tool.getNextStateSpec();
		this.getActions(next.pred, next.con);		
	}
}
