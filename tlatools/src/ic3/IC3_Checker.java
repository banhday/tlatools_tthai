package ic3;

import java.io.FileWriter;
import java.io.IOException;
import java.util.*;

import util.Assert;
import z3parser.Z3Constants;
import z3parser.Z3Encoder;
import z3parser.Z3Node;
import z3parser.Z3ErrorCode;
import com.microsoft.z3.*;

public class IC3_Checker implements Z3Constants, Z3ErrorCode, IC3_ErrorCode {
	private Z3Encoder z3Encoder;	
	private ArrayList<Z3SortSymbol> sorts;	
	private ArrayList<Z3FuncSymbol> fcns;
	private ArrayList<Z3VarSymbol> vars;
	//	private ArrayList<Z3VarSymbol> bvars;
//	private Context init_ctx;
//	private Context next_ctx;
	private Context ctx;
	private String[] predNames;
//	private String[] negPredNames;
	private BoolExpr[] preds;
	private BoolExpr[] negPreds;
	private Solver init_solver;
	private Solver next_solver;
	private Solver solver;

	// They are required by Java API to parse SMT-Lib2 strings.
	private Symbol[] t_sortNames;
	private Sort[] t_sorts;
	private Symbol[] t_declNames;
	private FuncDecl[] t_decls;
	
	private int[] predIndexes;

	//	private String nusmvFileName;
//	private int[] sat;
//	private int no;
	private BoolExpr cur_inv;
	private BoolExpr next_inv;

	private ArrayList<IC3_Frame> frames;
	private int k_ic3;

	private IC3_Clause init_clause;
	private IC3_Clause next_clause;

	private IC3_Checker() {}

	public IC3_Checker(Z3Encoder encoder) {
		this.z3Encoder = encoder;		
		this.sorts = new ArrayList<Z3SortSymbol>();
		this.fcns = new ArrayList<Z3FuncSymbol>();
		this.vars = new ArrayList<Z3VarSymbol>();
		this.frames = new ArrayList<IC3_Frame>();
		this.k_ic3 = 0;
		this.init_clause = null;
		this.next_clause = null;
	}

	public Sort getZ3Sort(String sortName) {
		int alen = this.sorts.size();
		for (int i = 0; i < alen; i++) {
			Z3SortSymbol s = this.sorts.get(i);
			if (s.getName().equals(sortName)) {
				return s.getSort();
			}
		}		
		return null;
	}
 
	// From Z3Node to Z3SortSymbol in Java API
	private void createSortList() {
		ArrayList<Z3Node> sorts = this.z3Encoder.getSortList();
		int alen = sorts.size();
		for (int i = 0; i < alen; i++) {
			Z3Node sort = sorts.get(i);
			this.sorts.add(this.createZ3SortSymbol(sort));			
		}
	}

	// From Z3Node to Z3VarSymbol in Java API
	private void createVarList() {
		// Variables in a given TLA+ specification
		Z3Node[] vars = this.z3Encoder.getVarList();
		for (int i = 0; i < vars.length; i++) {
			this.vars.add(this.createZ3VarSymbol(vars[i]));
		}
		// Variables are created during the translation.
		ArrayList<Z3Node> freshVars = this.z3Encoder.getFreshVarList();
		for (int i = 0; i < freshVars.size(); i++) {
			this.vars.add(this.createZ3VarSymbol(freshVars.get(i)));
		}
		// Strings are created during the translation.
		ArrayList<Z3Node> stringVars = this.z3Encoder.getStringList();
		for (int i = 0; i < stringVars.size(); i++) {
			this.vars.add(this.createZ3VarSymbol(stringVars.get(i)));
		}
	}

	// From Z3Nodes to Z3FuncSymbol in Java API
	private void createFcnList() {
		ArrayList<Z3Node> sorts = this.z3Encoder.getSortList();
		int alen = sorts.size();
		for (int i = 0; i < alen; i++) {
			Z3Node sort = sorts.get(i);
			switch (sort.opCode) {
			case OPCODE_fsort: {
				this.fcns.add(this.createZ3FuncSymbol(sort, OPCODE_alpha));
				this.fcns.add(this.createZ3FuncSymbol(sort, OPCODE_domain));
				break;
			}
			case OPCODE_ssort: 
			case OPCODE_sfsort:
			case OPCODE_srsort:
			case OPCODE_stsort: {
				this.fcns.add(this.createZ3FuncSymbol(sort, OPCODE_in));
				break;
			}
			case OPCODE_rsort:
			case OPCODE_tsort: {
				this.fcns.add(this.createZ3FuncSymbol(sort, OPCODE_domain));
				for (int j = 0; j < sort.getFieldSize(); j++) {
					this.fcns.add(this.createZ3FuncSymbol(sort, OPCODE_trsl, j));
				}				
				break;
			}			
			}
		}
	}

	// Z3VarSymbol with a name, an uninterpreted function in Z3 and a symbol in Java API of Z3
	private Z3VarSymbol createZ3VarSymbol(Z3Node var) {
		String name = var.name;
		Symbol symbol = this.ctx.mkSymbol(name);
		Sort sort = this.getZ3Sort(var.getSort().name);
		FuncDecl expr = this.ctx.mkConstDecl(name, sort);
		return new Z3VarSymbol(name, expr, symbol);
	}

	// Z3SortSymbol with a name, an uninterpreted sort in Z3 and a symbol in Java API of Z3
	private Z3SortSymbol createZ3SortSymbol(Z3Node sort) {
		String name = sort.name;		
		if (name.equals(Int)) {			
			return new Z3SortSymbol(name, this.ctx.mkIntSort(), this.ctx.mkIntSort().getName());
		}
		else if (name.equals(Bool)) {
			return new Z3SortSymbol(name, this.ctx.mkBoolSort(), this.ctx.mkBoolSort().getName());
		}
		else if (sort.opCode == OPCODE_rsort || sort.opCode == OPCODE_tsort) {
			Symbol symbol = this.ctx.mkSymbol(name);
			int alen = sort.getFieldSize();
			Symbol[] fields = new Symbol[alen];
			Sort[] codomains = new Sort[alen];
			for (int i = 0; i < alen; i++) {
				fields[i] = this.ctx.mkSymbol(sort.getField(i).name);
				codomains[i] = this.getZ3Sort(sort.getRange(i).name);
			}
			Sort s = this.ctx.mkTupleSort(symbol, fields, codomains);
			return new Z3SortSymbol(name, s, symbol);
		}
		else {
			Symbol symbol = this.ctx.mkSymbol(name);
			Sort s = this.ctx.mkUninterpretedSort(symbol);
			return new Z3SortSymbol(name, s, symbol);
		}
	}	

	private Z3FuncSymbol createZ3FuncSymbol(Z3Node sort, int opCode) {
		switch (opCode) {
		case OPCODE_domain: {
			String name = "domain_" + sort.name;
			Symbol symbol = this.ctx.mkSymbol(name);
			Sort[] inputSorts = new Sort[] { this.getZ3Sort(sort.name) };
			Sort outputSort = this.getZ3Sort(sort.getDomain(0).getSort().name);			
			FuncDecl func = this.ctx.mkFuncDecl(ctx.mkSymbol(name), inputSorts, outputSort);
			return new Z3FuncSymbol(name, func, symbol);			
		}
		case OPCODE_alpha: {
			String name = "alpha_" + sort.name;
			Symbol symbol = this.ctx.mkSymbol(name);
			Sort[] inputSorts = new Sort[] { this.getZ3Sort(sort.name), this.getZ3Sort(sort.dom.name) };
			Sort outputSort = this.getZ3Sort(sort.cod.name);
			FuncDecl func = this.ctx.mkFuncDecl(ctx.mkSymbol(name), inputSorts, outputSort);
			return new Z3FuncSymbol(name, func, symbol);			
		}
		case OPCODE_in: {
			String name = "in_" + sort.name;
			Symbol symbol = this.ctx.mkSymbol(name);
			Sort[] inputSorts = new Sort[] { this.getZ3Sort(sort.getElemSort().name), this.getZ3Sort(sort.name) };
			Sort outputSort = this.ctx.mkBoolSort();
			FuncDecl func = this.ctx.mkFuncDecl(ctx.mkSymbol(name), inputSorts, outputSort);
			return new Z3FuncSymbol(name, func, symbol);			
		}
		default: {
			return null;
		}
		}
	}

	private Z3FuncSymbol createZ3FuncSymbol(Z3Node sort, int opCode, int index) {
		String name = sort.getField(index).name + "_" + sort.name;	
		Symbol symbol = this.ctx.mkSymbol(name);
		FuncDecl func = ((TupleSort) this.getZ3Sort(sort.name)).getFieldDecls()[index];
		return new Z3FuncSymbol(name, func, symbol);		
	}

	// From list to array. Just for efficiency.
	private void constructPredNames() {
		this.predNames = new String[ this.z3Encoder.getPredNames().size() ];
		this.z3Encoder.getPredNames().toArray(this.predNames);		
	}

	private void createContextSolver() {
		HashMap<String, String> cfg = new HashMap<String, String>();
		// For each query, our solve spends at most 10 hours finding a solution and an unsat core.
		cfg.put("model", "true");    
		cfg.put("timeout", "36000000");
		cfg.put("proof", "true");
		cfg.put("unsat_core", "true");
		this.ctx = new Context(cfg);

		// init_solver contains the Init step.
		String initFile = this.z3Encoder.getInitFileName();
		BoolExpr init = this.ctx.parseSMTLIB2File(initFile, null, null, null, null);
		this.init_solver = this.ctx.mkSolver();
		this.init_solver.add(init);

		// next_solve contains the Next step.
		String nextFile = this.z3Encoder.getNextFileName();
		BoolExpr next = this.ctx.parseSMTLIB2File(nextFile, null, null, null, null);
		this.next_solver = this.ctx.mkSolver();
		this.next_solver.add(next);

		// solver is a general one.
		this.solver = this.ctx.mkSolver();

		// Constructs type symbols, fuction symbols and variables.
		this.createSortList();
		this.createVarList();
		this.createFcnList();

		// Save new data types, except Bool and Int.
		this.t_sortNames = new Symbol[ this.sorts.size() - 2];
		for (int i = 0, j = 2; i < this.t_sortNames.length; i++, j++) {			
			t_sortNames[i] = this.sorts.get(j).getSort().getName();			
		}
		this.t_sorts = new Sort[ this.sorts.size() - 2];
		for (int i = 0, j = 2; i < this.t_sorts.length; i++, j++) {			
			t_sorts[i] = this.sorts.get(j).getSort();			
		}

		// Save new function symbols, including variables.
		this.t_declNames = new Symbol[ this.vars.size() + this.fcns.size() ];
		this.t_decls = new FuncDecl[ this.vars.size() + this.fcns.size() ];
		for (int i = 0; i < this.vars.size(); i++) {
			t_declNames[i] = this.vars.get(i).getSymbol();
		}
		for (int i = 0; i < this.vars.size(); i++) {
			t_decls[i] = this.vars.get(i).getVar();
		}
		for (int i = this.vars.size(), j = 0; i < this.vars.size() + this.fcns.size(); i++, j++) {
			t_declNames[i] = this.fcns.get(j).getFunc().getName();
		}
		for (int i = this.vars.size(), j = 0; i < this.vars.size() + this.fcns.size(); i++, j++) {
			t_decls[i] = this.fcns.get(j).getFunc();
		}				
	}

	// cur_inv is P and shifted_inv is P'.
	// next_inv should be renamed to shifted_inv. I will do it later.
	private void createInvs() {
		Z3Node node1 = new Z3Node("assert", OPCODE_assert, this.z3Encoder.boolSort, null, 
				this.z3Encoder.raw_init_inv, tla_atom, NoSet),
				node2 = new Z3Node("assert", OPCODE_assert, this.z3Encoder.boolSort, null, 
						this.z3Encoder.raw_next_inv, tla_atom, NoSet);
		String strInv = this.z3Encoder.z3Tool.printZ3Node(node1, ""),
				strPInv = this.z3Encoder.z3Tool.printZ3Node(node2, "");
		this.cur_inv = this.ctx.parseSMTLIB2String(strInv, this.t_sortNames, this.t_sorts, this.t_declNames, this.t_decls);
		this.next_inv = this.ctx.parseSMTLIB2String(strPInv, this.t_sortNames, this.t_sorts, this.t_declNames, this.t_decls);
	}

	// Including pred, p_pred, not pred.
	// First I tried to use NuSMV as a model checker. 
	// Therefore, primed variables are named as next(pred), instead of p_pred. 
	// Unnecessary stuffs still remain. 
	// I will clean it later.
	private void createBoolExpr_Preds() {
		ArrayList<Z3Node> t_preds = this.z3Encoder.getPredicates();
		//		ArrayList<Z3Node> t_negPreds = this.z3Encoder.getNegPredicates();
		Z3Node pred, negPred, t;
		String str, name;
		int alen = t_preds.size();
		this.preds = new BoolExpr[alen];
		this.negPreds = new BoolExpr[alen];	
		this.predIndexes = new int[alen];		
		int alen_j = this.t_decls.length;		
		for (int i = 0; i < alen; i++) {
			if (i < alen / 2) {
				name = this.predNames[i];
			}
			else {
				// From alen / 2 to alen, a predicate's name is next(pred). 
				name = "p_" + this.predNames[i - alen / 2];
			}
			// Map every predicate to its Z3 symbol.
			for (int j = 0; j < alen_j; j++) {
				if (name.equals(this.t_decls[j].getName().toString())) {
					this.predIndexes[i] = j;
					break;
				}
			}
			// Construct assert pred and assert negPred for Java API
			// Just for convenience. We need to push and pop literals many times to a solver.
			// I don't want to construct a negative literal many times from a positive literal and declare assertions.
			t = new Z3Node(name, OPCODE_const, this.z3Encoder.boolSort, null, tla_atom, NoSet);
			pred = new Z3Node("assert", OPCODE_assert, this.z3Encoder.boolSort, null, t, tla_atom, NoSet);
			str = this.z3Encoder.z3Tool.printZ3Node(pred, "");			
			this.preds[i] = this.ctx.parseSMTLIB2String(str, this.t_sortNames, this.t_sorts, this.t_declNames, this.t_decls);
			t = new Z3Node("not", OPCODE_lnot, this.z3Encoder.boolSort, null, t, tla_atom, NoSet);
			negPred = new Z3Node("assert", OPCODE_assert, this.z3Encoder.boolSort, null, t, tla_atom, NoSet);
			str = this.z3Encoder.z3Tool.printZ3Node(negPred, "");
			this.negPreds[i] = this.ctx.parseSMTLIB2String(str, this.t_sortNames, this.t_sorts, this.t_declNames, this.t_decls);
		}				
	}	

	public void run() throws IOException {
		this.createContextSolver();
		this.constructPredNames();
		this.createBoolExpr_Preds();
		//		this.createNegPredNames();
		this.createInvs();
		// Just want to know how long to check a model.
		String timeFileName = this.z3Encoder.getDir() + "time_" + this.z3Encoder.getSpecFileName() + ".txt";		
		FileWriter file = new FileWriter(timeFileName);
		long start2 = System.nanoTime();
		this.run_ic3();
		long end2 = System.nanoTime();
		file.write(Long.toString(start2) + "\n");
		file.flush();
		file.write(Long.toString(end2) + "\n");
		file.flush();
		file.close();
	}	

	private void run_ic3() throws IOException {
		String fileName = this.z3Encoder.getDir() + "ic3_" + this.z3Encoder.getSpecFileName() + ".txt";
		FileWriter file = new FileWriter(fileName);
		this.constructFrame0();
		this.constructFrame1();
		this.prove(file);
		file.close();
	}

	// Frame 0 is the Init Step
	private void constructFrame0() {
		IC3_Frame frame0 = new IC3_Frame();
		BoolExpr[] assertions = this.init_solver.getAssertions();
		frame0.formula = this.ctx.mkAnd(assertions);
		this.frames.add(frame0);
	}

	// Initially, every frame is P and has only one clause P.
	private IC3_Frame constructPFrame() {
		IC3_Frame frame = new IC3_Frame();
		if (this.init_clause == null) {
			this.init_clause = new IC3_Clause(this.cur_inv);
		}
		if (this.next_clause == null) {
			this.next_clause = new IC3_Clause(this.next_inv);
		}
		frame.formula = this.cur_inv;		
		frame.clauses.add(this.init_clause);
		frame.shifted_clauses.add(this.next_clause);
		return frame;
	}

	// Initially, frame 1 is P. 
	private void constructFrame1() {
		if (this.frames.size() == 1) {
			IC3_Frame frame1 = this.constructPFrame();
			this.frames.add(frame1);
		}
	}

	// Get values of current predicates.
	private BoolExpr[] getCurPreds(Model model) {		
		int alen = this.predNames.length / 2, i , index;		
		Expr tmp;		
		BoolExpr[] res = new BoolExpr[alen];
		for (i = 0; i < alen; i++) {
			index = this.predIndexes[i];
			tmp = model.getConstInterp(this.t_decls[index]);
			if (tmp.equals(this.ctx.mkTrue())) {
				res[i] = this.preds[i];					
			}
			else if (tmp.equals(this.ctx.mkFalse())) {
				res[i] = this.negPreds[i];				
			}
		}
		return res;
	}

	// Get values of current predicates.
	private BoolExpr[] shiftCurPreds(Model model) {		
		int alen = this.predNames.length / 2, i , index;		
		Expr tmp;		
		BoolExpr[] res = new BoolExpr[alen];
		for (i = 0; i < alen; i++) {
			index = this.predIndexes[i];
			tmp = model.getConstInterp(this.t_decls[index]);
			if (tmp.equals(this.ctx.mkTrue())) {
				res[i] = this.preds[i + alen];					
			}
			else if (tmp.equals(this.ctx.mkFalse())) {
				res[i] = this.negPreds[i + alen];				
			}
		}
		return res;
	}

	private BoolExpr[] unshiftPrimedPreds(Model model) {		
		int left = this.predNames.length / 2, i , index;		
		Expr tmp;		
		BoolExpr[] res = new BoolExpr[left];
		for (i = left; i < this.predNames.length; i++) {
			index = this.predIndexes[i];
			tmp = model.getConstInterp(this.t_decls[index]);
			if (tmp.equals(this.ctx.mkTrue())) {
				res[i - left] = this.preds[i - left];					
			}
			else if (tmp.equals(this.ctx.mkFalse())) {
				res[i - left] = this.negPreds[i - left];				
			}
		}
		return res;
	}

	// Construct q' from q.
	// Here, we assume that the first half is for current predicates
	// and the second half is for next predicates. 
	private BoolExpr[] constructPrimedPreds(BoolExpr[] curPreds) {		
		int alen = curPreds.length, i, dis = alen;		
		BoolExpr[] res = new BoolExpr[alen];
		for (i = 0; i < alen; i++) {
			if (curPreds[i].equals(this.ctx.mkTrue())) {
				res[i] = this.preds[i + dis];
			}
			else if (curPreds[i].equals(this.ctx.mkFalse())) {
				res[i] = this.negPreds[i + dis];
			}			
		}		
		return res;
	}

	// Get p' from a given model.
	// Here, we assume that the first half is for current predicates
	// and the second half is for next predicates. 
	private BoolExpr[] getPrimedPreds(Model model) {
		int i0 = this.predNames.length / 2, alen = this.predNames.length, i , index;		
		Expr tmp;		
		BoolExpr[] res = new BoolExpr[i0];
		for (i = i0; i < alen; i++) {
			index = this.predIndexes[i];
			tmp = model.getConstInterp(this.t_decls[index]);
			if (tmp.equals(this.ctx.mkTrue())) {
				res[i - i0] = this.preds[i];					
			}
			else if (tmp.equals(this.ctx.mkFalse())) {
				res[i - i0] = this.negPreds[i];				
			}
		}
		return res;
	}

	// The result is boring. It is just a path for abstraction. 
	// We need to show a concrete path. 
	// Update later.
	private void printBadPath(IC3_StateK statek, FileWriter file) throws IOException {
		String str;
		IC3_StateK q = statek;
		while (q != null) {
			str = this.ctx.mkAnd(q.preds).toString();
			file.write("Step " + Integer.toString(q.k) + ": " + str + "\n");
			file.flush();
			q = q.next;
		}		
	}	

	//	private Expr[] getCurrentConcreteState(Model model) {
	//		Expr[] vars;
	//		for (i = 0; i < alen; i++) {
	//			index = this.predIndexes[i];
	//			tmp = model.getConstInterp(this.t_decls[index]);
	//			if (tmp.equals(this.ctx.mkTrue())) {
	//				res[i] = this.preds[i];					
	//			}
	//			else if (tmp.equals(this.ctx.mkFalse())) {
	//				res[i] = this.negPreds[i];				
	//			}
	//		}
	//		return vars;
	//	}

	// Check sat(I /\ not P)
	private boolean ic3_checkInit(FileWriter file) throws IOException  {		
		BoolExpr initStates = this.frames.get(0).formula;
		this.solver.push();
		this.solver.add(initStates);
		this.solver.add(this.ctx.mkNot(this.cur_inv));
		if (this.solver.check() == Status.SATISFIABLE) {
			file.write("BAD PATH \n");
			file.flush();
			Model model = this.solver.getModel();
			BoolExpr[] badPreds = this.getCurPreds(model);
			String str = (this.ctx.mkAnd(badPreds)).toString();
			file.write("Step 0: " + str + "\n");
			file.flush();			
			//			file.write("Concrete state: " + str + "\n");
			//			file.flush();
			return false;
		}
		this.solver.pop();
		return true;
	}

	// Check sat(I /\ T /\ not P')
	private boolean ic3_goOneStep(FileWriter file) throws IOException  {
		this.next_solver.push();
		BoolExpr initStates = this.frames.get(0).formula;
		this.next_solver.push();
		this.next_solver.add(initStates);
		this.next_solver.add(this.ctx.mkNot(this.next_inv));
		if (this.next_solver.check() == Status.SATISFIABLE) {
			file.write("BAD PATH \n");
			file.flush();
			Model model = this.next_solver.getModel();
			BoolExpr[] badPreds = this.getCurPreds(model);
			String str0 = (this.ctx.mkAnd(badPreds)).toString();
			file.write("Step 0: " +str0 + "\n");
			file.flush();
			badPreds = this.getPrimedPreds(model);
			String str1 = (this.ctx.mkAnd(badPreds)).toString();
			file.write("Step 1: " +str1 + "\n");
			file.flush();
			return false;
		}
		this.next_solver.pop();
		return true;
	}

	// Chech whether there exists two adjacent frames F_i and F_{i+1} s.t. F_i = F_{i+1}.
	private boolean checkFrames(FileWriter file) throws IOException {
		int alen = this.frames.size() - 1;
		for (int i = 0; i < alen; i++) {
			this.solver.push();
			this.solver.add(this.ctx.mkNot(this.ctx.mkEq(this.frames.get(i).formula, 
					this.frames.get(i + 1).formula)));
			if (this.solver.check() == Status.UNSATISFIABLE) {
				file.write("STRENTHEN INVARIANT\n");			
				file.flush();
				Expr inv = this.frames.get(i).formula.simplify();
				file.write(inv.toString());
				file.flush();
				return true;
			}
			this.solver.pop();
		}
		return false;
	}	

	// Before checking unsat(F_i /\ T /\ ~c'), we check whether c \in F_{i+1}.
	private void propagateClauses() {
		for (int i = 1; i < this.k_ic3; i++) {
			IC3_Frame frame = this.frames.get(i),
					frame1 = this.frames.get(i + 1);
			this.next_solver.push();
			this.next_solver.add(frame.formula);
			for (int j = 0; j < frame.clauses.size(); j++) {
				IC3_Clause c = frame.clauses.get(j),  
						shifted_c = frame.shifted_clauses.get(j);
				if (!frame1.hasClause(c)) {
					this.next_solver.push();
					this.next_solver.add(this.ctx.mkNot(shifted_c.formula));
					if (this.next_solver.check() == Status.UNSATISFIABLE) {						
						frame1.formula = this.ctx.mkAnd(new BoolExpr[] { frame1.formula, c.formula });
						frame1.clauses.add(c);
						frame1.shifted_clauses.add(shifted_c);
					}
					this.next_solver.pop();
				}			
			}
			this.next_solver.pop();
		}
		//		System.out.println(this.next_solver.toString());
	}

	// Get an element <q, i> of states s.t. i is minimal.
	private IC3_StateK getMinimalState(ArrayList<IC3_StateK> states) {
		int maxN = this.k_ic3 + 1,
				alen = states.size(), 
				pos = alen + 1;
		for (int i = 0; i < alen; i++) {
			if (states.get(i).k < maxN) {
				pos = i;
				maxN = states.get(i).k;				
			}
		}
		return states.get(pos);
	}

	// sat(F_0 /\ T /\ ~q /\ q')
	private boolean hasBadStatesAtStep1(IC3_StateK statek, FileWriter file) throws IOException {		
		BoolExpr F0 = this.frames.get(0).formula,
				notQ = this.ctx.mkNot(this.ctx.mkAnd(statek.preds)),
				shiftedQ = this.ctx.mkAnd(statek.shifted_preds);				
		boolean res = false;
		this.next_solver.push();
		this.next_solver.add(F0);
		this.next_solver.add(notQ);
		this.next_solver.add(shiftedQ);
		if (this.next_solver.check() == Status.SATISFIABLE) {
			Model model = this.next_solver.getModel();
			BoolExpr[] badPreds = this.getCurPreds(model),
					shiftedBadPreds = this.shiftCurPreds(model);
			// badState is at the initial step.
			IC3_StateK badState = new IC3_StateK(badPreds, shiftedBadPreds, statek.k - 1);
			badState.next = statek;
			this.printBadPath(badState, file);
			res = true;
		}		
		this.next_solver.pop();
		return res;
	}

	// Find a maximal I s.t. unsat(F_i /\ T /\ ~q /\ q')
	// ~q is inductive until q.k - 2
	private int findI(IC3_StateK q) {
		//		System.out.println(this.next_solver.toString());
		this.next_solver.push();
		this.next_solver.add(this.ctx.mkAnd(q.shifted_preds));
		this.next_solver.add(this.ctx.mkNot(this.ctx.mkAnd(q.preds)));	
		int left = q.k - 2, right = this.frames.size() - 1, res = -1;
		if (left < 1) {
			left = 1;
		}
//		for (int mid = left; mid <= right; mid++) {
		for (int mid = left; mid < right; mid++) {
			this.next_solver.push();
			this.next_solver.add(this.frames.get(mid).formula);
			Status status = this.next_solver.check();
			if (status == Status.SATISFIABLE) {
				this.next_solver.pop();
				res = mid;
				break;
			}
			if (status == Status.UNKNOWN) {
				this.next_solver.pop();
				Assert.fail(Z3Err, "Z3 cannot solve Fi /\\ T /\\ ~q /\\ q");
			}
			this.next_solver.pop();
		}
		this.next_solver.pop();
		// It is a risky assumption. If the query is unsat at all frames, we assume that it is sat at a "fresh" frame.
		if (res == -1) {
			res = right + 1;
		}
		return res - 1;
	}

	// F = F /\ c
	// Add an inductive strethening to a frame.
	private void addC(IC3_Clause clause, IC3_Clause shifted_clause, int alen) {
		IC3_Frame frame;		
		if (alen > this.frames.size()) {
			alen = this.frames.size();
		}
		for (int i = 1; i < alen; i++) {
			frame = this.frames.get(i);
			frame.formula = this.ctx.mkAnd(frame.formula, clause.formula);
			frame.clauses.add(clause);
			frame.shifted_clauses.add(shifted_clause);
		}
	}

	// W is a model for sat(F_{j+1} /\ T /\ ~q /\ q')
	private Model getW(IC3_Frame frame, IC3_StateK q) {
		Model w = null;
		this.next_solver.push();
		this.next_solver.add(frame.formula);
		this.next_solver.add(this.ctx.mkNot(this.ctx.mkAnd(q.preds)));
		this.next_solver.add(this.ctx.mkAnd(q.shifted_preds));		
		Status status = this.next_solver.check();
		if (status == Status.SATISFIABLE) {
			w = this.next_solver.getModel();
		}
		else if (status == Status.UNKNOWN) {
			Assert.fail(Z3Err, "Z3 cannot find a model.");
		}
		this.next_solver.pop();
		return w;
	}

	// Find an unsat core from unsat(F_i /\ T /\ ~q /\ q')
	// Here, an unsat core is a set of predicates of q'.
	// Therefore, it contains primed predicates.
	// To have an inductive strethening, we need to unshift the found unsat core. 
	private BoolExpr[] findUnsatCore(IC3_Frame F, IC3_StateK q) {

		this.next_solver.push();
		this.next_solver.add(F.formula);
		Status status = this.next_solver.check(q.shifted_preds);
		if (status == Status.SATISFIABLE) {
			this.next_solver.pop();
			return q.shifted_preds;
		}
		BoolExpr[] res = this.next_solver.getUnsatCore();
		if (res.length == 0) {
			res = q.shifted_preds;
		}
		this.next_solver.pop();
		return res;
	}

	// Construct an unprimed unsat core.
	private BoolExpr[] unshiftUnsatCore(BoolExpr[] core) {
		int alen = core.length, dis = this.preds.length / 2;		
		BoolExpr[] unshifted_core = new BoolExpr[alen];		
		for (int i = 0; i < core.length; i++) {
			String str = core[i].toString();
			int predLen = str.length();
			for (int j = dis; j < this.preds.length; j++) {
				String predName = this.preds[j].toString();
				int index = str.indexOf(predName);					
				if ((index == 0 && index + predName.length() == predLen) ||
						(index == 5 && index + predName.length() + 1 == predLen)) {
					if (str.indexOf("(not") >= 0) {
						unshifted_core[i] = this.negPreds[j - dis];
					}
					else {
						unshifted_core[i] = this.preds[j - dis];
					}
					break;
				}
			}
		}
		return unshifted_core;
	}
	
	// Negate a conjunction.
	private BoolExpr negConj(BoolExpr[] conj) {
		BoolExpr[] tmp = new BoolExpr[conj.length];
		for (int i = 0; i < conj.length; i++) {
			tmp[i] = this.ctx.mkNot(conj[i]);
		}
		BoolExpr res = this.ctx.mkOr(tmp);
		return res;
	}

	// Remove bad states
	private boolean removeCTI(IC3_StateK badState, FileWriter file) throws IOException {		
		ArrayList<IC3_StateK> states = new ArrayList<IC3_StateK>();
		states.add(badState);
		BoolExpr[] t, p_t;
		Model w;
		IC3_Clause indStr, shifted_indStr;
		while (states.size() > 0) {
			// System.out.println(this.next_solver.toString());
			IC3_StateK curStateK = this.getMinimalState(states);
			if (this.hasBadStatesAtStep1(curStateK, file)) {				
				return false;
			}
			// System.out.println(this.next_solver.toString());
			int i = this.findI(curStateK);
			BoolExpr[] unsatCore = this.findUnsatCore(this.frames.get(i), curStateK),
					unshifted_unsatCore = this.unshiftUnsatCore(unsatCore);			
			indStr = new IC3_Clause(this.negConj(unshifted_unsatCore));
			shifted_indStr = new IC3_Clause(this.negConj(unsatCore));
			// i + 2 since clause is added into frames 1, ..., i + 1 
			this.addC(indStr , shifted_indStr, i + 2); 
			if (i + 1 >= curStateK.k) {
				return true;
			}
			// w is not always null.
			// t is a predecessor of a bad state.
			w = this.getW(this.frames.get(i + 1), curStateK);
			t = this.getCurPreds(w);
			p_t = this.shiftCurPreds(w);
			IC3_StateK newState = new IC3_StateK(t, p_t, i + 1);
			newState.next = curStateK;
			states.add(newState);
		}
		return false;
	}

	private void addNewFrame() {
		IC3_Frame newFrame = this.constructPFrame();
		this.frames.add(newFrame);
		this.k_ic3++;
	}

	private boolean extendFrontier(FileWriter file) throws IOException {
		this.addNewFrame();
		this.next_solver.push();
		this.next_solver.add(this.ctx.mkNot(this.next_inv));
		this.next_solver.add(this.frames.get(this.k_ic3 - 1).formula);		
		// check sat(T /\ ~P /\ F_k)
		// nextBadState --> ~P' and in F_{k+1} 
		// curBadState is a predecessor of nextBadState and in F_k.
		while (this.next_solver.check() == Status.SATISFIABLE) {
			Model model = this.next_solver.getModel();
			BoolExpr[] badPreds = this.getCurPreds(model);
			BoolExpr[] shifted_badPreds = this.shiftCurPreds(model);
			IC3_StateK curBadState = new IC3_StateK(badPreds, shifted_badPreds, this.k_ic3 - 1);
			BoolExpr[] nextBadPreds = this.getPrimedPreds(model);
			BoolExpr[] unshifted_nextBadPreds = this.unshiftPrimedPreds(model);
			IC3_StateK nextBadState = new IC3_StateK(unshifted_nextBadPreds, nextBadPreds, this.k_ic3);
			curBadState.next = nextBadState;
			this.next_solver.pop();
			if (!this.removeCTI(curBadState, file)) {
				return false;
			}			
			this.next_solver.push();
			this.next_solver.add(this.ctx.mkNot(this.next_inv));
			this.next_solver.add(this.frames.get(this.k_ic3 - 1).formula);
		}		
		this.next_solver.pop();		
		return true;
	}
		
	private boolean prove(FileWriter file) throws IOException {		
		if (!ic3_checkInit(file)) {
			return false;
		}
		if (!ic3_goOneStep(file)) {
			return false;
		}
		this.k_ic3 = 1;
		while (true) {		
			if (!this.extendFrontier(file)) {
				return false;
			}
			this.propagateClauses();
			if (this.checkFrames(file)) {
				return true;
			}			
		}		
	}
}
