package ic3;

import java.io.FileWriter;
import java.io.IOException;
import java.util.*;
import z3parser.Z3Constants;
import z3parser.Z3Encoder;
import z3parser.Z3Node;
import com.microsoft.z3.*;

public class IC3_Checker implements Z3Constants {
	private Z3Encoder z3Encoder;	
	private ArrayList<Z3SortSymbol> sorts;	
	private ArrayList<Z3FuncSymbol> fcns;
	private ArrayList<Z3VarSymbol> vars;
//	private ArrayList<Z3VarSymbol> bvars;
	private Context init_ctx;
	private Context next_ctx;
	private Context ctx;
//	private int de_Bruijn_index;
	private String[] predNames;
	private String[] negPredNames;
	private BoolExpr[] preds;
	private BoolExpr[] negPreds;
	private Solver init_solver;
	private Solver next_solver;
	private Solver solver;
	
	private Symbol[] t_sortNames;
	private Sort[] t_sorts;
	private Symbol[] t_declNames;
	private FuncDecl[] t_decls;
	private int[] predIndexes;
	
	private String nusmvFileName;
	private int[] sat;
	private int no;
	private BoolExpr init_inv;
	private BoolExpr next_inv;
	
	private ArrayList<IC3_Frame> frames;
	private int k_ic3;
	
	private IC3_Clause init_clause;
	private IC3_Clause next_clause;
	
	
//	private Symbol[] 	sortNames;
//	private Sort[] 	sorts;
//	private Symbol[] 	declNames;
//	private FuncDecl[] 	decls;
	
	private IC3_Checker() {}
	
	public IC3_Checker(Z3Encoder encoder) {
		this.z3Encoder = encoder;		
		this.sorts = new ArrayList<Z3SortSymbol>();
		this.fcns = new ArrayList<Z3FuncSymbol>();
		this.vars = new ArrayList<Z3VarSymbol>();
//		this.bvars = new ArrayList<Z3VarSymbol>();
//		this.de_Bruijn_index = 0;
		this.frames = new ArrayList<IC3_Frame>();
		this.k_ic3 = 0;
		this.init_clause = null;
		this.next_clause = null;
	}
	
//	private void test() {				
//
//		ctx.mkSymbol("f__f");
//		ctx.mkSymbol("x__x");
//		ctx.mkSymbol("y__y");
//
//		Expr x = this.ctx.mkConst("x__x", this.getZ3Sort("tla_sort_Str"));
//		Expr y = this.ctx.mkConst("y__y", this.getZ3Sort("tla_sort_Str"));
//		FuncDecl f = this.ctx.mkFuncDecl("f__f", this.getZ3Sort("tla_sort_Str"), this.getZ3Sort("tla_sort_Str"));
//
//		Solver solver = this.ctx.mkSolver();
//
//		solver.push();
//
//		BoolExpr expr1 = this.ctx.mkAnd(ctx.mkEq(x, y), this.ctx.mkNot(ctx.mkEq(ctx.mkApp(f, x), this.ctx.mkApp(f, y))));
//
//		solver.add(expr1);
//
//		System.out.println(solver.toString());
//
//		if (solver.check() == Status.SATISFIABLE) {
//			System.out.println("SAT");
//		}
//		else if (solver.check() == Status.UNSATISFIABLE) {
//			System.out.println("UNSAT");
//		}
//		else {
//			System.out.println("UNKNOWN");
//		}
//
//
//		solver.pop();
//
//		solver.push();
//
//		BoolExpr expr2 = this.ctx.mkAnd(ctx.mkEq(x, x), this.ctx.mkEq(ctx.mkApp(f, x), this.ctx.mkApp(f, y)));
//		BoolExpr expr3 = this.ctx.mkAnd(ctx.mkEq(x, x));
//
//		solver.add(expr2);
//		solver.add(expr3);
//
//		System.out.println(solver.toString());
//
//		if (solver.check() == Status.SATISFIABLE) {
//			System.out.println("SAT");
//		}
//		else if (solver.check() == Status.UNSATISFIABLE) {
//			System.out.println("UNSAT");
//		}
//		else {
//			System.out.println("UNKNOWN");
//		}
//
//		solver.pop();
//
//		ctx.dispose();
//	}
//	
//	void quantifierExample1(Context ctx)
//  {
//      System.out.println("QuantifierExample");
////      Log.append("QuantifierExample");
//
//      Sort[] types = new Sort[3];
//      IntExpr[] xs = new IntExpr[3];
//      Symbol[] names = new Symbol[3];
//      IntExpr[] vars = new IntExpr[3];
//
//      for (int j = 0; j < 3; j++)
//      {
//          types[j] = this.ctx.getIntSort();
//          names[j] = this.ctx.mkSymbol("x_" + Integer.toString(j));
//          xs[j] = (IntExpr) this.ctx.mkConst(names[j], types[j]);
//          vars[j] = (IntExpr) this.ctx.mkBound(2 - j, types[j]); // <-- vars
//                                                            // reversed!
//      }
//
//      Expr body_vars = this.ctx.mkAnd(
//              this.ctx.mkEq(ctx.mkAdd(vars[0], this.ctx.mkInt(1)), this.ctx.mkInt(2)),
//              this.ctx.mkEq(ctx.mkAdd(vars[1], this.ctx.mkInt(2)),
//                      this.ctx.mkAdd(vars[2], this.ctx.mkInt(3))));
//
//      Expr body_const = this.ctx.mkAnd(
//              this.ctx.mkEq(ctx.mkAdd(xs[0], this.ctx.mkInt(1)), this.ctx.mkInt(2)),
//              this.ctx.mkEq(ctx.mkAdd(xs[1], this.ctx.mkInt(2)),
//                      this.ctx.mkAdd(xs[2], this.ctx.mkInt(3))));
//
//      Expr x = this.ctx.mkForall(types, names, body_vars, 1, null, null,
//              this.ctx.mkSymbol("Q1"), this.ctx.mkSymbol("skid1"));
//      System.out.println("Quantifier X: " + x.toString());
//
//      Expr y = this.ctx.mkForall(xs, body_const, 1, null, null,
//              this.ctx.mkSymbol("Q2"), this.ctx.mkSymbol("skid2"));
//      System.out.println("Quantifier Y: " + y.toString());
//  }
//
//	
//	public void run1() throws IOException {
//		ArrayList<String> files = this.z3Encoder.getFileNames();
//		for (int i = 0; i < files.size(); i++) {
//			String fileName = files.get(i);
//			HashMap<String, String> cfg = new HashMap<String, String>();
//	    cfg.put("model", "true");
//	    cfg.put("timeout", "36000000");
//	    Context t_ctx = new Context(cfg);
//	    Symbol[] sortNames = null;
//	    Sort[] sorts = null; 
//	    Symbol[] declNames = null;
//	    FuncDecl[] decls = null;
//	    BoolExpr res = t_ctx.parseSMTLIB2File(fileName, sortNames, sorts, declNames, decls);
//	    Solver solver = t_ctx.mkSolver();
//	    solver.add(res);
//	    String fileName1 = fileName.replaceAll(".txt", "_1.txt");			
//			FileWriter file1 = new FileWriter(fileName1);
//			file1.flush();
//			String str = solver.toString();
//			file1.write(str);
//			if (solver.check() == Status.SATISFIABLE) {
//	    	file1.write("SAT");
//	    }
//	    else if (solver.check() == Status.UNSATISFIABLE) {
//	    	file1.write("UNSAT");
//	    }
//	    else {
//	    	file1.write("UNKNOWN");
//	    }
//			file1.flush();
//			file1.close();
//		}
//	}
	
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
	
	private void createSortList() {
		ArrayList<Z3Node> sorts = this.z3Encoder.getSortList();
		int alen = sorts.size();
		for (int i = 0; i < alen; i++) {
			Z3Node sort = sorts.get(i);
			this.sorts.add(this.createZ3SortSymbol(sort));			
		}
	}
	
	private void createVarList() {
		Z3Node[] vars = this.z3Encoder.getVarList();
		for (int i = 0; i < vars.length; i++) {
			this.vars.add(this.createZ3VarSymbol(vars[i]));
		}
		ArrayList<Z3Node> freshVars = this.z3Encoder.getFreshVarList();
		for (int i = 0; i < freshVars.size(); i++) {
			this.vars.add(this.createZ3VarSymbol(freshVars.get(i)));
		}
		ArrayList<Z3Node> stringVars = this.z3Encoder.getStringList();
		for (int i = 0; i < stringVars.size(); i++) {
			this.vars.add(this.createZ3VarSymbol(stringVars.get(i)));
		}
	}
	
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
	
	private Z3VarSymbol createZ3VarSymbol(Z3Node var) {
		String name = var.name;
		Symbol symbol = this.ctx.mkSymbol(name);
		Sort sort = this.getZ3Sort(var.getSort().name);
		FuncDecl expr = this.ctx.mkConstDecl(name, sort);
		return new Z3VarSymbol(name, expr, symbol);
	}
	
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
	
//	private Expr getGlobalVarSymbol(String name) {
//		int alen = this.vars.size();
//		for (int i = 0; i < alen; i++) {
//			Z3VarSymbol var = this.vars.get(i);
//			if (var.getName().equals(name)) {
//				return var.getVar();
//			}
//		}
//		return null;
//	}
//	
//	private Expr getBoundVarSymbol(String name) {
//		int alen = this.bvars.size();
//		for (int i = 0; i < alen; i++) {
//			Z3VarSymbol var = this.bvars.get(i);
//			if (var.getName().equals(name)) {
//				return var.getVar();
//			}
//		}
//		return null;
//	}
//	
//	private FuncDecl getFuncSymbol(String name) {
//		int alen = this.fcns.size();
//		for (int i = 0; i < alen; i++) {
//			Z3FuncSymbol fcn = this.fcns.get(i);
//			if (fcn.getName().equals(name)) {
//				return fcn.getFunc();
//			}
//		}
//		return null;
//	}
	
//	private Expr createZ3ExprTree(Z3Node node) {
//		Expr res;
//		switch (node.opCode) {
//		case OPCODE_const: {
//			if (node.getSort().name.equals(Int)) {
//				res = this.ctx.mkInt(node.name);
//				break;
//			}
//			else {
//				res = this.getGlobalVarSymbol(node.name);
//				break;
//			}
//		}
//		case OPCODE_bv: {
//			res = this.getBoundVarSymbol(node.name);
//			break;
//		}
//		case OPCODE_add: {
//			res = this.ctx.mkMul((ArithExpr) this.createZ3ExprTree(node.getOperand(0)), 
//					 (ArithExpr) this.createZ3ExprTree(node.getOperand(1)));
//			break;
//		}
//		case OPCODE_mul: {
//			res = this.ctx.mkMul((ArithExpr) this.createZ3ExprTree(node.getOperand(0)), 
//					 (ArithExpr) this.createZ3ExprTree(node.getOperand(1)));
//			break;
//		}
//		case OPCODE_sub: {
//			res = this.ctx.mkSub((IntExpr) this.createZ3ExprTree(node.getOperand(0)), 
//					 (IntExpr) this.createZ3ExprTree(node.getOperand(1)));
//			break;
//		}
//		case OPCODE_div: {
//			res = this.ctx.mkDiv((IntExpr) this.createZ3ExprTree(node.getOperand(0)), 
//					 (IntExpr) this.createZ3ExprTree(node.getOperand(1)));
//			break;
//		}
//		case OPCODE_mod: {
//			res = this.ctx.mkMod((IntExpr) this.createZ3ExprTree(node.getOperand(0)), 
//					 (IntExpr) this.createZ3ExprTree(node.getOperand(1)));
//			break;
//		}
//		case OPCODE_lt: {
//			res = this.ctx.mkLt((ArithExpr) this.createZ3ExprTree(node.getOperand(0)), 
//					 (ArithExpr) this.createZ3ExprTree(node.getOperand(1)));
//			break;
//		}
//		case OPCODE_le: {
//			res = this.ctx.mkLe((ArithExpr) this.createZ3ExprTree(node.getOperand(0)), 
//					 (ArithExpr) this.createZ3ExprTree(node.getOperand(1)));
//			break;
//		}
//		case OPCODE_gt: {
//			res = this.ctx.mkGt((ArithExpr) this.createZ3ExprTree(node.getOperand(0)), 
//					 (ArithExpr) this.createZ3ExprTree(node.getOperand(1)));
//			break;
//		}
//		case OPCODE_ge: {
//			res = this.ctx.mkGe((ArithExpr) this.createZ3ExprTree(node.getOperand(0)), 
//					 (ArithExpr) this.createZ3ExprTree(node.getOperand(1)));
//			break;
//		}
//		case OPCODE_true: {
//			res = this.ctx.mkTrue();
//			break;
//		}
//		case OPCODE_false: {
//			res = this.ctx.mkFalse();
//			break;
//		}
//		case OPCODE_lnot: {
//			res = this.ctx.mkNot((BoolExpr) this.createZ3ExprTree(node.getOperand(0)));
//			break;
//		}
//		case OPCODE_land: {
//			int alen = node.getOperandSize();
//			BoolExpr[] exprs = new BoolExpr[ alen ];
//			for (int i = 0; i < alen; i++) {
//				exprs[i] = (BoolExpr) this.createZ3ExprTree(node.getOperand(i));
//			}
//			res = this.ctx.mkAnd(exprs);
////			res = this.ctx.mkAnd(exprs[0], exprs[1]);
//			break;
//		}
//		case OPCODE_lor: {
//			int alen = node.getOperandSize();
//			BoolExpr[] exprs = new BoolExpr[ alen ];
//			for (int i = 0; i < alen; i++) {
//				exprs[i] = (BoolExpr) this.createZ3ExprTree(node.getOperand(i));
//			}
//			res = this.ctx.mkOr(exprs);
//			break;
//		}		
//		case OPCODE_implies: {
//			int alen = node.getOperandSize();
//			BoolExpr[] exprs = new BoolExpr[ alen ];
//			for (int i = 0; i < alen; i++) {
//				exprs[i] = (BoolExpr) this.createZ3ExprTree(node.getOperand(i));
//			}
//			res = this.ctx.mkImplies(exprs[0], exprs[1]);
//			break;
//		}
//		case OPCODE_ite: {
//			BoolExpr con = (BoolExpr) this.createZ3ExprTree(node.getOperand(0));
//			Expr expr1 = this.createZ3ExprTree(node.getOperand(1)),
//					expr2  = this.createZ3ExprTree(node.getOperand(2));
//			res = this.ctx.mkITE(con, expr1, expr2);
//			break;
//		}
//		case OPCODE_eq: {
//			res = this.ctx.mkEq(this.createZ3ExprTree(node.getOperand(0)), 
//					 this.createZ3ExprTree(node.getOperand(1)));
//			break;
//		}
//		case OPCODE_be: {
//			int bvNo = node.getBoundedVarSize();
//			Sort[] sorts = new Sort[bvNo];
//			Symbol[] names = new Symbol[bvNo];	
//			Expr[] xs = new Expr[bvNo];
//			for (int i = 0; i < bvNo; i++) {
//				Z3Node bvar = node.getBoundedVar(i);
//				String sortName = bvar.getSort().name;
//				sorts[i] = this.getZ3Sort(sortName);
//				names[i] = this.ctx.mkSymbol(bvar.name);
//				xs[i] = this.ctx.mkBound(this.de_Bruijn_index++, sorts[i]);
//				this.bvars.add(new Z3VarSymbol(bvar.name, xs[i]));
//			}
//			Expr body = this.createZ3ExprTree(node.getExpr(0));
//			res = this.ctx.mkExists(sorts, names, body, 0, null, null, null, null);
//			this.de_Bruijn_index -= bvNo;
//			break;
//		}
//		case OPCODE_bf: {
//			int bvNo = node.getBoundedVarSize();
//			Sort[] sorts = new Sort[bvNo];
//			Symbol[] names = new Symbol[bvNo];
//			Expr[] xs = new Expr[bvNo];
//			for (int i = 0; i < bvNo; i++) {
//				Z3Node bvar = node.getBoundedVar(i);
//				String sortName = bvar.getSort().name;
//				sorts[i] = this.getZ3Sort(sortName);	
//				names[i] = this.ctx.mkSymbol(bvar.name);				
//				xs[i] = this.ctx.mkBound(this.de_Bruijn_index++, sorts[i]);
//				this.bvars.add(new Z3VarSymbol(bvar.name, xs[i]));
//			}
//			Expr body = this.createZ3ExprTree(node.getExpr(0));
//			res = this.ctx.mkForall(sorts, names, body, 0, null, null, null, null);
//			this.de_Bruijn_index -= bvNo;
//			break;
//		}
//		case OPCODE_in: 
//		case OPCODE_domain: 
//		case OPCODE_alpha: {
//			FuncDecl fcn = this.getFuncSymbol(node.name);
//			int alen = node.getOperandSize();
//			Expr[] args = new Expr[alen];
//			for (int i = 0; i < alen; i++) {
//				args[i] = this.createZ3ExprTree(node.getOperand(i));
//			}
//			res = this.ctx.mkApp(fcn, args);
//			break;
//		}
//		case OPCODE_trsl: 
//		case OPCODE_rs: {
//			Z3Node var = node.getOperand(0),
//					field = node.getOperand(1);
//			String fcnName = field.name + "_" + var.name;
//			FuncDecl fcn = this.getFuncSymbol(fcnName);
//			Expr arg = this.createZ3ExprTree(var);
//			res = fcn.apply(arg);
//			break;
//		}
//		default: {
//			res = null;
//			break;
//		}
//		}		
//		return res;
//	}
//	
//	private void constructAxioms(Solver solver) {
//		ArrayList<Z3Node> axioms = this.z3Encoder.getAxioms();
//		int alen = axioms.size();
//		for (int i = 0; i < alen; i++) {
//			Z3Node expr = axioms.get(i);
//			if (expr.opCode == OPCODE_assert) {
//				Z3Node axiom = expr.getOperand(0);
//				solver.add((BoolExpr) this.createZ3ExprTree(axiom)); 
//			}
//		}
//	}
	
	private void constructPredNames() {
		this.predNames = new String[ this.z3Encoder.getPredNames().size() ];
		this.z3Encoder.getPredNames().toArray(this.predNames);		
	}
	
	private void createContextSolver() {
		HashMap<String, String> cfg = new HashMap<String, String>();
    cfg.put("model", "true");    
    cfg.put("timeout", "36000000");
    cfg.put("unsat_core", "true");
    this.ctx = new Context(cfg);
		   
		String initFile = this.z3Encoder.getInitFileName();
		BoolExpr init = this.ctx.parseSMTLIB2File(initFile, null, null, null, null);
		this.init_solver = this.ctx.mkSolver();
		this.init_solver.add(init);
		
		String nextFile = this.z3Encoder.getNextFileName();
		BoolExpr next = this.ctx.parseSMTLIB2File(nextFile, null, null, null, null);
		this.next_solver = this.ctx.mkSolver();
		this.next_solver.add(next);
		
		this.solver = this.ctx.mkSolver();

		this.createSortList();
		this.createVarList();
		this.createFcnList();
				
		this.t_sortNames = new Symbol[ this.sorts.size() - 2];
		for (int i = 0, j = 2; i < this.t_sortNames.length; i++, j++) {			
			t_sortNames[i] = this.sorts.get(j).getSort().getName();			
		}
		
		this.t_sorts = new Sort[ this.sorts.size() - 2];
		for (int i = 0, j = 2; i < this.t_sorts.length; i++, j++) {			
			t_sorts[i] = this.sorts.get(j).getSort();			
		}
		
		this.t_declNames = new Symbol[ this.vars.size() + this.fcns.size() ];
		for (int i = 0; i < this.vars.size(); i++) {
			t_declNames[i] = this.vars.get(i).getSymbol();
		}
		for (int i = this.vars.size(), j = 0; i < this.vars.size() + this.fcns.size(); i++, j++) {
			t_declNames[i] = this.fcns.get(j).getFunc().getName();
		}
		
		this.t_decls = new FuncDecl[ this.vars.size() + this.fcns.size() ];
		for (int i = 0; i < this.vars.size(); i++) {
			t_decls[i] = this.vars.get(i).getVar();
		}
		for (int i = this.vars.size(), j = 0; i < this.vars.size() + this.fcns.size(); i++, j++) {
			t_decls[i] = this.fcns.get(j).getFunc();
		}				
	}
	
	private void createInvs() {
		Z3Node node1 = new Z3Node("assert", OPCODE_assert, this.z3Encoder.boolSort, null, 
																this.z3Encoder.raw_init_inv, tla_atom, NoSet),
					 node2 = new Z3Node("assert", OPCODE_assert, this.z3Encoder.boolSort, null, 
								this.z3Encoder.raw_next_inv, tla_atom, NoSet);
		String strInv = this.z3Encoder.z3Tool.printZ3Node(node1, ""),
					strPInv = this.z3Encoder.z3Tool.printZ3Node(node2, "");
		
		this.init_inv = this.ctx.parseSMTLIB2String(strInv, this.t_sortNames, this.t_sorts, this.t_declNames, this.t_decls);
		this.next_inv = this.ctx.parseSMTLIB2String(strPInv, this.t_sortNames, this.t_sorts, this.t_declNames, this.t_decls);
		
	}
	
	private void createBoolExpr_Preds() {
		ArrayList<Z3Node> t_preds = this.z3Encoder.getPredicates();
		ArrayList<Z3Node> t_negPreds = this.z3Encoder.getNegPredicates();
		Z3Node pred, negPred, t;
		String str, name;
		int alen = t_preds.size();
		this.preds = new BoolExpr[alen];
		this.negPreds = new BoolExpr[alen];	
		this.predIndexes = new int[ alen ];		
		int alen_j = this.t_decls.length;		
		for (int i = 0; i < alen; i++) {
			if (i < alen / 2) {
				name = this.predNames[i];
			}
			else {
				name = "p_" + this.predNames[i - alen / 2];
			}
			for (int j = 0; j < alen_j; j++) {
				if (name.equals(this.t_decls[j].getName().toString())) {
					this.predIndexes[i] = j;
					break;
				}
			}
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
		this.createNegPredNames();
		this.createInvs();
		String timeFileName = this.z3Encoder.getDir() + "time_" + this.z3Encoder.getSpecFileName() + ".txt";		
		FileWriter file = new FileWriter(timeFileName);
		long start1 = System.nanoTime();		
		this.createNuSMVFile(3);
		long end1 = System.nanoTime();
		long start2 = System.nanoTime();
		this.run_ic3();
		long end2 = System.nanoTime();
		file.write(Long.toString(start1) + "\n");
		file.flush();
		file.write(Long.toString(end1) + "\n");
		file.flush();
		file.write(Long.toString(start2) + "\n");
		file.flush();
		file.write(Long.toString(end2) + "\n");
		file.flush();
		file.close();
	}
	
	private void createNegPredNames() {
		this.negPredNames = new String[ this.predNames.length ];
		for (int i = 0; i < this.negPredNames.length; i++) {
			this.negPredNames[i] = "!" + this.predNames[i]; 
		}
	}
	
	private void nusmvVarDecl(FileWriter file) throws IOException {
		file.write("VAR\n");
		file.flush();
		int alen = this.predNames.length / 2;
		String decl;
		for (int i = 0; i < alen; i++) {
			decl = "\t" + this.predNames[i] + " : boolean;\n";
			file.write(decl);
			file.flush();
		}
	}
	
//	private void createBooleanFormula(int index, int maxIndex, FileWriter file, Solver solver) throws IOException {
//		if (index == maxIndex) {
//			String res = "\t";
//			if (this.sat[0] == 1) {
//				res = res + this.predNames[0];
//			}
//			else if (this.sat[0] == -1) {
//				res = res + this.negPredNames[0];
//			}
//			for (int i = 1; i < maxIndex; i++) {
//				if (this.sat[i] == 1) {
//					res = res + " & " + this.predNames[i];
//				}
//				else if (this.sat[i] == -1) {
//					res = res + " & " + this.negPredNames[i];
//				}
//			}
//			if (this.no == 0) {
//				file.write(res);
//				file.flush();
//			}
//			else {
//				res = " | \n" + res;
//				file.write(res);
//				file.flush();
//			}
//			this.no++;
//			return;
//		}
//		Status sres;
//		solver.push();
//		solver.add(preds[index]);
//		sres = solver.check();
//		if (sres == Status.SATISFIABLE) {
//			this.sat[index] = 1;
//			this.createBooleanFormula(index + 1, maxIndex, file, solver);
//			this.sat[index] = 0;
//			solver.pop();
//			solver.push();
//			solver.add(negPreds[index]);
//			sres = solver.check();
//			if (sres == Status.SATISFIABLE) {
//				this.sat[index] = -1;
//				this.createBooleanFormula(index + 1, maxIndex, file, solver);
//				this.sat[index] = 0;
//			}		
//			else if (sres == Status.UNKNOWN) {
//				System.out.println("UNKNOWN");
//				return;
//			}
//			solver.pop();
//		}
//		else if (sres == Status.UNSATISFIABLE) {
//			solver.pop();
//			solver.push();
//			solver.add(negPreds[index]);
//			this.sat[index] = -1;
//			this.createBooleanFormula(index + 1, maxIndex, file, solver);
//			solver.pop();
//		}
//		else if (sres == Status.UNKNOWN) {
//			System.out.println("UNKNOWN");
//			solver.pop();
//			return;
//		}		
//	}
//	
	private void createBooleanFormula(int index, int maxIndex, FileWriter file, Solver solver) throws IOException {
		if (index == maxIndex) {
			solver.push();			
			for (int i = 0; i < maxIndex; i++) {
				if (this.sat[i] == 1) {
					solver.add(this.preds[i]);
				}
				else if (this.sat[i] == -1) {
					solver.add(this.negPreds[i]);
				}
			}			
			
			if (solver.check() == Status.SATISFIABLE) {
				String res = "\t";
				if (this.sat[0] == 1) {
					res = res + this.predNames[0];
				}
				else if (this.sat[0] == -1) {
					res = res + this.negPredNames[0];
				}
				for (int i = 1; i < maxIndex; i++) {
					if (this.sat[i] == 1) {
						res = res + " & " + this.predNames[i];
					}
					else if (this.sat[i] == -1) {
						res = res + " & " + this.negPredNames[i];
					}
				}
				if (this.no == 0) {
					file.write(res);
					file.flush();
				}
				else {
					res = " | \n" + res;
					file.write(res);
					file.flush();
				}
				this.no++;
			}
			String str = solver.toString();
			solver.pop();			
			return;
		} 
		this.sat[index] = 1;
		this.createBooleanFormula(index + 1, maxIndex, file, solver);
		this.sat[index] = -1;
		this.createBooleanFormula(index + 1, maxIndex, file, solver);
		this.sat[index] = 0;
	}
	
	
	private void nusmvInit1(FileWriter file) throws IOException {
		file.write("\nINIT\n");
		file.flush();
		this.no = 0;
		int alen = this.predNames.length / 2, i , index;
//		this.createBooleanFormula(0, alen, file, this.init_solver);
		String str = "\t";
		Model model;
		Expr tmp;
		BoolExpr andExpr, notExpr;
		BoolExpr[] res = new BoolExpr[alen];
		this.init_solver.push();
		while (this.init_solver.check() == Status.SATISFIABLE) {
			str = "\t";
			model = this.init_solver.getModel();
			for (i = 0; i < alen; i++) {
				index = this.predIndexes[i];
				tmp = model.getConstInterp(this.t_decls[index]);
				if (tmp.equals(this.ctx.mkTrue())) {
					res[i] = this.preds[i];
					str = str + this.predNames[i] + " & ";
				}
				else if (tmp.equals(this.ctx.mkFalse())) {
					res[i] = this.negPreds[i];
					str = str + this.negPredNames[i] + " & ";
				}
			}
			andExpr = this.ctx.mkAnd(res);
			notExpr = this.ctx.mkNot(andExpr);
			this.init_solver.add(notExpr);
			str = str.substring(0, str.length() - 3);
			if (this.no == 0) {
				file.write(str);
				file.flush();
			}
			else {
				file.write(" |\n" + str);
				file.flush();
			}
			this.no++;
		}		
//		System.out.println(this.init_solver.toString());
		if (this.init_solver.check() == Status.UNKNOWN) {
			System.out.println("UNKNOWN - INIT");
		}
		this.init_solver.pop();
		file.write(" ;\n");
		file.flush();
	}
	
	private void nusmvTrans1(FileWriter file) throws IOException {
		file.write("\nTRANS\n");
		file.flush();
		this.no = 0;
		int alen = this.predNames.length, i , index;
//		this.createBooleanFormula(0, alen, file, this.next_solver);
		String str = "\t";
		Model model;
		Expr tmp;
		BoolExpr andExpr, notExpr;
		BoolExpr[] res = new BoolExpr[alen];
		this.next_solver.push();
		while (this.next_solver.check() == Status.SATISFIABLE) {
			str = "\t";
			model = this.next_solver.getModel();
			for (i = 0; i < alen; i++) {
				index = this.predIndexes[i];
				tmp = model.getConstInterp(this.t_decls[index]);
				if (tmp.equals(this.ctx.mkTrue())) {
					res[i] = this.preds[i];
					str = str + this.predNames[i] + " & ";
				}
				else if (tmp.equals(this.ctx.mkFalse())) {
					res[i] = this.negPreds[i];
					str = str + this.negPredNames[i] + " & ";
				}
			}
			andExpr = this.ctx.mkAnd(res);
			notExpr = this.ctx.mkNot(andExpr);
			this.next_solver.add(notExpr);
			str = str.substring(0, str.length() - 3);
			if (this.no == 0) {
				file.write(str);
				file.flush();
			}
			else {
				file.write(" |\n" + str);
				file.flush();
			}
			this.no++;
		}		
		if (this.next_solver.check() == Status.UNKNOWN) {
			System.out.println("UNKNOWN - NEXT");
		}
		this.next_solver.pop();
		file.write(" ;\n");
		file.flush();
		
	}
	
	private void nusmvInit2(FileWriter file) throws IOException {
		file.write("\nINIT\n");
		file.flush();
		this.no = 0;
		int alen = this.predNames.length / 2, i , index;
		String str = "\t";
		Model model;
		Expr tmp;
		BoolExpr andExpr, notExpr;
		BoolExpr[] res = new BoolExpr[alen];
		while (this.init_solver.check() == Status.SATISFIABLE) {
			str = "\t";
			model = this.init_solver.getModel();
			for (i = 0; i < alen; i++) {
				index = this.predIndexes[i];
				tmp = model.getConstInterp(this.t_decls[index]);
				if (tmp.equals(this.ctx.mkTrue())) {
					res[i] = this.preds[i];
					str = str + this.predNames[i] + " & ";
				}
				else if (tmp.equals(this.ctx.mkFalse())) {
					res[i] = this.negPreds[i];
				str = str + this.negPredNames[i] + " & ";
				}
			}
			andExpr = this.ctx.mkAnd(res);
			notExpr = this.ctx.mkNot(andExpr);
			this.init_solver.add(notExpr);
			str = str.substring(0, str.length() - 3);
			if (this.no == 0) {
				file.write(str);
				file.flush();
			}
			else {
				file.write(" |\n" + str);
				file.flush();
			}
			this.no++;
		}
		if (this.init_solver.check() == Status.UNKNOWN) {
			System.out.println("UNKNOWN - INIT");
		}
		file.write(" ;\n");
		file.flush();
	}
	
	private void writeCondition(FileWriter file, String condition, String connective) throws IOException {
		if (this.no == 0) {
			file.write(condition);
			file.flush();
		}
		else {
			file.write(connective + condition);
			file.flush();
		}
		this.no++;
	}
	
	private void 	InvTrans2(FileWriter file) throws IOException {
		BoolExpr[] res1 = new BoolExpr[] { this.init_inv, this.ctx.mkNot(this.next_inv) };
		BoolExpr andExpr = this.ctx.mkAnd(res1);
		this.next_solver.push();
		this.next_solver.add(andExpr);
		if (this.next_solver.check() == Status.UNSATISFIABLE) {
			String	str1 = this.z3Encoder.printNUSMV(this.z3Encoder.raw_init_inv),
					str2 = this.z3Encoder.printNUSMV(this.z3Encoder.z3Tool.fromZ3toNUSVM(this.z3Encoder.raw_next_inv)),
					condition = "\n\t!(" + str1 + " & (!(" + str2 + ")))";
			this.writeCondition(file, condition, " & ");
		}
		else if  (this.next_solver.check() == Status.SATISFIABLE) {
			int alen = this.predNames.length, i , index;
			//		this.createBooleanFormula(0, alen, file, this.next_solver);
			String str = "\t";
			Model model;
			Expr tmp;
			BoolExpr notExpr;
			BoolExpr[] res = new BoolExpr[alen];
			while (this.next_solver.check() == Status.SATISFIABLE) {
				str = "\t";
				model = this.next_solver.getModel();
				for (i = 0; i < alen; i++) {
					index = this.predIndexes[i];
					tmp = model.getConstInterp(this.t_decls[index]);
					if (tmp.equals(this.ctx.mkTrue())) {
						res[i] = this.preds[i];
						str = str + this.predNames[i] + " & ";
					}
					else if (tmp.equals(this.ctx.mkFalse())) {
						res[i] = this.negPreds[i];
						str = str + this.negPredNames[i] + " & ";
					}
				}
				andExpr = this.ctx.mkAnd(res);
				notExpr = this.ctx.mkNot(andExpr);
				this.next_solver.add(notExpr);
				str = str.substring(0, str.length() - 3);
				if (this.no == 0) {
					file.write(str);
					file.flush();
				}
				else {
					file.write(" |\n" + str);
					file.flush();
				}
				this.no++;
			}
			if (this.next_solver.check() == Status.UNKNOWN) {
				System.out.println("UNKNOWN - NEXT");
			}
		}		
		this.next_solver.pop();		
	}
	
	private void Predicates2Trans2(FileWriter file, BoolExpr pred1, BoolExpr pred2,
			String name1, String name2) throws IOException {
		this.next_solver.push();
		BoolExpr[] tmp = new BoolExpr[] { pred1, pred2 };
		BoolExpr andExpr = this.ctx.mkAnd(tmp);
		this.next_solver.add(andExpr);
		if (this.next_solver.check() == Status.UNSATISFIABLE) {
			String condition = "\n\t!(" + name1 + " & " + name2 + ")";
			this.writeCondition(file, condition, " & ");
		}
		this.next_solver.pop();
	}
	
	private void Predicates2Trans2(FileWriter file) throws IOException {
		int alen_i = this.predNames.length,
				alen_j = this.predNames.length, 
				i, j, iId, jId;
		String name1, name2;
		for (i = 0; i < alen_i; i++) 
			for (j = i + 1; j < alen_j; j++) {
//				iId = this.predIndexes[i];
//				jId = this.predIndexes[j];
				name1 = this.predNames[i];
				name2 = this.predNames[j];
				this.Predicates2Trans2(file, this.preds[i], this.preds[j], name1, name2);
//				this.Predicates2Trans2(file, this.preds[i], this.negPreds[j]);
//				this.Predicates2Trans2(file, this.negPreds[i], this.preds[j]);
//				this.Predicates2Trans2(file, this.negPreds[i], this.negPreds[j]);
			}		
	}
	
	private void nusmvTrans2(FileWriter file) throws IOException {
		file.write("\nTRANS\n");
		file.flush();
		this.no = 0;
		this.InvTrans2(file);
//		this.Predicates2Trans2(file);		
		file.write(" ;\n");
		file.flush();
	}
	
	private void nusmvInv(FileWriter file) throws IOException {
		file.write("\nSPEC AG ");
		file.flush();
		this.no = 0;		
		file.write(this.z3Encoder.getNuSMVInv());
		file.flush();		
	}
	
	private void createNuSMVFile(int id) throws IOException {

		this.sat = new int[ this.predNames.length ];
		this.nusmvFileName = this.z3Encoder.getDir() + "nusmv_" + this.z3Encoder.getSpecFileName() + ".txt";
		this.sat = new int[ this.predNames.length ];
		FileWriter file = new FileWriter(this.nusmvFileName);
		file.write("MODULE main\n\n");
		file.flush();
		this.nusmvVarDecl(file);		
		switch (id) {
		case 1: {
			this.nusmvInit1(file);
			this.nusmvTrans1(file);
			break;
		}
		case 2: {
			this.nusmvInit2(file);
			this.nusmvTrans2(file);
			break;
		}		
		default: {
			break;
		}
		}
		
		this.nusmvInv(file);
		file.close();
	}
	
	private FuncDecl getFunc(String name) {
		for (int i = 0; i < this.t_decls.length; i++) {
			if (this.t_decls[i].getName().toString().equals(name)) {
				return this.t_decls[i];
			}
		}
		return null;
	}		
	
	private void constructFrame0() {
		BoolExpr init_states = null,
				state = null;
		int alen = this.predNames.length / 2, i , index;
		Model model;
		Expr tmp;		
		BoolExpr[] res = new BoolExpr[alen];	
//		System.out.println(this.init_solver.toString());
		this.init_solver.push();
		while (this.init_solver.check() == Status.SATISFIABLE) {			
			model = this.init_solver.getModel();
			state = this.getCurrentState(model);
//			for (i = 0; i < alen; i++) {
//				index = this.predIndexes[i];
//				tmp = model.getConstInterp(this.t_decls[index]);
//				if (tmp.equals(this.ctx.mkTrue())) {
//					res[i] = this.preds[i];					
//				}
//				else if (tmp.equals(this.ctx.mkFalse())) {
//					res[i] = this.negPreds[i];				
//				}
//			}
//			state = this.ctx.mkAnd(res);
			if (init_states == null) {
				init_states = state; 
			}
			else {
				init_states = this.ctx.mkOr(new BoolExpr[] { init_states, state });
			}
			this.init_solver.add(this.ctx.mkNot(state));			
		}
		this.init_solver.pop();
		IC3_Frame frame0 = new IC3_Frame();
		frame0.formula = init_states;
		this.frames.add(frame0);
	}
	
	private BoolExpr getCurrentState(Model model) {
		BoolExpr state = null;
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
		state = this.ctx.mkAnd(res);
		return state;
	}
	
	private BoolExpr getPState(Model model) {
		BoolExpr state = null;
		int alen = this.predNames.length / 2, i , index, dis = alen;		
		Expr tmp;		
		BoolExpr[] res = new BoolExpr[alen];
		for (i = 0; i < alen; i++) {
			index = this.predIndexes[i];
			tmp = model.getConstInterp(this.t_decls[index]);
			if (tmp.equals(this.ctx.mkTrue())) {
				res[i] = this.preds[i + dis];					
			}
			else if (tmp.equals(this.ctx.mkFalse())) {
				res[i] = this.negPreds[i + dis];				
			}
		}
		state = this.ctx.mkAnd(res);
		return state;
	}
	
	private BoolExpr getNextState(Model model) {
		BoolExpr state = null;
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
		state = this.ctx.mkAnd(res);
		return state;
	}
	
	private boolean ic3_checkInit(FileWriter file) throws IOException  {
		this.next_solver.push();
		BoolExpr initStates = this.frames.get(0).formula;
		this.solver.push();
		this.solver.add(initStates);
		this.solver.add(this.ctx.mkNot(this.init_inv));
		if (this.solver.check() == Status.SATISFIABLE) {
			Model model = this.solver.getModel();
			BoolExpr badState = this.getCurrentState(model);
			String str = badState.toString();
			file.write(str);
			file.flush();
			return false;
		}
		this.solver.pop();
		return true;
	}
	
	private boolean ic3_goOneStep(FileWriter file) throws IOException  {
		this.next_solver.push();
		BoolExpr initStates = this.frames.get(0).formula;
		this.next_solver.push();
		this.next_solver.add(initStates);
		this.next_solver.add(this.ctx.mkNot(this.next_inv));
		if (this.next_solver.check() == Status.SATISFIABLE) {
			Model model = this.next_solver.getModel();
			BoolExpr badState = this.getCurrentState(model);
			String str0 = badState.toString();
			file.write(str0);
			file.flush();
			badState = this.getNextState(model);
			String str1 = badState.toString();
			file.write(str1);
			file.flush();
			return false;
		}
		this.next_solver.pop();
		return true;
	}
	
	private IC3_Frame constructPFrame() {
		IC3_Frame frame = new IC3_Frame();
		if (this.init_clause == null) {
			this.init_clause = new IC3_Clause(this.init_inv);
		}
		if (this.next_clause == null) {
			this.next_clause = new IC3_Clause(this.next_inv);
		}
		frame.formula = this.init_inv;		
		frame.clauses.add(this.init_clause);
		frame.p_clauses.add(this.next_clause);
		return frame;
	}
	
	private void constructFrame1() {
		if (this.frames.size() == 1) {
			IC3_Frame frame1 = this.constructPFrame();
			this.frames.add(frame1);
		}
	}
	
	private boolean checkFrames(FileWriter file) throws IOException {
		int alen = this.frames.size() - 1;
		for (int i = 0; i < alen; i++) {
			this.solver.push();
			this.solver.add(this.ctx.mkNot(this.ctx.mkEq(this.frames.get(i).formula, 
																										this.frames.get(i + 1).formula)));
			if (this.solver.check() == Status.UNSATISFIABLE) {
				file.write("STRENTHEN INVARIANT\n");			
				file.flush();
				file.write(this.frames.get(i).formula.toString());
				file.flush();
				return true;
			}
			this.solver.pop();
		}
		return false;
	}	
	
	private void propagateClauses() {
		for (int i = 1; i <= this.k_ic3; i++) {
			IC3_Frame frame = this.frames.get(i),
					frame1 = this.frames.get(i + 1);
			this.next_solver.push();
			this.next_solver.add(frame.formula);
			for (int j = 0; j < frame.clauses.size(); j++) {
				IC3_Clause c = frame.clauses.get(j),  
					p_c = frame.p_clauses.get(j);
				if (!frame1.hasClause(c)) {
					this.next_solver.push();
					this.next_solver.add(this.ctx.mkNot(p_c.formula));
					if (this.next_solver.check() == Status.UNSATISFIABLE) {						
						frame1.formula = this.ctx.mkAnd(new BoolExpr[] { frame1.formula, c.formula });
						frame1.clauses.add(c);
						frame1.p_clauses.add(p_c);

					}
					this.next_solver.pop();
				}			
			}
			this.next_solver.pop();
		}
//		System.out.println(this.next_solver.toString());
	}
	
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
	
	private void printBadPaths(IC3_StateK statek, FileWriter file) throws IOException {
		String str;
		IC3_StateK q = statek;
		while (q != null) {
			str = q.formula.toString();
			file.write(str);
			file.flush();
			q = q.next;
		}
		
	}
	
	private boolean hasBadStatesAtStep1(IC3_StateK statek, FileWriter file) throws IOException {
		this.next_solver.push();
		BoolExpr F0 = this.frames.get(0).formula,
				notQ = this.ctx.mkNot(statek.formula),
				primedQ = statek.p_formula,
				badState = null;		
		String str;
		boolean res = false;
		this.next_solver.add(F0);
		this.next_solver.add(notQ);
		this.next_solver.add(primedQ);
		if (this.next_solver.check() == Status.SATISFIABLE) {
			Model model = this.next_solver.getModel();
			badState = this.getCurrentState(model);
			str = badState.toString();
			file.write("BAD PATH");
			file.flush();
			file.write(str);
			file.flush();
			this.printBadPaths(statek, file);
			res = true;
		}		
		this.next_solver.pop();
		return res;
	}
		
	private int findI(IC3_StateK q) {
		int alen = this.frames.size() - 1;
//		System.out.println(this.next_solver.toString());
		this.next_solver.push();
		this.next_solver.add(q.p_formula);
		this.next_solver.add(this.ctx.mkNot(q.formula));
		boolean stop = false;
		int i = 0, left = 0, right = this.frames.size() - 2, middle, res = -1;
//		while (i < alen && !stop) {
//			this.next_solver.push();
//			this.next_solver.add(this.frames.get(i).formula);
//			//			System.out.println(this.next_solver.toString());
//			if (this.next_solver.check() == Status.UNSATISFIABLE) {
//				i++;				
//			}
//			else if (this.next_solver.check() == Status.SATISFIABLE) {
//				stop = true;
//			}
//			else if (this.next_solver.check() == Status.UNKNOWN) {
//				i = -1;
//				stop = true;				
//			}
//
//			//			System.out.println(this.next_solver.toString());
//			this.next_solver.pop();
//
//		}
		while (left <= right) {
			middle = (left + right) / 2;
			this.next_solver.push();
			this.next_solver.add(this.frames.get(middle).formula);
//			System.out.println(this.next_solver.toString());
			if (this.next_solver.check() == Status.UNSATISFIABLE) {
				res = middle;
				left = middle + 1;
				this.next_solver.pop();
			}
			else if (this.next_solver.check() == Status.SATISFIABLE) {				
				right = middle - 1;
				this.next_solver.pop();
			}
			else if (this.next_solver.check() == Status.UNKNOWN) {
				this.next_solver.pop();
				res = -1;
				break;
			}
		}
		this.next_solver.pop();
//		if (i	<= alen) {
//			return i - 1; 
//		}		
		return res;
//		return -1;
	}
	
	private void addC(IC3_Clause clause, IC3_Clause p_clause, int alen) {
		IC3_Frame frame;		
		for (int i = 0; i < alen; i++) {
			frame = this.frames.get(i);
			frame.formula = this.ctx.mkAnd(frame.formula, clause.formula);
			frame.clauses.add(clause);
			frame.p_clauses.add(p_clause);
		}
	}
	
	private Model getW(IC3_Frame frame, IC3_StateK q) {
		Model w = null;
		this.next_solver.push();
		this.next_solver.add(frame.formula);
		this.next_solver.add(this.ctx.mkNot(q.formula));
		this.next_solver.add(q.p_formula);		
		if (this.next_solver.check() == Status.SATISFIABLE) {
			w = this.next_solver.getModel();
		}
		this.next_solver.pop();
		return w;
	}
	
	private boolean removeCTI(BoolExpr s, BoolExpr p_s, FileWriter file) throws IOException {
		IC3_StateK state0 = new IC3_StateK(s, p_s, this.k_ic3), curStateK, newState;
		ArrayList<IC3_StateK> states = new ArrayList<IC3_StateK>();
		int i, j;
		states.add(state0);
		BoolExpr c, p_c, t, p_t;
		Model w;
		IC3_Clause clause, p_clause;
		while (states.size() > 0) {
//			System.out.println(this.next_solver.toString());
			curStateK = this.getMinimalState(states);
			if (this.hasBadStatesAtStep1(curStateK, file)) {				
				return false;
			}
//			System.out.println(this.next_solver.toString());

			i = this.findI(curStateK);
			c = this.ctx.mkNot(curStateK.formula);
			p_c = this.ctx.mkNot(curStateK.p_formula);
			clause = new IC3_Clause(c);
			p_clause = new IC3_Clause(p_c);
			this.addC(clause, p_clause, i + 2); 
			if (i + 1 >= curStateK.k) {
				return true;
			}
			w = this.getW(this.frames.get(i + 1), curStateK);
			t = this.getCurrentState(w);
			p_t = this.getPState(w);
			newState = new IC3_StateK(t, p_t, i + 1);
			newState.next = curStateK;
			states.add(newState);
		}
		return false;
	}
	
	private boolean extendFrontier(FileWriter file) throws IOException {
		IC3_Frame newFrame = this.constructPFrame();
		this.frames.add(newFrame);
		Model model = null;
		BoolExpr badState = null,
				p_badState = null;
		this.next_solver.push();
		this.next_solver.add(this.ctx.mkNot(this.next_inv));		
		this.next_solver.add(this.frames.get(this.k_ic3).formula);		
		while (this.next_solver.check() == Status.SATISFIABLE) {
			model = this.next_solver.getModel();
			badState = this.getCurrentState(model);
//			System.out.println(this.next_solver.toString());
			this.next_solver.pop();
//			System.out.println(this.next_solver.toString());
			p_badState = this.getPState(model);
			if (!this.removeCTI(badState, p_badState, file)) {
				return false;
			}			
			this.next_solver.push();
			this.next_solver.add(this.ctx.mkNot(this.next_inv));
			this.next_solver.add(this.frames.get(this.k_ic3).formula);
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
			this.k_ic3++;
		}		
	}
			
	private void run_ic3() throws IOException {
		String fileName = this.z3Encoder.getDir() + "ic3_" + this.z3Encoder.getSpecFileName() + ".txt";
		FileWriter file = new FileWriter(fileName);
		this.constructFrame0();
		this.constructFrame1();
		this.prove(file);
		file.close();
	}
}
