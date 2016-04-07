package ic3;

public class NuSMV {

	public NuSMV() {
		// TODO Auto-generated constructor stub
	}


//	private void nusmvVarDecl(FileWriter file) throws IOException {
//		file.write("VAR\n");
//		file.flush();
//		int alen = this.predNames.length / 2;
//		String decl;
//		for (int i = 0; i < alen; i++) {
//			decl = "\t" + this.predNames[i] + " : boolean;\n";
//			file.write(decl);
//			file.flush();
//		}
//	}

//	private void createBooleanFormula(int index, int maxIndex, FileWriter file, Solver solver) throws IOException {
//		if (index == maxIndex) {
//			solver.push();			
//			for (int i = 0; i < maxIndex; i++) {
//				if (this.sat[i] == 1) {
//					solver.add(this.preds[i]);
//				}
//				else if (this.sat[i] == -1) {
//					solver.add(this.negPreds[i]);
//				}
//			}			
//
//			if (solver.check() == Status.SATISFIABLE) {
//				String res = "\t";
//				if (this.sat[0] == 1) {
//					res = res + this.predNames[0];
//				}
//				else if (this.sat[0] == -1) {
//					res = res + this.negPredNames[0];
//				}
//				for (int i = 1; i < maxIndex; i++) {
//					if (this.sat[i] == 1) {
//						res = res + " & " + this.predNames[i];
//					}
//					else if (this.sat[i] == -1) {
//						res = res + " & " + this.negPredNames[i];
//					}
//				}
//				if (this.no == 0) {
//					file.write(res);
//					file.flush();
//				}
//				else {
//					res = " | \n" + res;
//					file.write(res);
//					file.flush();
//				}
//				this.no++;
//			}
//			String str = solver.toString();
//			solver.pop();			
//			return;
//		} 
//		this.sat[index] = 1;
//		this.createBooleanFormula(index + 1, maxIndex, file, solver);
//		this.sat[index] = -1;
//		this.createBooleanFormula(index + 1, maxIndex, file, solver);
//		this.sat[index] = 0;
//	}
//	
//	private void nusmvInit1(FileWriter file) throws IOException {
//		file.write("\nINIT\n");
//		file.flush();
//		this.no = 0;
//		int alen = this.predNames.length / 2, i , index;
//		//		this.createBooleanFormula(0, alen, file, this.init_solver);
//		String str = "\t";
//		Model model;
//		Expr tmp;
//		BoolExpr andExpr, notExpr;
//		BoolExpr[] res = new BoolExpr[alen];
//		this.init_solver.push();
//		while (this.init_solver.check() == Status.SATISFIABLE) {
//			str = "\t";
//			model = this.init_solver.getModel();
//			for (i = 0; i < alen; i++) {
//				index = this.predIndexes[i];
//				tmp = model.getConstInterp(this.t_decls[index]);
//				if (tmp.equals(this.ctx.mkTrue())) {
//					res[i] = this.preds[i];
//					str = str + this.predNames[i] + " & ";
//				}
//				else if (tmp.equals(this.ctx.mkFalse())) {
//					res[i] = this.negPreds[i];
//					str = str + this.negPredNames[i] + " & ";
//				}
//			}
//			andExpr = this.ctx.mkAnd(res);
//			notExpr = this.ctx.mkNot(andExpr);
//			this.init_solver.add(notExpr);
//			str = str.substring(0, str.length() - 3);
//			if (this.no == 0) {
//				file.write(str);
//				file.flush();
//			}
//			else {
//				file.write(" |\n" + str);
//				file.flush();
//			}
//			this.no++;
//		}		
//		//		System.out.println(this.init_solver.toString());
//		if (this.init_solver.check() == Status.UNKNOWN) {
//			System.out.println("UNKNOWN - INIT");
//		}
//		this.init_solver.pop();
//		file.write(" ;\n");
//		file.flush();
//	}
//
//	private void nusmvTrans1(FileWriter file) throws IOException {
//		file.write("\nTRANS\n");
//		file.flush();
//		this.no = 0;
//		int alen = this.predNames.length, i , index;
//		//		this.createBooleanFormula(0, alen, file, this.next_solver);
//		String str = "\t";
//		Model model;
//		Expr tmp;
//		BoolExpr andExpr, notExpr;
//		BoolExpr[] res = new BoolExpr[alen];
//		this.next_solver.push();
//		while (this.next_solver.check() == Status.SATISFIABLE) {
//			str = "\t";
//			model = this.next_solver.getModel();
//			for (i = 0; i < alen; i++) {
//				index = this.predIndexes[i];
//				tmp = model.getConstInterp(this.t_decls[index]);
//				if (tmp.equals(this.ctx.mkTrue())) {
//					res[i] = this.preds[i];
//					str = str + this.predNames[i] + " & ";
//				}
//				else if (tmp.equals(this.ctx.mkFalse())) {
//					res[i] = this.negPreds[i];
//					str = str + this.negPredNames[i] + " & ";
//				}
//			}
//			andExpr = this.ctx.mkAnd(res);
//			notExpr = this.ctx.mkNot(andExpr);
//			this.next_solver.add(notExpr);
//			str = str.substring(0, str.length() - 3);
//			if (this.no == 0) {
//				file.write(str);
//				file.flush();
//			}
//			else {
//				file.write(" |\n" + str);
//				file.flush();
//			}
//			this.no++;
//		}		
//		if (this.next_solver.check() == Status.UNKNOWN) {
//			System.out.println("UNKNOWN - NEXT");
//		}
//		this.next_solver.pop();
//		file.write(" ;\n");
//		file.flush();
//
//	}
//
//	private void nusmvInit2(FileWriter file) throws IOException {
//		file.write("\nINIT\n");
//		file.flush();
//		this.no = 0;
//		int alen = this.predNames.length / 2, i , index;
//		String str = "\t";
//		Model model;
//		Expr tmp;
//		BoolExpr andExpr, notExpr;
//		BoolExpr[] res = new BoolExpr[alen];
//		while (this.init_solver.check() == Status.SATISFIABLE) {
//			str = "\t";
//			model = this.init_solver.getModel();
//			for (i = 0; i < alen; i++) {
//				index = this.predIndexes[i];
//				tmp = model.getConstInterp(this.t_decls[index]);
//				if (tmp.equals(this.ctx.mkTrue())) {
//					res[i] = this.preds[i];
//					str = str + this.predNames[i] + " & ";
//				}
//				else if (tmp.equals(this.ctx.mkFalse())) {
//					res[i] = this.negPreds[i];
//					str = str + this.negPredNames[i] + " & ";
//				}
//			}
//			andExpr = this.ctx.mkAnd(res);
//			notExpr = this.ctx.mkNot(andExpr);
//			this.init_solver.add(notExpr);
//			str = str.substring(0, str.length() - 3);
//			if (this.no == 0) {
//				file.write(str);
//				file.flush();
//			}
//			else {
//				file.write(" |\n" + str);
//				file.flush();
//			}
//			this.no++;
//		}
//		if (this.init_solver.check() == Status.UNKNOWN) {
//			System.out.println("UNKNOWN - INIT");
//		}
//		file.write(" ;\n");
//		file.flush();
//	}
//
//	private void writeCondition(FileWriter file, String condition, String connective) throws IOException {
//		if (this.no == 0) {
//			file.write(condition);
//			file.flush();
//		}
//		else {
//			file.write(connective + condition);
//			file.flush();
//		}
//		this.no++;
//	}

//	private void 	InvTrans2(FileWriter file) throws IOException {
//		BoolExpr[] res1 = new BoolExpr[] { this.init_inv, this.ctx.mkNot(this.next_inv) };
//		BoolExpr andExpr = this.ctx.mkAnd(res1);
//		this.next_solver.push();
//		this.next_solver.add(andExpr);
//		if (this.next_solver.check() == Status.UNSATISFIABLE) {
//			String	str1 = this.z3Encoder.printNUSMV(this.z3Encoder.raw_init_inv),
//					str2 = this.z3Encoder.printNUSMV(this.z3Encoder.z3Tool.fromZ3toNUSVM(this.z3Encoder.raw_next_inv)),
//					condition = "\n\t!(" + str1 + " & (!(" + str2 + ")))";
//			this.writeCondition(file, condition, " & ");
//		}
//		else if  (this.next_solver.check() == Status.SATISFIABLE) {
//			int alen = this.predNames.length, i , index;
//			//		this.createBooleanFormula(0, alen, file, this.next_solver);
//			String str = "\t";
//			Model model;
//			Expr tmp;
//			BoolExpr notExpr;
//			BoolExpr[] res = new BoolExpr[alen];
//			while (this.next_solver.check() == Status.SATISFIABLE) {
//				str = "\t";
//				model = this.next_solver.getModel();
//				for (i = 0; i < alen; i++) {
//					index = this.predIndexes[i];
//					tmp = model.getConstInterp(this.t_decls[index]);
//					if (tmp.equals(this.ctx.mkTrue())) {
//						res[i] = this.preds[i];
//						str = str + this.predNames[i] + " & ";
//					}
//					else if (tmp.equals(this.ctx.mkFalse())) {
//						res[i] = this.negPreds[i];
//						str = str + this.negPredNames[i] + " & ";
//					}
//				}
//				andExpr = this.ctx.mkAnd(res);
//				notExpr = this.ctx.mkNot(andExpr);
//				this.next_solver.add(notExpr);
//				str = str.substring(0, str.length() - 3);
//				if (this.no == 0) {
//					file.write(str);
//					file.flush();
//				}
//				else {
//					file.write(" |\n" + str);
//					file.flush();
//				}
//				this.no++;
//			}
//			if (this.next_solver.check() == Status.UNKNOWN) {
//				System.out.println("UNKNOWN - NEXT");
//			}
//		}		
//		this.next_solver.pop();		
//	}

//	private void Predicates2Trans2(FileWriter file, BoolExpr pred1, BoolExpr pred2,
//			String name1, String name2) throws IOException {
//		this.next_solver.push();
//		BoolExpr[] tmp = new BoolExpr[] { pred1, pred2 };
//		BoolExpr andExpr = this.ctx.mkAnd(tmp);
//		this.next_solver.add(andExpr);
//		if (this.next_solver.check() == Status.UNSATISFIABLE) {
//			String condition = "\n\t!(" + name1 + " & " + name2 + ")";
//			this.writeCondition(file, condition, " & ");
//		}
//		this.next_solver.pop();
//	}
//
//	private void Predicates2Trans2(FileWriter file) throws IOException {
//		int alen_i = this.predNames.length,
//				alen_j = this.predNames.length, 
//				i, j, iId, jId;
//		String name1, name2;
//		for (i = 0; i < alen_i; i++) 
//			for (j = i + 1; j < alen_j; j++) {
//				//				iId = this.predIndexes[i];
//				//				jId = this.predIndexes[j];
//				name1 = this.predNames[i];
//				name2 = this.predNames[j];
//				this.Predicates2Trans2(file, this.preds[i], this.preds[j], name1, name2);
//				//				this.Predicates2Trans2(file, this.preds[i], this.negPreds[j]);
//				//				this.Predicates2Trans2(file, this.negPreds[i], this.preds[j]);
//				//				this.Predicates2Trans2(file, this.negPreds[i], this.negPreds[j]);
//			}		
//	}
//
//	private void nusmvTrans2(FileWriter file) throws IOException {
//		file.write("\nTRANS\n");
//		file.flush();
//		this.no = 0;
//		this.InvTrans2(file);
//		//		this.Predicates2Trans2(file);		
//		file.write(" ;\n");
//		file.flush();
//	}
//
//	private void nusmvInv(FileWriter file) throws IOException {
//		file.write("\nSPEC AG ");
//		file.flush();
//		this.no = 0;		
//		file.write(this.z3Encoder.getNuSMVInv());
//		file.flush();		
//	}
//
//	private void createNuSMVFile(int id) throws IOException {
//
//		this.sat = new int[ this.predNames.length ];
//		this.nusmvFileName = this.z3Encoder.getDir() + "nusmv_" + this.z3Encoder.getSpecFileName() + ".txt";
//		this.sat = new int[ this.predNames.length ];
//		FileWriter file = new FileWriter(this.nusmvFileName);
//		file.write("MODULE main\n\n");
//		file.flush();
//		this.nusmvVarDecl(file);		
//		switch (id) {
//		case 1: {
//			this.nusmvInit1(file);
//			this.nusmvTrans1(file);
//			break;
//		}
//		case 2: {
//			this.nusmvInit2(file);
//			this.nusmvTrans2(file);
//			break;
//		}		
//		default: {
//			break;
//		}
//		}
//
//		this.nusmvInv(file);
//		file.close();
//	}
//
	// Just names for NuSMV
//	private void createNegPredNames() {
//		this.negPredNames = new String[ this.predNames.length ];
//		for (int i = 0; i < this.negPredNames.length; i++) {
//			this.negPredNames[i] = "!" + this.predNames[i]; 
//		}
//	}
//	private FuncDecl getFunc(String name) {
//	for (int i = 0; i < this.t_decls.length; i++) {
//		if (this.t_decls[i].getName().toString().equals(name)) {
//			return this.t_decls[i];
//		}
//	}
//	return null;
//}		


}
