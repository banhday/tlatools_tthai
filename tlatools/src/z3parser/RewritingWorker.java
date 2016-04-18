package z3parser;

public class RewritingWorker implements Z3Constants {

	public RewritingWorker() {
		// TODO Auto-generated constructor stub
	}

	// After the translation, all nodes must have it's corresponding name in SMT2.
	// There are only three exceptional cases: OPCODE_in, _fa, and _IsAFcn
	public final void rename(Z3Node node) {
			if (node == null) {
				return;
			}
//			if (node.getSort() == null) {
//				Assert.fail(ConstraintErr, node.name + " has no sort.");				
//			}
			switch (node.opCode) {
			case OPCODE_domain: {
				Z3Node op = node.getOperand(0);
				node.name = "domain_" + op.getSort().name;
				break;
			}
			case OPCODE_in: {
				Z3Node op = node.getOperand(1);
				node.name = "in_" + op.getSort().name;
				break;
			}
			case OPCODE_fa:
			case OPCODE_alpha: {
				Z3Node lhs = node.getOperand(0),
						sort = lhs.getSort();
				if (sort.opCode == OPCODE_rsort || sort.opCode == OPCODE_tsort) {
					node.opCode = OPCODE_trsl;
					node.name = NoName;
					Z3Node arg = node.getOperand(1).clone();
					if (!arg.isChangedName) {
						arg.name = "z3f_" + arg.name;					
						node.setOperand(1, arg);
						arg.isChangedName = true;	
					}
				}
				else {
					node.name = "alpha_" + lhs.getSort().name;				
				}			
				break;
			}
			case OPCODE_rs:
			case OPCODE_trsl: {
				node.name = NoName;				
				Z3Node arg = node.getOperand(1).clone();
				if (!arg.isChangedName) {
					arg.name = "z3f_" + arg.name;					
					node.setOperand(1, arg);
					arg.isChangedName = true;	
				}
				break;
			}
			default: {					
			}
			}

			int i;
			for (i = 0; i < node.getExprSize(); i++) {
				this.rename(node.getExpr(i));
			}
			for (i = 0; i < node.getOperandSize(); i++) {
				this.rename(node.getOperand(i));
			}
			for (i = 0; i < node.getDomainSize(); i++) {
				this.rename(node.getDomain(i));
			}
			for (i = 0; i < node.getRangeSize(); i++) {
				this.rename(node.getRange(i));
			}		
			for (i = 0; i < node.getBoundedVarSize(); i++) {
				this.rename(node.getBoundedVar(i));
			}
			for (i = 0; i < node.getFieldSize(); i++) {
				this.rename(node.getField(i));
			}			
		}
}
