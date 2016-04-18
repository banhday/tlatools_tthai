package z3parser;

import tlc2.tool.ToolGlobals;

public interface Z3Constants extends ToolGlobals {
	public final String NoName 		= "";
	public final String NoSort 		= "";
	public final String Bool 		= "Bool";
	public final String SetBool		= "Set_Bool";
	public final String Int 		= "Int";	
	public final String SetInt 		= "Set_Int";
	public final String Str 		= "tla_sort_Str";
	public final String SetStr 		= "Set_tla_sort_Str";
	public final String U 			= "tla_sort_U";
	public final String NoCommand 	= "";
	
	public final int NoCode 		= 0;
	public final int NoKind 		= 0;
	public final int NoSet  		= 0;
	public final int NoTask 		= 0;
	
	
	// For primitive variables, functions, records and tuples
	// OPCODE_diamond is the maximum number which is used as a constant in TLA+.
	public final int OPCODE_var 	= OPCODE_diamond + 1;	// for TLA+ variables encoded as primitive variables in SMT-LIB 	
	public final int OPCODE_set		= OPCODE_var + 1;		// for TLA+ variables encoded as normal universal variables in SMT-LIB (unnecessary)	
	public final int OPCODE_fcn 	= OPCODE_set + 1;		// for TLA+ variables encoded as functional universal variables in SMT-LIB 
	public final int OPCODE_rcd 	= OPCODE_fcn + 1;		// for TLA+ variables encoded as record variables in SMT-LIB (unnecessary)
	public final int OPCODE_tuple 	= OPCODE_rcd + 1;		// for TLA+ variables encoded as tuple variables in SMT-LIB (unnecessary)
	public final int OPCODE_sort  	= OPCODE_tuple + 1;		// for Z3 Sorts
		
	//Two special kinds of sets. 
	// OPCODE_ps is for predefined sets such as tla_int, tla_bool, tla_U, tla_pair...
	// OPCODE_ept is for empty sets. Note that each sort has its own empty set.
	public final int OPCODE_ps 		= OPCODE_sort + 1;
	public final int OPCODE_ept		= OPCODE_ps + 1;
	
	public final int VarInfo		= OPCODE_ept + 1;		// for the invariant of primitive variables
	public final int SetInfo		= VarInfo + 1;			// for the invariant of sets
	public final int FcnInfo		= SetInfo + 1;			// for the invariant of functions
	public final int RcdInfo		= FcnInfo + 1;			// for the invariant of records
	public final int TupleInfo 		= RcdInfo + 1; 			// for the invariant of tuples
	
	public final int OPCODE_const	= RcdInfo + 1; 			// for TRUE and FALSE
	public final int OPCODE_IsAFcn	= OPCODE_const + 1; 	// for isFcn
	public final int OPCODE_trsl 	= OPCODE_IsAFcn + 1; 	// for tuple and record's application --> <e1, ..., en>[i] and rcd["hi"]
	public final int OPCODE_iapply	= OPCODE_trsl + 1;	 	// for "int" apply
	public final int OPCODE_2int  	= OPCODE_iapply + 1; 	// for the mapping from arbitrary objects to integers
	public final int OPCODE_alpha 	= OPCODE_2int + 1;		// for the "alpha" operator, it will replace OPCODE_fa
	public final int OPCODE_bv		= OPCODE_alpha + 1;	 	// for bounded variables
	public final int OPCODE_assert 	= OPCODE_bv + 1;		// for assertion
	public final int OPCODE_eqnot	= OPCODE_assert + 1;	// for equality from not
	public final int OPCODE_label 	= OPCODE_eqnot + 1;
	
	public final int OPCODE_bsort  	= OPCODE_label + 1;		// for basic sorts
	public final int OPCODE_fsort  	= OPCODE_bsort + 1;		// for sorts of functions
	public final int OPCODE_rsort  	= OPCODE_fsort + 1;		// for sorts of records
	public final int OPCODE_ssort  	= OPCODE_rsort + 1;		// for sorts of normal sets
	public final int OPCODE_sfsort 	= OPCODE_ssort + 1;		// for sorts of sets of functions
	public final int OPCODE_srsort 	= OPCODE_sfsort + 1;	// for sorts of sets of records
	public final int OPCODE_stsort 	= OPCODE_srsort + 1;	// for sorts of sets of tuples
	public final int OPCODE_tsort  	= OPCODE_stsort + 1;	// for sorts of tuples	
	
	public final int tla_atom		= OPCODE_tsort + 1;		// for Kind and for the atomic variable
	public final int tla_fcn		= tla_atom + 1;			// for Kind and for the function application	
	public final int tla_rcd		= tla_fcn + 1;			// for Kind and for the function application	
	public final int tla_tup  		= tla_rcd + 1;			// for Kind and for the function application
	public final int tla_setfcn		= tla_tup + 1; 			// for Kind and for the function application
	public final int tla_setrcd		= tla_setfcn + 1;  		// for Kind and for the function application
	public final int tla_settup 	= tla_setrcd + 1;  		// for Kind and for the function application
	public final int tla_set		= tla_settup + 1;		// for Kind and for sets
	public final int tla_empty		= tla_set + 1;			// for empty sets
	public final int tla_dotdot		= tla_empty + 1;		// for M .. N
	
	public final int typeOKTask		= tla_dotdot + 1;
	public final int initTask		= typeOKTask + 1;
	public final int nextTask		= initTask + 1;
	public final int invTask		= nextTask + 1;
	public final int predTask		= invTask + 1;
	public final int predInvTask	= predTask + 1;
		
	public final int OPCODE_add		= predInvTask + 1;
	public final int OPCODE_mul		= OPCODE_add + 1;
	public final int OPCODE_sub		= OPCODE_mul + 1;
	public final int OPCODE_div		= OPCODE_sub + 1;
	public final int OPCODE_mod		= OPCODE_div + 1;
	public final int OPCODE_lt		= OPCODE_mod + 1;
	public final int OPCODE_le		= OPCODE_lt + 1;
	public final int OPCODE_gt		= OPCODE_le + 1;
	public final int OPCODE_ge		= OPCODE_gt + 1;
	public final int OPCODE_true	= OPCODE_ge + 1;
	public final int OPCODE_false	= OPCODE_true + 1;
	public final int OPCODE_pred	= OPCODE_false + 1;
				
	public final int BoolIndex 		= 0;	
	public final int IntIndex 		= BoolIndex + 1;	
	public final int StrIndex 		= IntIndex + 1;
	public final int SetBoolIndex 	= StrIndex + 1;
	public final int SetIntIndex 	= SetBoolIndex + 1;
	public final int SetStrIndex 	= SetIntIndex + 1;
	public final int UIndex 		= SetStrIndex + 1;
	
	public final int iNull			= -1;
	
	public final String spaces8 	= "        ";	
	public final String spaces5		= "     ";
	public final String spaces4		= "    ";	
}