// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
// Last modified on Mon 30 Apr 2007 at 15:30:01 PST by lamport
//      modified on Wed Dec  5 23:18:37 PST 2001 by yuanyu

package tlc2.tool;

import java.io.IOException;
import java.io.Serializable;

import tla2sany.semantic.SemanticNode;
import tla2sany.semantic.SymbolNode;
import tlc2.TLCGlobals;
import tlc2.util.Context;
import tlc2.util.FP64;
import tlc2.value.MVPerm;
import tlc2.value.Value;
import tlc2.value.ValueInputStream;
import tlc2.value.ValueOutputStream;
import util.UniqueString;
import util.WrongInvocationException;

/**
 * This class represents a TLA+ state, which simply is an assignment
 * of explicit values to all the global variables.  This is the
 * mutable version, which means that in-place updates are used for
 * improved performance and reduced allocation.
 *
 * The viewMap was added by Rajeev Joshi.
 */
public final class TLCStateMut extends TLCState implements Cloneable, Serializable {
  private Value values[];
  private static Tool mytool = null;

  /**
   * If non-null, viewMap denotes the function to be applied to
   * a state before its fingerprint is computed.
   */
  private static SemanticNode viewMap = null;

  /**
   * If non-null, perms denotes the set of permutations under the
   * symmetry assumption.
   */
  private static MVPerm[] perms = null;

  private TLCStateMut(Value[] vals) { this.values = vals; }

  public static void init(Tool tool) {
    mytool = tool;
    Value[] vals = new Value[vars.length];
    Empty = new TLCStateMut(vals);
    viewMap = tool.getViewSpec();
    perms = tool.getSymmetryPerms();
  }

  public final TLCState createEmpty() {
    Value[] vals = new Value[vars.length];
    return new TLCStateMut(vals);
  }

  //TODO equals without hashcode!
  public final boolean equals(Object obj) {
    if (obj instanceof TLCStateMut) {
      TLCStateMut state = (TLCStateMut)obj;
      for (int i = 0; i < this.values.length; i++) {
	if (this.values[i] == null) {
	  if (state.values[i] != null) return false;
	}
	else if (state.values[i] == null ||
		 !this.values[i].equals(state.values[i])) {
	  return false;
	}
      }
      return true;
    }
    return false;
  }
  
  public final TLCState bind(UniqueString name, Value value, SemanticNode expr) {
    int loc = name.getVarLoc();
    this.values[loc] = value;
    return this;
  }

  public final TLCState bind(SymbolNode id, Value value, SemanticNode expr) {
    throw new WrongInvocationException("TLCStateMut.bind: This is a TLC bug.");
  }
  
  public final TLCState unbind(UniqueString name) {
    int loc = name.getVarLoc();
    this.values[loc] = null;
    return this;
  }

  public final Value lookup(UniqueString var) {
    int loc = var.getVarLoc();
    if (loc < 0) return null;
    return this.values[loc];
  }

  public final boolean containsKey(UniqueString var) {
    return (this.lookup(var) != null);
  }

  public final TLCState copy() {
    int len = this.values.length;
    Value[] vals = new Value[len];
    for (int i = 0; i < len; i++) {
      vals[i] = this.values[i];
    }
    return new TLCStateMut(vals);
  }

  public final TLCState deepCopy() {
    int len = this.values.length;
    Value[] vals = new Value[len];
    for (int i = 0; i < len; i++) {
      Value val = this.values[i];
      if (val != null) {
	vals[i] = val.deepCopy();
      }
    }
    return new TLCStateMut(vals);
  }

  public final StateVec addToVec(StateVec states) {
    return states.addElement(this.copy());
  }
  
  public final void deepNormalize() {
    for (int i = 0; i < this.values.length; i++) {
      Value val = this.values[i];
      if (val != null) {
	val.deepNormalize();
      }
    }
  }

  /**
   * This method returns the fingerprint of this state. We fingerprint
   * the values in the state according to the order given by vars.
   * This guarantees the same state has the same fingerprint.
   *
   * Since the values in this state can be shared by multiple threads
   * via the state queue. They have to be normalized before adding to
   * the state queue.  We do that here.
   */
	public final long fingerPrint() {
		int sz = this.values.length;

		// minVals is what is used to calculate/generate the fingerprint below.
		// If this state is part of a symmetry permutation and not the smallest
		// member, its current minVals will be replaced temporarily with the
		// values of the smallest state for the calculation of the fingerprint.
		Value[] minVals = this.values;
		if (perms != null) {
			Value[] vals = new Value[sz];
			// Find the "smallest" state under the symmetry permutations.
			// The following for loop converges to the smallest state under
			// symmetry by looping over all permutations applying each. If the
			// outcome turns out to be smaller than the current smallest, it
			// replaces it. Once all permutations (perms) have been seen, we
			// know we have found the smallest state.
			NEXT_PERM: for (int i = 0; i < perms.length; i++) {
				int cmp = 0;
				// For each value in values succinctly permute the current value
				// and compare it to its corresponding minValue in minVals.
				for (int j = 0; j < sz; j++) {
					vals[j] = this.values[j].permute(perms[i]);
					if (cmp == 0) {
						// Only compare unless an earlier compare has found a
						// difference already (if a difference has been found
						// earlier, still permute the remaining values of the
						// state to fully permute all state values).
						cmp = vals[j].compareTo(minVals[j]);
						if (cmp > 0) {
							// When cmp evaluates to >0, all subsequent
							// applications of perms[i] for the remaining values
							// won't make the resulting vals[] smaller than
							// minVals. Thus, exit preemptively from the loop
							// over vals. This works because perms is the cross
							// product of all symmetry sets.
							continue NEXT_PERM;
						}
					}
				}
				// cmp < 0 means the current state is part of a symmetry
				// permutation set/group and not the "smallest" one.
				if (cmp < 0) {
					if (minVals == this.values) {
						minVals = vals;
						vals = new Value[sz];
					} else {
						Value[] temp = minVals;
						minVals = vals;
						vals = temp;
					}
				}
			}
		}
		// Fingerprint the state:
		long fp = FP64.New();
		if (viewMap == null) {
			for (int i = 0; i < sz; i++) {
				fp = minVals[i].fingerPrint(fp);
			}
			if (this.values != minVals) {
				for (int i = 0; i < sz; i++) {
					this.values[i].deepNormalize();
				}
			}
		} else {
			for (int i = 0; i < sz; i++) {
				this.values[i].deepNormalize();
			}
			TLCStateMut state = this;
			if (minVals != this.values) {
				state = new TLCStateMut(minVals);
			}
			Value val = mytool.eval(viewMap, Context.Empty, state);
			fp = val.fingerPrint(fp);
		}
		return fp;
	}

  public final boolean allAssigned() {
    int len = this.values.length;    
    for (int i = 0; i < len; i++) {
      if (values[i] == null) return false;
    }
    return true;
  }

  public final void read(ValueInputStream vis) throws IOException {
    super.read(vis);
    int len = this.values.length;
    for (int i = 0; i < len; i++) {
      this.values[i] = vis.read();
    }
  }

  public final void write(ValueOutputStream vos) throws IOException {
    super.write(vos);
    int len = this.values.length;
    for (int i = 0; i < len; i++) {
      vos.write(this.values[i]);
    }
  }
  
  /* Returns a string representation of this state.  */
  public final String toString() {
    if (TLCGlobals.useView && viewMap != null) {
      Value val = mytool.eval(viewMap, Context.Empty, this);
      return Value.ppr(val.toString());
    }
    StringBuffer result = new StringBuffer();
    int vlen = vars.length;
    if (vlen == 1) {
      UniqueString key = vars[0].getName();
      Value val = this.lookup(key);
      String val_str = (val == null) ? "null" : Value.ppr(val.toString());
      result.append(key.toString());
      result.append(" = " + val_str + "\n");
    }
    else {
      for (int i = 0; i < vlen; i++) {
	UniqueString key = vars[i].getName();
	Value val = this.lookup(key);
	String val_str = (val == null) ? "null" : Value.ppr(val.toString());
	result.append("/\\ ");
	result.append(key.toString());
	result.append(" = " + val_str + "\n");
      }
    }
    return result.toString();
  }
  
  /* Returns a string representation of this state.  */
  public final String toString(TLCState lastState) {
    StringBuffer result = new StringBuffer();
    TLCStateMut lstate = (TLCStateMut)lastState;

    int vlen = vars.length;
    if (vlen == 1) {
      UniqueString key = vars[0].getName();
      Value val = this.lookup(key);
      Value lstateVal = lstate.lookup(key);
      if (!lstateVal.equals(val)) {
	String val_str = (val == null) ? "null" : Value.ppr(val.toString());
	result.append(key.toString());
	result.append(" = " + val_str + "\n");
      }
    }
    else {
      for (int i = 0; i < vlen; i++) {
	UniqueString key = vars[i].getName();
	Value val = this.lookup(key);
	Value lstateVal = lstate.lookup(key);
	if (!lstateVal.equals(val)) {
	  String val_str = (val == null) ? "null" : Value.ppr(val.toString());
	  result.append("/\\ ");
	  result.append(key.toString());
	  result.append(" = " + val_str + "\n");
	}
      }
    }
    return result.toString();
  }

}
