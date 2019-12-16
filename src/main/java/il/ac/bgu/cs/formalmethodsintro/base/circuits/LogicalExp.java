package il.ac.bgu.cs.formalmethodsintro.base.circuits;

import java.util.HashMap;

public interface LogicalExp {
	
	public static enum LogicalOp {
	    and, or, xor, not
	}
	
	public boolean getResult(HashMap<String, Boolean> values);
}
