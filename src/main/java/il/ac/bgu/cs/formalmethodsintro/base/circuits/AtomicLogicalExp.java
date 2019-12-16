package il.ac.bgu.cs.formalmethodsintro.base.circuits;

import java.util.HashMap;

public class AtomicLogicalExp implements LogicalExp {

	private String left;
	private String right;
	private LogicalOp op;
	
	public AtomicLogicalExp(String left, LogicalOp op, String right){
		this.left = left;
		this.right = right;
		this.op = op;
	}
	
	@Override
	public boolean getResult(HashMap<String, Boolean> values){
		if(op == LogicalOp.and){
			return values.get(left) && values.get(right);
		}else if(op == LogicalOp.not){
			return !values.get(left);
		}else if(op == LogicalOp.or){
			return values.get(left) || values.get(right);
		}else if(op == LogicalOp.xor){
			return values.get(left) ^ values.get(right);
		}else {
			System.out.println("Logical Op error");
			return false;
		}
	}

}
