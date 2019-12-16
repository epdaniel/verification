package il.ac.bgu.cs.formalmethodsintro.base.circuits;

import java.util.HashMap;

import il.ac.bgu.cs.formalmethodsintro.base.circuits.LogicalExp.LogicalOp;

public class CompoundLogicalExp implements LogicalExp {

	private LogicalExp left;
	private LogicalExp right;
	private LogicalOp op;

	public CompoundLogicalExp(LogicalExp left, LogicalOp op, LogicalExp right){
		this.left = left;
		this.right = right;
		this.op = op;
	}
	
	@Override
	public boolean getResult(HashMap<String, Boolean> values){
		if(op == LogicalOp.and){
			return left.getResult(values) && right.getResult(values);
		}else if(op == LogicalOp.not){
			return !left.getResult(values);
		}else if(op == LogicalOp.or){
			return left.getResult(values) || right.getResult(values);
		}else if(op == LogicalOp.xor){
			return left.getResult(values) ^ right.getResult(values);
		}else {
			System.out.println("Logical Op error");
			return false;
		}
	}

}
