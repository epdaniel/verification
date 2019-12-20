package il.ac.bgu.cs.formalmethodsintro.base;

import java.util.HashSet;

import il.ac.bgu.cs.formalmethodsintro.base.TSTestUtils.APs;
import il.ac.bgu.cs.formalmethodsintro.base.TSTestUtils.Actions;
import il.ac.bgu.cs.formalmethodsintro.base.TSTestUtils.States;
import il.ac.bgu.cs.formalmethodsintro.base.circuits.AtomicLogicalExp;
import il.ac.bgu.cs.formalmethodsintro.base.circuits.CircuitImp;
import il.ac.bgu.cs.formalmethodsintro.base.circuits.CompoundLogicalExp;
import il.ac.bgu.cs.formalmethodsintro.base.circuits.LogicalExp;
import il.ac.bgu.cs.formalmethodsintro.base.circuits.LogicalExp.LogicalOp;
import il.ac.bgu.cs.formalmethodsintro.base.programgraph.PGTransition;
import il.ac.bgu.cs.formalmethodsintro.base.programgraph.ProgramGraph;
import il.ac.bgu.cs.formalmethodsintro.base.transitionsystem.TSTransition;
import il.ac.bgu.cs.formalmethodsintro.base.transitionsystem.TransitionSystem;
import il.ac.bgu.cs.formalmethodsintro.base.util.Pair;

public class Main {

	public static void main(String[] args) {
		FvmFacade fvm = new FvmFacade();
		/* TransitionSystem<States, Actions, APs>  ts1 = TSTestUtils.simpleTransitionSystem();
		//ts.addState(States.g);
		//ts.addTransition(new TSTransition<States, Actions>(States.d,Actions.alpha,States.g));
		TransitionSystem<States, Actions, APs>  ts2 = TSTestUtils.threeStateTS();
		ts2.addToLabel(States.b, APs.S);
		//System.out.println("Reach:" + fvm.reach(ts1));
		//System.out.println("Reach2:" + fvm.reach(ts2));
		//System.out.println("Check: " + ts.getStates().contains(States.a));
		//printTS(ts1);
		//printTS(ts2);
		HashSet<Actions> handShake = new HashSet<Actions>();
		handShake.add(Actions.alpha);
		//handShake.add(Actions.beta);
		//handShake.add(Actions.gamma);
		//handShake.add(Actions.delta);
		//printTS(fvm.interleave(ts1, ts2, handShake));
		TransitionSystem<States, Actions, APs> sts1 = new TransitionSystem<States, Actions, APs>();
		TransitionSystem<States, Actions, APs> sts2 = new TransitionSystem<States, Actions, APs>();
		sts1.addInitialState(States.a);
		sts2.addInitialState(States.a);
		sts1.addTransition(new TSTransition<States, Actions>(States.a, Actions.beta,States.b));
		sts2.addTransition(new TSTransition<States, Actions>(States.a, Actions.alpha,States.b));
		//printTS(sts1);
		//printTS(sts2);
		//printTS(fvm.interleave(sts1, sts2, handShake));
		HashSet<String> registers = new HashSet<String>();
		HashSet<String> inputs = new HashSet<String>();
		HashSet<String> outputs = new HashSet<String>();
		registers.add("r");
		//registers.add("r2");
		inputs.add("x");
		outputs.add("y");
		CircuitImp c = new CircuitImp(registers, inputs, outputs);
		AtomicLogicalExp xXORr = new AtomicLogicalExp("r", LogicalOp.xor, "x");
		AtomicLogicalExp xORr = new AtomicLogicalExp("r", LogicalOp.or, "x");

		CompoundLogicalExp NOTxXORr = new CompoundLogicalExp(xXORr, LogicalOp.not, xXORr);
		//CompoundLogicalExp r1ANDr2ANDx = new CompoundLogicalExp(r1, LogicalOp.and, r2ANDx);

		c.addRule(new Pair<String, LogicalExp>("r", xORr));
		//c.addRule(new Pair<String, LogicalExp>("r2", r2XORx));
		c.addRule(new Pair<String, LogicalExp>("y", NOTxXORr));
		printTS(fvm.transitionSystemFromCircuit(c)); */
		
		try {
			ProgramGraph<String, String> g = fvm.programGraphFromNanoPromela("nanop.txt");
			for(PGTransition<String, String> t : g.getTransitions())
				System.out.println(t);
		} catch (Exception e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
	}
	
	public static void printTS(TransitionSystem<?, ?, ?> ts){
		System.out.println("Transition System: " + ts.getName() + "\nStates: " + ts.getStates() + "\nInitial States: " + ts.getInitialStates() + "\nActions: " + ts.getActions() + "\nTransitions: " + ts.getTransitions() + "\nAPs: " + ts.getAtomicPropositions() + "\nLabeling: " + ts.getLabelingFunction() + "\n");
	}
}
