package il.ac.bgu.cs.formalmethodsintro.base.circuits;

import java.util.HashMap;
import java.util.Map;
import java.util.HashSet;
import java.util.Set;

import il.ac.bgu.cs.formalmethodsintro.base.util.Pair;


public class CircuitImp implements Circuit{
	
	private Set<String> registers;
	private Set<String> inputs;
	private Set<String> outputs;
	
	//private HashMap<String, Boolean> registers;
	//private HashMap<String, Boolean> inputs;
	//private HashMap<String, Boolean> outputs;
	
	private Set<Pair<String, LogicalExp>> registersRules;
	private Set<Pair<String, LogicalExp>> outputRules;
	
	public CircuitImp(Set<String> registersNames, Set<String> inputNames, Set<String> outputNames){
		registers = registersNames;//new HashMap<String, Boolean>();
		inputs = inputNames;//new HashMap<String, Boolean>();
		outputs = outputNames;//new HashMap<String, Boolean>();
		registersRules = new HashSet<Pair<String, LogicalExp>>();
		outputRules = new HashSet<Pair<String, LogicalExp>>();
//		for(String regName : registersNames)
//			registers.put(regName, false);
//		for(String inName : inputNames)
//			inputs.put(inName, false);
//		for(String outName : outputNames)
//			outputs.put(outName, false);
	}

	@Override
	public Set<String> getInputPortNames() {
		return inputs;
	}

	@Override
	public Set<String> getRegisterNames() {
		return registers;
	}

	@Override
	public Set<String> getOutputPortNames() {
		return outputs;
	}

	@Override
	public Map<String, Boolean> updateRegisters(Map<String, Boolean> inputs, Map<String, Boolean> registers) {
		HashMap<String, Boolean> values = new HashMap<String, Boolean>();
		HashMap<String, Boolean> output = new HashMap<String, Boolean>();
		values.putAll(inputs);
		values.putAll(registers);
		for(Pair<String, LogicalExp> rule : registersRules){
			output.put(rule.first, rule.second.getResult(values));
		}
		//this.inputs = (HashMap<String, Boolean>) inputs;
		//this.registers = (HashMap<String, Boolean>) registers;
		return output;
	}

	@Override
	public Map<String, Boolean> computeOutputs(Map<String, Boolean> inputs, Map<String, Boolean> registers) {
		HashMap<String, Boolean> values = new HashMap<String, Boolean>();
		HashMap<String, Boolean> output = new HashMap<String, Boolean>();
		values.putAll(inputs);
		values.putAll(registers);
		for(Pair<String, LogicalExp> rule : outputRules){
			output.put(rule.first, rule.second.getResult(values));
		}
		//this.inputs = (HashMap<String, Boolean>) inputs;
		//this.registers = (HashMap<String, Boolean>) registers;
		return output;
	}
	
	public void addRule(Pair<String, LogicalExp> rule){
		if(registers.contains(rule.first))
			registersRules.add(rule);
		else if(outputs.contains(rule.first))
			outputRules.add(rule);
		else System.out.println("Add rule error!!");
	}
	
	public static Set<HashMap<String, Boolean>> initMaps(Set<String> names){
		HashSet<HashMap<String, Boolean>> output = new HashSet<HashMap<String, Boolean>>();
		Object[] namesArray = names.toArray();
		int numNames = names.size();
		double permutations = Math.pow(2.0, numNames);
		for(int i = 0; i < permutations; i++){
			HashMap<String, Boolean> permutation = new HashMap<String, Boolean>();
			String binaryStr = String.format("%" + numNames + "s" ,Integer.toBinaryString(i)).replace(' ', '0');
			for(int j = 0; j < numNames; j++){
				char c = binaryStr.charAt(j);
				if(c == '1')
					permutation.put((String)namesArray[j], true);
				else
					permutation.put((String) namesArray[j], false);
			}
			output.add(permutation);
		}
		return output;
		
	}

}
