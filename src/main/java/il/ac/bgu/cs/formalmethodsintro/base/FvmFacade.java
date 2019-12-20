package il.ac.bgu.cs.formalmethodsintro.base;

import java.io.InputStream;
import java.util.*;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.stream.Collectors;
import java.util.Set;

import il.ac.bgu.cs.formalmethodsintro.base.channelsystem.ParserBasedInterleavingActDef;
import org.antlr.v4.runtime.tree.TerminalNode;

import il.ac.bgu.cs.formalmethodsintro.base.automata.Automaton;
import il.ac.bgu.cs.formalmethodsintro.base.automata.MultiColorAutomaton;
import il.ac.bgu.cs.formalmethodsintro.base.channelsystem.ChannelSystem;
import il.ac.bgu.cs.formalmethodsintro.base.circuits.Circuit;
import il.ac.bgu.cs.formalmethodsintro.base.circuits.CircuitImp;
import il.ac.bgu.cs.formalmethodsintro.base.exceptions.StateNotFoundException;
import il.ac.bgu.cs.formalmethodsintro.base.ltl.LTL;
import il.ac.bgu.cs.formalmethodsintro.base.nanopromela.NanoPromelaFileReader;
import il.ac.bgu.cs.formalmethodsintro.base.nanopromela.NanoPromelaParser.AtomicstmtContext;
import il.ac.bgu.cs.formalmethodsintro.base.nanopromela.NanoPromelaParser.DostmtContext;
import il.ac.bgu.cs.formalmethodsintro.base.nanopromela.NanoPromelaParser.IfstmtContext;
import il.ac.bgu.cs.formalmethodsintro.base.nanopromela.NanoPromelaParser.IntexprContext;
import il.ac.bgu.cs.formalmethodsintro.base.nanopromela.NanoPromelaParser.OptionContext;
import il.ac.bgu.cs.formalmethodsintro.base.nanopromela.NanoPromelaParser.StmtContext;
import il.ac.bgu.cs.formalmethodsintro.base.programgraph.ActionDef;
import il.ac.bgu.cs.formalmethodsintro.base.programgraph.ConditionDef;
import il.ac.bgu.cs.formalmethodsintro.base.programgraph.PGTransition;
import il.ac.bgu.cs.formalmethodsintro.base.programgraph.ParserBasedActDef;
import il.ac.bgu.cs.formalmethodsintro.base.programgraph.ParserBasedCondDef;
import il.ac.bgu.cs.formalmethodsintro.base.programgraph.ProgramGraph;
import il.ac.bgu.cs.formalmethodsintro.base.transitionsystem.AlternatingSequence;
import il.ac.bgu.cs.formalmethodsintro.base.transitionsystem.TSTransition;
import il.ac.bgu.cs.formalmethodsintro.base.transitionsystem.TransitionSystem;
import il.ac.bgu.cs.formalmethodsintro.base.util.Pair;
import il.ac.bgu.cs.formalmethodsintro.base.verification.VerificationResult;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;

/**
 * Interface for the entry point class to the HW in this class. Our
 * client/testing code interfaces with the student solutions through this
 * interface only. <br>
 * More about facade: {@linkplain http://www.vincehuston.org/dp/facade.html}.
 */
public class FvmFacade {

    private static FvmFacade INSTANCE = null;

    /**
     * @return an instance of this class.
     */
    public static FvmFacade get() {
        if (INSTANCE == null) {
            INSTANCE = new FvmFacade();
        }
        return INSTANCE;
    }

    /**
     * Checks whether a transition system is action deterministic. I.e., if for
     * any given p and α there exists only a single tuple (p,α,q) in →. Note
     * that this must be true even for non-reachable states.
     *
     * @param <S> Type of states.
     * @param <A> Type of actions.
     * @param <P> Type of atomic propositions.
     * @param ts  The transition system being tested.
     * @return {@code true} iff the action is deterministic.
     */
    public <S, A, P> boolean isActionDeterministic(TransitionSystem<S, A, P> ts) {
        if (ts.getInitialStates().size() > 1) return false;
        Map<Pair<S, A>, Boolean> seenTransitions = new HashMap<Pair<S, A>, Boolean>();
        for (TSTransition<S, A> t : ts.getTransitions()) {
            if (seenTransitions.containsKey(new Pair<S, A>(t.getFrom(), t.getAction()))) {
                return false;
            }
            seenTransitions.put(new Pair<S, A>(t.getFrom(), t.getAction()), true);
        }
        return true;
    }

    /**
     * Checks whether an action is ap-deterministic (as defined in class), in
     * the context of a given {@link TransitionSystem}.
     *
     * @param <S> Type of states.
     * @param <A> Type of actions.
     * @param <P> Type of atomic propositions.
     * @param ts  The transition system being tested.
     * @return {@code true} iff the action is ap-deterministic.
     */
    public <S, A, P> boolean isAPDeterministic(TransitionSystem<S, A, P> ts) {
        if (ts.getInitialStates().size() > 1) return false;
        Map<S, Set<Set<P>>> seenTransitions = new HashMap<S, Set<Set<P>>>();
        for (TSTransition<S, A> t : ts.getTransitions()) {
            if (seenTransitions.containsKey(t.getFrom())) {
                Set<Set<P>> postLabels = seenTransitions.get(t.getFrom());
                if (postLabels.contains(ts.getLabel(t.getTo()))) {
                    return false;
                } else {
                    postLabels.add(ts.getLabel(t.getTo()));
                    seenTransitions.put(t.getFrom(), postLabels);
                }
            }
            Set<Set<P>> postLabels = new HashSet<Set<P>>();
            postLabels.add(ts.getLabel(t.getTo()));
            seenTransitions.put(t.getFrom(), postLabels);
        }
        return true;
    }

    /**
     * Checks whether an alternating sequence is an execution of a
     * {@link TransitionSystem}, as defined in class.
     *
     * @param <S> Type of states.
     * @param <A> Type of actions.
     * @param <P> Type of atomic propositions.
     * @param ts  The transition system being tested.
     * @param e   The sequence that may or may not be an execution of {@code ts}.
     * @return {@code true} iff {@code e} is an execution of {@code ts}.
     */
    public <S, A, P> boolean isExecution(TransitionSystem<S, A, P> ts, AlternatingSequence<S, A> e) {
        return isInitialExecutionFragment(ts, e) && isMaximalExecutionFragment(ts, e);
    }

    /**
     * Checks whether an alternating sequence is an execution fragment of a
     * {@link TransitionSystem}, as defined in class.
     *
     * @param <S> Type of states.
     * @param <A> Type of actions.
     * @param <P> Type of atomic propositions.
     * @param ts  The transition system being tested.
     * @param e   The sequence that may or may not be an execution fragment of
     *            {@code ts}.
     * @return {@code true} iff {@code e} is an execution fragment of
     * {@code ts}.
     */
    public <S, A, P> boolean isExecutionFragment(TransitionSystem<S, A, P> ts, AlternatingSequence<S, A> e) {
        while (!e.tail().isEmpty()) {
            S from = e.head();
            A action = e.tail().head();
            e = e.tail().tail();
            S to = e.head();
            try {
                if (!post(ts, from, action).contains(to))
                    return false;
            } catch (StateNotFoundException exp) {
                return false;
            }
        }
        return true;
    }

    /**
     * Checks whether an alternating sequence is an initial execution fragment
     * of a {@link TransitionSystem}, as defined in class.
     *
     * @param <S> Type of states.
     * @param <A> Type of actions.
     * @param <P> Type of atomic propositions.
     * @param ts  The transition system being tested.
     * @param e   The sequence that may or may not be an initial execution
     *            fragment of {@code ts}.
     * @return {@code true} iff {@code e} is an execution fragment of
     * {@code ts}.
     */
    public <S, A, P> boolean isInitialExecutionFragment(TransitionSystem<S, A, P> ts, AlternatingSequence<S, A> e) {
        return ts.getInitialStates().contains(e.head()) && isExecutionFragment(ts, e);
    }

    /**
     * Checks whether an alternating sequence is a maximal execution fragment of
     * a {@link TransitionSystem}, as defined in class.
     *
     * @param <S> Type of states.
     * @param <A> Type of actions.
     * @param <P> Type of atomic propositions.
     * @param ts  The transition system being tested.
     * @param e   The sequence that may or may not be a maximal execution fragment
     *            of {@code ts}.
     * @return {@code true} iff {@code e} is a maximal fragment of {@code ts}.
     */
    public <S, A, P> boolean isMaximalExecutionFragment(TransitionSystem<S, A, P> ts, AlternatingSequence<S, A> e) {
        return isStateTerminal(ts, e.last()) && isExecutionFragment(ts, e);
    }

    /**
     * Checks whether a state in {@code ts} is terminal.
     *
     * @param <S> Type of states.
     * @param <A> Type of actions.
     * @param ts  Transition system of {@code s}.
     * @param s   The state being tested for terminality.
     * @return {@code true} iff state {@code s} is terminal in {@code ts}.
     * @throws StateNotFoundException if {@code s} is not a state of {@code ts}.
     */
    public <S, A> boolean isStateTerminal(TransitionSystem<S, A, ?> ts, S s) {
        return post(ts, s).size() == 0;
    }

    /**
     * @param <S> Type of states.
     * @param ts  Transition system of {@code s}.
     * @param s   A state in {@code ts}.
     * @return All the states in {@code Post(s)}, in the context of {@code ts}.
     * @throws StateNotFoundException if {@code s} is not a state of {@code ts}.
     */
    public <S> Set<S> post(TransitionSystem<S, ?, ?> ts, S s) {
        if (!ts.getStates().contains(s)) throw new StateNotFoundException(s);
        Set<S> post = new HashSet<S>();
        for (TSTransition<S, ?> t : ts.getTransitions()) {
            if (t.getFrom().equals(s)) {
                post.add(t.getTo());
            }
        }
        return post;
    }

    /**
     * @param <S> Type of states.
     * @param ts  Transition system of {@code s}.
     * @param c   States in {@code ts}.
     * @return All the states in {@code Post(s)} where {@code s} is a member of
     * {@code c}, in the context of {@code ts}.
     * @throws StateNotFoundException if {@code s} is not a state of {@code ts}.
     */
    public <S> Set<S> post(TransitionSystem<S, ?, ?> ts, Set<S> c) {
        Set<S> post = new HashSet<S>();
        if (!ts.getStates().containsAll(c)) throw new StateNotFoundException(c);
        for (TSTransition<S, ?> t : ts.getTransitions()) {
            if (c.contains(t.getFrom())) {
                post.add(t.getTo());
            }
        }

        return post;
    }

    /**
     * @param <S> Type of states.
     * @param <A> Type of actions.
     * @param ts  Transition system of {@code s}.
     * @param s   A state in {@code ts}.
     * @param a   An action.
     * @return All the states that {@code ts} might transition to from
     * {@code s}, when action {@code a} is selected.
     * @throws StateNotFoundException if {@code s} is not a state of {@code ts}.
     */
    public <S, A> Set<S> post(TransitionSystem<S, A, ?> ts, S s, A a) {
        Set<S> post = new HashSet<S>();
        if (!ts.getStates().contains(s)) throw new StateNotFoundException(s);
        for (TSTransition<S, A> t : ts.getTransitions()) {
            if (t.getFrom().equals(s)) {
                if (t.getAction().equals(a))
                    post.add(t.getTo());
            }
        }
        return post;
    }

    /**
     * @param <S> Type of states.
     * @param <A> Type of actions.
     * @param ts  Transition system of {@code s}.
     * @param c   Set of states in {@code ts}.
     * @param a   An action.
     * @return All the states that {@code ts} might transition to from any state
     * in {@code c}, when action {@code a} is selected.
     */
    public <S, A> Set<S> post(TransitionSystem<S, A, ?> ts, Set<S> c, A a) {
        Set<S> post = new HashSet<S>();
        for (TSTransition<S, A> t : ts.getTransitions()) {
            if (t.getAction().equals(a) && c.contains(t.getFrom()))
                post.add(t.getTo());
        }
        return post;
    }

    /**
     * @param <S> Type of states.
     * @param ts  Transition system of {@code s}.
     * @param s   A state in {@code ts}.
     * @return All the states in {@code Pre(s)}, in the context of {@code ts}.
     */
    public <S> Set<S> pre(TransitionSystem<S, ?, ?> ts, S s) {
        Set<S> pre = new HashSet<S>();
        for (TSTransition<S, ?> t : ts.getTransitions()) {
            if (t.getTo().equals(s))
                pre.add(t.getFrom());
        }
        return pre;
    }

    /**
     * @param <S> Type of states.
     * @param ts  Transition system of {@code s}.
     * @param c   States in {@code ts}.
     * @return All the states in {@code Pre(s)} where {@code s} is a member of
     * {@code c}, in the context of {@code ts}.
     * @throws StateNotFoundException if {@code s} is not a state of {@code ts}.
     */
    public <S> Set<S> pre(TransitionSystem<S, ?, ?> ts, Set<S> c) {
        Set<S> pre = new HashSet<S>();
        HashMap<S, Boolean> founds = new HashMap<S, Boolean>();
        for (S s : c) {
            founds.put(s, false);
        }
        for (TSTransition<S, ?> t : ts.getTransitions()) {
            if (c.contains(t.getTo())) {
                pre.add(t.getFrom());
                founds.put(t.getTo(), true);
            }
        }
        for (Entry<S, Boolean> en : founds.entrySet())
            if (!en.getValue()) throw new StateNotFoundException(en.getKey());
        return pre;
    }

    /**
     * @param <S> Type of states.
     * @param <A> Type of actions.
     * @param ts  Transition system of {@code s}.
     * @param s   A state in {@code ts}.
     * @param a   An action.
     * @return All the states that {@code ts} might transitioned from, when in
     * {@code s}, and the last action was {@code a}.
     * @throws StateNotFoundException if {@code s} is not a state of {@code ts}.
     */
    public <S, A> Set<S> pre(TransitionSystem<S, A, ?> ts, S s, A a) {
        if (!ts.getStates().contains(s)) throw new StateNotFoundException(s);
        Set<S> pre = new HashSet<S>();
        for (TSTransition<S, A> t : ts.getTransitions()) {
            if (t.getTo().equals(s)) {
                if (t.getAction().equals(a))
                    pre.add(t.getFrom());
            }
        }
        return pre;
    }

    /**
     * @param <S> Type of states.
     * @param <A> Type of actions.
     * @param ts  Transition system of {@code s}.
     * @param c   Set of states in {@code ts}.
     * @param a   An action.
     * @return All the states that {@code ts} might transitioned from, when in
     * any state in {@code c}, and the last action was {@code a}.
     * @throws StateNotFoundException if {@code s} is not a state of {@code ts}.
     */
    public <S, A> Set<S> pre(TransitionSystem<S, A, ?> ts, Set<S> c, A a) {
        if (!ts.getStates().containsAll(c)) throw new StateNotFoundException(c);
        Set<S> pre = new HashSet<S>();
        for (TSTransition<S, A> t : ts.getTransitions()) {
            if (t.getAction().equals(a) && c.contains(t.getTo()))
                pre.add(t.getFrom());
        }
        return pre;
    }

    /**
     * Implements the {@code reach(TS)} function.
     *
     * @param <S> Type of states.
     * @param <A> Type of actions.
     * @param ts  Transition system of {@code s}.
     * @return All states reachable in {@code ts}.
     */
    public <S, A> Set<S> reach(TransitionSystem<S, A, ?> ts) {
        Set<S> reachable = new HashSet<>();
        for (S state : ts.getInitialStates()) {
            reachHelp(reachable, ts, state);
        }
        return reachable;
    }

    public <S, A> void reachHelp(Set<S> reachable, TransitionSystem<S, A, ?> ts, S s) {
        if (!reachable.contains(s))
            reachable.add(s);
        else return;
        if (!isStateTerminal(ts, s)) {
            for (S state : post(ts, s)) {
                reachHelp(reachable, ts, state);
            }
        }
    }

    /**
     * Compute the synchronous product of two transition systems.
     *
     * @param <S1> Type of states in the first system.
     * @param <S2> Type of states in the first system.
     * @param <A>  Type of actions (in both systems).
     * @param <P>  Type of atomic propositions (in both systems).
     * @param ts1  The first transition system.
     * @param ts2  The second transition system.
     * @return A transition system that represents the product of the two.
     */
    public <S1, S2, A, P> TransitionSystem<Pair<S1, S2>, A, P> interleave(TransitionSystem<S1, A, P> ts1,
                                                                          TransitionSystem<S2, A, P> ts2) {
        List<Pair<S1, S2>> toProcess = new ArrayList<Pair<S1, S2>>(); //set of states to process
        List<Pair<S1, S2>> wasProcessed = new ArrayList<Pair<S1, S2>>(); //set of states we already processed, to keep track
        TransitionSystem<Pair<S1, S2>, A, P> output = new TransitionSystem<Pair<S1, S2>, A, P>();
        output.setName("Interleaved Transition System");
        for (S1 is1 : ts1.getInitialStates()) {
            for (S2 is2 : ts2.getInitialStates()) {
                Pair<S1, S2> is = new Pair<S1, S2>(is1, is2);
                toProcess.add(is);
            }
        }
        while (!toProcess.isEmpty()) {
            Pair<S1, S2> state = toProcess.remove(0);
            wasProcessed.add(state);
            if (ts1.getInitialStates().contains(state.first) && ts2.getInitialStates().contains(state.second)) {
                output.addInitialState(state);
            } else output.addState(state);
            for (TSTransition<S1, A> t1 : ts1.getTransitions()) {
                if (!t1.getFrom().equals(state.first))
                    continue;
                Pair<S1, S2> toState = new Pair<S1, S2>(t1.getTo(), state.second);
                output.addTransition(new TSTransition<Pair<S1, S2>, A>(state, t1.getAction(), toState));
                output.addToLabel(toState, ts1.getLabel(toState.first));
                output.addToLabel(toState, ts2.getLabel(toState.second));
                if (!wasProcessed.contains(toState))
                    toProcess.add(toState);
            }
            for (TSTransition<S2, A> t2 : ts2.getTransitions()) {
                if (!t2.getFrom().equals(state.second))
                    continue;
                Pair<S1, S2> toState = new Pair<S1, S2>(state.first, t2.getTo());
                output.addToLabel(toState, ts1.getLabel(toState.first));
                output.addToLabel(toState, ts2.getLabel(toState.second));
                output.addTransition(new TSTransition<Pair<S1, S2>, A>(state, t2.getAction(), toState));
                if (!wasProcessed.contains(toState))
                    toProcess.add(toState);
            }
        }
        for (S1 s1 : ts1.getStates())
            for (S2 s2 : ts2.getStates())
                output.addState(new Pair<S1, S2>(s1, s2));
        return output;
    }

    /**
     * Compute the synchronous product of two transition systems.
     *
     * @param <S1>               Type of states in the first system.
     * @param <S2>               Type of states in the first system.
     * @param <A>                Type of actions (in both systems).
     * @param <P>                Type of atomic propositions (in both systems).
     * @param ts1                The first transition system.
     * @param ts2                The second transition system.
     * @param handShakingActions Set of actions both systems perform together.
     * @return A transition system that represents the product of the two.
     */
    public <S1, S2, A, P> TransitionSystem<Pair<S1, S2>, A, P> interleave(TransitionSystem<S1, A, P> ts1,
                                                                          TransitionSystem<S2, A, P> ts2, Set<A> handShakingActions) {
        List<Pair<S1, S2>> toProcess = new ArrayList<Pair<S1, S2>>(); //set of states to process
        List<Pair<S1, S2>> wasProcessed = new ArrayList<Pair<S1, S2>>(); //set of states we already processed, to keep track
        TransitionSystem<Pair<S1, S2>, A, P> output = new TransitionSystem<Pair<S1, S2>, A, P>();
        output.setName("Interleaved Transition System with HankShaking Actions");
        for (S1 is1 : ts1.getInitialStates()) {
            for (S2 is2 : ts2.getInitialStates()) {
                Pair<S1, S2> is = new Pair<S1, S2>(is1, is2);
                toProcess.add(is);
            }
        }
        while (!toProcess.isEmpty()) {
            Pair<S1, S2> state = toProcess.remove(0);
            wasProcessed.add(state);
            if (ts1.getInitialStates().contains(state.first) && ts2.getInitialStates().contains(state.second)) {
                output.addInitialState(state);
            } else output.addState(state);
            for (TSTransition<S1, A> t1 : ts1.getTransitions()) {
                if (!t1.getFrom().equals(state.first))
                    continue;
                if (handShakingActions.contains(t1.getAction())) { //This transition is using a handshaking action
                    for (TSTransition<S2, A> t2 : ts2.getTransitions()) { //find the corresponding ts2 transition
                        if (!t2.getFrom().equals(state.second) || !t2.getAction().equals(t1.getAction()))
                            continue;
                        Pair<S1, S2> toState = new Pair<S1, S2>(t1.getTo(), t2.getTo());
                        output.addTransition(new TSTransition<Pair<S1, S2>, A>(state, t1.getAction(), toState));
                        output.addToLabel(toState, ts1.getLabel(toState.first));
                        output.addToLabel(toState, ts2.getLabel(toState.second));
                        if (!wasProcessed.contains(toState))
                            toProcess.add(toState);
                    }
                    continue;
                }
                Pair<S1, S2> toState = new Pair<S1, S2>(t1.getTo(), state.second);
                output.addTransition(new TSTransition<Pair<S1, S2>, A>(state, t1.getAction(), toState));
                output.addToLabel(toState, ts1.getLabel(toState.first));
                output.addToLabel(toState, ts2.getLabel(toState.second));
                if (!wasProcessed.contains(toState))
                    toProcess.add(toState);
            }
            for (TSTransition<S2, A> t2 : ts2.getTransitions()) {
                if (!t2.getFrom().equals(state.second))
                    continue;
                if (handShakingActions.contains(t2.getAction())) // we already handled handshake actions in ts1 transitions loop
                    continue;
                Pair<S1, S2> toState = new Pair<S1, S2>(state.first, t2.getTo());
                output.addToLabel(toState, ts1.getLabel(toState.first));
                output.addToLabel(toState, ts2.getLabel(toState.second));
                output.addTransition(new TSTransition<Pair<S1, S2>, A>(state, t2.getAction(), toState));
                if (!wasProcessed.contains(toState))
                    toProcess.add(toState);
            }
        }
        for (S1 s1 : ts1.getStates())
            for (S2 s2 : ts2.getStates())
                output.addState(new Pair<S1, S2>(s1, s2));
        return output;
    }

    /**
     * Creates a new {@link ProgramGraph} object.
     *
     * @param <L> Type of locations in the graph.
     * @param <A> Type of actions of the graph.
     * @return A new program graph instance.
     */
    public <L, A> ProgramGraph<L, A> createProgramGraph() {
        return new ProgramGraph<>();
    }

    /**
     * Interleaves two program graphs.
     *
     * @param <L1> Type of locations in the first graph.
     * @param <L2> Type of locations in the second graph.
     * @param <A>  Type of actions in BOTH GRAPHS.
     * @param pg1  The first program graph.
     * @param pg2  The second program graph.
     * @return Interleaved program graph.
     */
    public <L1, L2, A> ProgramGraph<Pair<L1, L2>, A> interleave(ProgramGraph<L1, A> pg1, ProgramGraph<L2, A> pg2) {
        ProgramGraph<Pair<L1, L2>, A> interleaved = createProgramGraph();
        interleaved.setName("Interleaved Program Graph");
        // Adds all the cartesian product locations.
        for (L1 loc1 : pg1.getLocations())
            for (L2 loc2 : pg2.getLocations())
                interleaved.addLocation(new Pair<>(loc1, loc2));
        for (PGTransition<L1, A> t1 : pg1.getTransitions()) {
            for (L2 loc2 : pg2.getLocations())
                interleaved.addTransition(new PGTransition<>(new Pair(t1.getFrom(), loc2), t1.getCondition(), t1.getAction(), new Pair(t1.getTo(), loc2)));
        }
        for (PGTransition<L2, A> t2 : pg2.getTransitions()) {
            for (L1 loc1 : pg1.getLocations())
                interleaved.addTransition(new PGTransition<>(new Pair(loc1, t2.getFrom()), t2.getCondition(), t2.getAction(), new Pair(loc1, t2.getTo())));
        }
        //initial locations and initial conditions
        for (L1 loc1 : pg1.getInitialLocations()) {
            for (L2 loc2 : pg2.getInitialLocations()) {
                interleaved.setInitial(new Pair<L1, L2>(loc1, loc2), true);
            }
        }
        for (List<String> in1 : pg1.getInitalizations()) {
            for (List<String> in2 : pg2.getInitalizations()) {
                List<String> init = new ArrayList<String>();
                init.addAll(in1);
                init.addAll(in2);
                interleaved.addInitalization(init);
            }
        }
        return interleaved;
    }

    /**
     * Creates a {@link TransitionSystem} representing the passed circuit.
     *
     * @param c The circuit to translate into a {@link TransitionSystem}.
     * @return A {@link TransitionSystem} representing {@code c}.
     */
    public TransitionSystem<Pair<Map<String, Boolean>, Map<String, Boolean>>, Map<String, Boolean>, Object> transitionSystemFromCircuit(
            Circuit c) {
        TransitionSystem<Pair<Map<String, Boolean>, Map<String, Boolean>>, Map<String, Boolean>, Object> output = new TransitionSystem<Pair<Map<String, Boolean>, Map<String, Boolean>>, Map<String, Boolean>, Object>();
        output.setName("Transition System From Circuit");
        Set<HashMap<String, Boolean>> registersMaps = CircuitImp.initMaps(c.getRegisterNames());
        Set<HashMap<String, Boolean>> inputMaps = CircuitImp.initMaps(c.getInputPortNames());

        //All States
        for (HashMap<String, Boolean> registersMap : registersMaps)
            for (HashMap<String, Boolean> inputMap : inputMaps)
                output.addState(new Pair<Map<String, Boolean>, Map<String, Boolean>>(inputMap, registersMap));
        //Initial States
        HashMap<String, Boolean> falseRegistersMap = new HashMap<String, Boolean>();
        for (String rname : c.getRegisterNames()) {
            output.addAtomicProposition(rname);
            falseRegistersMap.put(rname, false);
        }
        for (HashMap<String, Boolean> inputMap : inputMaps) {
            output.addInitialState(new Pair<Map<String, Boolean>, Map<String, Boolean>>(inputMap, falseRegistersMap));
            output.addAction(inputMap);
        }
        for (String iname : c.getInputPortNames())
            output.addAtomicProposition(iname);
        for (String oname : c.getOutputPortNames())
            output.addAtomicProposition(oname);
        //Transitions and Labels
        for (Pair<Map<String, Boolean>, Map<String, Boolean>> state : output.getStates()) {
            for (Map<String, Boolean> action : output.getActions()) {
                Map<String, Boolean> tempInputs = state.first;
                Map<String, Boolean> tempRegisters = state.second;
                Map<String, Boolean> updatedRegs = c.updateRegisters(tempInputs, tempRegisters);
                output.addTransition(new TSTransition<>(state, action, new Pair<Map<String, Boolean>, Map<String, Boolean>>(action, updatedRegs)));
            }
            for (String register : state.second.keySet())
                if (state.second.get(register))
                    output.addToLabel(state, register);
            for (String input : state.first.keySet())
                if (state.first.get(input))
                    output.addToLabel(state, input);
            Map<String, Boolean> outputs = c.computeOutputs(state.first, state.second);
            for (String outputName : outputs.keySet())
                if (outputs.get(outputName))
                    output.addToLabel(state, outputName);
        }

        ArrayList<Pair<Map<String, Boolean>, Map<String, Boolean>>> toRemove = new ArrayList<>();
        ArrayList<TSTransition<Pair<Map<String, Boolean>, Map<String, Boolean>>, Map<String, Boolean>>> transToRemove = new ArrayList<>();
        Set<Pair<Map<String, Boolean>, Map<String, Boolean>>> reachable = reach(output);
        for(Pair<Map<String, Boolean>, Map<String, Boolean>> s : output.getStates()){
        	boolean isReachable = true;
        	if(!reachable.contains(s)){
        		toRemove.add(s);
        		isReachable = false;
        	}
        	if(!isReachable){
	        	for(TSTransition<Pair<Map<String, Boolean>, Map<String, Boolean>>, Map<String, Boolean>> t : output.getTransitions()){
	        		if(t.getFrom().equals(s)){
	        			transToRemove.add(t);
	        		}
	        	}
        	}
        }
        for(TSTransition<Pair<Map<String, Boolean>, Map<String, Boolean>>, Map<String, Boolean>> tran : transToRemove){
        	output.removeTransition(tran);
        }
        for(Pair<Map<String, Boolean>, Map<String, Boolean>> s : toRemove){
        	output.removeState(s);
        }
        
        return output;
    }

    /**
     * Creates a {@link TransitionSystem} from a program graph.
     *
     * @param <L>           Type of program graph locations.
     * @param <A>           Type of program graph actions.
     * @param pg            The program graph to be translated into a transition system.
     * @param actionDefs    Defines the effect of each action.
     * @param conditionDefs Defines the conditions (guards) of the program
     *                      graph.
     * @return A transition system representing {@code pg}.
     */
    public <L, A> TransitionSystem<Pair<L, Map<String, Object>>, A, String> transitionSystemFromProgramGraph(
            ProgramGraph<L, A> pg, Set<ActionDef> actionDefs, Set<ConditionDef> conditionDefs) {
        TransitionSystem<Pair<L, Map<String, Object>>, A, String> output = new TransitionSystem<Pair<L, Map<String, Object>>, A, String>();
        output.setName("Transition System From Program Graph");
        // initial states
        for (L loc_0 : pg.getInitialLocations()) {
            if(pg.getInitalizations().isEmpty()) { output.addInitialState(new Pair(loc_0, new HashMap<>()));}
            for (List<String> g : pg.getInitalizations()) {
                Map<String, Object> eval = new HashMap<String, Object>();
                Set<String> labels = new HashSet<String>();
                for (String g_i : g) {
                    eval = ActionDef.effect(actionDefs, eval, g_i);
                }
                Pair<L, Map<String, Object>> init_state = new Pair(loc_0, eval);
                output.addInitialState(init_state);
                labels.addAll(init_state.getSecond().entrySet().stream().map(et -> et.getKey() + " = " + et.getValue().toString()).collect(Collectors.toSet()));
                labels.add(loc_0.toString());
                output.addToLabel(init_state, labels);
            }
        }

        Queue<Pair<L, Map<String, Object>>> q = new LinkedList<>(output.getInitialStates());
        List<Pair<L, Map<String, Object>>> used_states = new LinkedList<>(output.getInitialStates());
        while (!q.isEmpty()) {
            Pair<L, Map<String, Object>> state = q.remove();
            for (PGTransition<L, A> trans : pg.getTransitions()) {
                L from = trans.getFrom();
                A action = trans.getAction();
                L to = trans.getTo();
                String cond = trans.getCondition();
                Map<String, Object> eval = state.getSecond();
                if (from.equals(state.first) && ConditionDef.evaluate(conditionDefs, eval, cond)) {
                    Pair<L, Map<String, Object>> new_state = new Pair<>(to, ActionDef.effect(actionDefs, eval, action));
                    //transitions and stats
                    if (!used_states.contains(new_state)) {
                        q.add(new_state);
                        used_states.add(new_state);
                    }
                    output.addTransition(new TSTransition<>(state, action, new_state));
                    //Labeling and AP's
                    Set<String> labels = new HashSet<String>();
                    labels.addAll(new_state.getSecond().entrySet().stream().map(et -> et.getKey() + " = " + et.getValue().toString()).collect(Collectors.toSet()));
                    labels.add(to.toString());
                    output.addToLabel(new_state, labels);
                }
            }
            Set<String> labels = new HashSet<String>();
            labels.add(state.getFirst().toString());
            output.addToLabel(state,new HashSet(labels));
        }
        return output;
    }


    /**
     * Creates a transition system representing channel system {@code cs}.
     *
     * @param <L> Type of locations in the channel system.
     * @param <A> Type of actions in the channel system.
     * @param cs  The channel system to be translated into a transition system.
     * @return A transition system representing {@code cs}.
     */
    public <L, A> TransitionSystem<Pair<List<L>, Map<String, Object>>, A, String> transitionSystemFromChannelSystem(
            ChannelSystem<L, A> cs) {

        Set<ActionDef> actions = Collections.singleton(new ParserBasedActDef());
        Set<ConditionDef> conditions = Collections.singleton(new ParserBasedCondDef());
        return transitionSystemFromChannelSystem(cs, actions, conditions);
    }

    public <L, A> TransitionSystem<Pair<List<L>, Map<String, Object>>, A, String> transitionSystemFromChannelSystem(
            ChannelSystem<L, A> cs, Set<ActionDef> actions, Set<ConditionDef> conditions) {
        Set<ActionDef> interleaveActions = Collections.singleton(new ParserBasedInterleavingActDef());

        TransitionSystem<Pair<List<L>, Map<String, Object>>, A, String> output = new TransitionSystem<Pair<List<L>, Map<String, Object>>, A, String>();
        List<Pair<List<L>, Map<String, Object>>> init_states = initial_helper(cs.getProgramGraphs(), actions);
        // initial states
        for (Pair<List<L>, Map<String, Object>> loc_0 : init_states) {
            output.addInitialState(loc_0);
            Set<String> labels = new HashSet<String>();
            labels.addAll(loc_0.getSecond().entrySet().stream().map(et -> et.getKey() + " = " + et.getValue().toString()).collect(Collectors.toSet()));
            labels.addAll(loc_0.getFirst().stream().map(x -> x.toString()).collect(Collectors.toSet()));
            output.addToLabel(loc_0, labels);
        }
        Queue<Pair<List<L>, Map<String, Object>>> q = new LinkedList<>(output.getInitialStates());
        List<Pair<List<L>, Map<String, Object>>> used_states = new LinkedList<>(output.getInitialStates());
        while (!q.isEmpty()) {
            Pair<List<L>, Map<String, Object>> state = q.remove();
            List<Pair<PGTransition<L, A>, Integer>> questionMarks = new LinkedList<>();
            List<Pair<PGTransition<L, A>, Integer>> exclamationMark = new LinkedList<>();
            Integer index = 0;
            for (ProgramGraph<L, A> pg : cs.getProgramGraphs()) {
                for (PGTransition<L, A> trans : pg.getTransitions()) {
                    L from = trans.getFrom();
                    A action = trans.getAction();
                    L to = trans.getTo();
                    String cond = trans.getCondition();
                    List<L> locs = state.getFirst();
                    Map<String, Object> eval = state.getSecond();
                    if (locs.get(index).equals(from) && ConditionDef.evaluate(conditions, eval, cond)) {
                        if (!action.toString().startsWith("_")) {
                            List<L> copy_locs = new LinkedList(locs);
                            copy_locs.set(index, to);
                            Map<String, Object> new_eval = ActionDef.effect(actions, eval, action);
                            Pair<List<L>, Map<String, Object>> new_state = new Pair(copy_locs, new_eval);
                            if (new_eval == null) continue;
                            if (!used_states.contains(new_state)) {
                                q.add(new_state);
                                used_states.add(new_state);
                            }
                            output.addTransition(new TSTransition<>(state, action, new_state));
                            //Labeling and AP's
                            Set<String> labels = new HashSet<String>();
                            labels.addAll(new_state.getSecond().entrySet().stream().map(et -> et.getKey() + " = " + et.getValue().toString()).collect(Collectors.toSet()));
                            labels.addAll(new_state.getFirst().stream().map(x -> x.toString()).collect(Collectors.toSet()));
                            output.addToLabel(new_state, labels);
                        } else {
                            if (action.toString().contains("?")) {
                                questionMarks.add(new Pair(trans, index));
                                doInterleaveAction(interleaveActions, output, q, used_states, state, exclamationMark, index, from, action, to, locs, eval);
                            } else {
                                exclamationMark.add(new Pair(trans, index));
                                doInterleaveAction(interleaveActions, output, q, used_states, state, questionMarks, index, from, action, to, locs, eval);
                            }


                        }
                    }

                }
                index++;
            }
        }

        return output;
    }

    private <L, A> void doInterleaveAction(Set<ActionDef> interleaveActions, TransitionSystem<Pair<List<L>, Map<String, Object>>, A, String> output, Queue<Pair<List<L>, Map<String, Object>>> q, List<Pair<List<L>, Map<String, Object>>> used_states, Pair<List<L>, Map<String, Object>> state, List<Pair<PGTransition<L, A>, Integer>> mark, Integer index, L from, A action, L to, List<L> locs, Map<String, Object> eval) {
        for (Pair<PGTransition<L, A>, Integer> e : mark) {
            if (!e.getSecond().equals(index)) {
                List<L> copy_locs = new LinkedList(locs);
                copy_locs.set(locs.indexOf(from), to);
                copy_locs.set(locs.indexOf(e.getFirst().getFrom()), e.getFirst().getTo());
                String newAction = e.getFirst().getAction().toString() + "|" + action.toString();
//                System.out.println(newAction);
                Map<String, Object> new_eval = ActionDef.effect(interleaveActions, eval, newAction);
                Pair<List<L>, Map<String, Object>> new_state = new Pair(copy_locs, new_eval);
                if (new_eval == null) continue;
                if (!used_states.contains(new_state)) {
                    q.add(new_state);
                    used_states.add(new_state);
                }
                output.addTransition(new TSTransition(state, newAction, new_state));
                //Labeling and AP's
                Set<String> labels = new HashSet<String>();
                labels.addAll(new_state.getSecond().entrySet().stream().map(et -> et.getKey() + " = " + et.getValue().toString()).collect(Collectors.toSet()));
                labels.addAll(new_state.getFirst().stream().map(x -> x.toString()).collect(Collectors.toSet()));
                output.addToLabel(new_state, labels);
            }
        }
    }

    public <L, A> List<Pair<List<L>, Map<String, Object>>> initial_helper(List<ProgramGraph<L, A>> pgs, Set<ActionDef> actions) {
        List<Pair<List<L>, Map<String, Object>>> res = new LinkedList<>();
        if (pgs.size() == 1) {
            Set<List<String>> gs = pgs.get(0).getInitalizations();
            if (gs.isEmpty()) {
                gs = new HashSet<>();
                gs.add(new LinkedList<>());
            }

            for (List<String> g : gs) {
                Map<String, Object> eval = new HashMap<String, Object>();
                for (String g_i : g) {
                    eval = ActionDef.effect(actions, eval, g_i);
                }
                for (L init : pgs.get(0).getInitialLocations()) {
                    List<L> loc = new LinkedList();
                    loc.add(init);
                    res.add(new Pair(loc, eval));
                }
            }
        } else {
            List<Pair<List<L>, Map<String, Object>>> rec = initial_helper(pgs.subList(0, pgs.size() - 1), actions);
            Set<List<String>> gs = pgs.get(pgs.size() - 1).getInitalizations();
            if (gs.isEmpty()) {
                gs = new HashSet<>();
                gs.add(new LinkedList<>());
            }
            for (List<String> g : gs)
                for (Pair<List<L>, Map<String, Object>> e : rec) {
                    Map<String, Object> eval = e.getSecond();
                    for (String g_i : g) {
                        eval = ActionDef.effect(actions, eval, g_i);
                    }
                    for (L loc : pgs.get(pgs.size() - 1).getInitialLocations()) {
                        Pair<List<L>, Map<String, Object>> dummy = new Pair(new LinkedList(e.getFirst()), eval);
                        dummy.getFirst().add(loc);
                        res.add(dummy);
                    }
                }
        }
        return res;
    }

    public List<PGTransition<String, String>> contextToPGTransitions(StmtContext c, boolean isNested){
        ArrayList<PGTransition<String, String>> output = new ArrayList<PGTransition<String, String>>();
    	if(c.isSimpleStmt()){ // Simple Statement
    		String action = c.getText();	
    		if(isNested)
        		output.add(new PGTransition<String, String>("", "", action,"")); 
    		else
    			output.add(new PGTransition<String, String>(c.getText(), "", action, ""));
    	} else if(c.isIfStmt()){ //If Statement
    		IfstmtContext ifStmt = c.ifstmt();
    		for(OptionContext op : ifStmt.option()){
                StmtContext opStmt = op.stmt();
    			List<PGTransition<String, String>> subTrans = contextToPGTransitions(opStmt, true);
    			for(PGTransition<String, String> subTran : subTrans){
    				if(!isNested && subTran.getFrom().equals(""))
    					subTran.setFrom(ifStmt.getText());
    				if(subTran.getFrom().equals(ifStmt.getText()) || subTran.getFrom().equals("")){
    					if(subTran.getCondition().equals(""))
    						subTran.setCondition("(" + op.boolexpr().getText() + ")");
    					else
    						subTran.setCondition("(" + op.boolexpr().getText() + ") && (" + subTran.getCondition() + ")");
    					
    				}
                }
    			output.addAll(subTrans);
            }
    	} else if(c.isDoStmt()){ //Do Statement
            DostmtContext stmt = c.dostmt();
            String exitCond = "";
            for (OptionContext op : stmt.option()) {
                StmtContext opStmt = op.stmt();
                if (!exitCond.equals(""))
    				exitCond += "||";
    			exitCond += "(" + op.boolexpr().getText() + ")";
    			List<PGTransition<String, String>> subTrans = contextToPGTransitions(opStmt, true);
    			for(PGTransition<String, String> subTran : subTrans){
    				if(!subTran.getFrom().equals(""))
    					subTran.setFrom(subTran.getFrom() + ";" + stmt.getText());
    				else if(!isNested)
    					subTran.setFrom(stmt.getText());
    				
    				if(subTran.getFrom().equals(stmt.getText()) || subTran.getFrom().equals(""))
    				{
    					if(subTran.getCondition().equals(""))	
    						subTran.setCondition("(" + op.boolexpr().getText() + ")");
    					else 
    						subTran.setCondition("(" + op.boolexpr().getText() + ") && (" + subTran.getCondition() + ")");
						
    				}

    				if(subTran.getTo().equals(""))
    					subTran.setTo(stmt.getText());
    				else
    					subTran.setTo(subTran.getTo() + ";" + stmt.getText());
                }
    			output.addAll(subTrans);
    			for(PGTransition<String, String> subTran :subTrans){
    				if(subTran.getFrom().equals(""))
    					output.add(new PGTransition<String, String>(stmt.getText(), subTran.getCondition(), subTran.getAction(), subTran.getTo()));
    			}
    		}
    		exitCond = "!(" + exitCond + ")";
    		if(isNested)
    			output.add(new PGTransition<String, String>("", exitCond, "", ""));
    		output.add(new PGTransition<String, String>(stmt.getText(), exitCond, "", ""));
        } else { //; - Chain Statements
    		List<PGTransition<String, String>> subTrans = contextToPGTransitions(c.stmt(0), isNested);
            String rest = c.stmt(1).getText();
    		for(PGTransition<String, String> subTran : subTrans){
    			if(isNested){
    				if(!subTran.getFrom().equals(""))
    					subTran.setFrom(subTran.getFrom() + ";" + rest);
    			}else
    				subTran.setFrom(subTran.getFrom() + ";" + rest);
    			
    		    if(subTran.getTo().equals(""))
    		    	subTran.setTo(rest);
    		    else
    		    	subTran.setTo(subTran.getTo() + ";" + rest);
            }
    		output.addAll(subTrans);
    		output.addAll(contextToPGTransitions(c.stmt(1), false));
        }
        return output;
    }

    public ProgramGraph<String, String> contextToProgramGraph(StmtContext context) {
        ProgramGraph<String, String> output = createProgramGraph();
        output.setInitial(context.getText(), true);
		List<PGTransition<String, String>> transitions = contextToPGTransitions(context, false);
        for (PGTransition<String, String> t : transitions) {
            output.addTransition(t);
        }
        return output;
    }

    /**
     * Construct a program graph from nanopromela code.
     *
     * @param filename The nanopromela code.
     * @return A program graph for the given code.
     * @throws Exception If the code is invalid.
     */
    public ProgramGraph<String, String> programGraphFromNanoPromela(String filename) throws Exception {
        StmtContext context = NanoPromelaFileReader.pareseNanoPromelaFile(filename);
        return contextToProgramGraph(context);
    }

    /**
     * Construct a program graph from nanopromela code.
     *
     * @param nanopromela The nanopromela code.
     * @return A program graph for the given code.
     * @throws Exception If the code is invalid.
     */
    public ProgramGraph<String, String> programGraphFromNanoPromelaString(String nanopromela) throws Exception {
        StmtContext context = NanoPromelaFileReader.pareseNanoPromelaString(nanopromela);
        return contextToProgramGraph(context);
    }

    /**
     * Construct a program graph from nanopromela code.
     *
     * @param inputStream The nanopromela code.
     * @return A program graph for the given code.
     * @throws Exception If the code is invalid.
     */
    public ProgramGraph<String, String> programGraphFromNanoPromela(InputStream inputStream) throws Exception {
        StmtContext context = NanoPromelaFileReader.parseNanoPromelaStream(inputStream);
        return contextToProgramGraph(context);
    }

    /**
     * Creates a transition system from a transition system and an automaton.
     *
     * @param <Sts>  Type of states in the transition system.
     * @param <Saut> Type of states in the automaton.
     * @param <A>    Type of actions in the transition system.
     * @param <P>    Type of atomic propositions in the transition system, which is
     *               also the type of the automaton alphabet.
     * @param ts     The transition system.
     * @param aut    The automaton.
     * @return The product of {@code ts} with {@code aut}.
     */
    public <
            Sts, Saut, A, P> TransitionSystem<Pair<Sts, Saut>, A, Saut> product(TransitionSystem<Sts, A, P> ts,
                                                                                Automaton<Saut, P> aut) {
        throw new java.lang.UnsupportedOperationException();
    }

    /**
     * Verify that a system satisfies an omega regular property.
     *
     * @param <S>    Type of states in the transition system.
     * @param <Saut> Type of states in the automaton.
     * @param <A>    Type of actions in the transition system.
     * @param <P>    Type of atomic propositions in the transition system, which is
     *               also the type of the automaton alphabet.
     * @param ts     The transition system.
     * @param aut    A Büchi automaton for the words that do not satisfy the
     *               property.
     * @return A VerificationSucceeded object or a VerificationFailed object
     * with a counterexample.
     */
    public <S, A, P, Saut> VerificationResult<S> verifyAnOmegaRegularProperty(TransitionSystem<S, A, P> ts,
                                                                              Automaton<Saut, P> aut) {
        throw new java.lang.UnsupportedOperationException();
    }

    /**
     * Translation of Linear Temporal Logic (LTL) formula to a Nondeterministic
     * Büchi Automaton (NBA).
     *
     * @param <L> Type of resultant automaton transition alphabet
     * @param ltl The LTL formula represented as a parse-tree.
     * @return An automaton A such that L_\omega(A)=Words(ltl)
     */
    public <L> Automaton<?, L> LTL2NBA(LTL<L> ltl) {
        throw new java.lang.UnsupportedOperationException();
    }

    /**
     * A translation of a Generalized Büchi Automaton (GNBA) to a
     * Nondeterministic Büchi Automaton (NBA).
     *
     * @param <L>    Type of resultant automaton transition alphabet
     * @param mulAut An automaton with a set of accepting states (colors).
     * @return An equivalent automaton with a single set of accepting states.
     */
    public <L> Automaton<?, L> GNBA2NBA(MultiColorAutomaton<?, L> mulAut) {
        throw new java.lang.UnsupportedOperationException();
    }

}
