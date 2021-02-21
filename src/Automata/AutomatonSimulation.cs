using System;
using System.Collections.Generic;
using System.Linq;

namespace Microsoft.Automata.Extensions
{
    /// <summary>
    /// Class of extensions methods for Automaton<T> related to computing simulation and state reducing s-NFA by using simulation,
    /// so they can be easily added to https://github.com/AutomataDotNet/
    /// </summary>
    public static class AutomatonSimulationExtension
    {
        /// <summary>
        /// If sfa has n states, returns new automaton equal to sfa where each state has number from {0,1,...,n-1} 
        /// </summary>
        /// <returns> new automaton with remapped states </returns>
        public static Automaton<T> RemapStates<T>(this Automaton<T> sfa)
        {
            // remap states
            Dictionary<int, int> statesMap = new Dictionary<int, int>();
            int i = 0;
            foreach (var state in sfa.States)
            {
                statesMap[state] = i;
                ++i;
            }

            // update finalstates
            HashSet<int> newFinalStates = new HashSet<int>();
            foreach (var finalState in sfa.GetFinalStates())
            {
                newFinalStates.Add(statesMap[finalState]);
            }

            // update moves
            List<Move<T>> newMoves = new List<Move<T>>();
            foreach (var move in sfa.GetMoves())
            {
                int source = statesMap[move.SourceState];
                int to = statesMap[move.TargetState];
                T label = move.Label;
                newMoves.Add(new Move<T>(source, to, label));
            }

            return Automaton<T>.Create(sfa.Algebra, statesMap[sfa.InitialState], newFinalStates, newMoves);
        }

        /// <summary>
        /// Returns simulation preorder of sfa as array of statesXstates using un-optimizied local SFA alg.
        /// </summary>
        /// <param name="debug"> if true, prints debug message </param>
        private static bool[,] getLocalSimulation<T>(this Automaton<T> sfa, bool debug = false)
        {
            // mapping of minterms to ints based on source state (first int)
            // so if we have state q and transitions from q labelled with psi and phi
            // we would have numToMinterm[q][0] = psi, numToMinterm[q][1] = phi so
            // 0 -> psi, 1 -> phi
            Dictionary<int, T[]> numToMinterm = new Dictionary<int, T[]>();

            // counters N(phi)_it = n
            // Counters[i,t][phi(mapped to intenger by numToMinterm)] = n
            int[,][] Counters = new int[sfa.MaxState + 1, sfa.MaxState + 1][];

            // inverse delta for local minterm automaton (using mapped minterms)
            //         stateto   statefrom, mapped minterm
            Dictionary<int, List<Tuple<int, int>>> deltaInvMinterm = new Dictionary<int, List<Tuple<int, int>>>();

            foreach (var state in sfa.States)
            {
                deltaInvMinterm[state] = new List<Tuple<int, int>>();
            }

            int debug_mintermCount = 0;
            int debug_numOfMoves = 0;
            int debug_numOfInnerLoop = 0;
            int debug_numOfInnerLoop1 = 0;
            string debugMessage = "";

            foreach (var state in sfa.States)
            {
                // get two arrays from transitions with source state = state
                // statesTo - i-th transition has target state statesTo[i]
                // predicates - i-th transition has label predicates[i]
                var movesFromState = new List<Move<T>>(sfa.GetMovesFrom(state));
                var predAndStates = movesFromState.ToArray();
                var statesTo = Array.ConvertAll(predAndStates, move => { return move.TargetState; });
                var predicates = Array.ConvertAll(predAndStates, move => { return move.Label; });

                // get local minterms for state
                var minterms = new List<Tuple<bool[], T>>(sfa.Algebra.GenerateMinterms(predicates));
                // 'map them to integers'
                numToMinterm[state] = new T[minterms.Count];

                debug_mintermCount += minterms.Count;

                // the number of counters is variable, depends on the number of minterms
                foreach (var state2 in sfa.States)
                {
                    Counters[state2, state] = new int[minterms.Count];
                }

                int j = 0; // mapping of minterm
                foreach (var minterm in minterms)
                {
                    numToMinterm[state][j] = minterm.Item2; // this minterm is mapped to i
                    int numOfGeneratingPred = 0; // number of transitions whose label created minterm
                    for (int i = 0; i < minterm.Item1.Length; ++i)
                    {
                        // get all the transitions whose label created minterm
                        if (minterm.Item1[i])
                        {
                            ++debug_numOfMoves;

                            ++numOfGeneratingPred;
                            deltaInvMinterm[statesTo[i]].Add(Tuple.Create(state, j));
                        }
                    }

                    // initialize counters with the number of transitions whose label created minterm
                    foreach (var state2 in sfa.States)
                    {
                        Counters[state2, state][j] = numOfGeneratingPred;
                    }

                    ++j;
                }
            }

            debugMessage = debug_mintermCount + ", " + debug_numOfMoves;

            // simulation preorder
            bool[,] simulation = new bool[sfa.MaxState + 1, sfa.MaxState + 1];
            // queue of pairs of states waiting to get processed
            Queue<Tuple<int, int>> processedPairs = new Queue<Tuple<int, int>>();
            // initialize simulation as (QxQ)-(FxQ)
            foreach (var i in sfa.States)
            {
                foreach (var j in sfa.States)
                {
                    if (sfa.GetFinalStates().Contains(i) && !sfa.GetFinalStates().Contains(j))
                    {
                        simulation[i, j] = false;
                        processedPairs.Enqueue(Tuple.Create(i, j));
                    }
                    else
                    {
                        simulation[i, j] = true;
                    }
                }
            }

            while (processedPairs.Count != 0)
            {
                var statePair = processedPairs.Dequeue();
                int i = statePair.Item1;
                int j = statePair.Item2;

                foreach (var tjMove in deltaInvMinterm[j])
                {
                    int t = tjMove.Item1;
                    int mintermMapping = tjMove.Item2;
                    --Counters[i, t][tjMove.Item2];
                    if (Counters[i, t][tjMove.Item2] == 0)
                    {
                        foreach (var siMove in sfa.GetMovesTo(i))
                        {
                            int s = siMove.SourceState;
                            ++debug_numOfInnerLoop1;
                            if (simulation[s, t])
                            {
                                ++debug_numOfInnerLoop;
                                var and = sfa.Algebra.MkAnd(numToMinterm[t][mintermMapping], siMove.Label);
                                if (sfa.Algebra.IsSatisfiable(and))
                                {
                                    simulation[s, t] = false;
                                    processedPairs.Enqueue(Tuple.Create(s, t));
                                }
                            }
                        }
                    }
                }


            }

            debugMessage += ", " + debug_numOfInnerLoop1 + ", " + debug_numOfInnerLoop;

            if (debug)
                Console.WriteLine(debugMessage);

            return simulation;
        }


        /// <summary>
        /// Returns simulation preorder of sfa as array of statesXstates using optimizied local SFA alg.
        /// </summary>
        private static bool[,] getLocalSimulationOptimizied<T>(this Automaton<T> sfa)
        {
            // mapping of minterms to ints based on source state (first int)
            // so if we have state q and transitions from q labelled with psi and phi
            // we would have numToMinterm[q][0] = psi, numToMinterm[q][1] = phi so
            // 0 -> psi, 1 -> phi
            Dictionary<int, T[]> numToMinterm = new Dictionary<int, T[]>();

            // counters N(phi)_it = n
            // Counters[i,t][phi(mapped to intenger by numToMinterm)] = n
            int[,][] Counters = new int[sfa.MaxState + 1, sfa.MaxState + 1][];

            // inverse delta for local minterm automaton (using mapped minterms)
            //         stateto   statefrom, mapped minterm
            Dictionary<int, List<Tuple<int, int>>> deltaInvMinterm = new Dictionary<int, List<Tuple<int, int>>>();

            foreach (var state in sfa.States)
            {
                deltaInvMinterm[state] = new List<Tuple<int, int>>();
            }


            foreach (var state in sfa.States)
            {
                // get two arrays from transitions with source state = state
                // statesTo - i-th transition has target state statesTo[i]
                // predicates - i-th transition has label predicates[i]
                var movesFromState = new List<Move<T>>(sfa.GetMovesFrom(state));
                var predAndStates = movesFromState.ToArray();
                var statesTo = Array.ConvertAll(predAndStates, move => { return move.TargetState; });
                var predicates = Array.ConvertAll(predAndStates, move => { return move.Label; });

                // get local minterms for state
                var minterms = new List<Tuple<bool[], T>>(sfa.Algebra.GenerateMinterms(predicates));
                // 'map them to integers'
                numToMinterm[state] = new T[minterms.Count];

                // the number of counters is variable, depends on the number of minterms
                foreach (var state2 in sfa.States)
                {
                    Counters[state2, state] = new int[minterms.Count];
                }

                int j = 0; // mapping of minterm
                foreach (var minterm in minterms)
                {
                    numToMinterm[state][j] = minterm.Item2; // this minterm is mapped to i
                    int numOfGeneratingPred = 0; // number of transitions whose label created minterm
                    for (int i = 0; i < minterm.Item1.Length; ++i)
                    {
                        // get all the transitions whose label created minterm
                        if (minterm.Item1[i])
                        {
                            ++numOfGeneratingPred;
                            deltaInvMinterm[statesTo[i]].Add(Tuple.Create(state, j));
                        }
                    }

                    // initialize counters with the number of transitions whose label created minterm
                    foreach (var state2 in sfa.States)
                    {
                        Counters[state2, state][j] = numOfGeneratingPred;
                    }

                    ++j;
                }
            }

            // simulation preorder
            bool[,] simulation = new bool[sfa.MaxState + 1, sfa.MaxState + 1];
            // queue of pairs of states waiting to get processed
            Queue<Tuple<int, int>> processedPairs = new Queue<Tuple<int, int>>();
            // initialize simulation as (QxQ)-(FxQ)
            foreach (var i in sfa.States)
            {
                foreach (var j in sfa.States)
                {
                    if (sfa.GetFinalStates().Contains(i) && !sfa.GetFinalStates().Contains(j))
                    {
                        simulation[i, j] = false;
                        processedPairs.Enqueue(Tuple.Create(i, j));
                    }
                    else
                    {
                        simulation[i, j] = true;
                    }
                }
            }

            // during processing of pairs we will save:
            // for all j such that t---psi--->j and j simulates i, we save to toProcess[i,t] = toProcess[i,t] or psi
            var toProcess = new T[sfa.MaxState + 1, sfa.MaxState + 1];
            // toProcess[i,t] is true if something was 'added' to toProcess[i,t] (toProcess[i,t] != false predicate) 
            var toProcessIsIn = new bool[sfa.MaxState + 1, sfa.MaxState + 1];
            // initialization
            foreach (var state1 in sfa.GetStates())
            {
                foreach (var state2 in sfa.GetStates())
                {
                    toProcess[state1, state2] = sfa.Algebra.False;
                    toProcessIsIn[state1, state2] = false;
                }
            }
            // every (i,t) where toProcess[i,t] = true is in this queue
            var toProcessQueue = new Queue<Tuple<int, int>>();

            bool end = false;
            while (!end)
            {
                // first we process all pairs, check if some counters get to zero and we gather all predicates for which counter reached zero
                while (processedPairs.Count != 0)
                {
                    var statePair = processedPairs.Dequeue();
                    int i = statePair.Item1;
                    int j = statePair.Item2;

                    foreach (var tjMove in deltaInvMinterm[j])
                    {
                        int t = tjMove.Item1;
                        int mintermMapping = tjMove.Item2;
                        --Counters[i, t][tjMove.Item2];
                        if (Counters[i, t][tjMove.Item2] == 0)
                        {
                            toProcess[i, t] = sfa.Algebra.MkOr(toProcess[i, t], numToMinterm[t][mintermMapping]);
                            if (!toProcessIsIn[i, t])
                            {
                                toProcessIsIn[i, t] = true;
                                toProcessQueue.Enqueue(Tuple.Create(i, t));
                            }
                        }
                    }
                }

                // now we process all pairs for which counters reached zero
                if (toProcessQueue.Count != 0)
                {
                    var sadf = toProcessQueue.Dequeue();
                    int i1 = sadf.Item1;
                    int t1 = sadf.Item2;
                    // and now we check if we want to remove something from simulation
                    foreach (var siMove in sfa.GetMovesTo(i1))
                    {
                        int s = siMove.SourceState;
                        if (simulation[s, t1])
                        {
                            var and = sfa.Algebra.MkAnd(toProcess[i1, t1], siMove.Label);
                            if (sfa.Algebra.IsSatisfiable(and))
                            {
                                simulation[s, t1] = false;
                                processedPairs.Enqueue(Tuple.Create(s, t1));
                            }
                        }
                    }
                    toProcess[i1, t1] = sfa.Algebra.False;
                    toProcessIsIn[i1, t1] = false;
                }
                else // if no counter reached zero, we can end
                {
                    end = true;
                }
            }
            return simulation;
        }

        /// <summary>
        /// Returns simulation preorder of sfa as array of statesXstates using global SFA alg.
        /// </summary>
        /// <param name="debug"> if true, prints debug message </param>
        private static bool[,] getGlobalSimulation<T>(this Automaton<T> sfa, bool debug = false)
        {

            // get three arrays from all transitions
            // statesFrom - i-th transition has source state statesFrom[i]
            // statesTo - i-th transition has target state statesTo[i]
            // predicates - i-th transition has label predicates[i]
            var moves = (new List<Move<T>>(sfa.GetMoves())).ToArray();
            var statesFrom = Array.ConvertAll(moves, move => { return move.SourceState; });
            var predicates = Array.ConvertAll(moves, move => { return move.Label; });
            var statesTo = Array.ConvertAll(moves, move => { return move.TargetState; });

            // get global minterms
            var minterms = new List<Tuple<bool[], T>>(sfa.Algebra.GenerateMinterms(predicates));
            string debugMessage = minterms.Count + ", ";

            // map numbers to minterms (alphabet of FA on which we compute simulation)
            var numToMinterm = new T[minterms.Count];

            // N_psi(_,t) = n
            // smallCounters[t, number that maps to psi] = n
            // for inital N_psi(i,t) all those counter are same for all i
            var smallCounters = new int[sfa.MaxState + 1, minterms.Count];
            // N_psi(i,t) = n
            // Counters[i,t][number that maps to psi] = n
            var Counters = new int[sfa.MaxState + 1, sfa.MaxState + 1, minterms.Count];

            int debug_numOfMoves = 0;
            int debug_numOfInnerLoop = 0;


            // reverse delta of global minterm normalized sfa (so also reverse Delta of FA)
            //         to           symbol, list of from
            Dictionary<int, Dictionary<int, List<int>>> deltaInv = new Dictionary<int, Dictionary<int, List<int>>>();
            foreach (var state in sfa.GetStates())
            {
                deltaInv[state] = new Dictionary<int, List<int>>();
            }

            //get deltaInv
            int mapSymbol = 0; // minterm is mapped to this, so it is symbol of FA
            foreach (var minterm in minterms)
            {
                numToMinterm[mapSymbol] = minterm.Item2;

                foreach (var state in sfa.GetStates())
                {
                    deltaInv[state][mapSymbol] = new List<int>();
                }

                for (int j = 0; j < minterm.Item1.Length; ++j)
                {
                    // get all transitions whose label created this minterm
                    if (minterm.Item1[j])
                    {
                        deltaInv[statesTo[j]][mapSymbol].Add(statesFrom[j]);
                        ++smallCounters[statesFrom[j], mapSymbol];


                        ++debug_numOfMoves;
                    }
                }

                ++mapSymbol; // at the end, this will be max symbol+1
            }

            debugMessage += debug_numOfMoves + ", ";

            // initialize counters
            foreach (var state in sfa.GetStates())
            {
                foreach (var state2 in sfa.GetStates())
                {
                    for (int j = 0; j < mapSymbol; ++j)
                    {
                        Counters[state, state2, j] = smallCounters[state, j];
                    }
                }
            }

            // simulation preorder
            bool[,] simulation = new bool[sfa.MaxState + 1, sfa.MaxState + 1];
            // queue of pairs of states waiting to get processed
            Queue<Tuple<int, int>> processedPairs = new Queue<Tuple<int, int>>();
            // initialize simulation as (QxQ)-(FxQ)
            foreach (var i in sfa.GetStates())
            {
                foreach (var j in sfa.GetStates())
                {
                    if (sfa.GetFinalStates().Contains(i) && !sfa.GetFinalStates().Contains(j))
                    {
                        simulation[i, j] = false;
                        processedPairs.Enqueue(Tuple.Create(i, j));
                    }
                    else
                    {
                        simulation[i, j] = true;
                    }
                }
            }

            // classic simulation preorder algorithm for FAs
            while (processedPairs.Count != 0)
            {
                var statePair = processedPairs.Dequeue();
                int i = statePair.Item1;
                int j = statePair.Item2;

                foreach (KeyValuePair<int, List<int>> entry in deltaInv[j])
                {
                    int symbol = entry.Key;
                    foreach (int t in entry.Value)
                    {
                        --Counters[t, i, symbol];
                        if (Counters[t, i, symbol] == 0)
                        {
                            foreach (var s in deltaInv[i][symbol])
                            {
                                ++debug_numOfInnerLoop;
                                if (simulation[s, t])
                                {
                                    simulation[s, t] = false;
                                    processedPairs.Enqueue(new Tuple<int, int>(s, t));
                                }
                            }
                        }
                    }
                }
            }

            if (debug)
                Console.WriteLine(debugMessage + debug_numOfInnerLoop);

            return simulation;
        }

        /// <summary>
        /// Returns simulation preorder of sfa as array of statesXstates using algorithm without mintermization or counters
        /// </summary>
        private static bool[,] getSimulationNoCount<T>(this Automaton<T> sfa)
        {
            // simulation preorder
            var simulation = new bool[sfa.MaxState + 1, sfa.MaxState + 1];
            // set of all states that stopped simulating i and we want to process them (similar to HHK with Remove sets, not INY with pairs)
            Dictionary<int, HashSet<int>> nonSimulation = new Dictionary<int, HashSet<int>>();
            // states whose nonSimulation is non-empty
            Queue<int> processedStates = new Queue<int>(sfa.GetFinalStates());

            /*
            // experiment with non-total automaton where we need to initialize simulation differently, it was slower
            var Gamma = new Dictionary<int, T>();
            var notGamma = new Dictionary<int, T>();
            foreach (var state in sfa.GetStates())
            {
                var movesFromState = new List<Move<T>>(sfa.GetMovesFrom(state));
                var predAndStates = movesFromState.ToArray();
                var predicates = Array.ConvertAll(predAndStates, move => { return move.Label; });

                T ors = sfa.Algebra.MkOr(predicates);
                Gamma[state] = ors;
                notGamma[state] = sfa.Algebra.MkNot(ors);
            }
            */

            foreach (var i in sfa.GetStates())
            {
                nonSimulation[i] = new HashSet<int>();
                foreach (var j in sfa.GetStates())
                {
                    if (sfa.GetFinalStates().Contains(i) && !sfa.GetFinalStates().Contains(j))// ||
                                                                                              //(sfa.Algebra.IsSatisfiable(sfa.Algebra.MkAnd(Gamma[i], notGamma[j]))))
                    {
                        nonSimulation[i].Add(j);
                        simulation[i, j] = false;
                    }
                    else
                    {
                        simulation[i, j] = true;
                    }
                }
                //if (nonSimulation[i].Count != 0)
                //    processedStates.Enqueue(i);
            }


            while (processedStates.Count != 0)
            {
                var i = processedStates.Dequeue();
                // in [[ Theta[t] ]] are saved all symbols a that t does not go above i via a (using Theta was slower)
                // Dictionary<int, T> Theta = new Dictionary<int, T>();

                // if we do not use Theta, we take all states that go above i, but they can potentionally stop
                // because they go to j (where j stopped simulating i and we are processing it)
                HashSet<int> statesGoingAboveChanged = new HashSet<int>();

                foreach (var j in nonSimulation[i])
                {
                    foreach (var tjMove in sfa.GetMovesTo(j))
                    {
                        statesGoingAboveChanged.Add(tjMove.SourceState);
                        /*int t = tjMove.SourceState;
                        T thetaT;
                        if (Theta.TryGetValue(t, out thetaT))
                        {
                            Theta[t] = sfa.Algebra.MkOr(thetaT, tjMove.Label);
                        }
                        else
                        {
                            Theta[t] = tjMove.Label;
                        }*/
                    }
                }
                nonSimulation[i].Clear();

                //foreach (var t in Theta.Keys)
                foreach (var t in statesGoingAboveChanged)
                {
                    //T psi = Theta[t];
                    T psi = sfa.Algebra.False;
                    foreach (var tMove in sfa.GetMovesFrom(t))
                    {
                        if (simulation[i, tMove.TargetState])
                        {
                            //psi = sfa.Algebra.MkDiff(psi, tMove.Label); // removing all symbols that t goes above i with
                            psi = sfa.Algebra.MkOr(psi, tMove.Label); // we get all symbols that t goes above i with
                        }
                    }

                    psi = sfa.Algebra.MkNot(psi); // remove this if we use Theta

                    // find pairs that we want to remove from simulation
                    if (sfa.Algebra.IsSatisfiable(psi))
                    {
                        foreach (var siMove in sfa.GetMovesTo(i))
                        {
                            int s = siMove.SourceState;
                            if (simulation[s, t])
                            {
                                if (sfa.Algebra.IsSatisfiable(sfa.Algebra.MkAnd(psi, siMove.Label)))
                                {
                                    if (nonSimulation[s].Count == 0)
                                        processedStates.Enqueue(s);
                                    simulation[s, t] = false;
                                    nonSimulation[s].Add(t);
                                }
                            }
                        }
                    }
                }
            }
            return simulation;
        }

        /// <summary>
        /// Returns simulation preorder of sfa as array of statesXstates using algorithm without mintermization or counters WITHOUT any optimizations (very slow)
        /// </summary>
        private static bool[,] getSimulationNoCountNoOpt<T>(this Automaton<T> sfa)
        {
            var simulation = new bool[sfa.MaxState + 1, sfa.MaxState + 1];
            Queue<Tuple<int, int>> processedPairs = new Queue<Tuple<int, int>>();
            foreach (var i in sfa.GetStates())
            {
                foreach (var j in sfa.GetStates())
                {
                    if (sfa.GetFinalStates().Contains(i) && !sfa.GetFinalStates().Contains(j))
                    {
                        processedPairs.Enqueue(Tuple.Create(i, j));
                        simulation[i, j] = false;
                    }
                    else
                    {
                        simulation[i, j] = true;
                    }
                }
            }


            while (processedPairs.Count != 0)
            {
                var statePair = processedPairs.Dequeue();
                int i = statePair.Item1;
                int j = statePair.Item2;

                foreach (var tjMove in sfa.GetMovesTo(j))
                {
                    int t = tjMove.SourceState;
                    T psi = tjMove.Label;

                    foreach (var tkMove in sfa.GetMovesFrom(t))
                    {
                        int k = tkMove.TargetState;
                        if (simulation[i, k])
                        {
                            psi = sfa.Algebra.MkDiff(psi, tkMove.Label);
                        }
                    }

                    if (sfa.Algebra.IsSatisfiable(psi))
                    {
                        foreach (var siMove in sfa.GetMovesTo(i))
                        {
                            int s = siMove.SourceState;
                            if (simulation[s, t])
                            {
                                if (sfa.Algebra.IsSatisfiable(sfa.Algebra.MkAnd(psi, siMove.Label)))
                                {
                                    simulation[s, t] = false;
                                    processedPairs.Enqueue(Tuple.Create(s, t));
                                }
                            }
                        }
                    }
                }
            }
            return simulation;
        }


        /// <summary>
        /// Returns automaton without dead states, this is copy paste of function EliminateDeatStates()
        /// but this creates new automaton, that one used equailty of labels to remove them and was very slow
        /// </summary>
        public static Automaton<T> EliminateDeadStatesBetter<T>(this Automaton<T> sfa)
        {
            //backwards reachability, collect states that reach some final state
            Stack<int> stack = new Stack<int>(sfa.GetFinalStates());
            HashSet<int> backReachableFromSomeFinal = new HashSet<int>(sfa.GetFinalStates());
            while (stack.Count > 0)
            {
                var backReachState = stack.Pop();
                foreach (var t in sfa.GetMovesTo(backReachState))
                {
                    var source = t.SourceState;
                    if (backReachableFromSomeFinal.Add(source)) //if returns false then already added
                        stack.Push(source);
                }
            }

            //eliminate all dead states, i.e. states not in backReachableFromSomeFinal
            var newMoves = new List<Move<T>>();
            foreach (var move in sfa.GetMoves())
            {
                if (backReachableFromSomeFinal.Contains(move.SourceState) && backReachableFromSomeFinal.Contains(move.TargetState))
                {
                    newMoves.Add(move);
                }
            }

            return Automaton<T>.Create(sfa.Algebra, sfa.InitialState, sfa.GetFinalStates(), newMoves);
        }

        /// <summary>
        /// Returns automaton with only one final state
        /// </summary>
        public static Automaton<T> MakeOnlyOneStateFinal<T>(this Automaton<T> sfa)
        {
            if (!sfa.HasMoreThanOneFinalState)
                return sfa;

            var newMoves = new List<Move<T>>();
            var newFinalState = sfa.MaxState + 1;
            foreach (var move in sfa.GetMoves())
            {
                newMoves.Add(move);
                if (sfa.IsFinalState(move.TargetState))
                {
                    // 'epsilon closure' of states going to some final state
                    newMoves.Add(new Move<T>(move.SourceState, newFinalState, move.Label));
                }
            }

            return Automaton<T>.Create(sfa.Algebra, sfa.InitialState, new HashSet<int> { newFinalState }, newMoves);
        }

        /// <summary>
        /// Returns simulation preorder
        /// </summary>
        /// <param name="which"> chooses algorithm by which simulation is computed </param>
        public static bool[,] getSimulation<T>(this Automaton<T> sfa, int which = 0)
        {
            var newsfa = sfa;
            switch (which)
            {
                case 0:
                    return newsfa.getLocalSimulation();
                case 1:
                    return newsfa.getLocalSimulationOptimizied();
                case 2:
                    return newsfa.getSimulationNoCountNoOpt();
                case 3:
                    return newsfa.getSimulationNoCount();
                case 4:
                    return newsfa.getGlobalSimulation();
                default:
                    throw new AutomataException("which is different than 0,1,2,3,4 ");
            }
        }

        /// <summary>
        /// Create smaller automaton by merging equal states, this is partly copy-paste of function JoinStates(), but this one is public
        /// </summary>
        /// <param name="GetRepresentative"> returns the state ID of representative of the equivalence class </param>
        /// <param name="MkDisjunction"> disjunctions of labels </param>
        /// <param name="initalStates"> used for reversing when we need set of initial state and not only one, the new initial states are also saved to it </param>
        public static Automaton<T> JoinStatesPublic<T>(this Automaton<T> sfa, Func<int, int> GetRepresentative, Func<IEnumerable<T>, T> MkDisjunction, ref IEnumerable<int> initalStates)
        {
            var condMap = new Dictionary<Tuple<int, int>, HashSet<T>>();
            foreach (var move in sfa.GetMoves())
            {
                int s = GetRepresentative(move.SourceState);
                int t = GetRepresentative(move.TargetState);
                var st = new Tuple<int, int>(s, t);
                HashSet<T> condSet;
                if (!condMap.TryGetValue(st, out condSet))
                {
                    condSet = new HashSet<T>();
                    condSet.Add(move.Label);
                    condMap[st] = condSet;
                }
                else
                    condSet.Add(move.Label);
            }
            int newInitState = GetRepresentative(sfa.InitialState);
            var newMoves = new List<Move<T>>();
            var newFinals = new HashSet<int>();
            foreach (var entry in condMap)
                newMoves.Add(Move<T>.Create(entry.Key.Item1, entry.Key.Item2, MkDisjunction(entry.Value)));
            foreach (var f in sfa.GetFinalStates())
                newFinals.Add(GetRepresentative(f));

            // get new initial states
            HashSet<int> inits = new HashSet<int>();
            foreach (var state in initalStates)
            {
                inits.Add(GetRepresentative(state));
            }
            initalStates = inits;


            return Automaton<T>.Create(sfa.Algebra, newInitState, newFinals, newMoves, false, false, sfa.isDeterministic);
        }

        /// <summary>
        /// Returns smaller automaton using simulation-based reduction.
        /// </summary>
        /// <param name="which"> which algorithm to use for computing simulation, 0 = local mintermization, 1 = local mint. optimizied, 2 = global mint., 3 = no count, no mint. opt., 4 = no count, no mint. </param>
        public static Automaton<T> NonDetStateRedBySim<T>(this Automaton<T> sfa, int which = 0)
        {
            IEnumerable<int> throwAway = new HashSet<int>();
            return sfa.NonDetStateRedBySim(ref throwAway, which);
        }

        /// <summary>
        /// Returns smaller automaton using simulation-based reduction.
        /// </summary>
        /// <param name="initalStates"> used for reversing when we need set of initial state and not only one, the new initial states are also saved to it </param>
        /// <param name="which"> which algorithm to use for computing simulation, 0 = local mintermization, 1 = local mint. optimizied, 2 = global mint., 3 = no count, no mint. opt., 4 = no count, no mint. </param>
        public static Automaton<T> NonDetStateRedBySim<T>(this Automaton<T> sfa, ref IEnumerable<int> initalStates, int which = 0)
        {
            bool[,] simulation = sfa.getSimulation(which);

            // get equivalence classes
            HashSet<int> usedStates = new HashSet<int>();
            var Blocks = new Dictionary<int, Block>();
            foreach (var a in sfa.GetStates())
            {
                if (usedStates.Contains(a))
                    continue;

                Block equivalent = new Block();

                foreach (var b in sfa.GetStates())
                {
                    if (simulation[a, b] && simulation[b, a])
                    {
                        equivalent.Add(b);
                        usedStates.Add(b);
                    }
                }

                foreach (var state in equivalent)
                {
                    Blocks[state] = equivalent;
                }
            }

            // use equivalence for reduction
            Func<int, int> GetRepresentative = (q => Blocks[q].GetRepresentative());
            var min = sfa.JoinStatesPublic(GetRepresentative, sfa.Algebra.MkOr, ref initalStates);
            min.EliminateDeadStatesBetter();

            // use transition removal and then removing of unreachable states for reduction
            List<Move<T>> moves = new List<Move<T>>();
            foreach (var state in min.GetStates())
            {
                // gets transitions so we can change them
                List<MutableMove<T>> movesNew = new List<Move<T>>(min.GetMovesFrom(state)).ConvertAll(move => new MutableMove<T>(move.SourceState, move.TargetState, move.Label));
                // for each transition state----psi--->upState, if there is transition state----phi----->downState where upState simulates downState,
                // we can replace transition to downState with state----phi and not(psi)--->downState (or remove this transition if phi and not(psi) is not sat)
                foreach (var move in min.GetMovesFrom(state))
                {
                    var upState = move.TargetState;
                    foreach (var updatingMove in movesNew)
                    {
                        var downState = updatingMove.TargetState;
                        if (downState != upState && simulation[downState, upState])
                        {
                            updatingMove.Label = sfa.Algebra.MkDiff(updatingMove.Label, move.Label);
                        }
                    }
                }
                movesNew.RemoveAll(item => !sfa.Algebra.IsSatisfiable(item.Label));
                moves.AddRange(movesNew.ConvertAll(move => new Move<T>(move.SourceState, move.TargetState, move.Label)));
            }
            return Automaton<T>.Create(sfa.Algebra, min.InitialState, min.GetFinalStates(), moves).EliminateDeadStatesBetter();
        }

        /* work in progress algorithm for computing simulation starting with equivalence classes and then refining them
        private static bool[,] getSimulationBlock<T>(this Automaton<T> sfa)
        {
            var finalBlock = new Block(sfa.GetFinalStates());
            var nonfinalBlock = new Block(sfa.GetNonFinalStates());
            var stateBlocks = new Dictionary<int, Block>(); // state in Block
            foreach (var q in sfa.GetFinalStates()) stateBlocks[q] = finalBlock;
            foreach (var q in sfa.GetNonFinalStates()) stateBlocks[q] = nonfinalBlock;

            var workSet = new BlockStack();

            var Blocks = new List<Block> { nonfinalBlock, finalBlock };
            var BlocksMapping = new Dictionary<Block, int>(); // mapping of blocks to int
            BlocksMapping[nonfinalBlock] = 0;
            BlocksMapping[finalBlock] = 1;

            var simulation = new List<List<bool>>(sfa.MaxState + 1);
            simulation[0][0] = true;
            simulation[0][1] = true;
            simulation[1][0] = false;
            workSet.Push(finalBlock);
            simulation[1][1] = true;



            Dictionary<int, HashSet<int>> nonSimulation = new Dictionary<int, HashSet<int>>();


            
            //Stores what block this was the split of
            var ComplementBlock = new Dictionary<Block, Block>();
            var BlockDelta = new Dictionary<int, Dictionary<Block, T>>();     //BlockDelta[q][B]= all symbols that go from q to B     
            var BlockPre = new Dictionary<Block, Dictionary<Block, T>>();     //BlockPre[A][B] = all symbols that go from any state q in B to A                  
            
            //Computes and memoizes BlockPre
            Func<Block, Dictionary<int, T>> GetBlockPre = (B) =>
            {
                if (BlockPre.ContainsKey(B))
                    return BlockPre[B];
                else
                {
                    var dicB = new Dictionary<int, T>();
                    foreach (var q in B)
                    {
                        foreach (var move in sfa.GetMovesTo(q)) //moves leading to q
                            if (stateBlocks[move.SourceState].Count > 1) //singleton blocks cannot be further split !!!!!!!!!!!!!!
                            {
                                if (dicB.ContainsKey(move.SourceState))
                                    dicB[move.SourceState] = sfa.Algebra.MkOr(dicB[move.SourceState], move.Label);
                                else
                                    dicB[move.SourceState] = move.Label;


                            }
                    }
                    BlockPre[B] = dicB;
                    return dicB;
                }
            };

            Func<Block, IEnumerable<Block>> sim = (B) =>
            {
                int b = BlocksMapping[B];
                var listOfBlocks = new List<Block>();
                for (int i = 0; i < simulation[b].Count; ++i)
                {
                    if (simulation[b][i])
                    {
                        listOfBlocks.Add(Blocks[i]);
                    }
                }

                return listOfBlocks;
            };

            while (!workSet.IsEmpty)
            {
                var I = workSet.Pop();
                var simI = sim(I);
                
                foreach (var moveToI in BlockPre[I])
                {
                    var S = moveToI.Key;
                    var psiSI = moveToI.Value;

                    foreach(Block R in sim(S))
                    {
                        var splitter = new Block();
                        foreach (var r in R)
                        {
                            T Gamma = sfa.Algebra.False;
                            foreach (Block J in simI)
                            {
                                T psirJ;
                                if (BlockDelta[r].TryGetValue(J, out psirJ))
                                    Gamma = sfa.Algebra.MkOr(Gamma, psirJ);
                            }
                            Gamma = sfa.Algebra.MkNot(Gamma);
                            if (sfa.Algebra.IsSatisfiable(sfa.Algebra.MkAnd(psiSI, Gamma)))
                                splitter.Add(r);
                        }
                        if (splitter == R)
                        {

                        }
                        else
                            Split(R, splitter);
                    }
                }
                
            return simulation;
        }*/
    }

    /// <summary>
    /// Move that is mutable, so it can be changed
    /// </summary>
    /// <typeparam name="L"> the type of the labels on moves </typeparam>
    internal class MutableMove<L>
    {
        /// <summary>
        /// Source state of the move
        /// </summary>
        public int SourceState;
        /// <summary>
        /// Target state of the move
        /// </summary>
        public int TargetState;
        /// <summary>
        /// Label of the move
        /// </summary>
        public L Label;

        /// <summary>
        /// Transition of an automaton.
        /// </summary>
        /// <param name="sourceState">source state of the transition</param>
        /// <param name="targetState">target state of the transition</param>
        /// <param name="lab">label of the transition</param>
        public MutableMove(int sourceState, int targetState, L lab)
        {
            this.SourceState = sourceState;
            this.TargetState = targetState;
            this.Label = lab;
        }
    }

}
