using Microsoft.Automata.Extensions;

namespace Microsoft.Automata
{
    public static class AutomatonSimulationExtensions
    {
        public enum Reductions
        {
            DeterminizeAndMinimize,
            
            ReduceByLocalSimulation,
            ReduceByLocalSimulationOptimizied,
            ReduceBySimulationNoCountNoOpt,
            ReduceBySimulationNoCount,
            ReduceByGlobalSimulation,
            
            ReduceByBisimulation
        }

        /// <summary>
        /// Reduction by selected 
        /// </summary>
        /// <param name="which">how to reduce - enum</param>
        /// <returns></returns>
        public static Automaton<T> ReduceSizeBy<T>(this Automaton<T> sfa, Reductions which)
        {
            if (sfa.IsEmpty)
                return sfa;

            if (sfa.IsEpsilon)
                return sfa;

            bool useSimulation = false;
            int simulationIndex = 0;
            switch (which)
            {
                case Reductions.DeterminizeAndMinimize:
                    return sfa.Determinize().Minimize();

                case Reductions.ReduceByLocalSimulation:
                    useSimulation = true;
                    simulationIndex = 0;
                    break;
                case Reductions.ReduceByLocalSimulationOptimizied:
                    useSimulation = true;
                    simulationIndex = 1;
                    break;
                case Reductions.ReduceBySimulationNoCountNoOpt:
                    useSimulation = true;
                    simulationIndex = 2;
                    break;
                case Reductions.ReduceBySimulationNoCount:
                    useSimulation = true;
                    simulationIndex = 3;
                    break;
                case Reductions.ReduceByGlobalSimulation:
                    useSimulation = true;
                    simulationIndex = 4;
                    break;

                case Reductions.ReduceByBisimulation:
                    return sfa.ReduceSizeByBisimulation();
            }

            if (useSimulation)
                return sfa.RemoveEpsilons().EliminateDeadStatesBetter().RemoveEpsilonLoops()
                    .RemapStates().MakeTotal().NonDetStateRedBySim(simulationIndex).EliminateDeadStatesBetter();

            return sfa;
        }
    }
}
