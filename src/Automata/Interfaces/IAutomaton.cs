﻿using System;
using System.Collections.Generic;

namespace Microsoft.Automata
{
    /// <summary>
    /// For accessing the key components of an automaton regardles of label tape
    /// </summary>
    public interface IAutomaton
    {
        //added, obviously
        Type LabelType { get; }

        //added, not present in IAutomaton<L>
        IEnumerable<int> GetFinalStates();

        //added, not present in IAutomaton<L>
        IReadOnlyDictionary<int, string> GetStateDescriptions();

        /// <summary>
        /// Enumerates all moves of the automaton.
        /// </summary>
        IEnumerable<IMove> GetMoves();

        /// <summary>
        /// Enumerates all states of the automaton.
        /// </summary>
        IEnumerable<int> GetStates();

        /// <summary>
        /// Provides a description of the state for visualization purposes.
        /// </summary>
        string DescribeState(int state);

        /// <summary>
        /// Provides a description of the label for visualization purposes.
        /// </summary>
        string DescribeLabel(object lab);

        /// <summary>
        /// Provides a description of the label for visualization purposes.
        /// </summary>
        string DescribeStartLabel();

        /// <summary>
        /// The initial state of the automaton.
        /// </summary>
        
        int InitialState { get; }
        /// <summary>
        /// Gets the algebra of the labels. Type IBooleanAlgebra<L>
        /// </summary>
        
        object Algebra { get; }
        /// <summary>
        /// Returns true iff the state is a final state.
        /// </summary>
        bool IsFinalState(int state);

        /// <summary>
        /// Enumerates all moves of the automaton from the given start state.
        /// </summary>
        IEnumerable<IMove> GetMovesFrom(int state);
    }

    /// <summary>
    /// For accessing the key components of an automaton.
    /// </summary>
    /// <typeparam name="L">type of labels in moves</typeparam>
    public interface IAutomaton<L> : IMinimalAutomaton<L>
    {
        /// <summary>
        /// Enumerates all moves of the automaton.
        /// </summary>
        IEnumerable<Move<L>> GetMoves();

        /// <summary>
        /// Enumerates all states of the automaton.
        /// </summary>
        IEnumerable<int> GetStates();

        /// <summary>
        /// Enumerates all final states of the automaton.
        /// </summary>
        IEnumerable<int> GetFinalStates();

        /// <summary>
        /// Provides a description of the state for visualization purposes.
        /// </summary>
        string DescribeState(int state);

        /// <summary>
        /// Provides a description of the label for visualization purposes.
        /// </summary>
        string DescribeLabel(L lab);

        /// <summary>
        /// Provides a description of the label for visualization purposes.
        /// </summary>
        string DescribeStartLabel();
    }

    /// <summary>
    /// A minimal incremental subset of IAutomaton<L> needed for certain operations
    /// </summary>
    /// <typeparam name="L"></typeparam>
    public interface IMinimalAutomaton<L>
    {
        /// <summary>
        /// The initial state of the automaton.
        /// </summary>
        int InitialState { get; }
        /// <summary>
        /// Gets the algebra of the labels.
        /// </summary>
        IBooleanAlgebra<L> Algebra { get; }
        /// <summary>
        /// Returns true iff the state is a final state.
        /// </summary>
        bool IsFinalState(int state);
        /// <summary>
        /// Enumerates all moves of the automaton from the given start state.
        /// </summary>
        IEnumerable<Move<L>> GetMovesFrom(int state);
    }
}
