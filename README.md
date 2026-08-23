# Automata Theory

A Python-based exploration of **Automata Theory**, focused on simulating and implementing fundamental concepts from formal languages, finite automata, grammars, and computational models.

The goal of this project is to mimic the behaviour of formal computational systems through Python and understand how theoretical concepts can be translated into practical algorithms.

## Projects

### 1. CFG Left Recursion Eliminator

An implementation for eliminating **left recursion** from Context-Free Grammars (CFGs).

Left recursion occurs when a grammar contains productions where a non-terminal can derive itself as the leftmost symbol. This can cause infinite recursion in top-down parsing algorithms.

This project:

- Detects direct left recursion.
- Eliminates direct left-recursive productions.
- Produces an equivalent grammar without direct left recursion.
- Demonstrates how grammar transformations can be implemented programmatically.

### 2. DFA State Equivalence

An implementation for determining whether two states in a **Deterministic Finite Automaton (DFA)** are equivalent.

Two states are equivalent if no input string can distinguish their behaviour. In other words, starting from either state produces the same acceptance result for every possible input.

This project explores:

- Accepting and non-accepting states.
- State distinguishability.
- Equivalent states.
- Equivalence classes.
- Comparing DFA states algorithmically.

### 3. DFA Minimisation

An implementation of **DFA minimisation**, reducing a DFA to an equivalent automaton with the smallest possible number of states.

The minimisation process includes:

1. Removing unreachable states.
2. Identifying distinguishable states.
3. Finding equivalent states.
4. Grouping equivalent states.
5. Constructing the minimal DFA.

The resulting DFA accepts the same language as the original DFA while eliminating redundant states.

### 4. DFA Parser

A parser based on a **Deterministic Finite Automaton**.

The parser processes an input string symbol by symbol and follows the corresponding DFA transitions until the entire input has been consumed.

The general process is:

    Input
      │
      ▼
    Initial State
      │
      ├── symbol ──► transition
      │
      ├── symbol ──► transition
      │
      ▼
    Current State
      │
      ├── Accept
      └── Reject

This demonstrates how a mathematical DFA can be directly represented and executed as a Python program.

## Project Structure

    automata-theory/
    │
    ├── cfg_left_recursion/
    │   └── ...
    │
    ├── dfa_state_equivalence/
    │   └── ...
    │
    ├── dfa_minimisation/
    │   └── ...
    │
    ├── dfa_parser/
    │   └── ...
    │
    ├── examples/
    │   └── ...
    │
    ├── tests/
    │   └── ...
    │
    └── README.md

## Goals

The main goals of this project are to:

- Understand the theoretical foundations of Automata Theory.
- Translate mathematical definitions into executable Python algorithms.
- Explore transformations of Context-Free Grammars.
- Understand DFA state equivalence.
- Implement DFA minimisation.
- Simulate DFA-based parsing.
- Gain practical experience with computational models.

## Concepts Covered

- Formal Languages
- Finite Automata
- Deterministic Finite Automata (DFA)
- Context-Free Grammars (CFG)
- Left Recursion
- Grammar Transformation
- State Equivalence
- State Distinguishability
- DFA Minimisation
- Parsing
- Computational Models

## Technologies

- **Python 3**
- Standard Python libraries

## Running the Project

Clone the repository:

    git clone <repository-url>
    cd automata-theory

Run an individual project with Python:

    python <project-file>.py

Examples and test cases can be found inside the corresponding project directories.

## Educational Purpose

This project is primarily intended as an educational exploration of **Automata Theory**.

Each implementation connects a theoretical concept with a practical Python program, making it possible to experiment with grammars and automata and observe their behaviour directly.

## Author

Developed as a Python implementation and exploration of concepts from **Automata Theory**.
