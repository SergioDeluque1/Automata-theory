## DFA Minimization (Kozen 1997, Lecture 14)

- **Full name**: Felipe Giraldo Neira
- **Class number**: 5730
- **Python version**: Python 3.13.2
- **Operating system**: Windows 11
- **Tools used**: PowerShell, VS Code

### Run

```powershell
# Opción 1
python main.py < input.txt

# Opción 2
Get-Content input.txt | python main.py
```

Input format:

- First line: integer `c > 0` (number of test cases)
- For each test case:
  - One line: integer `n > 0` (number of states; states are `0..n-1`, initial state is `0`)
  - One line: alphabet symbols separated by spaces
  - One line: accepting/final states separated by spaces (may be empty)
  - `n` lines follow: each line lists `|Σ|` transition targets for that state, in the same order as the alphabet

Output:

- For each test case, one line listing all equivalent state pairs `(i, j)` in lexicographical order, separated by spaces. If no pairs, print an empty line.

### Algorithm (Partition Refinement)

This implementation follows the partition refinement approach described in Kozen (1997), Lecture 14 (akin to Hopcroft-style DFA minimization):

1. Initialize a partition of the state set `Q` into two blocks: `F` (final) and `Q \ F` (non-final).
2. Repeatedly refine the partition: within each block, split states by their transition behavior, i.e., group together states whose transitions, for each symbol in the alphabet, lead to states in the same partition blocks.
3. Continue until no further refinement is possible (a fixed point is reached).
4. States that remain in the same block of the final partition are equivalent; all `(i, j)` within each block are collected and printed in lexicographical order.

Assumptions:

- DFA is deterministic, total, and has no inaccessible states.
- Initial state is `0`.