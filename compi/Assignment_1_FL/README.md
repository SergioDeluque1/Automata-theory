## README_ASSIGNMENT_1

### General info
+ Sergio Delúquez for the formal language's course 0127
+ compiled on a browser using OnlinegGDB's website on a mac (MacOS Tahoe 
26.0.1), Python 3.x

### Run
python3 main.py < input.txt


This program processes input specified in the input.txt file. The input format 
is as follows:

+ Number of test cases: An integer greater than 0.
For each test case:
+ Number of states: An integer n where states are numbered from 0 to n-1 (the 
initial state is 0).
+ Alphabet symbols: A space-separated list of symbols.
+ Accepting (final) states: A space-separated list of final states.
+ Transitions: n lines follow, each containing the transition targets for that 
state, listed in the same order as the alphabet symbols.

### Output
For each test case, output one line listing all equivalent state pairs (i, j) in 
lexicographical order, separated by spaces. If no pairs exist, print an empty 
line.

### How it works

1. Initialize the partition: Divide the states into two blocks: F (final 
states) and Q \ F (non-final states).

2. Refine the partition: Iteratively refine
the partition by grouping states that have identical transitions for each symbol 
in the alphabet. States within each block will transition to the same blocks.

3. Repeat until fixed point: Continue refining until no further partitioning is 
possible (i.e., the partition reaches a fixed point).

4. Identify equivalent states: States that remain in the same block of the 
final partition are considered equivalent. For each block, collect all pairs (i, 
j) and print them in lexicographical order.
