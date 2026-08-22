from collections import defaultdict

def minimize_dfa(n, alphabet, final_states, transition_table):
    # Step 1: Create initial partitions: non-final vs final states
    partitions = [set(), set()]  # partitions[0] = non-final, partitions[1] = final
    for state in range(n):
        if state in final_states:
            partitions[1].add(state)
        else:
            partitions[0].add(state)

    # Function to get the next state for a given state and symbol index
    def get_next_state(state, symbol_index):
        return transition_table[state][symbol_index]

    # Step 2: Refine partitions iteratively
    alphabet_size = len(alphabet)
    partitions = [tuple(sorted(partition)) for partition in partitions]  # Ensure partitions are sorted tuples

    while True:
        refined_partitions = defaultdict(set)

        # Go through each partition and split based on transitions
        for partition in partitions:
            transition_map = defaultdict(list)

            # For each state in the partition, we create a transition signature
            for state in partition:
                transition_key = tuple(get_next_state(state, i) for i in range(alphabet_size))
                transition_map[transition_key].append(state)

            # Create new refined partitions based on transition signatures
            for key, states in transition_map.items():
                refined_partitions[tuple(sorted(states))].update(states)

        # If no change in partitions, we break out
        new_partitions = list(refined_partitions.values())
        if len(new_partitions) == len(partitions):
            break
        partitions = new_partitions

    # Step 3: Identify equivalent state pairs
    state_to_partition = {}
    for partition in partitions:
        for state in partition:
            state_to_partition[state] = tuple(sorted(partition))  # Map state to partition

    # Find all equivalent state pairs
    equivalent_pairs = []
    for state1 in range(n):
        for state2 in range(state1 + 1, n):
            if state_to_partition[state1] == state_to_partition[state2]:
                equivalent_pairs.append((state1, state2))

    return equivalent_pairs

def main():
    # Read the number of test cases
    c = int(input())
    
    for _ in range(c):
        # Read number of states
        n = int(input())
        
        # Read the alphabet
        alphabet = input().split()
        
        # Read the final states
        final_states = set(map(int, input().split()))
        
        # Read the transition table
        transition_table = []
        for _ in range(n):
            transition_table.append(list(map(int, input().split())))

        # Get the equivalent state pairs
        equivalent_pairs = minimize_dfa(n, alphabet, final_states, transition_table)

        # Sort the equivalent pairs in lexicographical order
        equivalent_pairs.sort()

        # Output the equivalent state pairs
        if equivalent_pairs:
            print(" ".join(f"({pair[0]}, {pair[1]})" for pair in equivalent_pairs))
        else:
            print()

if __name__ == "__main__":
    main()
