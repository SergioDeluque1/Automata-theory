import sys
from collections import defaultdict
from typing import List, Set, Dict, Tuple


def read_int(line: str) -> int:
    return int(line.strip())


def parse_alphabet(line: str) -> List[str]:
    line = line.strip()
    if not line:
        return []
    return line.split()


def parse_states(line: str) -> Set[int]:
    line = line.strip()
    if not line:
        return set()
    return {int(x) for x in line.split()}


def refine_partitions(
    num_states: int,
    alphabet_size: int,
    transitions: List[List[int]],
    final_states: Set[int],
) -> List[Set[int]]:
    # Initial partition: finals vs non-finals
    finals_block = set(final_states)
    nonfinals_block = set(range(num_states)) - finals_block
    partitions: List[Set[int]] = []
    if finals_block:
        partitions.append(finals_block)
    if nonfinals_block:
        partitions.append(nonfinals_block)

    # Map state -> partition index
    state_to_block: List[int] = [-1] * num_states
    for idx, block in enumerate(partitions):
        for s in block:
            state_to_block[s] = idx

    # Iteratively split blocks by transition signatures to block IDs
    changed = True
    while changed:
        changed = False
        new_partitions: List[Set[int]] = []
        for block in partitions:
            # Group states in this block by signature
            signature_to_states: Dict[Tuple[int, ...], Set[int]] = defaultdict(set)
            for state in block:
                signature = tuple(
                    state_to_block[transitions[state][a_idx]] if alphabet_size > 0 else ()
                    for a_idx in range(alphabet_size)
                )
                signature_to_states[signature].add(state)

            if len(signature_to_states) == 1:
                # No split
                new_partitions.append(block)
            else:
                # Split into multiple blocks
                changed = True
                # Ensure deterministic order: sort each new block and append
                split_blocks = [set(sorted(group)) for group in signature_to_states.values()]
                # Stable order by smallest element in each block
                split_blocks.sort(key=lambda b: min(b))
                for nb in split_blocks:
                    new_partitions.append(nb)
        # Rebuild state_to_block if changed
        if changed:
            partitions = new_partitions
            for idx, block in enumerate(partitions):
                for s in block:
                    state_to_block[s] = idx

    return partitions


def equivalent_pairs_from_partitions(partitions: List[Set[int]]) -> List[Tuple[int, int]]:
    pairs: List[Tuple[int, int]] = []
    for block in partitions:
        if len(block) < 2:
            continue
        states_sorted = sorted(block)
        for i in range(len(states_sorted)):
            for j in range(i + 1, len(states_sorted)):
                pairs.append((states_sorted[i], states_sorted[j]))
    # Lexicographical order
    pairs.sort()
    return pairs


def process_case(n: int, alphabet: List[str], finals: Set[int], transitions: List[List[int]]) -> str:
    partitions = refine_partitions(n, len(alphabet), transitions, finals)
    pairs = equivalent_pairs_from_partitions(partitions)
    if not pairs:
        return ""
    return " ".join(f"({i}, {j})" for i, j in pairs)


def main() -> None:
    data = sys.stdin.read().splitlines()
    it = iter(data)

    def next_nonblank(it_lines):
        for raw in it_lines:
            if raw.strip() != "":
                return raw
        raise StopIteration

    try:
        t_line = next_nonblank(it)
    except StopIteration:
        return
    c = read_int(t_line)

    outputs: List[str] = []
    for case_idx in range(c):
        n = read_int(next_nonblank(it))
        alphabet = parse_alphabet(next_nonblank(it))
        finals = parse_states(next_nonblank(it))

        transitions: List[List[int]] = []
        for state in range(n):
            line = next_nonblank(it).strip()
            nums = [int(x) for x in line.split()] if line else []
            if len(nums) == len(alphabet):
                row = nums
            elif len(nums) == len(alphabet) + 1:
                # Accept rows that start with the state index: [state, t1, t2, ...]
                if nums[0] != state:
                    raise ValueError(
                        f"Row header/state mismatch at case {case_idx + 1}, state {state}: "
                        f"found leading '{nums[0]}'. Row: '{line}'"
                    )
                row = nums[1:]
            else:
                raise ValueError(
                    f"Transition row length mismatch at case {case_idx + 1}, state {state}: "
                    f"expected {len(alphabet)} values (|Σ|) or {len(alphabet)+1} including state id, "
                    f"got {len(nums)}. Row: '{line}'"
                )
            transitions.append(row)

        outputs.append(process_case(n, alphabet, finals, transitions))

    # Print exactly one line per test case
    for out in outputs:
        print(out)


if __name__ == "__main__":
    main()


