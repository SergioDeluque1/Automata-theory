def eliminate_left_recursion(num_cases, cases):
    results = []
    
    for case in cases:
        num_nonterminals = case[0]
        productions = case[1]
        
        # Create a dictionary of nonterminal -> list of productions
        grammar = {}
        for prod in productions:
            nonterminal, rules = prod.split(" -> ")
            rules = rules.split()
            grammar[nonterminal] = rules
        
        # Store the transformed productions
        transformed_grammar = []
        
        # Process each nonterminal to eliminate left recursion
        for A in grammar:
            recursive_rules = []
            non_recursive_rules = []
            
            for rule in grammar[A]:
                if rule.startswith(A):
                    # left-recursive rule
                    recursive_rules.append(rule[1:])  # remove the A
                else:
                    # Non-recursive rule
                    non_recursive_rules.append(rule)
            
            # Left recursion transformation
            if recursive_rules:
                new_nonterminal = A + "'"
                
                # A -> BA'
                for rule in non_recursive_rules:
                    transformed_grammar.append(f"{A} -> {rule} {new_nonterminal}")
                
                # A' -> aA' | e
                for rule in recursive_rules:
                    transformed_grammar.append(f"{new_nonterminal} -> {rule} {new_nonterminal}")
                transformed_grammar.append(f"{new_nonterminal} -> e")
            else:
                # No left recursion, just copy the non-recursive rules
                for rule in non_recursive_rules:
                    transformed_grammar.append(f"{A} -> {rule}")
        
        # Store the result for test
        results.append(transformed_grammar)
    
    return results

# Read input
def read_input():
    n = int(input())  # Number of test cases
    cases = []
    
    for _ in range(n):
        k = int(input())  # Number of NTs
        productions = []
        
        for _ in range(k):
            productions.append(input().strip())
        
        cases.append((k, productions))
    
    return n, cases

# Output result function
def output_result(results):
    for result in results:
        for line in result:
            print(line)
        print()

# Main execution
if __name__ == "__main__":
    num_cases, cases = read_input()
    results = eliminate_left_recursion(num_cases, cases)
    output_result(results)
