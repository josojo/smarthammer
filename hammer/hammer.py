import sys
from pathlib import Path
from lean_server.server import LeanServer
from proof.proof import ProofSearchState
from api.claude.client import Client
from proof.proof import Hypothesis


def iterate_until_valid_proof(proof_state: ProofSearchState, hyptotheses_number, client: Client, lean_client: LeanServer, max_iteration=1, verbose=False):
    cnt = 0
    starting_code = ""
    while (cnt < max_iteration):
        proof_candidate = proof_state.generate_proof_candidate_for_hypotheses(
            client, 
            hyptotheses_number,
            starting_code,
            verbose
        )
        if proof_candidate:
            code = proof_state.hypothesis_as_code(hyptotheses_number) + proof_candidate
            result = lean_client.run_code(code, None, verbose)
            print(result)
            if result == '{ "env": 1}':
                return proof_candidate
            else:
                ## todo: cut of the proof at the invalid place and retry it
                print(f"Proof candidate {proof_candidate} failed")
        cnt += 1
    return None


def prove_theorem(name: str, hypotheses: list[str], goal: str, verbose=False) -> ProofSearchState:
    """
    Attempts to prove a theorem using the ProofSearchState.
    
    Args:
        name: Name of the theorem
        hypothesis: List of hypothesis statements
        goal: The goal to prove
        
    Returns:
        ProofSearchState containing the proof attempt
    """
    lean_client = LeanServer()
    
    # Create proof search state
    proof_state = ProofSearchState(name, hypotheses, goal)

    claude_client = Client()
    
    # Generate and test hypotheses
    proof_state.add_hypotheses(claude_client, verbose)
    print("Added hypotheses")
    print(proof_state.theoretical_hypotheses)
    
    # Try to generate proofs for different numbers of hypotheses
    valid_proofs = []
    for i in range(len(proof_state.theoretical_hypotheses)):
        proof = iterate_until_valid_proof(proof_state, i, claude_client, lean_client, 1, verbose)
        if proof:
            proof_state.proven_hypotheses.append(Hypothesis( "p"+len(proof_state.proven_hypotheses), proof_state.theoretical_hypotheses[i], proof))
            valid_proofs.append(i)
    # Remove the valid proofs from the list
    valid_proofs.reverse()
    for i in valid_proofs:
        proof_state.theoretical_hypotheses.pop(i)
    return proof_state

def main(name, hypothesis, goal):
    """Main entry point for the theorem prover."""
    
    try:
        proof_state = prove_theorem(name, hypothesis, goal, True)
        if proof_state.proof:
            print(f"Proof found for theorem {name}:")
            print(proof_state.proof)
        else:
            print(f"Could not find proof for theorem {name}")
    except Exception as e:
        print(f"Error while proving theorem: {e}")
        sys.exit(1)

if __name__ == "__main__":
    name = "p1"
    hypotheses = ["(n : ℕ)", "(oh0 : 0 < n)"]
    goal = "Nat.gcd (21*n + 4) (14*n + 3) = 1"
    main(name, hypotheses, goal)
