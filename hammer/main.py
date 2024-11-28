import sys
from hammer.lean.server import LeanServer
from hammer.proof.proof import ProofSearchState, Hypothesis
from hammer.api.claude.client import Client
from hammer.proof.utils import  extract_proof_from_text


def iterate_until_valid_proof(
    proof_state: ProofSearchState,
    hyptotheses_number,
    client: Client,
    lean_client: LeanServer,
    max_iteration=1,
    max_correction_iteration=1,
    verbose=False,
):
    cnt = 0
    starting_code = ""
    while cnt < max_iteration:
        proof_candidate = proof_state.generate_proof_candidate_for_hypotheses(
            client, hyptotheses_number, starting_code, verbose
        )
        if proof_candidate:
            code = proof_state.hypothesis_as_code(hyptotheses_number) + proof_candidate
            result = lean_client.run_code(code, 0, verbose)
            if isinstance(result, dict) and (
                "messages" not in result
                or not any(
                    msg.get("severity") == "error" for msg in result.get("messages", [])
                )
            ):
                return proof_candidate
            else:
                for _ in range(0, max_correction_iteration):
                    error_messages = [msg for msg in result.get("messages", []) if msg.get("severity") == "error"]
                    first_error = error_messages[0] if error_messages else None
                    prompt = f"The following proof \n```lean4 \n {proof_state.hypothesis_as_code(hyptotheses_number)}{proof_candidate}\n ```\n failed with error: \n {first_error}. \n Please propose a complete lean proof that corrects this error and proves the theorem. Put your proof into a new ```lean ``` block."
                    response = client.send(prompt, verbose)
                    code = proof_state.hypothesis_as_code(hyptotheses_number) + extract_proof_from_text(response)[0]
                    result = lean_client.run_code(code, 0, verbose)
                    if isinstance(result, dict) and (
                        "messages" not in result
                        or not any(
                            msg.get("severity") == "error" for msg in result.get("messages", [])
                        )
                    ):
                        return proof_candidate
                    # if verbose:
                        # error_messages = [msg for msg in result.get("messages", []) if msg.get("severity") == "error"]
                        # first_error = error_messages[0] if error_messages else None
                        # print(f"Proof candidate: {proof_candidate} failed with the error {first_error}")
        cnt += 1
    return None


def iterate_until_valid_final_proof(
    proof_state: ProofSearchState,
    client: Client,
    lean_client: LeanServer,
    max_iteration=1,
    max_correction_iteration=1,
    verbose=False,
):
    cnt = 0
    starting_code = ""
    while cnt < max_iteration:
        proof_candidate = proof_state.generate_final_proof(
            client, starting_code, verbose
        )
        if proof_candidate:
            code = proof_state.get_theorem_code() + proof_candidate
            result = lean_client.run_code(code, 0, verbose)
            if isinstance(result, dict) and (
                "messages" not in result
                or not any(
                    msg.get("severity") == "error" for msg in result.get("messages", [])
                )
            ):
                return proof_candidate
            else:
                for _ in range(0, max_correction_iteration):
                    error_messages = [msg for msg in result.get("messages", []) if msg.get("severity") == "error"]
                    first_error = error_messages[0] if error_messages else None
                    prompt = f"The following proof \n```lean4 \n {proof_state.get_theorem_code()}{proof_candidate}\n ```\n failed with error: \n {first_error}. \n Please propose a complete lean proof that corrects this error and proves the theorem. Put your proof into a new ```lean ``` block."
                    response = client.send(prompt, verbose)
                    code = proof_state.get_theorem_code() + extract_proof_from_text(response)[0]
                    result = lean_client.run_code(code, 0, verbose)
                    if isinstance(result, dict) and (
                        "messages" not in result
                        or not any(
                            msg.get("severity") == "error" for msg in result.get("messages", [])
                        )
                    ):
                        return proof_candidate
        cnt += 1
    return None


def prove_theorem_via_hypotheses_search(
    proof_state: ProofSearchState,
    api_client: Client,
    lean_client: LeanServer,
    verbose=False,
):
    proof_state.add_hypotheses(api_client, verbose)
    print("Added hypotheses")
    print(proof_state.theoretical_hypotheses)

    # Try to generate proofs for different numbers of hypotheses
    valid_proofs = []
    for i in range(len(proof_state.theoretical_hypotheses)):
        proof = iterate_until_valid_proof(
            proof_state, i, api_client, lean_client, 1, verbose
        )
        if proof:
            proof_state.proven_hypotheses.append(
                Hypothesis(
                    "p" + str(len(proof_state.proven_hypotheses)),
                    proof_state.theoretical_hypotheses[i],
                    proof,
                )
            )
            valid_proofs.append(i)
    # Remove the valid proofs from the list
    valid_proofs.reverse()
    for i in valid_proofs:
        proof_state.theoretical_hypotheses.pop(i)
    print(
        "In total ",
        len(proof_state.proven_hypotheses),
        "hypotheses proven from initially ",
        str(len(proof_state.theoretical_hypotheses))
        + str(len(proof_state.proven_hypotheses))
        + "available ones",
    )
    return proof_state


def find_final_proof(
    proof_state: ProofSearchState, api_client, lean_client, nr_tries=1, verbose=False
):
    proof = iterate_until_valid_final_proof(
        proof_state, api_client, lean_client, nr_tries, verbose
    )
    proof_state.proof = proof_state.build_final_proof(proof)
    return proof_state.proof


def prove_theorem(
    name: str, hypotheses: list[str], goal: str, verbose=False
) -> ProofSearchState:
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
    proof_state = ProofSearchState(name, hypotheses, goal)
    claude_client = Client()

    prove_theorem_via_hypotheses_search(
        proof_state, claude_client, lean_client, verbose
    )
    find_final_proof(proof_state, lean_client, verbose)


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
    name = "thm1"
    hypotheses = ["(n : ℕ)", "(oh0 : 0 < n)"]
    goal = "Nat.gcd (21*n + 4) (14*n + 3) = 1"
    main(name, hypotheses, goal)
