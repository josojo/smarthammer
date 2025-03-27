#!/usr/bin/env python3
import requests
import re
import time
import json
import random
from typing import List, Dict, Tuple, Any, Optional

from hammer.api.types import AIForHypothesesProof

# API configuration
API_BASE_URL = "http://localhost:8000"  # Change this to your API endpoint


def fetch_lean_file() -> str:
    """Fetch the miniF2F Lean4 file from GitHub."""
    url = "https://raw.githubusercontent.com/yangky11/miniF2F-lean4/main/MiniF2F/Test.lean"
    url = "https://github.com/josojo/miniF2F-lean4/blob/easy/MiniF2F/Test.lean"  # only easy ones for now
    response = requests.get(url)
    if response.status_code != 200:
        raise Exception(f"Failed to fetch Lean file: {response.status_code}")
    return response.text


def parse_theorems(lean_text: str) -> List[Dict[str, Any]]:
    """Parse theorems from the Lean file."""
    # Regular expression to match theorem blocks
    theorem_pattern = (
        r"theorem\s+([^\s:]+)(?:\s*\([^)]*\))*\s*(?::\s*(.*?)\s*:=\s*by\s+sorry)"
    )

    theorems = []
    for match in re.finditer(theorem_pattern, lean_text, re.DOTALL):
        theorem_name = match.group(1)
        goal_text = match.group(2) if match.group(2) else ""

        # Extract the full theorem text for complete context
        full_theorem = match.group(0)

        # Parse hypotheses and variables
        hypotheses = []
        variables = []

        # Extract hypotheses from full theorem text
        hypothesis_pattern = r"\(h[₀₁₂₃₄₅₆₇₈₉]+\s*:\s*([^)]+)\)"
        for hyp_match in re.finditer(hypothesis_pattern, full_theorem):
            hypotheses.append(hyp_match.group(1).strip())

        # Extract variables from full theorem text
        var_pattern = r"\(([a-zA-Z][a-zA-Z0-9_\s:]*?)\s*:\s*([^)]+)\)"
        for var_match in re.finditer(var_pattern, full_theorem):
            var_names = var_match.group(1).strip().split()
            var_type = var_match.group(2).strip()
            for var_name in var_names:
                if var_name and var_name not in (
                    "h₀",
                    "h₁",
                    "h₂",
                    "h₃",
                    "h₄",
                    "h₅",
                    "h₆",
                    "h₇",
                    "h₈",
                    "h₉",
                ):
                    variables.append(f"{var_name} : {var_type}")

        theorems.append(
            {
                "name": theorem_name,
                "full_text": full_theorem,
                "goal": goal_text,
                "hypotheses": hypotheses,
                "variables": variables,
            }
        )

    return theorems


def submit_theorem_to_api(theorem: Dict[str, Any]) -> Tuple[str, Dict[str, Any]]:
    """Submit a theorem to the API for proving."""
    endpoint = f"{API_BASE_URL}/prove/"

    # Format hypotheses as a list of strings
    hypotheses_list = theorem["hypotheses"]

    # For simple theorems, we can use the goal directly
    goal = theorem["goal"]

    # Create request payload
    payload = {
        "name": theorem["name"],
        "hypotheses": hypotheses_list,
        "goal": goal,
        "ai_for_hypotheses_generation": AIForHypothesesProof.GEMINI.value,
        "ai_for_hypotheses_proof": [AIForHypothesesProof.GEMINI.value],
        "ai_for_final_proof": AIForHypothesesProof.GEMINI.value,
        "max_iteration_hypotheses_proof": 3,
        "max_correction_iteration_hypotheses_proof": 3,
        "max_iteration_final_proof": 3,
        "max_correction_iteration_final_proof": 3,
        "verbose": True,
        "code_for_env_0": "import Mathlib",  # Default environment import
    }

    try:
        response = requests.post(endpoint, json=payload)
        response_data = response.json()
        return response_data.get("task_id", "unknown"), response_data
    except Exception as e:
        print(f"Error submitting theorem {theorem['name']}: {e}")
        return "error", {"error": str(e)}


def check_task_status(task_id: str) -> Dict[str, Any]:
    """Check the status of a theorem proving task."""
    endpoint = f"{API_BASE_URL}/status/{task_id}"

    try:
        response = requests.get(endpoint)
        return response.json()
    except Exception as e:
        print(f"Error checking task {task_id}: {e}")
        return {"status": "error", "error": str(e)}


def main():
    print("Fetching miniF2F Lean4 file...")
    lean_text = fetch_lean_file()

    print("Parsing theorems...")
    theorems = parse_theorems(lean_text)
    print(f"Found {len(theorems)} theorems")

    # Take a sample of theorems to benchmark
    sample_size = min(3, len(theorems))  # Adjust sample size as needed
    sampled_theorems = random.sample(theorems, sample_size)

    print(f"Submitting {sample_size} theorems to the API...")
    task_map = {}
    for theorem in sampled_theorems:
        print(f"Submitting theorem: {theorem['name']}")
        task_id, response = submit_theorem_to_api(theorem)
        task_map[task_id] = {
            "theorem": theorem,
            "submit_time": time.time(),
            "response": response,
        }
        print(f"  Task ID: {task_id}")
        time.sleep(1)  # To avoid overwhelming the API

    print("\nWaiting for results...")
    max_wait_time = 600  # 10 minutes max wait time
    wait_interval = 10  # Check every 10 seconds
    start_time = time.time()

    results = {"completed": 0, "failed": 0, "pending": 0, "details": []}

    while time.time() - start_time < max_wait_time:
        all_complete = True

        for task_id, task_info in task_map.items():
            if task_info.get("status") in ("completed", "failed"):
                continue

            status_data = check_task_status(task_id)
            current_status = status_data.get("status", "unknown")

            if current_status not in ("completed", "failed"):
                all_complete = False
                task_map[task_id]["status"] = current_status
            else:
                task_map[task_id]["status"] = current_status
                task_map[task_id]["result"] = status_data.get("result")
                task_map[task_id]["logs"] = status_data.get("logs")

                # Print completion message
                theorem_name = task_map[task_id]["theorem"]["name"]
                print(f"Theorem {theorem_name} ({task_id}): {current_status}")

        if all_complete:
            break

        print(f"Waiting for {wait_interval} seconds...")
        time.sleep(wait_interval)

    # Compile final results
    for task_id, task_info in task_map.items():
        theorem_name = task_info["theorem"]["name"]
        status = task_info.get("status", "pending")

        if status == "completed":
            results["completed"] += 1
        elif status == "failed":
            results["failed"] += 1
        else:
            results["pending"] += 1

        results["details"].append(
            {
                "theorem_name": theorem_name,
                "task_id": task_id,
                "status": status,
                "proof": (
                    task_info.get("result", {}).get("proof")
                    if status == "completed"
                    else None
                ),
            }
        )

    # Print summary
    print("\n===== BENCHMARK RESULTS =====")
    print(f"Total theorems tested: {len(task_map)}")
    print(
        f"Completed: {results['completed']} ({results['completed']/len(task_map)*100:.1f}%)"
    )
    print(f"Failed: {results['failed']} ({results['failed']/len(task_map)*100:.1f}%)")
    print(
        f"Still Pending: {results['pending']} ({results['pending']/len(task_map)*100:.1f}%)"
    )

    # Save detailed results to a file
    with open("benchmark_results.json", "w") as f:
        json.dump(results, f, indent=2)
    print("Detailed results saved to benchmark_results.json")


if __name__ == "__main__":
    main()
