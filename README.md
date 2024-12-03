# Smart Hammer

This repo contains code for a smart hammer that tries to prove Lean code.

The main idea of this code is to create, for any theorem, many hypotheses and substatements that we then either prove true or false. We will continue adding new hypotheses and substatements until a proof becomes obvious from the hypotheses.

Current performance against miniF2F:

## Installing

- Install lean4
- Install [repl](https://github.com/leanprover-community/repl/)
Copy .env.example to .env and set the env variables.

```cmd
python -m venv "venv"
source venv/bin/activate
pip install -r requirements.txt
```

## Running Tests

To run the unit tests:

```cmd
pytest
```

and for running only one test:

```cmd
pytest -qs test/hammer_e2e_wo_api/test_hammer.py
test/hammer_proof_fixing/test_iterate_until_successful.py
```

for running manual tests:

```cmd
ytest -sq ./test/with_api_interaction/hammer_proof_fixing/test_final_proof_fixing_with_real_client.py -m manual
```

or

```cmd
   pytest -v -m manual
```

## Linting

```cmd
python -m black .
```

## Starting the sever

The server relies on redis to manage tasks

```cmd
brew install redis
brew services start redis
```

Starting the worker that executes tasks:

```cmd
OBJC_DISABLE_INITIALIZE_FORK_SAFETY=YES python -m hammer.worker
```

Setting the OBJC_DISABLE_INITIALIZE_FORK_SAFETY variable is required for macOS to work smoothly
starting the api server to accept requests:

```cmd
uvicorn hammer.api.server:app --reload
```

Sending a request:

```cmd
curl -X POST "http://localhost:8000/prove/" -H "Content-Type: application/json" -d '{
    "name": "thm1",
    "hypotheses": ["(n : ℕ)", "(oh0 : 0 < n)"],
    "goal": "Nat.gcd (21*n + 4) (14*n + 3) = 1"
}'
```

To get the status

```cmd
curl "http://localhost:8000/status/{task_id}"
```

And to get the streamed progress:

```cmd
curl -N http://localhost:8000/logs/{task_id}
```
