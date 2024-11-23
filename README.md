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
pytest -q test/hammer_e2e_wo_api/test_hammer.py
```

## Linting

```cmd
black .
```
