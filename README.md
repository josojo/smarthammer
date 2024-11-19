# Smart Hammer

This repo contains the code to run a smart hammer that tries to prove lean code. 

The main idea of this code is to create a for any theorem to prove many hypthesis and substatements, that we then either find true or false. We will continue adding new hpythesis and substatements, until a proof becomes obvious from the hypthesises.

Current performance against miniF2F:

## Installing

- Install lean4
- Install [repl](https://github.com/leanprover-community/repl/)
Copy .env.example to .env and set the env variables.

```
python -m venv "venv"
source venv/bin/activate
pip install -r requirements.txt
```
## Running Tests

To run the unit tests:

