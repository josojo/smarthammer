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

## Deployment

# Login to Azure
az login

# Create a resource group
az group create --name smarthammer-rg --location eastus

# Create Azure Container Registry (ACR)
az acr create --resource-group smarthammer-rg --name smarthammerrepo --sku Basic
az acr login --name smarthammerrepo

# Build and push the images to ACR
docker-compose build
docker tag smarthammer_app smarthammerrepo.azurecr.io/smarthammer:latest
docker tag redis:alpine smarthammerrepo.azurecr.io/redis:latest
docker push smarthammerrepo.azurecr.io/smarthammer:latesdocker push smarthammerrepo.azurecr.io/smarthammer:latestt
docker push smarthammerrepo.azurecr.io/redis:latest

# Create Azure Cache for Redis (managed Redis service)
az redis create \
  --resource-group smarthammer-rg \
  --name smarthammer-redis \
  --location eastus \
  --sku Basic \
  --vm-size c0

# Create Container Apps environment
az containerapp env create \
  --name smarthammer-env \
  --resource-group smarthammer-rg \
  --location eastus

# Deploy the application
az containerapp create \
  --name smarthammer \
  --resource-group smarthammer-rg \
  --environment smarthammer-env \
  --image smarthammerrepo.azurecr.io/smarthammer:latest \
  --target-port 8000 \
  --ingress external \
  --env-vars "REDIS_URL=redis://<redis-hostname>:6379"

# Enable monitoring
az monitor log-analytics workspace create \
  --resource-group smarthammer-rg \
  --workspace-name smarthammer-logs

# Link it to your container app
az containerapp env update \
  --name smarthammer-env \
  --resource-group smarthammer-rg \
  --logs-workspace-id <workspace-id> \
  --logs-workspace-key <workspace-key>

# Configure scaling (optional)
az containerapp update \
  --name smarthammer \
  --resource-group smarthammer-rg \
  --min-replicas 1 \
  --max-replicas 10 \
  --scale-rule-name http-rule \
  --scale-rule-type http \
  --scale-rule-http-concurrency 100





