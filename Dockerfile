# Use Python 3.10 instead of 3.9
FROM python:3.10-slim

# Install system dependencies
RUN apt-get update && apt-get install -y \
    git \
    curl \
    build-essential \
    && rm -rf /var/lib/apt/lists/*

# Set working directory
WORKDIR /app

# Copy application files
COPY . .

# Install Python dependencies
COPY requirements.txt .
RUN pip install -r requirements.txt

# Install Elan (Lean version manager)
RUN curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh -s -- -y

# Add Elan to PATH
ENV PATH="/root/.elan/bin:$PATH"

# Setup REPL
WORKDIR /app/repl
RUN git clone https://github.com/leanprover-community/repl.git .

# Install specific Lean version from toolchain
RUN elan default $(cat lean-toolchain)

# Build REPL
RUN lake update && \
    lake build

# Setup Mathlib
WORKDIR /app/repl/test/Mathlib
RUN lake exe cache get

# Debug step to verify REPL setup
RUN ls -la /app/repl/test/Mathlib && \
    ls -la /app/repl/.lake/build/bin && \
    which lake && \
    lake --version

# Set environment variable for REPL path
ENV REPLPATH=/app/repl/test/Mathlib

# Return to app directory
WORKDIR /app

# Expose port (adjust if needed)
EXPOSE 8000

# Start command using the same structure as your Procfile
CMD ["sh", "-c", "uvicorn hammer.api.server:app --host 0.0.0.0 --port ${PORT:-8000} & python -m hammer.worker"] 