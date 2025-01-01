#!/bin/bash
set -e

echo "Starting REPL setup..."

# Create a writable directory in /tmp
WORK_DIR="/tmp/repl_setup"
mkdir -p "$WORK_DIR"
cd "$WORK_DIR"

# Install necessary system packages (using apt-get with sudo)
apt-get update && apt-get install -y \
    build-essential \
    cmake \
    ninja-build \
    libssl-dev \
    pkg-config

# Install Elan
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh -s -- -y

# Add Elan to PATH
export PATH="$HOME/.elan/bin:$PATH"

# Install Lean version as specified in lean-toolchain
pwd
git clone https://github.com/leanprover-community/repl.git
cd repl
LEAN_VERSION=$(cat lean-toolchain)
elan default $LEAN_VERSION

# Build REPL
lake update
lake build
cd test/Mathlib
lake exe cache get > /dev/null
# Add Elan to PATH
export PATH="$HOME/.elan/bin:$PATH"

# Install Lean version as specified in lean-toolchain
pwd
git clone https://github.com/leanprover-community/repl.git
cd repl
LEAN_VERSION=$(cat lean-toolchain)
elan default $LEAN_VERSION

# Build REPL
lake update
lake build
cd test/Mathlib
lake exe cache get > /dev/null

# Copy built files to the app directory (if needed)
mkdir -p /app/repl
cp -r "$WORK_DIR/repl"/* /app/repl/

echo "REPL setup completed successfully"