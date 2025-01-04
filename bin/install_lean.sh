#!/bin/bash
set -e

echo "Starting REPL setup..."

# Create directory in the app root instead of /tmp
WORK_DIR="$HOME/repl_setup"
mkdir -p "$WORK_DIR"
cd "$WORK_DIR"

echo "Current PATH: $PATH"
echo "Current directory: $(pwd)"
echo "Listing available commands:"
which git || echo "git not found"

# Install Elan
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh -s -- -y

# Add Elan to PATH
export PATH="$HOME/.elan/bin:$PATH"

# Clone REPL repository
echo "Cloning REPL repository..."
export GIT_EXEC_PATH=/app/.apt/usr/lib/git-core
/app/.apt/usr/bin/git clone https://github.com/leanprover-community/repl.git
cd repl

# Install Lean version as specified in lean-toolchain
LEAN_VERSION=$(cat lean-toolchain)
elan default $LEAN_VERSION

# Build REPL
lake update
lake build
cd test/Mathlib
echo "Downloading Mathlib..."
lake exe cache get > /dev/null

echo "Copying built files to home directory..."
mkdir -p "$HOME/repl"
cp -r "$WORK_DIR/repl"/* "/app/repl/"
ls -al "$WORK_DIR/repl"
ls -al "/app/repl"

# Add a marker file to indicate successful installation
touch "$HOME/repl/.installation_complete"

echo "REPL setup completed successfully"

echo "Final contents of /app before slug creation:"
ls -alR /app

echo "Final contents of /app/repl:"
ls -al /app/repl

