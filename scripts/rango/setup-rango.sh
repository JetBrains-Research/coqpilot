#!/usr/bin/env bash
set -e

# Note: this script requires `git` and `pyenv` to be installed as prerequisites

REPO_URL="git@github.com:GlebSolovev/rango.git" # TODO: replace with the original repo once changes are accepted
BRANCH_NAME="coqpilot-adapter-gpu"
PYTHON_VERSION="3.11"

if [[ "$1" == "--rango_dir" && -n "$2" ]]; then
  RANGO_DIR="$2"
  shift 2
else
  echo "Error: \`--rango_dir RANGO_DIR\` should be specified."
  exit 1
fi

if [ ! -d "$RANGO_DIR" ]; then
  echo "Cloning Rango into $RANGO_DIR..."
  git clone "$REPO_URL" "$RANGO_DIR"
  cd "$RANGO_DIR"
  git checkout "$BRANCH_NAME"
  git submodule update --init --recursive
  echo "Rango repository is sucessfully initialized..."
else
  echo "Rango repository already exists at $RANGO_DIR..."
  cd "$RANGO_DIR"
fi

# Set up `pyenv` to use the desired Python version
echo "Setting up \`pyenv\` to use Python $PYTHON_VERSION..."
export PYENV_ROOT="$HOME/.pyenv"
export PATH="$PYENV_ROOT/bin:$PATH"
eval "$(pyenv init -)"
pyenv install "$PYTHON_VERSION" -s
pyenv shell "$PYTHON_VERSION"
pip3 install --upgrade pip
echo "Python is ready: $(python3 --version)"

if [ ! -d "venv" ]; then
  echo "Creating Python virtual environment..."
  python3 -m venv venv
else
  echo "Python virtual environment is already created..."
fi

echo "Entering Python virtual environment..."
# Activate the venv
# shellcheck disable=SC1091
source venv/bin/activate
pip install --upgrade pip

echo "Installing Rango dependencies..."
pip3 install -e .

cd coqpyt
pip3 install .

cd ../CoqStoq
pip3 install -e .

echo "Rango environment setup complete!"
