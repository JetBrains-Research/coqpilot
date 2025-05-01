#!/usr/bin/env bash
set -e

# Note: this script requires `git` and `pyenv` to be installed as prerequisites

REPO_URL="git@github.com:GlebSolovev/rango.git" # TODO: replace with the original repo once changes are accepted
BRANCH_NAME="coqpilot-adapter"
PYTHON_VERSION="3.11"

MODEL_NAME="deepseek-bm25-proof-tfidf-proj-thm-prem-final"
MODEL_CHECKPOINT_URL="https://github.com/GlebSolovev/rango/releases/download/v2.4.2/$MODEL_NAME.tar.gz"

INSTALL_MODEL=false

while [[ $# -gt 0 ]]; do
  case "$1" in
    --rango_dir)
      RANGO_DIR="$2"
      shift 2
      ;;
    --install_local_model)
      INSTALL_MODEL=true
      shift
      ;;
    *)
      echo "Unknown argument: $1"
      exit 1
      ;;
  esac
done

if [[ -z "$RANGO_DIR" ]]; then
  echo "Error: \`--rango_dir RANGO_DIR\` must be specified."
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

if $INSTALL_MODEL; then
  MODEL_DIR="$RANGO_DIR/models/$MODEL_NAME"
  if [ -d "$MODEL_DIR" ]; then
    echo "Model already installed at $MODEL_DIR, skipping..."
  else
    echo "Downloading and installing model to $MODEL_DIR..."
    mkdir -p "$RANGO_DIR/tmp_model_download"
    curl -L "$MODEL_CHECKPOINT_URL" -o "$RANGO_DIR/tmp_model_download/model.tar.gz"

    mkdir -p "$RANGO_DIR/models"
    tar -xzf "$RANGO_DIR/tmp_model_download/model.tar.gz" -C "$RANGO_DIR/models"
    rm -rf "$RANGO_DIR/tmp_model_download"

    echo "Model installed successfully at $MODEL_DIR."
  fi
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
