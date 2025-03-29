#!/usr/bin/env bash
set -e

if [[ "$1" == "--rango_dir" && -n "$2" ]]; then
  RANGO_DIR="$2"
  shift 2
else
  echo "Error: \`--rango_dir RANGO_DIR\` should be specified."
  exit 1
fi

if [ -d "$RANGO_DIR" ]; then
  echo "Removing existing Rango directory at $RANGO_DIR"
  rm -rf "$RANGO_DIR"
else
  echo "No existing Rango directory found at $RANGO_DIR"
fi
