#!/usr/bin/env bash
# Requires Python 3.10+ and a C++20 compiler.
set -euo pipefail
cd "$(dirname "$0")"
build_dir=$(mktemp -d)
trap 'rm -rf "$build_dir"' EXIT
python3 make_instance.py > "$build_dir/instance.txt"
g++ -std=c++20 -O3 -march=native -Wall -Wextra -pedantic check_prefixes.cpp -o "$build_dir/check"
"$build_dir/check" < "$build_dir/instance.txt"
