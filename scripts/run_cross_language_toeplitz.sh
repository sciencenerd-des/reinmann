#!/usr/bin/env bash
set -euo pipefail

repo_root=$(cd "$(dirname "$0")/.." && pwd)
experiment_dir="$repo_root/experiments/cross_language_toeplitz"
output_dir="$repo_root/research/cross_language_toeplitz"
max_row=${1:-30}
output_dir=${2:-$repo_root/research/cross_language_toeplitz}

mkdir -p "$output_dir"

python3 "$experiment_dir/python_reference.py" \
  --max-row "$max_row" \
  --output "$output_dir/python.json"
node "$experiment_dir/javascript_midpoint.js" \
  "$max_row" "$output_dir/javascript.json"
npx --no-install tsc -p "$experiment_dir/tsconfig.json"
node "$experiment_dir/typescript_interval.ts" \
  "$max_row" "$output_dir/typescript.json"
python3 "$experiment_dir/compare_results.py" \
  --python "$output_dir/python.json" \
  --javascript "$output_dir/javascript.json" \
  --typescript "$output_dir/typescript.json" \
  --output-json "$output_dir/comparison.json" \
  --output-md "$output_dir/REPORT.md"
