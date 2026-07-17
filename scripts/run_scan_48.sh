#!/usr/bin/env bash
# One-shot helper: extended arbitrary-row minor scan (falsification evidence).
set -euo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")/.."
exec python3 scripts/arbitrary_row_minor_scan.py --max-row 48
