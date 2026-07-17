#!/usr/bin/env bash
#
# verify_axiom_clean.sh — guard the repository's headline claim:
#   the entire RH *reduction* chain is proven with 0 `sorry` and 0 custom axioms.
#
# Two independent checks:
#   1. Source-level grep for `sorry`/`admit` tokens and project-declared `axiom`s
#      in the active library (Reinmann/*.lean), ignoring comments and docstrings.
#   2. Semantic check: run Reinmann/AxiomAudit.lean and confirm every audited
#      theorem depends on exactly Lean's three foundational axioms
#      [propext, Classical.choice, Quot.sound] — nothing more.
#
# Exit 0 iff both checks pass. Intended for local use and CI.
set -uo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

fail=0
CANON='[propext, Classical.choice, Quot.sound]'

echo "== Check 1: source grep for sorry / admit / axiom in Reinmann/*.lean =="

# Comment-aware scanner: for every .lean file, blank out `--` line comments and
# `/- ... -/` block comments (including nested/multiline), then flag any surviving
# `sorry`/`admit`/`sorryAx` token or top-level `axiom` declaration. Blanking the
# comments first is what keeps docstrings (which legitimately discuss `sorry`)
# from tripping the guard, while still catching real occurrences in live code.
strip_and_scan() {
  local kind="$1"   # "code" | "axiom"
  find Reinmann -name '*.lean' -print0 | while IFS= read -r -d '' f; do
    awk -v file="$f" -v kind="$kind" '
      BEGIN { depth = 0 }
      {
        line = $0; out = ""; i = 1; n = length(line)
        while (i <= n) {
          two = substr(line, i, 2)
          if (depth > 0) {
            if (two == "-/") { depth--; i += 2 }
            else if (two == "/-") { depth++; i += 2 }
            else i++
          } else {
            if (two == "/-") { depth++; i += 2 }
            else if (two == "--") { break }        # rest of line is a comment
            else { out = out substr(line, i, 1); i++ }
          }
        }
        if (kind == "code") {
          if (out ~ /(^|[^A-Za-z0-9_])(sorry|admit|sorryAx)([^A-Za-z0-9_]|$)/)
            printf "%s:%d:%s\n", file, NR, $0
        } else {
          if (out ~ /(^|[[:space:]])axiom[[:space:]]+[A-Za-z]/)
            printf "%s:%d:%s\n", file, NR, $0
        }
      }
    ' "$f"
  done
}

sorry_hits="$(strip_and_scan code || true)"
axiom_hits="$(strip_and_scan axiom || true)"

if [[ -n "$sorry_hits" ]]; then
  echo "FAIL: found sorry/admit tokens:"
  echo "$sorry_hits"
  fail=1
else
  echo "OK: no sorry/admit in Reinmann/*.lean"
fi

if [[ -n "$axiom_hits" ]]; then
  echo "FAIL: found project-declared axioms:"
  echo "$axiom_hits"
  fail=1
else
  echo "OK: no project-declared axioms in Reinmann/*.lean"
fi

echo
echo "== Check 2: #print axioms on the reduction chain (AxiomAudit.lean) =="

audit_out="$(lake env lean Reinmann/AxiomAudit.lean 2>&1)"
audit_status=$?

if [[ $audit_status -ne 0 ]]; then
  echo "FAIL: AxiomAudit.lean did not elaborate:"
  echo "$audit_out"
  exit 1
fi

# `#print axioms` wraps long axiom lists across continuation lines (leading
# whitespace); join them back onto their parent line before matching.
audit_flat="$(echo "$audit_out" | awk '
  /^[[:space:]]/ && buf != "" { sub(/^[[:space:]]+/, " "); buf = buf $0; next }
  { if (buf != "") print buf; buf = $0 }
  END { if (buf != "") print buf }
')"

# Every non-empty line must end with the canonical axiom list.
bad="$(echo "$audit_flat" | grep 'depends on axioms' | grep -vF "$CANON" || true)"
n_lines="$(echo "$audit_flat" | grep -c 'depends on axioms')"

if [[ -n "$bad" ]]; then
  echo "FAIL: theorem(s) depend on non-canonical axioms:"
  echo "$bad"
  fail=1
elif [[ "$n_lines" -eq 0 ]]; then
  echo "FAIL: AxiomAudit produced no '#print axioms' output"
  fail=1
else
  echo "OK: all $n_lines audited theorems depend only on $CANON"
fi

echo
if [[ $fail -eq 0 ]]; then
  echo "AXIOM-CLEAN: 0 sorry, 0 custom axioms. Reduction chain verified."
  exit 0
else
  echo "AXIOM AUDIT FAILED."
  exit 1
fi
