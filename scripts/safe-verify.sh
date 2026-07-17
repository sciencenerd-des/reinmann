#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

if ! command -v lake >/dev/null 2>&1; then
  echo "safe-verify: lake is not available on PATH" >&2
  exit 127
fi

if ! command -v lean >/dev/null 2>&1; then
  echo "safe-verify: lean is not available on PATH" >&2
  exit 127
fi

project_files=("./Reinmann.lean")
while IFS= read -r -d '' file; do
  project_files+=("$file")
done < <(find Reinmann -type f -name '*.lean' -print0)

if [ "${#project_files[@]}" -eq 0 ]; then
  echo "safe-verify: no Lean files found" >&2
  exit 1
fi

targets=()
if [ "$#" -eq 0 ]; then
  targets=("${project_files[@]}")
else
  for file in "$@"; do
    targets+=("$file")
  done
fi

scan_file() {
  local file="$1"

  if [ ! -f "$file" ]; then
    echo "safe-verify: file not found: $file" >&2
    exit 1
  fi

  awk -v file="$file" '
    BEGIN { depth = 0; failed = 0 }
    {
      source = $0
      code = ""
      i = 1
      n = length(source)

      while (i <= n) {
        two = substr(source, i, 2)
        if (depth > 0) {
          if (two == "-/") { depth--; i += 2 }
          else if (two == "/-") { depth++; i += 2 }
          else i++
        } else {
          if (two == "/-") { depth++; i += 2 }
          else if (two == "--") { break }
          else { code = code substr(source, i, 1); i++ }
        }
      }

      if (code ~ /(^|[^A-Za-z0-9_])sorry([^A-Za-z0-9_]|$)/) {
        printf "%s:%d: forbidden verification shortcut: sorry\n", file, NR
        failed = 1
      }
      if (code ~ /(^|[^A-Za-z0-9_])admit([^A-Za-z0-9_]|$)/) {
        printf "%s:%d: forbidden verification shortcut: admit\n", file, NR
        failed = 1
      }
      if (code ~ /^[[:space:]]*(private[[:space:]]+)?axiom([[:space:]]|$)/) {
        printf "%s:%d: forbidden verification shortcut: axiom declaration\n", file, NR
        failed = 1
      }
      if (code ~ /^[[:space:]]*(private[[:space:]]+)?constant([[:space:]]|$)/) {
        printf "%s:%d: forbidden verification shortcut: constant declaration\n", file, NR
        failed = 1
      }
      if (code ~ /^[[:space:]]*(private[[:space:]]+)?opaque([[:space:]]|$)/) {
        printf "%s:%d: forbidden verification shortcut: opaque declaration\n", file, NR
        failed = 1
      }
      if (code ~ /(^|[^A-Za-z0-9_])unsafe([^A-Za-z0-9_]|$)/) {
        printf "%s:%d: forbidden verification shortcut: unsafe declaration or modifier\n", file, NR
        failed = 1
      }
      if (code ~ /^[[:space:]]*set_option[[:space:]]+autoImplicit[[:space:]]+true([[:space:]]|$)/) {
        printf "%s:%d: forbidden verification shortcut: set_option autoImplicit true\n", file, NR
        failed = 1
      }
      if (code ~ /^[[:space:]]*set_option[[:space:]]+relaxedAutoImplicit[[:space:]]+true([[:space:]]|$)/) {
        printf "%s:%d: forbidden verification shortcut: set_option relaxedAutoImplicit true\n", file, NR
        failed = 1
      }
    }
    END { exit(failed ? 1 : 0) }
  ' "$file"
}

for file in "${project_files[@]}"; do
  scan_file "$file"
done

echo "safe-verify: shortcut scan passed for ${#project_files[@]} Lean file(s)."

if [ "$#" -eq 0 ]; then
  lake build
  for file in "${project_files[@]}"; do
    lake env lean "$file"
  done
else
  for file in "${targets[@]}"; do
    if [ ! -f "$file" ]; then
      echo "safe-verify: file not found: $file" >&2
      exit 1
    fi

    lake env lean "$file"
  done
fi
