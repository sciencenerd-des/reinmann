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

project_files=()
while IFS= read -r -d '' file; do
  project_files+=("$file")
done < <(find . -type f -name '*.lean' -not -path './.lake/*' -print0)

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

  perl -ne '
    my @checks = (
      [qr/(?<![A-Za-z0-9_])sorry(?![A-Za-z0-9_])/, "sorry"],
      [qr/(?<![A-Za-z0-9_])admit(?![A-Za-z0-9_])/, "admit"],
      [qr/^\s*(?:private\s+)?axiom\b/, "axiom declaration"],
      [qr/^\s*(?:private\s+)?constant\b/, "constant declaration"],
      [qr/^\s*(?:private\s+)?opaque\b/, "opaque declaration"],
      [qr/(?<![A-Za-z0-9_])unsafe(?![A-Za-z0-9_])/, "unsafe declaration or modifier"],
      [qr/^\s*set_option\s+autoImplicit\s+true\b/, "set_option autoImplicit true"],
      [qr/^\s*set_option\s+relaxedAutoImplicit\s+true\b/, "set_option relaxedAutoImplicit true"],
    );

    for my $check (@checks) {
      if ($_ =~ $check->[0]) {
        print "$ARGV:$.: forbidden verification shortcut: $check->[1]\n";
        $failed = 1;
      }
    }

    END {
      exit($failed ? 1 : 0);
    }
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
