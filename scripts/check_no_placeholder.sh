#!/usr/bin/env bash
set -euo pipefail
matches=$(grep -R --line-number -E '\b(sorry|admit|axiom)\b' OUSVRBLO lakefile.lean 2>/dev/null || true)
if [[ -n "$matches" ]]; then
  echo "$matches"
  echo "Found placeholder proof keywords in Lean sources."
  exit 1
fi
