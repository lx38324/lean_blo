#!/usr/bin/env bash
set -euo pipefail

{
  lake exe cache get || true
  lake build
} > lean-build.log 2>&1

bash scripts/check_no_placeholder.sh
python3 scripts/check_docs_sanity.py
python3 scripts/check_lean_build_log.py

echo "OUSVR-BLO verification passed"
