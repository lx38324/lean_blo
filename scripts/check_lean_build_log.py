#!/usr/bin/env python3
"""Fail CI on Lean errors, warnings, unsolved goals, or placeholder diagnostics."""
from __future__ import annotations

from pathlib import Path
import re
import sys

LOG = Path("lean-build.log")
if not LOG.exists():
    print("lean-build.log is missing", file=sys.stderr)
    raise SystemExit(1)

text = LOG.read_text(encoding="utf-8", errors="replace")
lines = text.splitlines()

line_patterns: tuple[tuple[str, re.Pattern[str]], ...] = (
    ("Lean error", re.compile(r"^\s*error:")),
    ("Lean warning", re.compile(r"^\s*warning:")),
    ("unsolved goals", re.compile(r"unsolved goals", re.IGNORECASE)),
    ("placeholder declaration", re.compile(
        r"declaration uses ['\"](?:sorry|admit|axiom)['\"]", re.IGNORECASE
    )),
    ("failed required target", re.compile(
        r"Some required targets logged failures", re.IGNORECASE
    )),
    ("Lean process failure", re.compile(r"Lean exited with code", re.IGNORECASE)),
)

problems: list[str] = []
for number, line in enumerate(lines, start=1):
    for label, pattern in line_patterns:
        if pattern.search(line):
            problems.append(f"line {number}: {label}: {line}")
            break

if problems:
    print("Lean build-log diagnostic scan failed:", file=sys.stderr)
    for problem in problems:
        print(f"  {problem}", file=sys.stderr)
    raise SystemExit(1)

success = any("Build completed successfully" in line for line in lines)
if not success:
    print("Lean build log has no successful completion marker", file=sys.stderr)
    raise SystemExit(1)

print(f"Lean build-log diagnostic scan passed ({len(lines)} log lines)")
