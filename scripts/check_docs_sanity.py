#!/usr/bin/env python3
"""Reject control-character and visibly corrupted TeX in Markdown sources."""
from __future__ import annotations

from pathlib import Path
import re
import sys

ROOT = Path(__file__).resolve().parents[1]
FILES = [ROOT / "README.md", *sorted((ROOT / "docs").glob("**/*.md"))]

PATTERNS: tuple[tuple[str, re.Pattern[bytes]], ...] = (
    ("possible stripped \\frac command", re.compile(rb"(?<!\\f)rac(?:\\{|[0-9])")),
    ("possible stripped \\tau command", re.compile(rb"(?<!\\t)au_t\^e")),
    ("possible stripped \\rho command", re.compile(rb"(?<!\\r)ho_t\^[PB]")),
)
VISIBLE_BAD = (b"C_bb_t", b"C_dd_t")

errors: list[str] = []
for path in FILES:
    data = path.read_bytes()

    for offset, byte in enumerate(data):
        if byte < 0x20 and byte != 0x0A:
            line = data[:offset].count(b"\n") + 1
            errors.append(
                f"{path.relative_to(ROOT)}:{line}: ASCII control 0x{byte:02x}"
            )

    for label, pattern in PATTERNS:
        for match in pattern.finditer(data):
            line = data[:match.start()].count(b"\n") + 1
            errors.append(
                f"{path.relative_to(ROOT)}:{line}: {label}: {match.group()!r}"
            )

    for token in VISIBLE_BAD:
        start = 0
        while True:
            offset = data.find(token, start)
            if offset < 0:
                break
            line = data[:offset].count(b"\n") + 1
            errors.append(
                f"{path.relative_to(ROOT)}:{line}: malformed token {token!r}"
            )
            start = offset + len(token)

if errors:
    print("documentation sanitation failed:", file=sys.stderr)
    for error in errors:
        print(f"  {error}", file=sys.stderr)
    raise SystemExit(1)

print(f"documentation sanitation passed ({len(FILES)} Markdown files)")
