#!/usr/bin/env python3
"""Reject corrupted Markdown and stale ICML theorem export references."""
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

EXPECTED_EXPORTS = (
    "fallback_safe_finite_horizon",
    "certified_gain_average",
    "certified_gain_same_iterate",
    "certified_gain_objective_gradient_same_iterate",
    "positive_gain_strictly_tightens",
    "proximal_response_error_certificate",
    "proximal_baseline_sequence_certificate",
    "stochastic_expected_finite_horizon",
    "stochastic_expected_gain_adjusted_average",
    "stochastic_expected_same_iterate",
    "stochastic_positive_gain_strictly_tightens",
    "stochastic_variance_rate",
)
EXPORT_FILE = ROOT / "OUSVRBLO" / "ICMLTheoryPackage.lean"
EXPORT_DOCS = (
    ROOT / "README.md",
    ROOT / "docs" / "ICML_METHOD_THEORY_PACKAGE.md",
    ROOT / "docs" / "ICML_THEORY_DEPENDENCY_AUDIT.md",
    ROOT / "docs" / "FORMALIZATION_SCOPE.md",
)

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

if not EXPORT_FILE.exists():
    errors.append(f"missing theorem export file: {EXPORT_FILE.relative_to(ROOT)}")
else:
    export_text = EXPORT_FILE.read_text(encoding="utf-8")
    for name in EXPECTED_EXPORTS:
        if f"theorem {name}" not in export_text:
            errors.append(
                f"{EXPORT_FILE.relative_to(ROOT)}: missing theorem export {name}"
            )

for doc in EXPORT_DOCS:
    if not doc.exists():
        errors.append(f"missing theorem documentation: {doc.relative_to(ROOT)}")
        continue
    text = doc.read_text(encoding="utf-8")
    for name in EXPECTED_EXPORTS:
        token = f"ICMLTheoryPackage.{name}"
        if token not in text:
            errors.append(f"{doc.relative_to(ROOT)}: missing export reference {token}")

if errors:
    print("documentation sanitation failed:", file=sys.stderr)
    for error in errors:
        print(f"  {error}", file=sys.stderr)
    raise SystemExit(1)

print(
    "documentation sanitation passed "
    f"({len(FILES)} Markdown files, {len(EXPECTED_EXPORTS)} theorem exports)"
)
