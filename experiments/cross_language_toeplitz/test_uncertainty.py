"""Regression tests for decimal enclosure parsing and determinant controls."""

from __future__ import annotations

import importlib.util
import sys
from fractions import Fraction
from pathlib import Path


SCRIPT = Path(__file__).resolve().parents[2] / "scripts" / "arbitrary_row_minor_scan.py"
SPEC = importlib.util.spec_from_file_location("arbitrary_row_minor_scan", SCRIPT)
if SPEC is None or SPEC.loader is None:
    raise RuntimeError("could not load arbitrary_row_minor_scan.py")
MODULE = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = MODULE
SPEC.loader.exec_module(MODULE)


def test_half_ulp_accounts_for_negative_scientific_exponent() -> None:
    assert MODULE.half_ulp("1.230e-40") == Fraction(1, 2 * 10**43)


def test_half_ulp_accounts_for_positive_scientific_exponent() -> None:
    assert MODULE.half_ulp("1.20e+3") == Fraction(5)


def test_half_ulp_plain_decimal_is_unchanged() -> None:
    assert MODULE.half_ulp("0.125") == Fraction(1, 2000)


def test_determinant_sign_controls() -> None:
    point = MODULE.Interval.point
    cases = [
        ([1, 2, 5, 13, 33], 1),
        ([1, 2, 4, 8, 16], 0),
        ([1, 1, 2, 6, 24], -1),
    ]
    for values, expected in cases:
        interval = MODULE.determinant([point(Fraction(value)) for value in values], (2, 3, 4))
        actual = 1 if interval.lo > 0 else -1 if interval.hi < 0 else 0
        assert actual == expected
