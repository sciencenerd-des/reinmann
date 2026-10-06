"""Exact interval reference for the cross-language Xi minor scan."""

from __future__ import annotations

import argparse
import hashlib
import itertools
import json
import platform
from fractions import Fraction
from functools import lru_cache
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
COEFFICIENTS = ROOT / "research" / "figures" / "coeffs_M120.txt"


class Interval:
    def __init__(self, lo: Fraction, hi: Fraction) -> None:
        if lo > hi:
            raise ValueError("invalid interval")
        self.lo = lo
        self.hi = hi

    @classmethod
    def point(cls, value: int | Fraction) -> "Interval":
        fraction = Fraction(value)
        return cls(fraction, fraction)

    def __add__(self, other: "Interval") -> "Interval":
        return Interval(self.lo + other.lo, self.hi + other.hi)

    def __neg__(self) -> "Interval":
        return Interval(-self.hi, -self.lo)

    def __sub__(self, other: "Interval") -> "Interval":
        return self + (-other)

    def __mul__(self, other: "Interval") -> "Interval":
        products = (
            self.lo * other.lo,
            self.lo * other.hi,
            self.hi * other.lo,
            self.hi * other.hi,
        )
        return Interval(min(products), max(products))


class ScaledInterval:
    """Exact interval whose endpoints share one common decimal scale."""

    def __init__(self, lo: int, hi: int) -> None:
        if lo > hi:
            raise ValueError("invalid interval")
        self.lo = lo
        self.hi = hi

    @classmethod
    def point(cls, value: int) -> "ScaledInterval":
        return cls(value, value)

    def __add__(self, other: "ScaledInterval") -> "ScaledInterval":
        return ScaledInterval(self.lo + other.lo, self.hi + other.hi)

    def __neg__(self) -> "ScaledInterval":
        return ScaledInterval(-self.hi, -self.lo)

    def __sub__(self, other: "ScaledInterval") -> "ScaledInterval":
        return self + (-other)

    def __mul__(self, other: "ScaledInterval") -> "ScaledInterval":
        products = (
            self.lo * other.lo,
            self.lo * other.hi,
            self.hi * other.lo,
            self.hi * other.hi,
        )
        return ScaledInterval(min(products), max(products))


def last_place_exponent(token: str) -> int:
    mantissa, separator, exponent = token.lower().partition("e")
    fractional_digits = len(mantissa.partition(".")[2])
    scientific_exponent = int(exponent) if separator else 0
    return scientific_exponent - fractional_digits


def half_ulp(token: str) -> Fraction:
    exponent = last_place_exponent(token)
    if exponent >= 0:
        return Fraction(10**exponent, 2)
    return Fraction(1, 2 * 10 ** (-exponent))


def load_coefficients(path: Path) -> list[Interval]:
    tokens = path.read_text().strip().splitlines()[1:]
    result: list[Interval] = []
    for token in tokens:
        value = Fraction(token)
        radius = half_ulp(token)
        result.append(Interval(value - radius, value + radius))
    return result


def load_scaled_coefficients(path: Path) -> tuple[list[ScaledInterval], int]:
    """Load the same enclosures as integers at one exact common scale."""
    tokens = path.read_text().strip().splitlines()[1:]
    places = max(0, max(-last_place_exponent(token) for token in tokens))
    scale = 10**places
    result: list[ScaledInterval] = []
    for token in tokens:
        midpoint = Fraction(token) * scale * 2
        radius = half_ulp(token) * scale * 2
        if midpoint.denominator != 1 or radius.denominator != 1:
            raise ValueError(f"non-integral common scale for token {token}")
        result.append(
            ScaledInterval(
                midpoint.numerator - radius.numerator,
                midpoint.numerator + radius.numerator,
            )
        )
    return result, places


def signed_moment(coefficients: list[Interval], index: int) -> Interval:
    value = coefficients[index]
    return value if index % 2 == 0 else -value


def entry(coefficients: list[Interval], row: int, column: int) -> Interval:
    if column > row:
        return type(coefficients[0]).point(0)
    return signed_moment(coefficients, row - column)


@lru_cache(maxsize=None)
def signed_permutations(size: int) -> tuple[tuple[tuple[int, ...], int], ...]:
    result: list[tuple[tuple[int, ...], int]] = []
    for permutation in itertools.permutations(range(size)):
        inversions = sum(
            permutation[i] > permutation[j]
            for i in range(size)
            for j in range(i + 1, size)
        )
        result.append((permutation, -1 if inversions % 2 else 1))
    return tuple(result)


def determinant(coefficients: list[Interval], rows: tuple[int, ...]) -> Interval:
    size = len(rows)
    result = Interval.point(0)
    for permutation, sign in signed_permutations(size):
        term = Interval.point(1)
        for row_index, column in enumerate(permutation):
            term *= entry(coefficients, rows[row_index], column)
        result += term if sign > 0 else -term
    return result


def sign_code(interval: Interval) -> str:
    if interval.lo > 0:
        return "+"
    if interval.hi < 0:
        return "-"
    if interval.lo == 0 and interval.hi == 0:
        return "0"
    return "?"


def scan(coefficients: list[Interval], order: int, max_row: int) -> dict[str, object]:
    counts = {"positive": 0, "negative": 0, "zero": 0, "inconclusive": 0}
    digest = hashlib.sha256()
    codes = {"+": "positive", "-": "negative", "0": "zero", "?": "inconclusive"}
    for rows in itertools.combinations(range(max_row + 1), order):
        code = sign_code(determinant(coefficients, rows))
        counts[codes[code]] += 1
        digest.update(f"{','.join(map(str, rows))}:{code}\n".encode())
    return {
        "order": order,
        "total": sum(counts.values()),
        "counts": counts,
        "sign_stream_sha256": digest.hexdigest(),
    }


def control_sign(values: tuple[int, int, int, int, int]) -> int:
    coefficients = [Interval.point(value) for value in values]
    interval = determinant(coefficients, (2, 3, 4))
    return 1 if interval.lo > 0 else -1 if interval.hi < 0 else 0


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--max-row", type=int, default=30)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    raw = COEFFICIENTS.read_bytes()
    coefficients, _ = load_scaled_coefficients(COEFFICIENTS)
    if args.max_row >= len(coefficients):
        raise SystemExit("--max-row exceeds the coefficient cache")
    payload = {
        "implementation": "python-scaled-integer-interval-leibniz",
        "runtime": platform.python_version(),
        "input": str(COEFFICIENTS.relative_to(ROOT)),
        "input_sha256": hashlib.sha256(raw).hexdigest(),
        "max_row": args.max_row,
        "uncertainty": "half-unit in each token's last displayed decimal place",
        "controls": {
            "positive": control_sign((1, 2, 5, 13, 33)),
            "zero": control_sign((1, 2, 4, 8, 16)),
            "negative": control_sign((1, 1, 2, 6, 24)),
        },
        "orders": [scan(coefficients, order, args.max_row) for order in (3, 4)],
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(payload, indent=2) + "\n")
    print(json.dumps(payload, indent=2))


if __name__ == "__main__":
    main()
