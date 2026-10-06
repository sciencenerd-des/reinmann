"""Interval scan for arbitrary-row, initial-column Toeplitz minors.

This is a falsification tool for the Lean targets
``XiInitialColumnMinorThreeFromContig`` and
``XiInitialColumnMinorGeFourFromContig``.  For fixed columns ``0, ..., k-1`` it
enumerates strictly increasing row selections and evaluates the determinant
with exact rational interval arithmetic.

The coefficient cache contains decimal strings produced by a cross-precision
calculation.  Each stored decimal is enclosed by half a unit in its last
place.  Consequently the signs below are certified for that stored-decimal
enclosure; this script does not turn the cache-generation procedure into a
formal proof of the Xi coefficients.
"""

from __future__ import annotations

import argparse
import itertools
import json
from dataclasses import dataclass
from decimal import Decimal, localcontext
from fractions import Fraction
from functools import lru_cache
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
COEFFS = ROOT / "research" / "figures" / "coeffs_M120.txt"
OUT_JSON = ROOT / "research" / "ARBITRARY_ROW_MINOR_SCAN.json"
OUT_MD = ROOT / "research" / "ARBITRARY_ROW_MINOR_SCAN.md"


@dataclass(frozen=True)
class Interval:
    lo: Fraction
    hi: Fraction

    def __post_init__(self) -> None:
        if self.lo > self.hi:
            raise ValueError("invalid interval")

    @staticmethod
    def point(value: Fraction) -> "Interval":
        return Interval(value, value)

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


def last_place_exponent(token: str) -> int:
    """Return the base-10 exponent of the last displayed mantissa digit."""
    mantissa, separator, exponent = token.lower().partition("e")
    fractional_digits = len(mantissa.partition(".")[2])
    scientific_exponent = int(exponent) if separator else 0
    return scientific_exponent - fractional_digits


def half_ulp(token: str) -> Fraction:
    exponent = last_place_exponent(token)
    if exponent >= 0:
        return Fraction(10**exponent, 2)
    return Fraction(1, 2 * 10 ** (-exponent))


def load_coefficients(path: Path) -> tuple[str, list[Interval]]:
    lines = path.read_text().strip().splitlines()
    cert_metadata = lines[0].split("=", 1)[1]
    coefficients: list[Interval] = []
    for token in lines[1:]:
        value = Fraction(token)
        radius = half_ulp(token)
        coefficients.append(Interval(value - radius, value + radius))
    return cert_metadata, coefficients


def signed_moment(coefficients: list[Interval], index: int) -> Interval:
    value = coefficients[index]
    return value if index % 2 == 0 else -value


def entry(coefficients: list[Interval], row: int, col: int) -> Interval:
    if col > row:
        return Interval.point(Fraction(0))
    return signed_moment(coefficients, row - col)


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
    result = Interval.point(Fraction(0))
    for permutation, sign in signed_permutations(size):
        term = Interval.point(Fraction(1))
        for i, column in enumerate(permutation):
            term = term * entry(coefficients, rows[i], column)
        result = result + (term if sign > 0 else -term)
    return result


def fraction_text(value: Fraction, digits: int = 18) -> str:
    with localcontext() as context:
        context.prec = digits
        return format(Decimal(value.numerator) / Decimal(value.denominator), ".15E")


def scan_order(coefficients: list[Interval], size: int, max_row: int) -> dict[str, object]:
    counts = {"certified_positive": 0, "certified_negative": 0, "exact_zero": 0, "inconclusive": 0}
    best: tuple[Fraction, tuple[int, ...]] | None = None
    negative_rows: list[tuple[int, ...]] = []
    for rows in itertools.combinations(range(max_row + 1), size):
        interval = determinant(coefficients, rows)
        if interval.lo > 0:
            counts["certified_positive"] += 1
            if best is None or interval.lo < best[0]:
                best = (interval.lo, rows)
        elif interval.hi < 0:
            counts["certified_negative"] += 1
            negative_rows.append(rows)
        elif interval.lo == 0 and interval.hi == 0:
            counts["exact_zero"] += 1
        else:
            counts["inconclusive"] += 1

    best_payload = None
    if best is not None:
        best_payload = {
            "rows": list(best[1]),
            "lower_bound": fraction_text(best[0]),
        }
    return {
        "size": size,
        "columns": list(range(size)),
        "max_row": max_row,
        "counts": counts,
        "tightest_certified_positive": best_payload,
        "certified_negative_examples": [list(rows) for rows in negative_rows[:10]],
    }


def render_markdown(payload: dict[str, object]) -> str:
    lines = [
        "# Arbitrary-Row Initial-Column Minor Scan",
        "",
        "**Status:** falsification evidence only; not an RH proof.",
        "",
        f"- Coefficient cache: `{COEFFS.relative_to(ROOT)}`",
        f"- Cache cross-precision metadata: `{payload['cache_cert_metadata']}`",
        f"- Decimal enclosure: half a unit in the last stored decimal place",
        f"- Maximum row scanned: `{payload['max_row']}`",
        "- Columns: the initial interval `0, ..., k-1`",
        "",
        "The interval signs are certified for the stored decimal enclosures. The",
        "cross-precision metadata is provenance, not a formal interval proof of",
        "the Cauchy extraction or of the Xi function itself.",
        "",
        "| order | certified + | certified - | exact zero | inconclusive | tightest positive |",
        "|---:|---:|---:|---:|---:|---|",
    ]
    for result in payload["orders"]:  # type: ignore[index]
        counts = result["counts"]
        best = result["tightest_certified_positive"]
        best_text = "none" if best is None else f"rows={best['rows']}, lo={best['lower_bound']}"
        lines.append(
            f"| {result['size']} | {counts['certified_positive']} | "
            f"{counts['certified_negative']} | {counts['exact_zero']} | "
            f"{counts['inconclusive']} | `{best_text}` |"
        )
    lines.extend(
        [
            "",
            "A certified negative count would falsify the corresponding discrete",
            "PF target for the scanned row box and should stop that route. A zero",
            "or inconclusive count is not evidence of failure.",
            "",
        ]
    )
    return "\n".join(lines)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--max-row", type=int, default=20)
    parser.add_argument("--output-json", type=Path, default=OUT_JSON)
    parser.add_argument("--output-md", type=Path, default=OUT_MD)
    args = parser.parse_args()
    if args.max_row < 0:
        raise SystemExit("--max-row must be nonnegative")

    cert_metadata, coefficients = load_coefficients(COEFFS)
    if args.max_row >= len(coefficients):
        raise SystemExit(f"--max-row exceeds cache (max {len(coefficients) - 1})")
    payload: dict[str, object] = {
        "cache": str(COEFFS.relative_to(ROOT)),
        "cache_cert_metadata": cert_metadata,
        "enclosure": "half-unit in the last stored decimal place",
        "max_row": args.max_row,
        "orders": [scan_order(coefficients, size, args.max_row) for size in (3, 4)],
    }
    args.output_json.write_text(json.dumps(payload, indent=2) + "\n")
    args.output_md.write_text(render_markdown(payload))
    print(f"wrote {args.output_json}")
    print(f"wrote {args.output_md}")
    for result in payload["orders"]:  # type: ignore[index]
        print(result["size"], result["counts"])


if __name__ == "__main__":
    main()
