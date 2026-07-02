"""
Focused numerical probe for the order-3 Toeplitz/PF frontier.

Uses the certified xi Taylor coefficients cached by rh_report_figures.py:
  research/figures/coeffs_M120.txt

The script computes the contiguous order-3 Toeplitz determinants

  det [ mu(n+2)  mu(n+1)  mu(n)
        mu(n+3)  mu(n+2)  mu(n+1)
        mu(n+4)  mu(n+3)  mu(n+2) ]

where mu(n) = (-1)^n b_n, then writes a compact research log with the smallest
raw and scale-normalized margins. This is evidence only, not a proof.
"""

from __future__ import annotations

from pathlib import Path

import mpmath as mp


ROOT = Path(__file__).resolve().parents[1]
COEFFS = ROOT / "research" / "figures" / "coeffs_M120.txt"
OUT = ROOT / "research" / "ORDER3_TOEPLITZ_FRONTIER_LOG.md"


def load_coefficients(path: Path) -> tuple[float, list[mp.mpf]]:
    lines = path.read_text().strip().splitlines()
    min_cert = float(lines[0].split("=", 1)[1])
    return min_cert, [mp.mpf(line) for line in lines[1:]]


def det3(mu: list[mp.mpf], n: int) -> mp.mpf:
    return mp.det(
        mp.matrix(
            [
                [mu[n + 2], mu[n + 1], mu[n]],
                [mu[n + 3], mu[n + 2], mu[n + 1]],
                [mu[n + 4], mu[n + 3], mu[n + 2]],
            ]
        )
    )


def normalized_expr(mu: list[mp.mpf], n: int) -> mp.mpf:
    """Central-scale expression det3 / mu(n+2)^3 via adjacent ratios."""
    center = mu[n + 2]
    x = mu[n + 1] / center
    y = mu[n] / center
    z = mu[n + 3] / center
    w = mu[n + 4] / center
    return 1 - 2 * x * z - y * w + x * x * w + y * z * z


def main() -> None:
    mp.mp.dps = 100
    min_cert, b = load_coefficients(COEFFS)
    mu = [((-1) ** n) * coeff for n, coeff in enumerate(b)]
    max_n = len(mu) - 5

    rows = []
    for n in range(max_n + 1):
        raw = det3(mu, n)
        normalized = raw / (mu[n + 2] ** 3)
        ratio_form = normalized_expr(mu, n)
        rows.append((n, raw, normalized, ratio_form))

    raw_min = min(rows, key=lambda item: item[1])
    normalized_min = min(rows, key=lambda item: item[2])
    all_positive = all(raw > 0 for _, raw, _, _ in rows)
    ratio_matches = all(abs(norm - ratio) <= mp.mpf("1e-80") for _, _, norm, ratio in rows)

    scale_rows = []
    for n, _, norm, _ in rows:
        N = mp.mpf(n + 1)
        scale_rows.append((n, norm * N, norm * N**2, norm * N**3))

    preview = "\n".join(
        f"| {n} | `{mp.nstr(raw, 10)}` | `{mp.nstr(norm, 10)}` | `{mp.nstr(ratio, 10)}` |"
        for n, raw, norm, ratio in rows[:20]
    )
    tail_preview = "\n".join(
        f"| {n} | `{mp.nstr(norm, 10)}` | `{mp.nstr(s1, 10)}` | `{mp.nstr(s2, 10)}` | `{mp.nstr(s3, 10)}` |"
        for (n, _, norm, _), (_, s1, s2, s3) in zip(rows[-12:], scale_rows[-12:])
    )

    OUT.write_text(
        "\n".join(
            [
                "# Order-3 Toeplitz Frontier Log",
                "",
                "**Status:** numerical evidence only, not a proof.",
                "",
                f"- Coefficient cache: `{COEFFS.relative_to(ROOT)}`",
                f"- Cached certification floor: at least `{min_cert:.0f}` significant digits",
                f"- Tested offsets: `n = 0..{max_n}`",
                f"- All raw order-3 determinants positive: `{all_positive}`",
                f"- Smallest raw determinant: `n={raw_min[0]}`, value `{mp.nstr(raw_min[1], 16)}`",
                f"- Smallest normalized determinant `det / mu(n+2)^3`: "
                f"`n={normalized_min[0]}`, value `{mp.nstr(normalized_min[2], 16)}`",
                f"- Ratio-form identity matched numerically: `{ratio_matches}`",
                "",
                "## First 20 Offsets",
                "",
                "| n | raw determinant | normalized determinant | ratio expression |",
                "|---:|---:|---:|---:|",
                preview,
                "",
                "## Tail Scaling Probe",
                "",
                "| n | normalized | `(n+1)D` | `(n+1)^2 D` | `(n+1)^3 D` |",
                "|---:|---:|---:|---:|---:|",
                tail_preview,
                "",
                "## Interpretation",
                "",
                "The order-3 rung stays positive across the certified coefficient range.",
                "The raw values shrink rapidly because the xi coefficients have factorial",
                "scale decay; the normalized determinant is the better diagnostic for",
                "where the positivity margin is tight.  This supports the Lean target",
                "`XiToeplitzOrder3Positive`, but does not prove it.",
                "",
                "The ratio expression is",
                "",
                "```text",
                "D_n = 1 - 2*x*z - y*w + x^2*w + y*z^2",
                "x = mu(n+1)/mu(n+2), y = mu(n)/mu(n+2),",
                "z = mu(n+3)/mu(n+2), w = mu(n+4)/mu(n+2).",
                "```",
                "",
                "The tail scaling table is a heuristic guide for the asymptotic proof:",
                "a stable column suggests the power of `n` that should appear in a",
                "future lower bound for the normalized determinant.",
                "",
            ]
        )
    )
    print(f"wrote {OUT}")
    print(f"all positive: {all_positive}")
    print(f"min raw: n={raw_min[0]} value={mp.nstr(raw_min[1], 12)}")
    print(
        "min normalized: "
        f"n={normalized_min[0]} value={mp.nstr(normalized_min[2], 12)}"
    )
    print(f"ratio identity matched: {ratio_matches}")


if __name__ == "__main__":
    main()
