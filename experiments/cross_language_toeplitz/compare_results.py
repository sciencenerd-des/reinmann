"""Fail closed on disagreement and render the cross-language experiment report."""

from __future__ import annotations

import argparse
import json
from pathlib import Path


EXPECTED_CONTROLS = {"positive": 1, "zero": 0, "negative": -1}


def load(path: Path) -> dict[str, object]:
    return json.loads(path.read_text())


def by_order(payload: dict[str, object]) -> dict[int, dict[str, object]]:
    return {int(item["order"]): item for item in payload["orders"]}  # type: ignore[index]


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--python", type=Path, required=True)
    parser.add_argument("--javascript", type=Path, required=True)
    parser.add_argument("--typescript", type=Path, required=True)
    parser.add_argument("--output-json", type=Path, required=True)
    parser.add_argument("--output-md", type=Path, required=True)
    args = parser.parse_args()

    payloads = {
        "Python": load(args.python),
        "JavaScript": load(args.javascript),
        "TypeScript": load(args.typescript),
    }
    failures: list[str] = []
    for language, payload in payloads.items():
        if payload["controls"] != EXPECTED_CONTROLS:
            failures.append(f"{language} control failure: {payload['controls']}")

    hashes = {str(payload["input_sha256"]) for payload in payloads.values()}
    rows = {int(payload["max_row"]) for payload in payloads.values()}
    if len(hashes) != 1:
        failures.append("input SHA-256 mismatch")
    if len(rows) != 1:
        failures.append("max-row mismatch")

    python_orders = by_order(payloads["Python"])
    javascript_orders = by_order(payloads["JavaScript"])
    typescript_orders = by_order(payloads["TypeScript"])
    comparison_rows: list[dict[str, object]] = []
    for order in (3, 4):
        py = python_orders[order]
        js = javascript_orders[order]
        ts = typescript_orders[order]
        if py["counts"] != ts["counts"]:
            failures.append(f"order-{order} Python/TypeScript interval-count mismatch")
        if py["sign_stream_sha256"] != ts["sign_stream_sha256"]:
            failures.append(f"order-{order} Python/TypeScript sign-stream mismatch")
        py_counts = py["counts"]
        certified_total = int(py_counts["positive"]) + int(py_counts["negative"]) + int(py_counts["zero"])
        if certified_total == int(py["total"]):
            certified_counts = {
                "positive": int(py_counts["positive"]),
                "negative": int(py_counts["negative"]),
                "zero": int(py_counts["zero"]),
            }
            if js["counts"] != certified_counts:
                failures.append(f"order-{order} JavaScript certified-count mismatch")
            if js["sign_stream_sha256"] != py["sign_stream_sha256"]:
                failures.append(f"order-{order} JavaScript certified sign-stream mismatch")
        comparison_rows.append(
            {
                "order": order,
                "total": py["total"],
                "interval_counts": py_counts,
                "javascript_midpoint_counts": js["counts"],
                "interval_sign_stream_sha256": py["sign_stream_sha256"],
            }
        )

    result = {
        "status": "passed" if not failures else "failed",
        "failures": failures,
        "input_sha256": next(iter(hashes)) if len(hashes) == 1 else sorted(hashes),
        "max_row": next(iter(rows)) if len(rows) == 1 else sorted(rows),
        "controls": EXPECTED_CONTROLS,
        "orders": comparison_rows,
        "interpretation": (
            "bounded falsification evidence over stored decimal enclosures; "
            "not a proof of the coefficient-generation procedure, an infinite positivity theorem, or RH"
        ),
    }
    args.output_json.parent.mkdir(parents=True, exist_ok=True)
    args.output_md.parent.mkdir(parents=True, exist_ok=True)
    args.output_json.write_text(json.dumps(result, indent=2) + "\n")

    lines = [
        "# Cross-Language Toeplitz-Minor Replication",
        "",
        "**Status:** bounded falsification evidence only; not an RH proof.",
        "",
        f"- Differential check: **{result['status']}**",
        f"- Input SHA-256: `{result['input_sha256']}`",
        f"- Row box: `0..{result['max_row']}`",
        "- Controls: positive, geometric-zero, and negative determinants all classified as expected",
        "",
        "| order | selections | certified + | certified - | zero | inconclusive | JS midpoint + |",
        "|---:|---:|---:|---:|---:|---:|---:|",
    ]
    for row in comparison_rows:
        interval = row["interval_counts"]
        midpoint = row["javascript_midpoint_counts"]
        lines.append(
            f"| {row['order']} | {row['total']} | {interval['positive']} | "
            f"{interval['negative']} | {interval['zero']} | {interval['inconclusive']} | "
            f"{midpoint['positive']} |"
        )
    lines.extend(
        [
            "",
            "Python and TypeScript used exact interval arithmetic but independent implementations;",
            "JavaScript used an exact midpoint Bareiss determinant as an algorithmically distinct",
            "differential check. Agreement rules were specified before examining these outputs.",
            "",
            "No certified negative in this finite box means only that the tested data did not",
            "falsify the order-3 or order-4 target. It does not certify the upstream Xi coefficient",
            "extraction, any untested row, any higher order, total positivity, or RH.",
            "",
        ]
    )
    if failures:
        lines.extend(["## Failures", "", *[f"- {failure}" for failure in failures], ""])
    args.output_md.write_text("\n".join(lines))
    print(json.dumps(result, indent=2))
    if failures:
        raise SystemExit(1)


if __name__ == "__main__":
    main()
