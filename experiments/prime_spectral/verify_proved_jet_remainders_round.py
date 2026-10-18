"""Verify the proved Gamma/zeta ordinary-jet remainder evidence closure.

This checks bindings and recorded outcomes; Lean and Arb replay independently.
"""
import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess

ROOT = Path(__file__).resolve().parents[2]
OUT = ROOT / "research/prime_spectral/verification_2026_10_18_proved_jet_remainders"
BASE = ROOT / "research/prime_spectral/verification_2026_10_18_em_identity/manifest.json"
PIN = "6dd599e94a6dd8099b8636833a23ecd37f5a5888"
ROOT_FILES = {"Reinmann.lean", "Reinmann/AxiomAudit.lean"}
OLD_ROOT = ROOT / "research/prime_spectral/verification_2026_10_18_stirling/historical_8e187b5"
MODULES = ["StirlingAnalytic", "ZetaJetRemainder"]
REPORT = ROOT / "research/prime_spectral/XI_PROVED_JET_REMAINDERS_2026_10_18.md"
E1_FILES = ["Reinmann/StirlingCell.lean", "Reinmann/StirlingSum.lean", "Reinmann/StirlingGamma.lean",
            "research/prime_spectral/XI_STIRLING_E1_2026_10_18.md",
            "research/prime_spectral/XI_EVALUATOR_ROUTE_DECISION_2026_10_18.md",
            "research/prime_spectral/verification_2026_10_18_stirling/full_build.log",
            "research/prime_spectral/verification_2026_10_18_stirling/axiom_audit.log"]


def sha(path):
    with path.open("rb") as stream:
        return hashlib.file_digest(stream, "sha256").hexdigest()


def check(record=False):
    bound = {}
    previous = json.loads(BASE.read_text())
    assert len(previous["artifacts_sha256"]) == 1174
    for name, expected in previous["artifacts_sha256"].items():
        path = OLD_ROOT / name if name in ROOT_FILES else ROOT / name
        assert sha(path) == expected, name
        bound[path] = expected
    for name in E1_FILES + sorted(ROOT_FILES):
        path = OUT / "historical_6dd599e" / name if name in ROOT_FILES else ROOT / name
        expected = hashlib.sha256(subprocess.check_output(["git", "show", PIN+":"+name], cwd=ROOT)).hexdigest()
        assert sha(path) == expected, name
        bound[path] = expected
    old_audit = (ROOT / E1_FILES[-1]).read_text()
    assert "all 455 audited theorems depend only on [propext, Classical.choice, Quot.sound]" in old_audit
    ci = json.loads((OUT / "ci_6dd599e.json").read_text())
    assert ci["head_sha"] == PIN and ci["status"] == "completed" and ci["conclusion"] == "success"
    audit = (ROOT / "Reinmann/AxiomAudit.lean").read_text()
    umbrella = (ROOT / "Reinmann.lean").read_text()
    declarations = []
    for module in MODULES:
        path = ROOT / "Reinmann" / (module+".lean")
        names = ["Reinmann."+module+"."+name for name in re.findall(r"^theorem\s+(\w+)", path.read_text(), re.M)]
        assert len(names) == (25 if module == "StirlingAnalytic" else 10)
        declarations += names
        assert "import Reinmann."+module in umbrella and "import Reinmann."+module in audit
        bound[path] = sha(path)
    assert all("#print axioms "+name in audit for name in declarations)
    assert len(re.findall(r"^#print axioms", audit, re.M)) == 490
    assert not any(re.search(r"^import Reinmann$", p.read_text(), re.M)
                   for p in (ROOT / "Reinmann").glob("*.lean"))
    build = (OUT / "full_build.log").read_text()
    assert re.search(r"Build completed successfully \(\d+ jobs\)\.", build) and "error:" not in build
    proof_audit = (OUT / "axiom_audit.log").read_text()
    assert "all 490 audited theorems depend only on [propext, Classical.choice, Quot.sound]" in proof_audit
    assert "AXIOM-CLEAN:" in proof_audit and "FAIL:" not in proof_audit
    probe = json.loads((OUT / "probe.json").read_text())
    for name, expected in probe["source_sha256"].items():
        assert sha(ROOT / name) == expected, name
    assert probe["status"] == "external_hard_tile_with_Lean_proved_analytic_jet_errors"
    assert probe["centre"] == ["1/2", "14"] and probe["jet_degree"] == 16
    assert probe["zeta_N"] == 21 and probe["zeta_terms"] == 20
    assert probe["gamma_shift"] == 12 and probe["gamma_retained_corrections"] == 6
    assert probe["zeta_each_ordinary_coefficient_error"] == "1e-7"
    assert probe["Gamma_each_ordinary_coefficient_error"] == "4e-14"
    assert probe["zeta_error_theorem"] in declarations and probe["Gamma_error_theorem"] in declarations
    row = probe["row"]
    assert row["all_17_overlap_builtin_reference"] and row["all_17_complex_radii_below_1e_8"]
    assert len(row["ordinary_jet"]) == 17 and len(row["timings_seconds"]) == 7 and row["seconds"] > 0
    assert float(re.match(r"\[?([\d.eE+-]+)", probe["tile_margin_lower"]).group(1)) > 0
    assert not probe["Lean_finite_exp_log_jet_arithmetic_certified"]
    assert not probe["Lean_complete_hard_tile_certified"] and probe["Lean_complete_hard_tile_seconds"] is None
    for path in OUT.rglob("*"):
        if path.is_file() and path.name != "manifest.json":
            bound[path] = sha(path)
    for name in ROOT_FILES:
        bound[ROOT / name] = sha(ROOT / name)
    for path in [BASE, REPORT, Path(__file__).resolve(),
                 ROOT / "experiments/prime_spectral/xi_proved_remainders_probe.py"]:
        bound[path] = sha(path)
    result = {
        "status": "actual_Gamma_zeta_ordinary_jet_remainder_bounds_verified",
        "base_commit": PIN, "base_CI_conclusion": "success", "base_CI_url": ci["html_url"],
        "new_audited_declarations": declarations, "total_audited_declarations": 490,
        "new_round_remote_CI_verified": False,
        "Lean_actual_Stirling_remainder_holomorphy_proved": True,
        "Lean_uniform_logGamma_remainder_on_unit_disk": "1e-14",
        "Lean_actual_Gamma_each_ordinary_coefficient_error": "4e-14",
        "Lean_actual_zeta_each_ordinary_coefficient_error_N21": "1e-7",
        "Lean_complete_hard_tile_certified": False,
        "Lean_finite_exp_log_jet_arithmetic_certified": False,
        "Lean_complete_hard_tile_seconds": None, "thirty_five_Lean_tiles_seconds": None,
        "full_zero_free_rectangle_certified": False,
        "published_DH_and_formalization_files_unchanged": True, "PF_implies_RH_bridges_changed": False,
        "scope": "35 kernel-checked theorems proving actual Gamma/zeta ordinary-jet analytic remainder errors on the full hard unit disk. External finite arithmetic still needed; no complete Lean hard tile, rectangle or RH proof.",
        "artifacts_sha256": {str(path.relative_to(ROOT)): value for path, value in sorted(bound.items())},
    }
    manifest = OUT / "manifest.json"
    if record:
        if manifest.exists():
            raise FileExistsError("Immutable manifest already exists")
        manifest.write_text(json.dumps(result, indent=2)+"\n")
    else:
        assert json.loads(manifest.read_text()) == result, "Round differs from manifest"
    print(result["status"], len(declarations), "new audited theorems;", len(bound), "bound artifacts")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--record", action="store_true")
    check(parser.parse_args().record)
