"""Verify EM foundations, the actual proof audit, and prior immutable bindings.

This checks recorded evidence. Replay proofs with lake build and the semantic
axiom audit; replay numerical validation with xi_em_bernstein_validation.py.
"""
import argparse
import hashlib
import json
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[2]
OUT = ROOT / "research/prime_spectral/verification_2026_10_18_em_foundations"
BASE = ROOT / "research/prime_spectral/verification_2026_10_18_evaluator_comparison/manifest.json"
PIN = "570a5cfb45e4f74c35b0167d87f45059ba5ca13f"
CHANGED = {"Reinmann.lean", "Reinmann/AxiomAudit.lean"}
MODULES = ["BernoulliQuadrature", "BernoulliBernsteinBounds", "EulerMaclaurinCell", "EulerMaclaurinTail"]
REPORT = ROOT / "research/prime_spectral/XI_EM_FOUNDATIONS_2026_10_18.md"


def sha(path):
    with path.open("rb") as stream:
        return hashlib.file_digest(stream, "sha256").hexdigest()


def check(record=False):
    bound = {}
    previous = json.loads(BASE.read_text())
    assert len(previous["artifacts_sha256"]) == 1147
    for name, expected in previous["artifacts_sha256"].items():
        path = OUT / "historical_570a5cf" / name if name in CHANGED else ROOT / name
        assert sha(path) == expected, name
        bound[path] = expected

    audit = (ROOT / "Reinmann/AxiomAudit.lean").read_text()
    umbrella = (ROOT / "Reinmann.lean").read_text()
    declarations = []
    for module in MODULES:
        path = ROOT / "Reinmann" / (module + ".lean")
        declarations += ["Reinmann."+module+"."+name for name in
                         re.findall(r"^theorem\s+(\w+)", path.read_text(), re.M)]
        assert "import Reinmann."+module in umbrella
        assert "import Reinmann."+module in audit
        bound[path] = sha(path)
    assert len(declarations) == 22
    assert all("#print axioms "+name in audit for name in declarations)
    assert len(re.findall(r"^#print axioms", audit, re.M)) == 394
    assert not any(re.search(r"^import Reinmann$", p.read_text(), re.M)
                   for p in (ROOT / "Reinmann").glob("*.lean"))
    build = (OUT / "full_build.log").read_text()
    assert re.search(r"Build completed successfully \(\d+ jobs\)\.", build)
    assert "error:" not in build
    proof_audit = (OUT / "axiom_audit.log").read_text()
    assert "all 394 audited theorems depend only on [propext, Classical.choice, Quot.sound]" in proof_audit
    assert "AXIOM-CLEAN:" in proof_audit and "FAIL:" not in proof_audit

    ci = json.loads((OUT / "ci_570a5cf.json").read_text())
    assert ci["head_sha"] == PIN and ci["status"] == "completed" and ci["conclusion"] == "success"
    validation = json.loads((OUT / "bernstein_evaluator.json").read_text())
    for name, expected in validation["source_sha256"].items():
        assert sha(ROOT / name) == expected, name
    assert validation["centre"] == ["1/2", "14"] and validation["jet_degree"] == 16
    assert validation["timing_repeats"] == 7 and validation["timing_statistic"] == "median"
    assert validation["Lean_B12_whole_interval_bound_proved"]
    assert validation["Lean_EM_periodic_integral_bound_proved"]
    assert not validation["Lean_zeta_EM_identity_proved"]
    assert not validation["Lean_complex_Stirling_identity_and_error_proved"]
    assert not validation["Lean_complete_hard_tile_certified"]
    assert [row["terms"] for row in validation["rows"]] == [10, 12, 16]
    assert all(row["all_17_overlap_builtin_reference"] and row["all_17_complex_radii_below_1e_8"]
               and len(row["ordinary_jet"]) == 17 and len(row["timings_seconds"]) == 7
               and row["seconds"] > 0 and row["bernoulli_bound"] == "6112/15015"
               and row["bernoulli_order"] == 12 and row["zeta_corrections"] == 6
               for row in validation["rows"])

    for path in OUT.rglob("*"):
        if path.is_file() and path.name != "manifest.json":
            bound[path] = sha(path)
    for name in CHANGED:
        bound[ROOT / name] = sha(ROOT / name)
    for path in [BASE, REPORT, Path(__file__).resolve(),
                 ROOT / "experiments/prime_spectral/xi_em_bernstein_validation.py"]:
        bound[path] = sha(path)
    result = {
        "status": "finite_EM_components_and_periodic_integral_bound_verified",
        "base_commit": PIN, "base_CI_conclusion": "success", "base_CI_url": ci["html_url"],
        "new_audited_declarations": declarations, "total_audited_declarations": 394,
        "new_round_remote_CI_verified": False,
        "Lean_finite_Bernoulli_quadrature_proved": True,
        "Lean_actual_shifted_power_derivative_chain_proved": True,
        "Lean_B12_whole_interval_bound_proved": True,
        "Lean_EM_periodic_integral_bound_proved": True,
        "Lean_zeta_EM_identity_proved": False,
        "Lean_complex_Stirling_identity_and_error_proved": False,
        "Lean_complete_hard_tile_certified": False,
        "Lean_complete_hard_tile_seconds": None, "thirty_five_Lean_tiles_seconds": None,
        "full_zero_free_rectangle_certified": False,
        "published_DH_and_formalization_files_unchanged": True,
        "PF_implies_RH_bridges_changed": False,
        "scope": "22 kernel-checked finite EM and integral-bound theorems; external validation of the proved B12 constant. No complete Lean zeta/Gamma evaluator, hard tile, rectangle or RH proof.",
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
