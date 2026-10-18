"""Check the actual zeta EM proof round and preserve prior immutable evidence.

Recorded evidence checks are separate from Lean proof replay and Arb replay.
"""
import argparse
import hashlib
import json
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[2]
OUT = ROOT / "research/prime_spectral/verification_2026_10_18_em_identity"
BASE = ROOT / "research/prime_spectral/verification_2026_10_18_em_foundations/manifest.json"
PIN = "d14bb18f8109ad7723919ccb94b714eefc519491"
CHANGED = {"Reinmann.lean", "Reinmann/AxiomAudit.lean"}
MODULES = ["EulerMaclaurinFinite", "EulerMaclaurinZeta", "EulerMaclaurinAnalytic"]
REPORT = ROOT / "research/prime_spectral/XI_EM_IDENTITY_2026_10_18.md"


def sha(path):
    with path.open("rb") as stream:
        return hashlib.file_digest(stream, "sha256").hexdigest()


def check(record=False):
    bound = {}
    previous = json.loads(BASE.read_text())
    assert len(previous["artifacts_sha256"]) == 1161
    for name, expected in previous["artifacts_sha256"].items():
        path = OUT / "historical_d14bb18" / name if name in CHANGED else ROOT / name
        assert sha(path) == expected, name
        bound[path] = expected
    audit = (ROOT / "Reinmann/AxiomAudit.lean").read_text()
    umbrella = (ROOT / "Reinmann.lean").read_text()
    declarations = []
    for module in MODULES:
        path = ROOT / "Reinmann" / (module+".lean")
        declarations += ["Reinmann."+module+"."+name for name in
                         re.findall(r"^theorem\s+(\w+)", path.read_text(), re.M)]
        assert "import Reinmann."+module in umbrella
        assert "import Reinmann."+module in audit
        bound[path] = sha(path)
    assert len(declarations) == 31
    assert all("#print axioms "+name in audit for name in declarations)
    assert len(re.findall(r"^#print axioms", audit, re.M)) == 425
    assert not any(re.search(r"^import Reinmann$", p.read_text(), re.M)
                   for p in (ROOT / "Reinmann").glob("*.lean"))
    for name in ("hard_disk_identity", "hard_disk_error_le", "zeta_eq_model_add_remainder_upper"):
        assert "Reinmann.EulerMaclaurinAnalytic."+name in declarations
    build = (OUT / "full_build.log").read_text()
    assert re.search(r"Build completed successfully \(\d+ jobs\)\.", build)
    assert "error:" not in build
    proof_audit = (OUT / "axiom_audit.log").read_text()
    assert "all 425 audited theorems depend only on [propext, Classical.choice, Quot.sound]" in proof_audit
    assert "AXIOM-CLEAN:" in proof_audit and "FAIL:" not in proof_audit
    ci = json.loads((OUT / "ci_d14bb18.json").read_text())
    assert ci["head_sha"] == PIN and ci["status"] == "completed" and ci["conclusion"] == "success"
    validation = json.loads((OUT / "model_validation.json").read_text())
    for name, expected in validation["source_sha256"].items():
        assert sha(ROOT / name) == expected, name
    assert validation["status"] == "formal_EM_model_matches_archived_evaluator"
    assert validation["ordinary_jet_degree"] == 16 and validation["precision_bits"] == 192
    assert len(validation["rows"]) == 15
    assert all(row["all_17_model_coefficients_overlap"] and row["centre_error_inside_explicit_bound"]
               for row in validation["rows"])
    assert {row["N"] for row in validation["rows"]} == {11, 13, 17}
    assert not validation["Lean_complete_hard_tile_certified"]
    for path in OUT.rglob("*"):
        if path.is_file() and path.name != "manifest.json":
            bound[path] = sha(path)
    for name in CHANGED:
        bound[ROOT / name] = sha(ROOT / name)
    for path in [BASE, REPORT, Path(__file__).resolve(),
                 ROOT / "experiments/prime_spectral/xi_em_identity_validation.py"]:
        bound[path] = sha(path)
    result = {
        "status": "actual_zeta_EM_identity_and_upper_half_strip_continuation_verified",
        "base_commit": PIN, "base_CI_conclusion": "success", "base_CI_url": ci["html_url"],
        "new_audited_declarations": declarations, "total_audited_declarations": 425,
        "new_round_remote_CI_verified": False,
        "Lean_actual_zeta_EM_identity_proved": True,
        "Lean_zeta_EM_domain": "Re s > -11 and Im s > 0",
        "Lean_closed_unit_disk_at_half_plus_14i_covered": True,
        "Lean_actual_zeta_EM_symbolic_error_bound_proved": True,
        "Lean_uniform_numeric_zeta_jet_enclosure_proved": False,
        "Lean_complex_Stirling_identity_and_error_proved": False,
        "Lean_complete_hard_tile_certified": False,
        "Lean_complete_hard_tile_seconds": None, "thirty_five_Lean_tiles_seconds": None,
        "full_zero_free_rectangle_certified": False,
        "published_DH_and_formalization_files_unchanged": True,
        "PF_implies_RH_bridges_changed": False,
        "scope": "31 kernel-checked summation, zeta-series and analytic-continuation theorems. Actual order-12 zeta EM identity and symbolic error bound on the upper half-strip, including the full hard unit disk. No Gamma/jet numeric evaluator, complete hard tile, rectangle or RH proof.",
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
