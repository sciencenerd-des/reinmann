"""Bind the first actual Xi tile and standalone mixed-row/analytic prerequisites.

The prior publication manifest is immutable. Only the two library integration
files differ from that closure; their publication versions are preserved here.
"""
import argparse
import hashlib
import json
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[2]
OUT = ROOT / "research/prime_spectral/verification_2026_10_18_first_tile"
BASE = ROOT / "research/prime_spectral/verification_2026_10_18_publication/manifest.json"
REPORT = ROOT / "research/prime_spectral/FIRST_XI_TILE_AND_MIXED_ROWS_2026_10_18.md"
MODS = ["XiAdaptiveTiles", "XiLocalCauchy", "XiFirstTile", "SplitPairMixedRows",
        "SplitPairPatchedRemainder", "SplitPairCoefficientIdentity"]
CHANGED = {"Reinmann.lean", "Reinmann/AxiomAudit.lean"}


def sha(path):
    with path.open("rb") as stream:
        return hashlib.file_digest(stream, "sha256").hexdigest()


def run(record=False):
    bound = {}
    previous = json.loads(BASE.read_text())
    for name, expected in previous["artifacts_sha256"].items():
        path = ROOT / name
        preserved = OUT / "historical_0e4a6e8" / name if name in CHANGED else path
        assert sha(preserved) == expected, name
        bound[preserved] = expected
    umbrella = (ROOT / "Reinmann.lean").read_text()
    audit = (ROOT / "Reinmann/AxiomAudit.lean").read_text()
    public = []
    for module in MODS:
        path = ROOT / "Reinmann" / (module + ".lean")
        bound[path] = sha(path)
        assert "import Reinmann." + module in umbrella, module
        for theorem in re.findall(r"^theorem\s+(\w+)", path.read_text(), re.M):
            name = "Reinmann." + module + "." + theorem
            assert "#print axioms " + name in audit, name
            public.append(name)
    full = (OUT / "full_build.log").read_text()
    assert "Build completed successfully" in full and "error:" not in full
    axioms = (OUT / "axiom_audit.log").read_text()
    assert "AXIOM-CLEAN:" in axioms and "FAIL:" not in axioms
    assert f"all {len(re.findall(r'^#print axioms', audit, re.M))} audited theorems" in axioms
    lean_cert = json.loads((OUT / "leancert_compatibility_receipt.json").read_text())
    assert lean_cert["status"] == "kernel_only_exp_log_compatible"
    assert lean_cert["proof_sha256"] == sha(OUT / "LeanCertCompatibility.lean")
    assert all(line.endswith("[propext, Classical.choice, Quot.sound]") for line in lean_cert["axiom_audit"])
    trust = (OUT / "leancert_evaluator_trust.log").read_text()
    assert "sorryAx" not in trust and "_native.native_decide" in trust
    pilot = json.loads((OUT / "arb_adaptive_taylor.json").read_text())
    pilot_source = ROOT / "experiments/prime_spectral/xi_adaptive_tile_pilot.py"
    assert pilot["source_sha256"] == sha(pilot_source)
    assert pilot["status"] == "arb_adaptive_count_pilot_complete" and pilot["pending"] == 0
    assert pilot["tiles"] == len(pilot["accepted"]) == 35
    partial = json.loads((OUT / "arb_adaptive_natural_summary.json").read_text())
    assert partial["source_sha256"] == sha(pilot_source)
    assert partial["status"] == "arb_adaptive_count_pilot_budget_exhausted" and partial["pending"] > 0
    for path in OUT.rglob("*"):
        if path.is_file() and path.name != "manifest.json":
            bound[path] = sha(path)
    for name in CHANGED:
        bound[ROOT / name] = sha(ROOT / name)
    for path in [BASE, REPORT, Path(__file__).resolve(), pilot_source,
                 ROOT / "experiments/prime_spectral/check_leancert_v430.py",
                 ROOT / "lean-toolchain", ROOT / "lakefile.toml", ROOT / "lake-manifest.json"]:
        bound[path] = sha(path)
    result = {
        "status": "first_actual_tile_and_standalone_split_pair_prerequisites_verified",
        "publication_base_commit": "0e4a6e8203c570be8d52246650dc0c1b294b47c6",
        "published_doi": "10.5281/zenodo.23401370",
        "published_scientific_files_unchanged": True,
        "new_audited_declarations": public,
        "total_audited_declarations": len(re.findall(r"^#print axioms", audit, re.M)),
        "actual_Xi_tile_centre": "1/2", "actual_Xi_tile_radius": "1/100",
        "full_rectangle_certified": False,
        "arb_proposed_tiles": 35, "LeanCert_kernel_exp_log_verified": True,
        "simple_pole_remainder_and_coefficient_identity_proved": True,
        "general_entire_split_pair_oscillation_assembly_complete": False,
        "PF_implies_RH_bridges_changed": False,
        "scope": "Local evaluator certificate and standalone analytic/algebraic prerequisites; no RH proof, full zero-free rectangle, or modified published release.",
        "artifacts_sha256": {str(path.relative_to(ROOT)): digest for path, digest in sorted(bound.items())}}
    manifest = OUT / "manifest.json"
    if record:
        if manifest.exists():
            raise FileExistsError("Manifest already exists; do not silently replace it")
        manifest.write_text(json.dumps(result, indent=2) + "\n")
    else:
        assert json.loads(manifest.read_text()) == result, "Round differs from manifest"
    print(result["status"], len(public), "new audited declarations;", len(bound), "bound artifacts")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--record", action="store_true")
    run(parser.parse_args().record)
