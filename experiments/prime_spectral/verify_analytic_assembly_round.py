"""Verify the analytic split-pair assembly and honestly scoped hard-tile receipts.

This validates artifact bindings and recorded checks; rerun lake build, the axiom
audit and check_hard_panel.py to replay proofs. Historical manifests stay intact.
"""
import argparse
import hashlib
import json
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[2]
OUT = ROOT / "research/prime_spectral/verification_2026_10_18_analytic_assembly"
BASE = ROOT / "research/prime_spectral/verification_2026_10_18_first_tile/manifest.json"
REPORT = ROOT / "research/prime_spectral/ANALYTIC_SPLIT_PAIR_AND_HARD_TILE_2026_10_18.md"
MODULES = ["AnalyticSplitPair", "AnalyticToeplitzJacobi", "GammaHeightMajorant"]
CHANGED = {"Reinmann.lean", "Reinmann/AxiomAudit.lean"}
PANEL = ROOT / "research/prime_spectral/hard_tile_2026_10_18/PanelBenchmark.lean"
SCRIPTS = ["check_hard_panel.py", "xi_hard_tile_pilot.py", "xi_hard_panel_cost.py"]
CANON = "[propext, Classical.choice, Quot.sound]"


def sha(path):
    with path.open("rb") as stream:
        return hashlib.file_digest(stream, "sha256").hexdigest()


def run(record=False):
    bound = {}
    previous = json.loads(BASE.read_text())
    assert len(previous["artifacts_sha256"]) == 1096
    for name, expected in previous["artifacts_sha256"].items():
        preserved = OUT / "historical_855c2c5" / name if name in CHANGED else ROOT / name
        assert sha(preserved) == expected, name
        bound[preserved] = expected

    umbrella = (ROOT / "Reinmann.lean").read_text()
    audit = (ROOT / "Reinmann/AxiomAudit.lean").read_text()
    public = []
    for module in MODULES:
        path = ROOT / "Reinmann" / (module + ".lean")
        bound[path] = sha(path)
        assert "import Reinmann." + module in umbrella
        for theorem in re.findall(r"^theorem\s+(\w+)", path.read_text(), re.M):
            name = "Reinmann." + module + "." + theorem
            assert "#print axioms " + name in audit, name
            public.append(name)
    assert len(public) == 16
    imports = set()
    pending = ["Reinmann"]
    while pending:
        module = pending.pop()
        if module in imports:
            continue
        imports.add(module)
        path = ROOT / (module.replace(".", "/") + ".lean")
        pending.extend(re.findall(r"^import (Reinmann\.\w+)$", path.read_text(), re.M))
    imports.remove("Reinmann")
    assert {"Reinmann." + module for module in MODULES} <= imports
    assert not any(re.search(r"^import Reinmann$", path.read_text(), re.M)
                   for path in (ROOT / "Reinmann").glob("*.lean"))
    total = len(re.findall(r"^#print axioms", audit, re.M))
    assert total == 364
    full = (OUT / "full_build.log").read_text()
    assert "Build completed successfully (3598 jobs)." in full and "error:" not in full
    axioms = (OUT / "axiom_audit.log").read_text()
    assert "AXIOM-CLEAN:" in axioms and "FAIL:" not in axioms
    assert f"all {total} audited theorems depend only on {CANON}" in axioms

    ci = json.loads((OUT / "ci_855c2c5.json").read_text())
    assert ci["head_sha"] == "855c2c5039ed894b92bdba570947c320832118b3"
    assert ci["status"] == "completed" and ci["conclusion"] == "success"
    assert ci["id"] == 39101056242

    panel = json.loads((OUT / "panel_receipt.json").read_text())
    assert panel["status"] == "completed" and panel["exit_code"] == 0
    assert panel["source_sha256"] == sha(PANEL)
    assert panel["log_sha256"] == sha(OUT / "panel.log")
    assert len(panel["axiom_audit"]) == 3
    assert all(line.endswith(CANON) for line in panel["axiom_audit"])
    assert not panel["Lean_Xi_jet_certified"] and not panel["Lean_hard_tile_certified"]
    assert panel["Lean_hard_tile_seconds"] is None and panel["thirty_five_tile_seconds"] is None
    assert all(value > 0 for value in panel["timings_seconds"].values())
    thin = json.loads((OUT / "leancert_thin_receipt.json").read_text())
    assert thin["pin"] == "5a59804aa7c499f81ffd5eedf2a2cc5f9e8766d1"
    assert thin["status"] == "kernel_only_exp_log_compatible"
    assert not thin["project_dependency_files_changed"]

    arb = json.loads((OUT / "hard_tile_arb.json").read_text())
    assert arb["source_sha256"] == sha(ROOT / "experiments/prime_spectral/xi_hard_tile_pilot.py")
    assert arb["status"] == "external_arb_hard_tile_only"
    assert arb["centre"] == ["1/2", "14"] and arb["degree"] == 16
    assert len(arb["jet"]) == 17 and arb["unit_circle"][-1]["arcs"] == 1024
    assert not arb["Lean_centre_and_jet_certified"]
    range_pilot = json.loads((OUT / "range_cost.json").read_text())
    assert range_pilot["source_sha256"] == sha(ROOT / "experiments/prime_spectral/xi_hard_panel_cost.py")
    assert range_pilot["status"] == "external_range_quadrature_cost_pilot"
    assert range_pilot["theta_terms"] == 1 and range_pilot["moment_component"] == 0
    assert range_pilot["rows"][-1]["panels"] == 32768
    assert not any(row["target_met"] for row in range_pilot["rows"])

    paper = ROOT / "paper/formal_split_pair"
    assert (paper / "main.pdf").read_bytes().startswith(b"%PDF-")
    tex = (paper / "main.tex").read_text()
    assert "We do not prove RH or a low zero-free rectangle" in tex
    assert "We do not claim a separate new formal instantiation" in tex
    paper_log = (OUT / "paper_build.log").read_text()
    assert "main.pdf" in paper_log and "error:" not in paper_log
    visual = json.loads((OUT / "paper_visual_review.json").read_text())
    assert visual["pdf_sha256"] == sha(paper / "main.pdf")
    assert visual["pages_rendered_and_inspected"] == 5
    assert visual["status"] == "layout_checked_after_repair"

    for path in OUT.rglob("*"):
        if path.is_file() and path.name != "manifest.json":
            bound[path] = sha(path)
    for name in CHANGED:
        bound[ROOT / name] = sha(ROOT / name)
    for path in [BASE, REPORT, PANEL, Path(__file__).resolve(), paper / "main.tex", paper / "main.pdf"]:
        bound[path] = sha(path)
    for name in SCRIPTS:
        path = ROOT / "experiments/prime_spectral" / name
        bound[path] = sha(path)
    result = {
        "status": "analytic_split_pair_actual_Taylor_Jacobi_and_panel_verified",
        "base_commit": "855c2c5039ed894b92bdba570947c320832118b3",
        "base_CI_conclusion": ci["conclusion"],
        "base_CI_url": ci["html_url"],
        "new_round_remote_CI_verified": False,
        "new_audited_declarations": public,
        "total_audited_declarations": total,
        "entire_split_pair_assembly_complete": True,
        "actual_original_Taylor_minor_bridge_complete": True,
        "simple_zeros_and_isolated_boundary_pair_required": True,
        "PF_implies_RH_bridges_changed": False,
        "Gamma_shift_product_bound_proved": True,
        "uniform_numeric_small_Xi_strip_majorant_proved": False,
        "panel_seconds": panel["timings_seconds"],
        "Lean_hard_tile_certified": False,
        "Lean_hard_tile_seconds": None,
        "thirty_five_tile_seconds": None,
        "full_rectangle_certified": False,
        "scale_current_range_quadrature": False,
        "paper_status": "local_unreviewed_formalization_draft",
        "published_DH_scientific_files_unchanged": True,
        "scope": "Standalone oscillation theorem and actual Taylor bridge, Gamma component, one weighted integral panel. No RH proof, complete hard tile, or zero-free rectangle.",
        "artifacts_sha256": {str(path.relative_to(ROOT)): digest for path, digest in sorted(bound.items())}}
    manifest = OUT / "manifest.json"
    if record:
        if manifest.exists():
            raise FileExistsError("Immutable manifest already exists")
        manifest.write_text(json.dumps(result, indent=2) + "\n")
    else:
        assert json.loads(manifest.read_text()) == result, "Round differs from manifest"
    print(result["status"], len(public), "new audited declarations;", len(bound), "bound artifacts")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--record", action="store_true")
    run(parser.parse_args().record)
