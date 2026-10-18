"""Check the evaluator/Gamma round, pinned publication and prior evidence closure.

Bindings and recorded outcomes are checked here. Replay actual proofs with lake
build and verify_axiom_clean.sh; replay Arb calculations with their two drivers.
"""
import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess
import tarfile

ROOT = Path(__file__).resolve().parents[2]
OUT = ROOT / "research/prime_spectral/verification_2026_10_18_evaluator_comparison"
BASE = ROOT / "research/prime_spectral/verification_2026_10_18_analytic_assembly/manifest.json"
PIN = "7376a2336c3fe9cceaa137b247962dde3ecfc6a3"
CHANGED = {"Reinmann.lean", "Reinmann/AxiomAudit.lean", "paper/formal_split_pair/main.tex",
           "paper/formal_split_pair/main.pdf"}
SCRIPTS = ["xi_evaluator_comparison.py", "xi_reflection_majorant.py", "release_formal_split_pair.py"]
REPORT = ROOT / "research/prime_spectral/XI_EVALUATOR_COMPARISON_2026_10_18.md"


def sha(path):
    with path.open("rb") as stream:
        return hashlib.file_digest(stream, "sha256").hexdigest()


def check(record=False):
    bound = {}
    previous = json.loads(BASE.read_text())
    assert len(previous["artifacts_sha256"]) == 1121
    for name, expected in previous["artifacts_sha256"].items():
        path = OUT / "historical_7376a23" / name if name in CHANGED else ROOT / name
        assert sha(path) == expected, name
        bound[path] = expected

    module = ROOT / "Reinmann/GammaReflectionMajorant.lean"
    audit = (ROOT / "Reinmann/AxiomAudit.lean").read_text()
    declarations = ["Reinmann.GammaReflectionMajorant."+name for name in
                    re.findall(r"^theorem\s+(\w+)", module.read_text(), re.M)]
    assert len(declarations) == 8
    assert all("#print axioms "+name in audit for name in declarations)
    assert "import Reinmann.GammaReflectionMajorant" in (ROOT / "Reinmann.lean").read_text()
    assert not any(re.search(r"^import Reinmann$", p.read_text(), re.M)
                   for p in (ROOT / "Reinmann").glob("*.lean"))
    assert len(re.findall(r"^#print axioms", audit, re.M)) == 372
    build = (OUT / "full_build.log").read_text()
    assert "Build completed successfully (3599 jobs)." in build and "error:" not in build
    proof_audit = (OUT / "axiom_audit.log").read_text()
    assert "all 372 audited theorems depend only on [propext, Classical.choice, Quot.sound]" in proof_audit
    assert "AXIOM-CLEAN:" in proof_audit and "FAIL:" not in proof_audit

    ci = json.loads((OUT / "ci_7376a23.json").read_text())
    assert ci["head_sha"] == PIN and ci["status"] == "completed" and ci["conclusion"] == "success"
    comparison = json.loads((OUT / "comparison.json").read_text())
    assert comparison["source_sha256"] == sha(ROOT / "experiments/prime_spectral/xi_evaluator_comparison.py")
    assert comparison["centre"] == ["1/2", "14"] and comparison["jet_degree"] == 16
    assert comparison["timing_repeats"] == 7 and comparison["timing_statistic"] == "median"
    assert all(row["all_17_overlap_builtin_reference"] for row in comparison["rows"])
    assert all(len(row["ordinary_jet"]) == 17 and len(row["timings_seconds"]) == 7
               for row in comparison["rows"])
    mellin = next(row for row in comparison["rows"] if row.get("panel_degree") == 12)
    em = next(row for row in comparison["rows"] if row.get("zeta_corrections") == 6)
    assert mellin["all_17_complex_radii_below_1e_8"] and em["all_17_complex_radii_below_1e_8"]
    assert mellin["panels"] == 20 and em["terms"] == 10
    assert em["point_jet_series_exp_log_calls"] < mellin["point_jet_series_exp_log_calls"]
    assert em["seconds"] < mellin["seconds"]
    tile = comparison["selected_external_hard_tile"]
    assert tile["status"] == "external_complete_hard_tile" and tile["seconds"] > 0
    assert not tile["Lean_complete_hard_tile_certified"]
    majorant = json.loads((OUT / "reflection_majorant.json").read_text())
    assert majorant["source_sha256"] == sha(ROOT / "experiments/prime_spectral/xi_reflection_majorant.py")
    assert majorant["zeta_source_sha256"] == comparison["source_sha256"]
    assert majorant["arcs"] == 1024 and not majorant["Lean_uniform_numeric_majorant_certified"]

    publication = json.loads((OUT / "formalization_publication_receipt.json").read_text())
    assert publication["status"] == "published_and_public_files_verified"
    assert publication["id"] == 23449490 and publication["doi"] == "10.5281/zenodo.23449490"
    assert publication["source_commit"] == PIN and publication["public_files_verified"]
    assert publication["anonymous_public_file_downloads_verified"]
    release = OUT / "release"
    for item in publication["files"]:
        path = release / item["name"]
        assert path.stat().st_size == item["bytes"]
        assert sha(path) == item["sha256"] == item["download_sha256"]
    assert len(publication["files"]) == 4
    assert sha(release / "formal-split-pair.pdf") == sha(ROOT / "paper/formal_split_pair/main.pdf")
    with tarfile.open(release / "formal-split-pair-source-7376a23.tar.gz") as archive:
        inner = json.loads(archive.extractfile("SOURCE_MANIFEST.json").read())
        assert inner["theorem_source_commit"] == PIN and inner["audited_declarations"] == 364
        for name, expected in inner["files_sha256"].items():
            content = archive.extractfile(name).read()
            assert hashlib.sha256(content).hexdigest() == expected, name
            if name.startswith("source/"):
                original = subprocess.check_output(["git", "show", PIN+":"+name.removeprefix("source/")], cwd=ROOT)
                assert original == content, name
        assert archive.extractfile("paper/main.tex").read() == (ROOT / "paper/formal_split_pair/main.tex").read_bytes()
    visual = json.loads((OUT / "paper_visual_review.json").read_text())
    assert visual["pages_rendered_and_inspected"] == 5
    assert visual["pdf_sha256"] == sha(ROOT / "paper/formal_split_pair/main.pdf")
    assert not visual["substantive_external_human_review_completed"]

    for path in OUT.rglob("*"):
        if path.is_file() and path.name != "manifest.json":
            bound[path] = sha(path)
    for name in CHANGED:
        bound[ROOT / name] = sha(ROOT / name)
    for path in [BASE, module, REPORT, Path(__file__).resolve(), ROOT / "paper/formal_split_pair/RELEASE.md"]:
        bound[path] = sha(path)
    for name in SCRIPTS:
        path = ROOT / "experiments/prime_spectral" / name
        bound[path] = sha(path)
    result = {
        "status": "evaluator_comparison_Gamma_anchors_and_formalization_release_verified",
        "base_commit": PIN, "base_CI_conclusion": "success", "base_CI_url": ci["html_url"],
        "new_audited_declarations": declarations, "total_audited_declarations": 372,
        "new_round_remote_CI_verified": False,
        "selected_external_evaluator": "Euler_Maclaurin_and_shifted_Stirling",
        "Arb_Mellin_degree12_seconds": mellin["seconds"], "Arb_EM_six_corrections_seconds": em["seconds"],
        "Arb_complete_hard_tile_seconds": tile["seconds"], "Lean_complete_hard_tile_certified": False,
        "Lean_complete_hard_tile_seconds": None, "thirty_five_Lean_tiles_seconds": None,
        "Gamma_reflection_anchors_and_Beta_comparison_proved": True,
        "Lean_explicit_EM_and_complex_Stirling_remainders_proved": False,
        "Lean_uniform_numeric_Xi_majorant_proved": False, "full_zero_free_rectangle_certified": False,
        "formalization_preprint_DOI": publication["doi"], "formalization_source_pin": PIN,
        "formalization_source_audited_declarations": 364, "external_human_review_claimed": False,
        "published_DH_scientific_files_unchanged": True, "PF_implies_RH_bridges_changed": False,
        "scope": "Explicit external evaluator comparison and local tile, eight Lean Gamma theorems, and a published unreviewed standalone formalization preprint. No Lean hard tile, DH atlas, zero-free rectangle or RH proof.",
        "artifacts_sha256": {str(path.relative_to(ROOT)): value for path, value in sorted(bound.items())}}
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
