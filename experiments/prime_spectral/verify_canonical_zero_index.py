"""Replay canonical-zero-index proof receipts and the immutable approximant checkpoint."""
import argparse
import gzip
import hashlib
import importlib.util
import json
from pathlib import Path
import re
import subprocess

ROOT = Path(__file__).resolve().parents[2]
OUT = ROOT / "research/prime_spectral/verification_2026_10_20_canonical_zero_index"
SOURCES = ["Reinmann/CanonicalZeroIndex.lean",
           "Reinmann/XiZeroCorrespondence.lean", "Reinmann/XiCanonicalProductSector.lean"]
NOTE = "research/prime_spectral/CANONICAL_ZERO_INDEX_2026_10_20.md"
PARENT = "research/prime_spectral/verification_2026_10_20_real_approximants/manifest.json"


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def check(record=False):
    subprocess.run(["python3", "experiments/prime_spectral/verify_real_genus_zero_approximants.py"],
                   cwd=ROOT, check=True)
    spec = importlib.util.spec_from_file_location(
        "rectangle_audit", ROOT / "experiments/prime_spectral/verify_xi_rectangle.py")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    names = []
    for source in SOURCES:
        code = module.strip_comments((ROOT / source).read_text())
        assert not re.search(r"\b(sorry|admit|sorryAx|native_decide|axiom)\b", code), source
        namespace = re.search(r"^namespace (\S+)", code, re.M).group(1)
        names += [namespace + "." + n for n in re.findall(
            r"^\s*(?:@\[[^\]]*\]\s*)*(?:theorem|lemma)\s+(\w+)", code, re.M)]
    assert len(names) == 24 and len(set(names)) == 24
    expected = "import Reinmann.XiCanonicalProductSector\n\n" + "".join(
        "#print axioms " + name + "\n" for name in names)
    assert (OUT / "Audit.lean").read_text() == expected
    module.audit(OUT / "axioms.log", names)
    commands = [
        ["lake", "build", "Reinmann.XiCanonicalProductSector"],
        *[["lake", "env", "lean", source] for source in SOURCES],
        ["lake", "env", "lean", str((OUT / "Audit.lean").relative_to(ROOT))],
        ["lake", "build"], ["bash", "scripts/verify_axiom_clean.sh"],
    ]
    checks = json.loads((OUT / "checks.json").read_text())
    assert [row["argv"] for row in checks["commands"]] == commands
    for row in checks["commands"]:
        assert row["returncode"] == 0 and row["seconds"] >= 0, row
        path = ROOT / row["log"]
        assert path.parent == OUT
        raw = gzip.decompress(path.read_bytes()) if path.suffix == ".gz" else path.read_bytes()
        assert hashlib.sha256(raw).hexdigest() == row["output_sha256"], row
        assert len(raw) == row["output_bytes"], row
        assert "error:" not in raw.decode(), row
    assert "all 1619 audited theorems" in (OUT / "root_guard.log").read_text()
    for log in ["index_source.log", "correspondence_source.log", "assembly_source.log"]:
        assert (OUT / log).read_bytes() == b"", log
    paths = [ROOT / p for p in SOURCES + [NOTE, PARENT, "Reinmann.lean",
             "Reinmann/AxiomAudit.lean", "lakefile.toml", "lean-toolchain"]]
    paths += [Path(__file__).resolve()]
    paths += [p for p in OUT.iterdir() if p.is_file() and p.name != "manifest.json"]
    result = {
        "parent_real_approximants_manifest_sha256": sha(ROOT / PARENT),
        "public_declarations_audited": names,
        "standard_axioms_only": True,
        "canonical_actual_zero_index_constructed": True,
        "exact_analytic_multiplicity_fibers_proved": True,
        "conjugation_indexing_constructed": True,
        "actual_Xi_zero_strip_correspondence_proved": True,
        "canonical_product_conditional_bridge_proved": True,
        "actual_Xi_inverse_zero_summability_proved": False,
        "simple_zero_or_modulus_gap_assumptions_used": False,
        "actual_Xi_canonical_product_data_constructed": False,
        "unconditional_KatkovaSectorBridge_43_proved": False,
        "root_audit_count_unchanged": 1619,
        "height_increased": False, "RH_proved": False,
        "artifacts_sha256": {str(p.relative_to(ROOT)): sha(p) for p in sorted(set(paths))},
    }
    target = OUT / "manifest.json"
    if record:
        if target.exists():
            raise FileExistsError(target)
        target.write_text(json.dumps(result, indent=2) + "\n")
    else:
        assert json.loads(target.read_text()) == result, "Manifest mismatch"
    print("Verified 24 canonical-index/zero-correspondence/bridge declarations and",
          len(result["artifacts_sha256"]), "bindings; actual Xi product identity and summability remain open")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--record", action="store_true")
    check(parser.parse_args().record)
