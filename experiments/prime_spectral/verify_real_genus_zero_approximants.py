"""Replay the real-approximant proof receipts and immutable sector checkpoint."""
import argparse
import gzip
import hashlib
import importlib.util
import json
from pathlib import Path
import re
import subprocess

ROOT = Path(__file__).resolve().parents[2]
OUT = ROOT / "research/prime_spectral/verification_2026_10_20_real_approximants"
SOURCES = ["Reinmann/RealGenusZeroApproximants.lean",
           "Reinmann/FoldedSectorGeometry.lean", "Reinmann/XiGenusZeroSector.lean"]
NOTE = "research/prime_spectral/REAL_GENUS_ZERO_APPROXIMANTS_2026_10_20.md"
PARENT = "research/prime_spectral/verification_2026_10_20_polynomial_sector/manifest.json"


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def check(record=False):
    subprocess.run(["python3", "experiments/prime_spectral/verify_polynomial_sector_pf.py"],
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
    assert len(names) == 18 and len(set(names)) == 18
    expected = "import Reinmann.XiGenusZeroSector\n\n" + "".join(
        "#print axioms " + name + "\n" for name in names)
    assert (OUT / "Audit.lean").read_text() == expected
    module.audit(OUT / "axioms.log", names)
    commands = [
        ["lake", "build", "Reinmann.XiGenusZeroSector"],
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
    for log in ["approximants_source.log", "geometry_source.log", "xi_source.log"]:
        assert (OUT / log).read_bytes() == b"", log
    paths = [ROOT / p for p in SOURCES + [NOTE, PARENT, "Reinmann.lean",
             "Reinmann/AxiomAudit.lean", "lakefile.toml", "lean-toolchain"]]
    paths += [Path(__file__).resolve()]
    paths += [p for p in OUT.iterdir() if p.is_file() and p.name != "manifest.json"]
    result = {
        "parent_polynomial_sector_manifest_sha256": sha(ROOT / PARENT),
        "public_declarations_audited": names,
        "standard_axioms_only": True,
        "real_polynomial_approximants_constructed": True,
        "sector_positivity_derived_from_indexed_zeros": True,
        "product_coefficients_proved_real": True,
        "conditional_actual_Xi_product_transfer_proved": True,
        "conditional_strip_indexed_product_bridge_proved": True,
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
    print("Verified 18 real-approximant/geometry/Xi-transfer declarations and",
          len(result["artifacts_sha256"]), "bindings; actual Xi product data remain open")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--record", action="store_true")
    check(parser.parse_args().record)
