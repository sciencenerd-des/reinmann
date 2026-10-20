"""Verify saved polynomial-sector proofs and the immutable product checkpoint."""
import argparse
import gzip
import hashlib
import importlib.util
import json
from pathlib import Path
import re
import subprocess

ROOT = Path(__file__).resolve().parents[2]
OUT = ROOT / "research/prime_spectral/verification_2026_10_20_polynomial_sector"
SOURCES = ["Reinmann/QuadraticPF.lean", "Reinmann/PolynomialSectorPF.lean"]
NOTE = "research/prime_spectral/POLYNOMIAL_SECTOR_PF_2026_10_20.md"
PARENT = "research/prime_spectral/verification_2026_10_20_products/manifest.json"


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def check(record=False):
    subprocess.run(["python3", "experiments/prime_spectral/verify_finite_pf_products.py"],
                   cwd=ROOT, check=True)
    spec = importlib.util.spec_from_file_location(
        "rectangle_audit", ROOT / "experiments/prime_spectral/verify_xi_rectangle.py")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    names = []
    for name in SOURCES:
        code = module.strip_comments((ROOT / name).read_text())
        assert not re.search(r"\b(sorry|admit|sorryAx|native_decide|axiom)\b", code), name
        namespace = re.search(r"^namespace (\S+)", code, re.M).group(1)
        names += [namespace + "." + n for n in re.findall(r"^theorem (\w+)", code, re.M)]
    assert len(names) == 14
    expected = "import Reinmann.PolynomialSectorPF\n\n" + "".join(
        "#print axioms " + n + "\n" for n in names)
    assert (OUT / "Audit.lean").read_text() == expected
    module.audit(OUT / "axioms.log", names)
    checks = json.loads((OUT / "checks.json").read_text())
    assert len(checks["commands"]) == 6
    for row in checks["commands"]:
        assert row["returncode"] == 0, row
        path = ROOT / row["log"]
        raw = gzip.decompress(path.read_bytes()) if path.suffix == ".gz" else path.read_bytes()
        assert hashlib.sha256(raw).hexdigest() == row["output_sha256"], row
        assert len(raw) == row["output_bytes"], row
        assert "error:" not in raw.decode(), row
    paths = [ROOT / p for p in SOURCES + [NOTE, PARENT]] + [Path(__file__).resolve()]
    paths += [p for p in OUT.iterdir() if p.is_file() and p.name != "manifest.json"]
    result = {
        "parent_products_manifest_sha256": sha(ROOT / PARENT),
        "public_declarations_audited": names,
        "standard_axioms_only": True,
        "arbitrary_minor_quadratic_criterion_proved": True,
        "polynomial_sector_sufficiency_proved": True,
        "sector_polynomial_analytic_limit_proved": True,
        "simple_zero_or_modulus_gap_assumptions_used": False,
        "actual_Xi_canonical_product_identified": False,
        "KatkovaSectorBridge_43_proved": False,
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
    print("Verified 14 polynomial-sector declarations and", len(result["artifacts_sha256"]),
          "bindings; actual Xi product and rank-43 bridge remain open")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--record", action="store_true")
    check(parser.parse_args().record)
