"""Verify saved finite-PF product proofs, audits and the earlier checkpoint."""
import argparse
import gzip
import hashlib
import importlib.util
import json
from pathlib import Path
import re
import subprocess

ROOT = Path(__file__).resolve().parents[2]
OUT = ROOT / "research/prime_spectral/verification_2026_10_20_products"
SOURCES = ["Reinmann/MatrixMinorProduct.lean", "Reinmann/FinitePFConvolution.lean"]
PRIOR = ["Reinmann/AnalyticPFLimit.lean", "Reinmann/XiTaylorIdentification.lean",
         "Reinmann/XiCenterPositive.lean"]
NOTE = "research/prime_spectral/FINITE_PF_PRODUCTS_2026_10_20.md"
PARENT = "research/prime_spectral/verification_2026_10_20_analytic_limits/manifest.json"
BOUNDARY = ["Reinmann.finitePF_of_coefficientwise_limit",
            "Reinmann.finitePF_of_real_polynomial_locallyUniformLimit",
            "Reinmann.foldedXi_taylor", "Reinmann.foldedXi_zero_re_pos"]


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def check(record=False):
    subprocess.run(["python3", "experiments/prime_spectral/verify_analytic_pf_limits.py"],
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
    expected = "import Reinmann.FinitePFConvolution\n\n" + "".join(
        "#print axioms " + n + "\n" for n in names)
    assert (OUT / "Audit.lean").read_text() == expected
    module.audit(OUT / "axioms.log", names)
    assert re.findall(r"^#print axioms (\S+)", (OUT / "PriorBoundaryAudit.lean").read_text(),
                      re.M) == BOUNDARY
    module.audit(OUT / "prior_boundary.log", BOUNDARY)
    checks = json.loads((OUT / "checks.json").read_text())
    assert len(checks["commands"]) == 8
    for row in checks["commands"]:
        assert row["returncode"] == 0, row
        path = ROOT / row["log"]
        raw = gzip.decompress(path.read_bytes()) if path.suffix == ".gz" else path.read_bytes()
        assert hashlib.sha256(raw).hexdigest() == row["output_sha256"], row
        assert len(raw) == row["output_bytes"], row
        assert "error:" not in raw.decode(), row
    paths = [ROOT / p for p in SOURCES + PRIOR + [NOTE, PARENT]] + [Path(__file__).resolve()]
    paths += [p for p in OUT.iterdir() if p.is_file() and p.name != "manifest.json"]
    result = {
        "parent_analytic_limits_manifest_sha256": sha(ROOT / PARENT),
        "new_public_declarations_audited": names,
        "prior_boundary_declarations_audited": BOUNDARY,
        "standard_axioms_only": True,
        "fixed_rank_product_closure_proved": True,
        "same_rank_reciprocal_transport_used": False,
        "polynomial_quadratic_sector_criterion_proved": False,
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
    print("Verified 14 new product declarations, 4 prior-boundary declarations and",
          len(result["artifacts_sha256"]), "bindings; rank-43 bridge remains open")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--record", action="store_true")
    check(parser.parse_args().record)
