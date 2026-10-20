"""Check the saved analytic finite-PF limit proofs and their immutable parent."""
import argparse
import hashlib
import importlib.util
import json
from pathlib import Path
import re
import subprocess

ROOT = Path(__file__).resolve().parents[2]
OUT = ROOT / "research/prime_spectral/verification_2026_10_20_analytic_limits"
SOURCES = ["Reinmann/FinitePFAnalyticLimits.lean", "Reinmann/GenusZeroProductLimits.lean"]
NOTE = "research/prime_spectral/FINITE_PF_ANALYTIC_LIMITS_2026_10_20.md"
PARENT = "research/prime_spectral/verification_2026_10_20_sector/manifest.json"


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def check(record=False):
    subprocess.run(["python3", "experiments/prime_spectral/verify_sector_start.py"],
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
        names.extend(namespace + "." + theorem for theorem in
                     re.findall(r"^theorem (\w+)", code, re.M))
    assert len(names) == 8
    audit_source = "import Reinmann.GenusZeroProductLimits\n\n" + "".join(
        "#print axioms " + name + "\n" for name in names)
    assert (OUT / "Audit.lean").read_text() == audit_source
    module.audit(OUT / "axioms.log", names)
    checks = json.loads((OUT / "checks.json").read_text())
    assert len(checks["commands"]) == 6
    for row in checks["commands"]:
        assert row["returncode"] == 0, row
        assert "error:" not in (ROOT / row["log"]).read_text(), row
    paths = [ROOT / p for p in SOURCES + [NOTE, PARENT]] + [Path(__file__).resolve()]
    paths += [p for p in OUT.iterdir() if p.is_file() and p.name != "manifest.json"]
    result = {
        "parent_sector_manifest_sha256": sha(ROOT / PARENT),
        "public_declarations_audited": names,
        "standard_axioms_only": True,
        "actual_Xi_canonical_product_identified": False,
        "KatkovaSectorBridge_43_proved": False,
        "height_increased": False,
        "RH_proved": False,
        "artifacts_sha256": {str(p.relative_to(ROOT)): sha(p) for p in sorted(set(paths))},
    }
    target = OUT / "manifest.json"
    if record:
        if target.exists():
            raise FileExistsError(target)
        target.write_text(json.dumps(result, indent=2) + "\n")
    else:
        assert json.loads(target.read_text()) == result, "Manifest mismatch"
    print("Verified eight analytic limit declarations and", len(result["artifacts_sha256"]),
          "bindings; polynomial sector and actual Xi product remain open")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--record", action="store_true")
    check(parser.parse_args().record)
