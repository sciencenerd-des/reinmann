"""Verify the attributed PNT+ backport and local actual-Xi PF43 proof receipts."""
import argparse
import difflib
import gzip
import hashlib
import importlib.util
import io
import json
from pathlib import Path
import re
import subprocess
import tarfile

ROOT = Path(__file__).resolve().parents[2]
OUT = ROOT / "research/prime_spectral/verification_2026_10_20_pnt_hadamard"
VENDOR = ROOT / "Reinmann/PNTPlus"
NOTE = "research/prime_spectral/PNT_HADAMARD_BACKPORT_2026_10_20.md"
PARENT = "research/prime_spectral/verification_2026_10_20_canonical_zero_index/manifest.json"
OWN = ["Reinmann/XiHadamardProduct.lean", "Reinmann/XiFinitePFCertified.lean"]
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
PIN = "127b50e33f6033e2147921167a117af96d9ba4ea"


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def check(record=False):
    subprocess.run(["python3", "experiments/prime_spectral/verify_canonical_zero_index.py"],
                   cwd=ROOT, check=True)
    spec = importlib.util.spec_from_file_location(
        "rectangle_audit", ROOT / "experiments/prime_spectral/verify_xi_rectangle.py")
    scanner = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(scanner)
    upstream = json.loads((VENDOR / "UPSTREAM.json").read_text())
    assert upstream["commit"] == PIN
    assert upstream["upstream_toolchain"] == "leanprover/lean4:v4.35.0"
    assert upstream["local_toolchain"] == (ROOT / "lean-toolchain").read_text().strip()
    assert upstream["local_toolchain"] == "leanprover/lean4:v4.30.0"
    files = upstream["files"]
    assert len(files) == 61 and len({r["local_path"] for r in files}) == 61
    # Read archive members as data; never extract or execute upstream material.
    with tarfile.open(fileobj=io.BytesIO((OUT / "upstream_sources.tar.gz").read_bytes()),
                      mode="r:gz") as tf:
        members = tf.getmembers()
        assert all(m.isfile() for m in members)
        assert len({m.name for m in members}) == len(members) == 73
        archived = {m.name: tf.extractfile(m).read() for m in members}
    assert archived["pnt/LICENSE"] == (VENDOR / "LICENSE").read_bytes()
    assert b"Apache License" in archived["pnt/LICENSE"]
    patch = []
    expected_modules = set()
    for row in files:
        raw = archived["pnt/" + row["upstream_path"]]
        assert hashlib.sha256(raw).hexdigest() == row["upstream_sha256"]
        local = ROOT / row["local_path"]
        assert local.is_relative_to(VENDOR)
        assert sha(local) == row["local_sha256"], local
        # Preserve every existing copyright/license/author preamble. Ten
        # upstream helper files begin with module and have no such preamble.
        if raw.startswith(b"/-\nCopyright"):
            assert raw.split(b"-/", 1)[0] == local.read_bytes().split(b"-/", 1)[0]
        else:
            assert raw.startswith(b"module\n") and local.read_bytes().startswith(b"module\n")
        patch += list(difflib.unified_diff(
            raw.decode().splitlines(keepends=True), local.read_text().splitlines(keepends=True),
            fromfile="a/" + row["upstream_path"], tofile="b/" + row["local_path"]))
        expected_modules.add(row["local_path"][:-5].replace("/", "."))
    assert gzip.decompress((OUT / "backport.patch.gz").read_bytes()).decode() == "".join(patch)
    assert sum(len(archived["pnt/" + r["upstream_path"]].splitlines()) for r in files) == 14306
    expected_modules |= {p[:-5].replace("/", ".") for p in OWN}
    for source in [r["local_path"] for r in files] + OWN:
        code = scanner.strip_comments((ROOT / source).read_text())
        assert not re.search(r"\b(sorry|admit|sorryAx|axiom|native_decide|unsafe|implemented_by|skipKernelTC)\b", code), source
        assert "import PrimeNumberTheoremAnd." not in code, source
        for module in re.findall(r"^(?:public\s+)?(?:meta\s+)?import\s+([\w.]+)", code, re.M):
            if module.startswith("Reinmann.PNTPlus."):
                assert module in expected_modules, (source, module)
    raw = (OUT / "axioms.log").read_text()
    assert "error:" not in raw
    modules = re.findall(r"^AUDIT_MODULE (\S+)$", raw, re.M)
    assert len(modules) == 63 and set(modules) == expected_modules
    flat = re.sub(r"\n\s+", " ", raw)
    rows = re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", flat)
    empty = re.findall(r"'([^']+)' does not depend on any axioms", flat)
    assert all(set(map(str.strip, a.split(","))) <= ALLOWED for _, a in rows)
    names = [n for n, _ in rows] + empty
    assert len(names) == 831 and len(set(names)) == 825
    headline = ["Reinmann.XiHadamardProduct." + n for n in
                ["foldedXi_order", "summable_inverse_zeros", "foldedXi_product", "katkovaSectorBridge"]]
    headline += ["Reinmann.XiFinitePFCertified.finitePF43", "Reinmann.XiFinitePFCertified.finitePF58"]
    assert all(names.count(n) == 2 for n in headline)
    expected_commands = [["lake", "build", "Reinmann.XiFinitePFCertified"]]
    expected_commands += [["lake", "env", "lean", r["local_path"]] for r in files]
    expected_commands += [["lake", "env", "lean", p] for p in OWN]
    expected_commands += [["lake", "env", "lean", str((OUT / p).relative_to(ROOT))]
                          for p in ["Audit.lean", "TypeCheck.lean"]]
    expected_commands += [["lake", "build"], ["bash", "scripts/verify_axiom_clean.sh"]]
    checks = json.loads((OUT / "checks.json").read_text())
    assert [r["argv"] for r in checks["commands"]] == expected_commands
    assert len(checks["commands"]) == 68
    for row in checks["commands"]:
        assert row["returncode"] == 0 and row["seconds"] >= 0, row
        log = ROOT / row["log"]
        assert log.parent == OUT
        data = gzip.decompress(log.read_bytes()) if log.suffix == ".gz" else log.read_bytes()
        assert len(data) == row["output_bytes"], row
        assert hashlib.sha256(data).hexdigest() == row["output_sha256"], row
        assert "error:" not in data.decode(), row
    assert "all 1619 audited theorems" in (OUT / "root_guard.log").read_text()
    for p in ["xi_product_source.log", "finite_pf_source.log", "types.log"]:
        assert (OUT / p).read_bytes() == b"", p
    paths = [ROOT / p for p in OWN + [NOTE, PARENT, "Reinmann.lean",
             "Reinmann/AxiomAudit.lean", "lakefile.toml", "lean-toolchain"]]
    paths += [p for p in VENDOR.rglob("*") if p.is_file()]
    paths += [p for p in OUT.iterdir() if p.is_file() and p.name != "manifest.json"]
    paths += [Path(__file__).resolve()]
    result = {
        "parent_canonical_index_manifest_sha256": sha(ROOT / PARENT),
        "upstream_PNT_commit": PIN,
        "ported_modules": 61, "upstream_source_lines": 14306,
        "audited_modules": sorted(modules), "audited_theorems": sorted(set(names)),
        "audited_theorem_count": 825, "standard_axioms_only": True,
        "actual_folded_Xi_order_three_fourths_proved": True,
        "actual_folded_Xi_inverse_zero_summability_proved": True,
        "actual_folded_Xi_normalized_genus_zero_identity_proved": True,
        "KatkovaSectorBridge_all_positive_fixed_ranks_proved": True,
        "actual_finitePF43_proved_without_theorem_hypotheses": True,
        "finitePF58_retains_external_quasiRH_input": True,
        "external_OpenAI_proof_rebuilt_locally": False,
        "root_audit_count_unchanged": 1619,
        "new_modules_covered_by_hosted_CI": False,
        "RH_proved": False, "unbounded_rank_PF_proved": False,
        "height_increased": False, "published_versions_changed": False,
        "artifacts_sha256": {str(p.relative_to(ROOT)): sha(p) for p in sorted(set(paths))},
    }
    target = OUT / "manifest.json"
    if record:
        if target.exists():
            raise FileExistsError(target)
        target.write_text(json.dumps(result, indent=2) + "\n")
    else:
        assert json.loads(target.read_text()) == result, "Manifest mismatch"
    print("Verified 61-module backport, 825 theorem audits and", len(result["artifacts_sha256"]),
          "bindings; PF43 is locally proved, PF58 retains external quasiRH, no RH claim")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--record", action="store_true")
    check(parser.parse_args().record)
