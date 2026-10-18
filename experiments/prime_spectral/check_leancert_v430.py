"""Isolated, kernel-only exp/log check against a frozen LeanCert v4.30 source.

Does not edit lakefile.toml, lake-manifest.json or the repository toolchain.
The thin interval API avoids compiler-trust axioms in the general evaluator.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import tarfile
import time
import urllib.request

ROOT = Path(__file__).resolve().parents[2]
PIN = "5a59804aa7c499f81ffd5eedf2a2cc5f9e8766d1"
ARCHIVE_SHA256 = "ee0dc3770c7cd56f0e91f201841e82f7b44a994d64ade3fdebec14c0326d25a5"
PROOF = ROOT / "research/prime_spectral/verification_2026_10_18_first_tile/LeanCertCompatibility.lean"


def run(output, source=None):
    output = output.resolve()
    output.mkdir(parents=True, exist_ok=True)
    if source is None:
        archive = output / "source.tar.gz"
        if not archive.exists():
            urllib.request.urlretrieve(f"https://codeload.github.com/alerad/leancert/tar.gz/{PIN}", archive)
        assert hashlib.sha256(archive.read_bytes()).hexdigest() == ARCHIVE_SHA256
        with tarfile.open(archive) as tar:
            tar.extractall(output, filter="data")
        source = output / f"leancert-{PIN}"
    source = source.resolve()
    assert (source / "lean-toolchain").read_text().strip() == "leanprover/lean4:v4.30.0"
    modules = []
    seen = set()
    mathlib = set()

    def visit(module):
        if module in seen:
            return
        seen.add(module)
        p = source / (module.replace(".", "/") + ".lean")
        for dep in re.findall(r"^(?:public )?import\s+(\S+)", p.read_text(), re.M):
            if dep.startswith("LeanCert."):
                visit(dep)
            elif dep.startswith("Mathlib."):
                mathlib.add(dep)
        modules.append(module)

    visit("LeanCert.Core.IntervalRat.Taylor")
    # Build missing local Mathlib artifacts before the isolated source compilation.
    subprocess.run(["lake", "build", *sorted(mathlib)], cwd=ROOT, check=True,
                   stdout=(output / "mathlib_build.log").open("w"), stderr=subprocess.STDOUT)
    env = os.environ.copy()
    paths = subprocess.check_output(["lake", "env", "printenv", "LEAN_PATH"], cwd=ROOT).decode().strip()
    lean = subprocess.check_output(["lake", "env", "which", "lean"], cwd=ROOT).decode().strip()
    build = output / "olean"
    env["LEAN_PATH"] = str(build) + os.pathsep + paths
    records = []
    for module in modules:
        src = source / (module.replace(".", "/") + ".lean")
        target = build / (module.replace(".", "/") + ".olean")
        target.parent.mkdir(parents=True, exist_ok=True)
        start = time.monotonic()
        proc = subprocess.run([lean, "--root=" + str(source), "-o", str(target), str(src)],
                              cwd=ROOT, env=env, capture_output=True, text=True)
        (output / (module + ".log")).write_text(proc.stdout + proc.stderr)
        records.append({"module": module, "seconds": time.monotonic() - start,
                        "exit_code": proc.returncode, "source_sha256": hashlib.sha256(src.read_bytes()).hexdigest()})
        if proc.returncode:
            raise RuntimeError(f"Compilation failed: {module}; see {output}")
    start = time.monotonic()
    proc = subprocess.run([lean, str(PROOF)], cwd=ROOT, env=env, capture_output=True, text=True)
    (output / "compatibility.log").write_text(proc.stdout + proc.stderr)
    lines = [line for line in proc.stdout.splitlines() if "depends on axioms" in line]
    assert proc.returncode == 0, proc.stdout + proc.stderr
    assert len(lines) == 2 and all(line.endswith("[propext, Classical.choice, Quot.sound]") for line in lines), lines
    result = {"status": "kernel_only_exp_log_compatible", "pin": PIN, "lean": "v4.30.0",
              "mathlib": "v4.30.0", "archive_sha256": ARCHIVE_SHA256,
              "proof_sha256": hashlib.sha256(PROOF.read_bytes()).hexdigest(),
              "proof_seconds": time.monotonic() - start, "modules": records,
              "axiom_audit": lines, "project_dependency_files_changed": False,
              "scope": "Thin rational Taylor interval API only; does not certify arbitrary LeanCert tactics or a Xi rectangle."}
    (output / "receipt.json").write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps({k: v for k, v in result.items() if k != "modules"}, indent=2))


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=ROOT / "tmp/leancert-v430-compatibility")
    parser.add_argument("--source-root", type=Path)
    args = parser.parse_args()
    run(args.output, args.source_root)
