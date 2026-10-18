"""Package, verify and optionally publish the standalone formalization preprint.

The theorem sources are frozen at 7376a23. The revised manuscript is separately
bound. Credentials are header-only; receipts contain no credentials. A resumed
upload uses its saved draft id and never creates a duplicate record.
"""
import argparse
import gzip
import hashlib
import io
import json
from pathlib import Path
import subprocess
import tarfile
from urllib.parse import urlparse

ROOT = Path(__file__).resolve().parents[2]
PIN = "7376a2336c3fe9cceaa137b247962dde3ecfc6a3"
OUT = ROOT / "research/prime_spectral/verification_2026_10_18_evaluator_comparison"
TITLE = "Finite and analytic split-pair oscillation and the Toeplitz–Jacobi bridge"
README = """Finite and analytic split-pair oscillation and the Toeplitz-Jacobi bridge
Unreviewed formalization preprint, 18 October 2026

The theorem sources are pinned to Git commit
7376a2336c3fe9cceaa137b247962dde3ecfc6a3
https://github.com/sciencenerd-des/reinmann/tree/7376a2336c3fe9cceaa137b247962dde3ecfc6a3
Lean and Mathlib: v4.30.0. CI for this exact commit passed:
https://github.com/sciencenerd-des/reinmann/actions/runs/39113141784
The build and 364-declaration axiom audit use only propext, Classical.choice,
and Quot.sound. Source scanning found no unfinished proofs or project axioms.

1. Check each public file's SHA256 against FORMAL_SPLIT_PAIR_RELEASE.json.
2. Extract formal-split-pair-source-7376a23.tar.gz into a new directory.
3. Check the extracted files against SOURCE_MANIFEST.json (standard SHA256).
4. Install elan, enter source/, then run:
   lake exe cache get
   lake build
   bash scripts/verify_axiom_clean.sh
The lake manifest pins dependencies; cache/build commands need network access
on a first run. The code is Apache-2.0; the paper is CC-BY-4.0.

The revised manuscript is included separately from the pinned theorem sources.
It states simple selected zeros and an isolated boundary-pair hypothesis.
No general multiplicity/tie theorem, Lean DH zero atlas, low zero-free rectangle,
or RH proof is claimed. The published DH controls motivate the work but are
external numerical certificates, not a Lean instantiation of the theorem.
AI assistance is disclosed. No completed external human review is claimed.
"""


def digest(data, algorithm="sha256"):
    return hashlib.new(algorithm, data).hexdigest()


def package(directory):
    directory.mkdir(parents=True, exist_ok=True)
    paths = subprocess.check_output([
        "git", "ls-tree", "-r", "--name-only", PIN, "--", "Reinmann", "Reinmann.lean",
        "LICENSE", "lean-toolchain", "lakefile.toml", "lake-manifest.json",
        "scripts/verify_axiom_clean.sh"], cwd=ROOT).decode().splitlines()
    assert len(paths) > 140 and "Reinmann/AnalyticToeplitzJacobi.lean" in paths
    files = {"source/" + name: subprocess.check_output(["git", "show", PIN+":"+name], cwd=ROOT)
             for name in paths}
    paper = ROOT / "paper/formal_split_pair"
    files["paper/main.tex"] = (paper / "main.tex").read_bytes()
    files["paper/main.pdf"] = (paper / "main.pdf").read_bytes()
    assert b"We do not prove RH or a low zero-free rectangle" in files["paper/main.tex"]
    assert b"364" in files["paper/main.tex"] and PIN.encode() in files["paper/main.tex"]
    files["README_RELEASE.txt"] = README.encode()
    ci = json.loads((OUT / "ci_7376a23.json").read_text())
    assert ci["head_sha"] == PIN and ci["status"] == "completed" and ci["conclusion"] == "success"
    files["verification/ci_7376a23.json"] = json.dumps(ci, indent=2).encode()+b"\n"
    base = ROOT / "research/prime_spectral/verification_2026_10_18_analytic_assembly"
    for name in ["axiom_audit.log", "full_build.log"]:
        files["verification/"+name] = (base / name).read_bytes()
    manifest = {"theorem_source_commit": PIN, "audited_declarations": 364,
                "manuscript_status": "unreviewed_preprint",
                "files_sha256": {name: digest(data) for name, data in sorted(files.items())}}
    files["SOURCE_MANIFEST.json"] = json.dumps(manifest, indent=2).encode()+b"\n"
    buffer = io.BytesIO()
    with tarfile.open(fileobj=buffer, mode="w", format=tarfile.PAX_FORMAT) as archive:
        for name, data in sorted(files.items()):
            info = tarfile.TarInfo(name)
            info.size, info.mtime = len(data), 0
            info.mode = 0o755 if name.endswith(".sh") else 0o644
            archive.addfile(info, io.BytesIO(data))
    source = directory / "formal-split-pair-source-7376a23.tar.gz"
    source.write_bytes(gzip.compress(buffer.getvalue(), mtime=0))
    with tarfile.open(source) as archive:
        assert set(archive.getnames()) == set(files)
        for name, expected in manifest["files_sha256"].items():
            assert digest(archive.extractfile(name).read()) == expected, name
    pdf = directory / "formal-split-pair.pdf"
    pdf.write_bytes(files["paper/main.pdf"])
    readme = directory / "README_RELEASE.txt"
    readme.write_text(README)
    bound = {p.name: {"bytes": p.stat().st_size, "sha256": digest(p.read_bytes())}
             for p in [pdf, source, readme]}
    outer = {"status": "formalization_release_files_verified", "source_commit": PIN,
             "audited_declarations": 364, "files": bound,
             "scope": "Standalone simple-zero isolated-pair theorem; no RH proof, formal DH atlas or zero-free rectangle."}
    release = directory / "FORMAL_SPLIT_PAIR_RELEASE.json"
    release.write_text(json.dumps(outer, indent=2)+"\n")
    return [pdf, source, readme, release]


def publish(files, do_publish):
    import requests
    session = requests.Session()
    session.headers["Authorization"] = "Bearer " + Path.home().joinpath(".config/zenodo/token").read_text().strip()

    def request(method, url, **kwargs):
        if urlparse(url).hostname != "zenodo.org":
            raise ValueError("Unexpected Zenodo host")
        try:
            response = session.request(method, url, timeout=(10, 60), **kwargs)
        except requests.RequestException as error:
            raise RuntimeError(type(error).__name__) from None
        if response.status_code not in (200, 201, 202):
            raise RuntimeError(f"Zenodo HTTP {response.status_code}")
        return response

    receipt_path = OUT / "formalization_publication_receipt.json"
    if receipt_path.exists():
        receipt = json.loads(receipt_path.read_text())
        identifier = receipt["id"]
    else:
        owned = request("GET", "https://zenodo.org/api/deposit/depositions", params={"size": 100}).json()
        matches = [item for item in owned if item.get("metadata", {}).get("title") == TITLE]
        if len(matches) > 1:
            raise ValueError("Multiple matching records; do not create a duplicate")
        draft = matches[0] if matches else request("POST", "https://zenodo.org/api/deposit/depositions", json={}).json()
        identifier = draft["id"]
        receipt = {"id": identifier, "status": "created_unpublished_draft"}
        receipt_path.write_text(json.dumps(receipt, indent=2)+"\n")
    if identifier == 23401370:
        raise ValueError("Refusing to modify the earlier DH record")
    base = f"https://zenodo.org/api/deposit/depositions/{identifier}"
    draft = request("GET", base).json()
    def verify_public():
        record = requests.get(f"https://zenodo.org/api/records/{identifier}", timeout=(10, 60))
        if record.status_code != 200:
            raise RuntimeError("Publication submitted; public record not yet verified")
        public = record.json()
        assert public["metadata"]["title"] == TITLE
        assert {item["key"] for item in public["files"]} == {p.name for p in files}
        for item in public["files"]:
            path = next(p for p in files if p.name == item["key"])
            url = item["links"]["self"]
            assert urlparse(url).hostname == "zenodo.org"
            response = requests.get(url, timeout=(10, 60))
            if response.status_code != 200:
                raise RuntimeError("Anonymous public-file download failed")
            downloaded = response.content
            assert digest(downloaded) == digest(path.read_bytes())
        receipt.update(status="published_and_public_files_verified", doi=public["doi"],
                       record_url=f"https://zenodo.org/records/{identifier}", public_files_verified=True,
                       anonymous_public_file_downloads_verified=True)
        receipt_path.write_text(json.dumps(receipt, indent=2)+"\n")
        print("Published and public-file verified:", receipt["doi"], receipt["record_url"], flush=True)

    if draft["submitted"]:
        verify_public()
        return
    assert draft["state"] == "unsubmitted"
    metadata = {
        "upload_type": "publication", "publication_type": "preprint", "publication_date": "2026-10-18",
        "title": TITLE, "creators": [{"name": "Mondal, Biswajit"}], "version": "1.0.0",
        "access_right": "open", "license": "cc-by-4.0", "prereserve_doi": True,
        "description": "<p><strong>Unreviewed formalization preprint. No completed external human peer review is claimed.</strong></p><p>A Lean formalization of finite and analytic split-pair oscillation and the actual Taylor-series Toeplitz–Jacobi bridge. The entire-function theorem constructs the reciprocal simple-pole remainder and coefficient identity, proves a mixed-row determinant bound, derives dominant subset gaps from an isolated boundary conjugate pair, and transfers both signs to original ordinary Taylor-coefficient minors. The theorem assumes distinct simple selected zeros, finite closed-disk zero coverage and an isolated modulus tie; it does not replace general PF-to-RH bridges.</p><p>The active Lean sources are pinned to public commit 7376a2336c3fe9cceaa137b247962dde3ecfc6a3, using Lean/Mathlib v4.30.0. CI passes the full build and 364-declaration standard-axiom audit. The supplement includes those sources, the revised manuscript, audit/CI receipts and SHA256 bindings. AI assistance is disclosed.</p><p>The published Davenport–Heilbronn controls motivate the work. A Lean-certified DH zero atlas and a formal shift-44 application remain open. No proof of RH, complete hard Xi tile or low zero-free rectangle is claimed.</p>",
        "keywords": ["Toeplitz minors", "total positivity", "entire functions", "formal verification", "Lean", "pole asymptotics"],
        "related_identifiers": [
            {"identifier": "https://github.com/sciencenerd-des/reinmann/tree/"+PIN, "relation": "isSupplementedBy", "resource_type": "software"},
            {"identifier": "10.5281/zenodo.23401370", "relation": "references", "resource_type": "publication-preprint"}]}
    draft = request("PUT", base, json={"metadata": metadata}).json()
    bucket = draft["links"]["bucket"]
    checks = []
    for path in files:
        data = path.read_bytes()
        item = request("PUT", bucket+"/"+path.name, data=data).json()
        assert item["checksum"].removeprefix("md5:") == digest(data, "md5")
        assert int(item["size"]) == len(data)
        downloaded = request("GET", bucket+"/"+path.name).content
        assert digest(downloaded) == digest(data) and len(downloaded) == len(data)
        checks.append({"name": path.name, "bytes": len(data), "sha256": digest(data), "download_sha256": digest(downloaded)})
        print("Uploaded and downloaded SHA256-verified:", path.name, flush=True)
    draft = request("GET", base).json()
    assert not draft["submitted"] and draft["state"] == "unsubmitted"
    assert draft["metadata"]["title"] == TITLE
    assert {item["filename"] for item in draft["files"]} == {p.name for p in files}
    receipt.update(status="draft_all_files_download_verified", files=checks,
                   reserved_doi=draft["metadata"]["prereserve_doi"]["doi"], source_commit=PIN)
    receipt_path.write_text(json.dumps(receipt, indent=2)+"\n")
    if not do_publish:
        print("Verified unpublished draft:", identifier)
        return
    published = request("POST", base+"/actions/publish").json()
    assert published["submitted"] and published["state"] == "done"
    verify_public()


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output-dir", type=Path, default=ROOT / "tmp/formalization-release-2026-10-18")
    parser.add_argument("--upload", action="store_true")
    parser.add_argument("--publish", action="store_true")
    args = parser.parse_args()
    paths = package(args.output_dir)
    print("Packaged and verified:", len(paths), "release files", flush=True)
    if args.upload or args.publish:
        publish(paths, args.publish)
