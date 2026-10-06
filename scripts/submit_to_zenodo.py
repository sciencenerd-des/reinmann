#!/usr/bin/env python3
"""Prepare Zenodo depositions as drafts.  Publishing is left to the web UI.

Two-step workflow, so the reserved DOI can be printed in the PDF:

  # 1. create a draft (new record, or a new version of an existing one) and
  #    reserve its DOI
  python3 scripts/submit_to_zenodo.py reserve --metadata paper/zenodo_weil_tail.json
  python3 scripts/submit_to_zenodo.py reserve --metadata zenodo.json --new-version-of 21416395

  # 2. after the DOI is in the manuscript, upload the files to that draft
  python3 scripts/submit_to_zenodo.py upload --deposition ID --file a.pdf --file b.tar.gz

The token is read from ZENODO_TOKEN or from ~/.config/zenodo/token (chmod 600).
It is never accepted on the command line, where it would land in shell history.
"""
import argparse
import json
import os
import stat
import sys

import requests

TOKEN_FILE = os.path.expanduser("~/.config/zenodo/token")


def load_token():
    token = os.environ.get("ZENODO_TOKEN")
    if token:
        return token.strip()
    if os.path.exists(TOKEN_FILE):
        mode = os.stat(TOKEN_FILE).st_mode
        if mode & (stat.S_IRWXG | stat.S_IRWXO):
            sys.exit(f"Error: {TOKEN_FILE} is readable by others; run chmod 600 on it.")
        with open(TOKEN_FILE) as f:
            return f.read().strip()
    sys.exit(f"Error: set ZENODO_TOKEN or write the token to {TOKEN_FILE} (chmod 600).")


def check(r, ok, what):
    if r.status_code not in ok:
        sys.exit(f"Failed to {what}: {r.status_code} - {r.text}")
    return r.json() if r.content else {}


def reserve(args, base, params):
    with open(args.metadata) as f:
        metadata = json.load(f)
    metadata["prereserve_doi"] = True
    dep_url = f"{base}/api/deposit/depositions"

    if args.new_version_of:
        print(f"Opening a new version of record {args.new_version_of}...")
        r = requests.post(f"{dep_url}/{args.new_version_of}/actions/newversion", params=params)
        draft_url = check(r, (201,), "create new version")["links"]["latest_draft"]
        dep = check(requests.get(draft_url, params=params), (200,), "read new-version draft")
        # A new version inherits the previous files; the release replaces them all.
        for f in dep.get("files", []):
            print(f"Removing inherited file {f['filename']}...")
            check(requests.delete(f"{draft_url}/files/{f['id']}", params=params),
                  (204,), "remove inherited file")
    else:
        print("Creating deposition draft...")
        dep = check(requests.post(dep_url, params=params, json={}), (201,), "create deposition")

    dep_id = dep["id"]
    r = requests.put(f"{dep_url}/{dep_id}", params=params, json={"metadata": metadata})
    dep = check(r, (200,), "update metadata")
    doi = dep["metadata"]["prereserve_doi"]["doi"]
    print(f"Draft ID:     {dep_id}")
    print(f"Reserved DOI: {doi}")
    print(f"Draft URL:    {base}/deposit/{dep_id}")


def upload(args, base, params):
    dep_url = f"{base}/api/deposit/depositions/{args.deposition}"
    dep = check(requests.get(dep_url, params=params), (200,), "read deposition")
    if dep.get("submitted"):
        sys.exit("Error: this deposition is already published; files cannot change.")
    existing = {f["filename"]: f["id"] for f in dep.get("files", [])}
    bucket_url = dep["links"]["bucket"]

    for path in args.file:
        if not os.path.exists(path):
            sys.exit(f"Error: File '{path}' not found.")
        name = os.path.basename(path)
        if name in existing:
            print(f"Replacing existing '{name}'...")
            check(requests.delete(f"{dep_url}/files/{existing[name]}", params=params),
                  (204,), "remove old file")
        print(f"Uploading '{name}'...")
        with open(path, "rb") as f:
            r = requests.put(f"{bucket_url}/{name}", data=f, params=params)
        meta = check(r, (200, 201), f"upload {name}")
        print(f"  checksum {meta.get('checksum')}")

    print("\nFiles uploaded. The deposition is still a DRAFT.")
    print(f"Review and publish it here: {base}/deposit/{args.deposition}")


def main():
    parser = argparse.ArgumentParser(description="Prepare Zenodo deposition drafts")
    parser.add_argument("--production", action="store_true",
                        help="Target production (zenodo.org) instead of Sandbox")
    sub = parser.add_subparsers(dest="cmd", required=True)

    p = sub.add_parser("reserve", help="create a draft and reserve its DOI")
    p.add_argument("--metadata", required=True, help="JSON file with Zenodo deposit metadata")
    p.add_argument("--new-version-of", help="record ID to open a new version of")

    p = sub.add_parser("upload", help="upload files to an existing draft")
    p.add_argument("--deposition", required=True, help="draft ID printed by 'reserve'")
    p.add_argument("--file", action="append", required=True, help="file to upload (repeatable)")

    args = parser.parse_args()
    base = "https://zenodo.org" if args.production else "https://sandbox.zenodo.org"
    print(f"Targeting: {base}")
    params = {"access_token": load_token()}
    (reserve if args.cmd == "reserve" else upload)(args, base, params)


if __name__ == "__main__":
    main()
