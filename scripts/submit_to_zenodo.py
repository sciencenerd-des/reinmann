#!/usr/bin/env python3
import os
import sys
import argparse
import requests

def main():
    parser = argparse.ArgumentParser(description="Submit paper to Zenodo or Zenodo Sandbox")
    parser.add_argument("--token", help="Zenodo personal access token (or set ZENODO_TOKEN env var)")
    parser.add_argument("--production", action="store_true", help="Target production (zenodo.org) instead of Sandbox")
    parser.add_argument("--publish", action="store_true", help="Actually publish the deposition (default: draft only)")
    parser.add_argument("--file", default="paper/rh_reduction_paper.pdf", help="Path to the PDF file to upload")
    
    args = parser.parse_args()
    
    token = args.token or os.environ.get("ZENODO_TOKEN")
    if not token:
        print("Error: Zenodo personal access token is required. Use --token or set ZENODO_TOKEN environment variable.", file=sys.stderr)
        sys.exit(1)
        
    base_url = "https://zenodo.org" if args.production else "https://sandbox.zenodo.org"
    print(f"Targeting: {base_url}")
    
    # Metadata definition
    metadata = {
        "metadata": {
            "title": "A Machine-Checked Reduction of the Riemann Hypothesis to Pólya--Frequency Positivity of the xi Taylor Coefficients",
            "upload_type": "publication",
            "publication_type": "preprint",
            "description": (
                "We present a formally verified study, in Lean 4 / Mathlib, of the "
                "Laguerre--Pólya / total-positivity approach to the Riemann Hypothesis (RH). "
                "We do not prove RH. We prove a chain of conditional reductions, each checked by "
                "the Lean kernel and depending only on the foundational axioms, that convert RH "
                "into total-positivity statements about an explicit positive kernel and into "
                "an operator-positivity (pseudo-Hermitian) statement. Our central result is a "
                "tightness theorem: modulo three classical, machine-uncertified but standard "
                "inputs (Pólya--Jensen, Aissen--Schoenberg--Whitney/Edrei, and the Laguerre--Pólya "
                "closure), RH is equivalent to total positivity of the Toeplitz matrix of the "
                "sign-normalized xi Taylor coefficients."
            ),
            "creators": [
                {
                    "name": "Mondal, Biswajit",
                    "affiliation": "Independent Researcher"
                }
            ],
            "access_right": "open",
            "license": "cc-by-4.0"
        }
    }
    
    headers = {"Content-Type": "application/json"}
    params = {"access_token": token}
    
    # 1. Create a new deposition
    print("Creating deposition draft...")
    dep_url = f"{base_url}/api/deposit/depositions"
    r = requests.post(dep_url, params=params, json={}, headers=headers)
    if r.status_code != 201:
        print(f"Failed to create deposition: {r.status_code} - {r.text}", file=sys.stderr)
        sys.exit(1)
        
    dep_data = r.json()
    dep_id = dep_data["id"]
    bucket_url = dep_data["links"]["bucket"]
    html_url = dep_data["links"].get("html", f"{base_url}/deposit/{dep_id}")
    print(f"Deposition draft created successfully. ID: {dep_id}")
    print(f"Draft Web URL: {html_url}")
    
    # 2. Update metadata
    print("Updating deposition metadata...")
    update_url = f"{dep_url}/{dep_id}"
    r = requests.put(update_url, params=params, json=metadata, headers=headers)
    if r.status_code != 200:
        print(f"Failed to update metadata: {r.status_code} - {r.text}", file=sys.stderr)
        sys.exit(1)
    print("Metadata updated successfully.")
    
    # 3. Upload file
    file_path = args.file
    if not os.path.exists(file_path):
        print(f"Error: File '{file_path}' not found.", file=sys.stderr)
        sys.exit(1)
        
    filename = os.path.basename(file_path)
    upload_url = f"{bucket_url}/{filename}"
    print(f"Uploading file '{filename}' to {upload_url}...")
    
    with open(file_path, "rb") as f:
        r = requests.put(upload_url, data=f, params=params)
        
    if r.status_code not in (200, 201):
        print(f"Failed to upload file: {r.status_code} - {r.text}", file=sys.stderr)
        sys.exit(1)
    print("File uploaded successfully.")
    
    # 4. Optional Publish
    if args.publish:
        print("Publishing deposition...")
        publish_url = f"{dep_url}/{dep_id}/actions/publish"
        r = requests.post(publish_url, params=params)
        if r.status_code != 202:
            print(f"Failed to publish: {r.status_code} - {r.text}", file=sys.stderr)
            sys.exit(1)
        print("Deposition published successfully!")
    else:
        print("\nSubmission prepared successfully as a DRAFT.")
        print(f"Please review and publish it manually here: {html_url}")

if __name__ == "__main__":
    main()
