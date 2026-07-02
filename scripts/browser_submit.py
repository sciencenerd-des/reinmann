#!/usr/bin/env python3
import sys
import os
import argparse
from playwright.sync_api import sync_playwright

def main():
    parser = argparse.ArgumentParser(description="Submit paper to Zenodo via Browser Automation")
    parser.add_argument("--production", action="store_true", help="Target production (zenodo.org) instead of Sandbox")
    parser.add_argument("--file", default="paper/rh_reduction_paper.pdf", help="Path to the PDF file to upload")
    args = parser.parse_args()

    base_url = "https://zenodo.org" if args.production else "https://sandbox.zenodo.org"
    file_path = os.path.abspath(args.file)

    if not os.path.exists(file_path):
        print(f"Error: File '{file_path}' not found.", file=sys.stderr)
        sys.exit(1)

    print("Starting browser automation...")
    with sync_playwright() as p:
        # Launch headed browser so the user can see it and log in
        browser = p.chromium.launch(headless=False)
        context = browser.new_context()
        page = context.new_page()

        print(f"Navigating to login page: {base_url}/login")
        page.goto(f"{base_url}/login")

        print("\n" + "="*60)
        print("ACTION REQUIRED in the browser window:")
        print("1. Log in to Zenodo (using your account, GitHub, or ORCID).")
        print("2. Once logged in, go to the New Upload page:")
        print(f"   {base_url}/uploads/new")
        print("3. Return to this terminal and press ENTER to continue automated filling.")
        print("="*60 + "\n")

        input("Press ENTER here after logging in and reaching the New Upload page...")

        print("Checking if we are on the uploads page...")
        if "uploads/new" not in page.url:
            print("Navigating to new upload page...")
            page.goto(f"{base_url}/uploads/new")
            page.wait_for_load_state("networkidle")

        print("Starting automated upload and form filling...")

        # 1. Upload file
        print("Uploading paper file...")
        try:
            # Look for file input
            page.wait_for_selector("input[type='file']", timeout=15000)
            file_input = page.locator("input[type='file']")
            file_input.set_input_files(file_path)
            print("File upload initiated.")
        except Exception as e:
            print(f"Could not locate file input automatically: {e}")
            print("Please drag & drop or select the PDF file manually in the browser.")

        # 2. Fill Title
        print("Filling Title...")
        title_text = "A Machine-Checked Reduction of the Riemann Hypothesis to Pólya--Frequency Positivity of the xi Taylor Coefficients"
        try:
            # Try InvenioRDM field or standard selectors
            title_input = page.locator("input[name='metadata.title']").or_(
                page.locator("input#title")
            ).or_(
                page.get_by_label("Title", exact=True)
            ).or_(
                page.get_by_placeholder("A title...")
            )
            title_input.wait_for(state="visible", timeout=5000)
            title_input.fill(title_text)
            print("Filled title.")
        except Exception as e:
            print(f"Could not fill Title automatically: {e}")
            print(f"Please fill Title manually: '{title_text}'")

        # 3. Fill Authors
        print("Filling Creator/Author...")
        try:
            # In InvenioRDM, Creators are usually a list component
            # Let's try adding creator
            add_creator_btn = page.get_by_role("button", name="Add creator").or_(
                page.locator("button:has-text('Add creator')")
            ).or_(
                page.locator("button:has-text('Add author')")
            )
            if add_creator_btn.is_visible():
                add_creator_btn.click()
                page.wait_for_timeout(500)
            
            # Fill family name / given name / name
            name_input = page.locator("input[name*='creators.0.person_or_org.name']").or_(
                page.locator("input[placeholder*='Family name, Given names']")
            ).or_(
                page.locator("input[name*='creators.0.name']")
            )
            name_input.wait_for(state="visible", timeout=5000)
            name_input.fill("Mondal, Biswajit")
            
            affiliation_input = page.locator("input[name*='creators.0.affiliations.0.name']").or_(
                page.locator("input[placeholder*='Affiliation']")
            )
            if affiliation_input.is_visible():
                affiliation_input.fill("Independent Researcher")
            
            print("Filled creator.")
        except Exception as e:
            print(f"Could not fill Creator automatically: {e}")
            print("Please fill Creator manually: 'Mondal, Biswajit' (Independent Researcher)")

        # 4. Fill Description / Abstract
        print("Filling Description...")
        description_text = (
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
        )
        try:
            # Description is often a rich text editor or textarea
            desc_input = page.locator("textarea[name='metadata.description']").or_(
                page.locator("div.ck-editor__editable")
            ).or_(
                page.locator("#description")
            )
            desc_input.wait_for(state="visible", timeout=5000)
            if desc_input.locator("p").is_visible():
                desc_input.locator("p").first.fill(description_text)
            else:
                desc_input.fill(description_text)
            print("Filled description.")
        except Exception as e:
            print(f"Could not fill Description automatically: {e}")
            print("Please paste the abstract/description manually.")

        print("\n" + "="*60)
        print("AUTOMATION FINISHED PRE-FILLING.")
        print("Please check the browser window to:")
        print("1. Complete any missing mandatory fields.")
        print("2. Review the uploaded file and information.")
        print("3. Click 'Save' and then 'Publish' when you are ready.")
        print("Do not close the browser until you are done.")
        print("="*60 + "\n")

        input("Press ENTER in this terminal to close the browser and exit...")
        browser.close()

if __name__ == "__main__":
    main()
