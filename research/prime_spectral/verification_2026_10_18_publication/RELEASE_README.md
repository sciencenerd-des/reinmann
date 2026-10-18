# DH controls: unreviewed publication, 18 October 2026

DOI: https://doi.org/10.5281/zenodo.23401370

This is an unreviewed preprint. The author explicitly waived the human-read
prerequisite and authorized publication. No completed external human review,
reviewer endorsement, universal detection law or RH proof is claimed.

The supplement has two layers. The 70 parts reconstruct the immutable complete
scientific capsule, including all certificates and plotting inputs. The small
publication-update archive supplies the final 18 October PDF, editable source,
metadata, reproduction guide and review disclosure. Only four publication files
replace their base versions; exact historical copies are retained. Experimental
inputs, certificates, figures and mathematical arguments are unchanged.

1. Download all 70 .partNN files, DH_SUPPLEMENT_PARTS.json and
   reassemble_dh_supplement.py into one directory. Run:

       python3 reassemble_dh_supplement.py

   The verified base archive has 145540103 bytes and SHA256
   1a899aba7d560e41692fce94c6ad0352e75822545db128462af8607be272293c.
2. Extract that archive into a new directory. Then extract
   dh-controls-publication-update-2026-10-18.tar.gz into the SAME directory.
   Its updated paper files intentionally replace their historical base versions.
3. From the extracted directory run:

       python3 verify_publication_update.py

   This checks every scientific-base artifact against its original manifest,
   the four declared replacements, their historical copies and the final release
   files. Earlier full-paper verifiers are historical; run those on an untouched
   base copy, not on the replaced current paper. Numerical replay commands are in
   paper/DH_CONTROLS_REPRODUCTION.md. No new numerical searches were run for this
   wording-only publication update.

The top-level Zenodo PDF is byte-identical to paper/dh_controls_paper.pdf in this
publication update. The source builds with Tectonic from paper/, using the figures
and tables in the scientific base. SOURCE_DATE_EPOCH=1792281600 was used for the
release PDF. The latest formal Lean work is separately tracked on GitHub; this
capsule and this preprint do not assert a completed Xi rectangle certificate.

Historical notes about a required human read describe the earlier draft and are
superseded only for publication authorization by this explicit unreviewed release.
They are preserved as provenance, not presented as a completed human review.
