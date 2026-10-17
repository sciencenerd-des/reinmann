Complete DH controls supplement, split for reliable transfer.

Download all 70 .partNN files and DH_SUPPLEMENT_PARTS.json into one directory.
Use the included cross-platform verifier:

  python3 reassemble_dh_supplement.py

It checks every part before creating the archive, then checks the complete archive.
Alternatively, reassemble in filename order and check the hash yourself:

  cat dh-controls-supplement-2026-10-17.tar.gz.part?? > dh-controls-supplement-2026-10-17.tar.gz
  shasum -a 256 dh-controls-supplement-2026-10-17.tar.gz

Expected SHA256: 1a899aba7d560e41692fce94c6ad0352e75822545db128462af8607be272293c
Expected bytes: 145540103

The JSON manifest also binds the size and SHA256 of each individual part.
Only extract after verifying the reassembled SHA256. The archive has 1005 regular members.
The included scientific manifest binds 1004 artifacts. The current paper PDF is
paper/dh_controls_paper.pdf (SHA256 ea0908b5320226842791f9b732993c67138bc9c7762197cb45f3a2bc60224ed5).
Follow paper/DH_CONTROLS_REPRODUCTION.md inside the extracted archive.
The latest formal Lean developments are additionally available on the rh-structural-theory branch
of https://github.com/sciencenerd-des/reinmann .
