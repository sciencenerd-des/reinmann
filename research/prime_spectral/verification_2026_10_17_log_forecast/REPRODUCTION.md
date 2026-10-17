# Reproducing the fixed logarithmic forecast test

Start with `paper/dh_log_forecast_note.md`, `research/prime_spectral/LOG_FORECAST_RESULTS_2026_10_17.md` and the fixed `preregistered_forecast.json` in this directory. The capsule includes the previous scientific closure because the current verifier checks it unchanged, apart from declared review-status documentation.

From the extracted repository root:

    uv run --with python-flint==0.8.0 --with numpy --with mpmath --python 3.12 python experiments/prime_spectral/verify_log_forecast_round.py
    uv run --with python-flint==0.8.0 --with numpy --with mpmath --python 3.12 python experiments/prime_spectral/test_log_forecast_controls.py
    uv run --with python-flint==0.8.0 --with numpy --with mpmath --python 3.12 python experiments/prime_spectral/verify_log_forecast_witnesses.py

The last command reconstructs the two negative rational witnesses at4352bits and writes its receipt. Run the read-only manifest check first. Replays, figure regeneration and new searches may change diagnostic timestamps or PDF bytes; use a copy when preserving the exact capsule. Do not overwrite or re-register the frozen forecast after seeing outcomes.

Raw target records are under `b002/` and `b001/`. Both `atlas_H160/atlas.json` and `atlas_replay.json` are needed for completeness and replay claims. N192 window searches and N256 sensitivity searches record exact rational supports and witnesses. The plain-control finite spectra and the expressly post hoc wider-C diagnostic are separate records. Earlier full-paper manifests bind historical revisions; use the current verifier above for this capsule.

The required human read is pending. This capsule contains no private Gmail correspondence IDs or credentials. It is a local research artifact, not a published paper or RH proof. The new note and scope correction received no new human review or Lean build in this round.
