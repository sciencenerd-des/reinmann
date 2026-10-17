# Final matched-mixture mechanism test — fixed before target selection

The primary definitions, grids, slope formula, ±0.25 cutoff tolerance and stop rule were fixed in `verification_2026_10_17_final_mechanism/measurement_design.json` before the new measurements. The forecast was fixed before selecting either future mixture, in `preregistered_forecast.json`, SHA256 `d8dc2a26b3d9981b8df6dab574b9ef708ae993a03065ec697b16ba735f535616`.

The fixed b=0.001 odd-gamma mixture gives κ=1.0975310108891705 from N=192 ground eigenvalues at C=32,34,36,38,40,42. The b=0.002 mixture and N=128 grids are sensitivity checks, not alternative fits chosen after testing. All sampled finite spectra are rigorously positive; this does not certify a full positive window.

Six saved N=192 negative witnesses, normalized to unit L2 norm, give κ′=0.3603024675237778 from the squared transform derivative at their respective lowest off-line pair heights. The implementation checks both the transform value and its derivative against independent formulas (12 checks). Adjacent slopes vary: neither κ nor κ′ is established as a limiting exponent. The saved vectors also vary with b, so the derivative fit is not a controlled experiment varying C alone.

The prescribed slope is 2/(κ−κ′)=2.7128629486728104, anchored at (b,C)=(0.001,6015/128). The final forecasts are:

| Offset b | Mechanism C | Six-point descriptive C | Fixed mechanism tolerance |
|---|---:|---:|---:|
| 1/2000 | 48.8726008041181 | 48.86821859994401 | ±0.25 |
| 1/4000 | 50.753014108236194 | 50.82072298760485 | ±0.25 |

The descriptive fit is only a comparison and is not a replacement forecast after seeing an error. No target zero or window trial was computed before freezing these values. Definitions bind the forecast hash and carry later timestamps.

Each target requires a complete H=160 atlas and fresh 320-bit contour / 640-bit root-gate replay before a window search. Its disk radius is 10^-80, far below the pair separation. Search N=192 at 4096 bits on [48,56], expand the upper endpoint by 8 up to 128 if necessary, then bisect to width at most 1/32. Positive endpoints are finite-section evidence only; negative endpoints are rational full-form trial certificates. N=256 searches are sensitivity checks; saved N=192 negative witnesses are reconstructed at 4352 bits.

If either mechanism prediction misses the fixed tolerance, or is undefined, stop mechanism forecasting and retain the logarithmic fit as descriptive only. Do not refit or add another held-out target. A successful finite forecast would still not prove a support lower bound, universal law or an RH mechanism. This is the final forecast round requested by the author.

Reproduction uses Python 3.12, python-flint 0.8.0, NumPy and mpmath. Run scripts from the repository root. `final_log_mechanism.py design`, then its `b001` and `b002` actions create the fixed design and matched spectra in a fresh output directory; existing spectra are reused. Use `saved_witness_derivative_probe.py` for the derivative stage: it implements series sinh through exponentials, compatible with FLINT 0.8, and independently checks the analytic derivative. The frozen driver's original `derivatives` action encountered an unavailable series API; its diagnostic log is retained and is not counted as a passed measurement.

`freeze_final_log_forecast.py` refuses to overwrite an existing forecast. After it succeeds, `final_log_mixture_path.py --key b0005` and `--key b00025` run selection, atlas, replay and common-resolution searches. `final_log_resolution_replay.py --key ...` supplies N=256 sensitivity and the 4352-bit rational reconstruction. Finally run `assess_final_log_forecast.py`, `plot_final_log_forecast.py` (also requires matplotlib), and `verify_final_log_round.py`. The last verifier checks an existing manifest by default and refuses to replace an existing one with `--record`. Keep archived receipts immutable; use a fresh disposable calculation directory for a complete regeneration.
