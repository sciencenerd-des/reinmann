# Narrow added-figure technical AI review — 16 October 2026

A separate AI agent reviewed only the two new figure generators/displays, their caption claims and the generated validation record. This is not human review. The required human read and author-controlled publication gate remain pending. No publication or external contact occurred. Previously frozen scientific results were not modified or newly recertified by this review.

## Outcome

No remaining mathematical, numerical or visible-layout correction is requested within this narrow scope. The generator and current validation record agree with their bound certified inputs. The paper uses the verified filenames; the original added PDF figures are preserved separately and hash-listed below. This report binds the current manuscript source and figure files, not the final rebuilt full-paper PDF.

## Folded-sector figure

I independently recomputed the root-ball checks at 1024bits from the refined atlas, explicitly including each disk radius. They confirm 235 critical-line folded zeros, seven conjugate folded pairs,43 smaller line-zero radii before the steepest pair, exactly one folded zero inside radius 64, and no off-line folded zero there. The steepest pair has radius approximately 7344.473513670062 and angle approximately 0.007199957879014496, strictly between pi/437 and pi/436. The global high-ordinate envelope at 340 is smaller than this angle.

The caption and legend now correctly distinguish the folded zero w=-gamma_1^2 from the corresponding reciprocal pole z=+gamma_1^2 of 1/F(-z). The positive reciprocal pole is the one used in the existing shift-one argument. Plotting the positive horizontal radius does not move the folded zero to the positive real axis.

For r=|w|=gamma^2+b^2 and |b|<1, gamma>sqrt(r-1), so the plotted upper envelope 2*atan(1/sqrt(r-1)) follows from 2*atan(|b|/gamma). Its displayed domain beyond 340^2+1 is correct. The caption now states that radius formula/domain explicitly. The pale radius<=340^2 region is covered by the complete height 340 atlas. The wedge caption identifies the sufficient PF 435 guarantee and does not assert failure of PF 436 merely because its narrower sufficient wedge is exceeded. Root locations shown are midpoints; interval assertions are made on whole balls.

Visual inspection initially found that the inset hid the main steepest point, arrow tip and part of its label. The inset/annotation were moved, and I inspected the regenerated PNG: the point, arrow and complete label are now visible. The caption's w_0 notation is now defined. No outstanding clipping or data-label collision was identified in these two standalone displays.

## Attribution figure

I independently recomputed all seven controls' signs, mismatch percentages and finite-total/quotient ratios at 1024bits and checked overlap with the validation enclosures. The relative mismatch is 100*abs(abs(D)-L)/L, with D the dominant negative quartet and L the positive critical-line sum. This is explicitly normalized to L, as the revised caption says.

The largest mismatch is approximately 15.60797995percent (conductor 17), all seven are below 16percent, and exactly five are below 3.5percent. All finite totals P_H and certified geometric quotients Q are negative. The absolute ratio |P_H/Q| ranges from 257.76314485 (DH 5) to 12562.87177449 (Epstein 5), agreeing with the caption's rounded factors 258–12563. The plot uses magnitudes on a logarithmic axis and prints the signs above bars; its labels and legend match the certified records.

The caption properly separates finite-atlas cancellation from a full spectral certificate. Under the written explicit formula, Q-P_H is the omitted zero sum, but these figures do not independently prove an analytic negligible-tail bound. The dominant quartet and line sum alone are not asserted to equal P_H, which also includes the other atlas quartets.

## Provenance and limits

The validation record's input/source hashes match the current files. Both numerical rechecks share FLINT/Arb and earlier certified root/witness inputs; they are not a new independent special-function implementation, full atlas replay or human review. The displayed tail envelope retains the existing written strip bound |b|<1 and entire-function/explicit-formula dependencies. No new zero, window, Toeplitz-rank or RH claim is made by these figures. Final paper compilation, page layout, updated supplement packaging and any private draft upload remain separate authoring-agent checks.

## Reviewed-file SHA 256 hashes

Paths are relative to the worktree repository root.

- `paper/dh_controls_paper.tex`
  `b658d197ab9adbf07f2537028ca6dd99bfc3178de47fa6781fdeba0b3eeaac73`
- `experiments/prime_spectral/plot_added_control_figures.py`
  `0702e513a6c98c27ab02dab9dbedff43f5f65be811ec296919c18875cb346017`
- `research/prime_spectral/verification_2026_10_16_figures/figure_validation.json`
  `39824324a76430cdacab5abb456813e9836a1698d74bf2742dca22660abaf889`
- `research/prime_spectral/verification_2026_10_16_figures/figure_replay.log`
  `b5569573fe8238f243c60aae2c74134c0850225cbe4cbaf14da9663a335f3f97`
- `research/prime_spectral/verification_2026_10_13_calibration/dh5_refined_atlas.json`
  `dcd26428e3a43e075379f9b7ea9d5a2f52a18e82531fa505d3dc0a238e06667b`
- `research/prime_spectral/verification_2026_10_13_calibration/zero_attribution.json`
  `19d0b6fcce8ecc4dfa6f4557e76de183efbcd4114377006b7858204fbc461d2e`
- `paper/figures/dh_folded_wedge_verified.pdf`
  `b10c0a6ebd77b5605d22a8d8c3ee2ba3c6d6148ee64fdb1a8c023487204aa3d9`
- `paper/figures/dh_folded_wedge_verified.png`
  `a0480a4920d3bc0058225beea773a443dfb379ccb33f24d3e7fe094224cf5757`
- `paper/figures/dh_attribution_bars_verified.pdf`
  `6735de5f306ddab29f82e5e25cf4c7ad2f7e599c4f61de06ab6b889161eb27a1`
- `paper/figures/dh_attribution_bars_verified.png`
  `446485ac47b20ae4223b8ed33176a7d0c51fad4147993317205aa0deadd76435`
- `research/prime_spectral/verification_2026_10_16_figures/original_figures/dh_attribution_bars.pdf`
  `01e741da57aa548dc0a9a970f2cfa393b8c7afe3b3a15325cddb039b5971645e`
- `research/prime_spectral/verification_2026_10_16_figures/original_figures/dh_folded_wedge.pdf`
  `379be1f68ea67cc28ed3c9c21510d6738f37c6950541e16695f29e6aa3b0442d`
