# Second band and collision-path controls — 15 October 2026

The second-band forecast and requested nearby-shift strip were recorded before any new coefficients or cells were computed. This is a local pre-registration with retained hashes, not an independent public time stamp. No publication or public message is part of this round.

## Forecast confirmed

The forecast entry interval was1535–1539, with the last negative expected at1970–1974 (nominal1537–1972). The certified second shift-44 band is **1536–1972**. Every rank1401–1535 and1973–2000 is positive. Endpoint errors are(-1,0), with no phase/frequency refitting. All 600 new signs match the leading cosine from the prior asymptotic record. Entry and last-negative displacements from the first band are872 and873, consistent with the noninteger period scale872.66973123454.

The requested shifts 40–48 at ranks 521–700 contain1620 cells, all resolved. Only shift 44 has negative members, starting at 664. Combined with the historical grid and targeted column, rank664 at shift 44 is the first failure among DH contiguous minors **tested in this study**. It is not globally first; earlier untested shifts and non-solid minors remain open.

## Cheap certified coefficient extension

The positive-theta lemma in the manuscript proves all ordinary coefficients mu_n nonnegative. Thus for every R>0,

    0 <= mu_n <= F(R)/R^n.

The first 1,451 evaluated coefficients are retained. An outward evaluation of F(2^20)=Lambda(1/2+1024)/Lambda(1/2) bounds the 600 remaining coefficients through 2050. The resulting broad intervals suffice for every second-band determinant; no uncomputed coefficient is silently set to0. The longer full-jet calculation was cancelled as redundant and produced no accepted output.

A separate AI reviewer evaluated F(R) afresh, checked all 600 tail intervals, replayed all 600 second-band signs and all 1,620 nearby-shift signs at 33,280bits, and directly checked both band edges and nearby ranks 663/664. That technical review is supplementary; the user's required human read remains pending.

## Mixture collision path

Three exact rational mixtures target lowest off-line offsets 0.015,0.008 and0.004 at conductor13, with a separate complete atlas and higher-precision replay for each. Root disks are far smaller than the off-line reflected-pair separation. Their N192 endpoints are39.5625,41.28125 and42.90625, with normalized coordinates0.608312,0.634740 and0.659726, compared with 0.569871 at offset 0.03. N256 endpoints are39.515625,41.2421875 and42.875, differences below 0.05. All new quotients are certified at 4,096bits, and exact witnesses are reassembled at 4,352bits. The lowest quartet dominates each finite-atlas attribution, but the infinite tail remains material.

A descriptive four-point fit gives C≈37.2961+2.88554 log(0.03/b), RMSE 0.2216. This is a description over a finite 7.5-fold offset change, not an asymptotic rate or evidence of a universal offset-free detection law. Finite-family negative endpoints remain support upper bounds, and positive sections do not supply full-support lower bounds. A finite sequence cannot establish boundedness or divergence at the actual b-to-zero limit.

## Publication and communication

[Human reviewer shortlist and request draft](../../paper/HUMAN_REVIEW_REQUEST.md) prepared, unsent. David Platt is the suggested first reader; Andrew Booker is an alternative. Fredrik Johansson and Per Alexandersson are possible targeted numerical/theory readers. No one has been contacted or represented as having agreed.

[Liu reproducibility note draft](../../paper/LIU_REPLAY_NOTE_DRAFT.md) prepared, unsent. A factual public note would be useful after author approval. The related-work section now reports the frozen A/B replay with its retained-versus-clean distinction and runtime adaptation.

The [post-publication formal plan](POST_PUBLICATION_FORMAL_TARGETS_2026_10_15.md) scopes the finite-product split-pair theorem and `ZetaNoLowStripZero (141/10)`. These are conditional next projects, not completed Lean results. No new Lean proof or RH proof is claimed.

Three new tests pass. An initial test-only integer parsing limit rejected a 9,864-digit certificate endpoint; the trusted-file test now explicitly permits the required integer size, with the original failure retained. No numerical certificate was accepted through an unresolved gate.
