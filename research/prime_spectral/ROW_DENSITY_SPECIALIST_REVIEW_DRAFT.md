# Specialist review request — draft only, not sent

Subject: Cubic-row substitution in the alternate 11/12 Mobius-family argument

Dear [reader],

Could you check the narrow source/exponent audit in
`ROW_DENSITY_AND_CUBIC_OBSTRUCTION_2026_10_22.md`? It concerns OpenAI's
unrefereed alternate October-5 manuscript, `paper2.tex` at commit
1581d4cbdd69a0faf34b2089614fe2a814316a6a, rather than the separate 7/8 replay.
We claim no new mean-square estimate or zero-free theorem.

Under a family bound sum_{N(u)<=H}|A_u(D)|^2 << D^(1+epsilon)H and principal
rows p^k with error O(D/H^(1/k)), elementary extraction gives
sigma_k(h)=max(1/2+(k-1)h/(2k),1-h/k), H=D^h. Its unrestricted optimum is
k/(k+1), while the h>1 infimum is 1-1/(2k). For k=1 every h>=1/2 minimizes.
Thus cubic rows would give 5/6 in the existing range, and 3/4 would need a
new short-family result.

The substantive questions are:

1. Sextic Poisson uses mu_K gamma_{-1}=chi(-1)G^(-1) bar(alpha) gamma_2.
   Cubic Poisson instead gives mu_K gamma_{-2}=bar(alpha) gamma_2^2.
   Equivalently this is bar(alpha)G^(-1)gamma_1, a sextic Gauss coefficient.
   Is there an established coefficient realization with controlled completion
   and summation costs? Broeker–Hoffstein's fourth-power-index relations seem
   relevant but do not immediately give the same squarefree-index cutoff.
2. The existing local reflection formula maps j to -j-2 modulo 6: j=1 becomes
   quadratic, j=2 remains cubic. Is there an alternative realization that
   changes this conclusion without importing a GRH-dependent dispersion estimate?
3. Do we correctly identify the second independent gap as the positive-gap
   requirement Hcal/Sigma << D^(-vartheta), violated by H=D^(3/4) in the
   basic X=D, Hcal=D^2/H configuration?

Our exact verifier also checks the failed p^3 sextic-row identity at column
norm 7 and row norm 13, and a DH reciprocal-coefficient multiplicativity
obstruction at 7*13. These are algebraic controls, not cancellation estimates.
The proposed RH endpoint remains unproved, and the note does not assert a
universal barrier for metaplectic methods.

Thank you,
Biswajit Mondal

Attachments if the author chooses to send: the audit note and its source/equation
index, plus the small exact verifier and `exact_checks.json`. No recipient has
been selected and no message has been sent by this research round.
