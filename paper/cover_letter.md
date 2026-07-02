Biswajit Mondal
b.mondal0000@gmail.com

June 7, 2026

To the Editors,
*Experimental Mathematics*

Dear Editors,

I am submitting for your consideration the manuscript **"A Machine-Checked
Reduction of the Riemann Hypothesis to Pólya–Frequency Positivity of the ξ Taylor
Coefficients"** for publication in *Experimental Mathematics*.

**What the paper is — and is not.** This is a formalization and reduction study. It
does **not** prove the Riemann Hypothesis, and it makes no such claim. Its
contribution is a chain of *conditional reductions*, each checked by the Lean 4
kernel and depending only on the foundational axioms {propext, Classical.choice,
Quot.sound}, that convert RH into explicit total-positivity and operator-positivity
statements. The central result is a **tightness theorem**: modulo three standard
classical inputs (Pólya–Jensen, Aissen–Schoenberg–Whitney/Edrei, and Laguerre–Pólya
closure), RH is *equivalent* to total positivity of the Toeplitz matrix of the
sign-normalized ξ Taylor coefficients — so that single remaining input cannot be
"postulated" as progress without assuming RH itself.

**Why *Experimental Mathematics*.** The paper pairs formal verification with an
unusually deep, cross-certified computation: the ξ Taylor coefficients b₀,…,b₁₂₀
(with |b₁₂₀| ≈ 10⁻⁴⁴⁹), agreeing to over 230 significant digits across two
independent precisions, are used to verify the reduction's premise at scale — all
contiguous Pólya-frequency minors through order 16, log-concavity through n = 118,
and Jensen hyperbolicity through degree 6. This combination of rigorous computation
and machine-checked theory is squarely within your journal's scope, and the work's
value is precisely in the experimental delimitation of the open frontier.

**Distinct contributions.**
1. A correct, tight, axiom-clean Lean reduction of RH to one sign-correct
   positivity statement.
2. Identification and repair of a target-function error (building on the completed
   zeta Λ₀, whose zeros are *not* the Riemann zeros, rather than on Riemann's ξ).
3. An independent operator-positivity (pseudo-Hermitian) reduction.
4. Reproducible high-precision numerical evidence localizing the open content to a
   uniformity statement.

**Originality and ethics.** This manuscript is original, has not been published
elsewhere, and is not under consideration by any other journal. I am the sole
author. A disclosure of AI-assisted tools (used for drafting, code scaffolding, and
consistency checking, under my direction and responsibility) is included in the
manuscript per current best practice; these tools are not authors. The Lean
development and verification scripts are available for review, and I am happy to
provide the repository archive and a commit hash on request.

Thank you for your consideration. I would be glad to suggest qualified referees in
analytic number theory and in formalized mathematics if helpful.

Sincerely,
Biswajit Mondal
b.mondal0000@gmail.com
