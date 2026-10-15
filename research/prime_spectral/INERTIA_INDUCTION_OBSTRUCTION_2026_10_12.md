# Exact inertia reduction and the obstruction to a raw rank-one induction

The proposed count \(\lfloor2C-7/4\rfloor+1\) increases by one at half-unit increments of \(C\). That does not imply a rank-one relation between the full Weil operators. This note completes the elementary obstruction analysis for D6 and states the exact identity a viable replacement must use.

## A prime translation has infinitely many directions of both signs

Let the additive interval have length \(S=\log C\), and let \(0<d=\log q<S\). On \(L^2(0,S)\), extend functions by zero and let \(T_d\) denote compressed translation by \(d\). A geometric arithmetic term is a nonzero scalar multiple of \(T_d+T_d^*\).

Choose an interval \(I\subset(0,S-d)\) shorter than \(d\). The spaces \(L^2(I)\) and \(L^2(I+d)\) are disjoint. For every \(g\in L^2(I)\), set
\[
 f_\pm=2^{-1/2}(g\pm\tau_dg).
\]
In the subspace \(L^2(I)\oplus L^2(I+d)\), the compression of \(T_d+T_d^*\) is
\[
 \begin{pmatrix}0&I\\I&0\end{pmatrix}.
\]
Any images outside these two intervals are orthogonal to the subspace and do not change its compressed quadratic form. Consequently
\[
 \langle f_\pm,(T_d+T_d^*)f_\pm\rangle
 =\pm\|g\|^2.
\]
The same identity holds for every linear combination in either of the two infinite-dimensional \(f_\pm\) spaces. Thus a newly active prime term has infinite positive and negative index on this compression, as well as infinite rank. It cannot be a raw one-direction update.

This concerns the new arithmetic term by itself; it does **not** assert that the full Weil operator has infinitely many negative eigenvalues. The positive archimedean part and all other terms must remain in the full form.

Increasing the support also adds the infinite-dimensional space of functions on the newly admitted shell. No exact rank-one support-extension identity follows from counting a proposed low-energy cluster.

## The exact identity available after a coercive complement

Let a closed lower-bounded form have a split \(X\oplus Y\), with \(X\) finite-dimensional, and write
\[
 q_t(x,y)=\langle x,(H-t)x\rangle+
 2\Re\langle Bx,y\rangle+\langle y,(D-t)y\rangle .
\]
Assume \(D-t\ge dI>0\), the cross coupling \(B:X\to Y\) is bounded, and this is the actual form decomposition, with \(y\in D((D-t)^{1/2})\). Then
\[
 q_t(x,y)=\langle x,S_t x\rangle+
 \|(D-t)^{1/2}(y+(D-t)^{-1}Bx)\|^2,
\]
\[
 S_t=H-t-B^*(D-t)^{-1}B.
\tag{1}
\]
Indeed \((D-t)^{-1}Bx\) lies in \(D(D)\), so the square and the form-domain change of coordinates are legitimate. The invertible triangular change
\((x,y)\mapsto(x,y+(D-t)^{-1}Bx)\) gives the exact negative-index identity
\[
 n_-(q_t)=n_-(S_t).
\tag{2}
\]
This is the standard Schur/Feshbach reduction; see [Dusson–Sigal–Stamm](https://arxiv.org/pdf/2105.02058). It is not an RH-specific identity.

An induction between \(C\) and \(C+\tfrac12\) needs compatible finite coordinates, certified coercive complements, and an **exact relation between the two effective matrices \(S_t\)**. The signs in (1) matter: the complementary resolvent correction is subtracted. A norm estimate on it can lose the exponentially small internal sign margins.

The full-operator rank-one version of D6 is ruled out by the construction above. The proposed effective-block induction remains open; no relation of the form \(S_{C+1/2}=S_C\oplus(\text{one nonnegative scalar})\) has been obtained. This is a proved obstruction and a precise remaining identity, not an induction proving RH.
