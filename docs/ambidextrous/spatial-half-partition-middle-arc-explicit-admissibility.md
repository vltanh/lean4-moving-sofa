# Explicit convexity and contact-curvature range for the \(P_J\) middle-arc diagnostic

**Scope.** This is a bounded *admissibility check* for the explicit smooth
bump directions used in PJ-MID and PJ-COUP; it does not prove any global
\(P_J\) inequality. A finite-angle niche evaluation is a diagnostic,
not an upper bound for true area. In particular, one cannot test a
local variational identity at an arbitrarily large bump amplitude and
still assume the perturbed support represents a convex cap in the
reference contact chart.

Use the notation of
[PJ-COUP](spatial-half-partition-coupled-middle-variation.md),
with \(L=\pi/2\), \(\beta=\arctan Y\), and the explicit reference
middle-support curvature densities

\[
\rho_f(t)=\tfrac34 R\cos(t/2+\pi/8),\qquad
\rho_g(t)=\tfrac34 R\sin(t/2+\pi/8).
\]

The exact reference constant isolation in
[NL](one-sixth-fullturn-near-reference-certificate.md) gives
\(13/10<R<131/100\).
Define

\[
\begin{aligned}
\phi(t)&=\begin{cases}
\sin^4\!\left(\frac{5\pi}{2}(t-11/20)\right),
&t\in[11/20,19/20],\\
0,&\text{else},
\end{cases}\\
\psi(t)&=\begin{cases}
\sin^4\!\left(\frac{5\pi}{2}(t-3/5)\right),
&t\in[3/5,1],\\
0,&\text{else}.
\end{cases}
\end{aligned}
\tag{PJ-ADM.1}
\]

Both functions are \(C^2\) with compact support in
\(T=(\beta,L-\beta)\); the old support and its first two
derivatives match identically at the ends. The two bumps may be
used independently, with arbitrary signs.

**Lemma PJ-ADM1 (explicit safe bump size).** For
\(|\varepsilon|\le1/2000\), every support

\[
f_\varepsilon=f_*+\varepsilon\phi,\qquad
g_\varepsilon=g_*+\varepsilon\sigma\psi,\quad
\sigma\in\{-1,0,1\},
\]

has strictly positive open-quarter curvature and strictly less than
unit curvature everywhere. In particular the perturbation is a
genuine convex-cap support, retains the reference's axis and top-face
data, and stays inside the curvature-only hypotheses needed for the
local graph analysis. This is a **necessary geometric safety check**,
not by itself a proof of global branch admission.

**Proof.** On \([11/20,19/20]\),
\(t/2+\pi/8\in(0.66,0.87)\), while on \([3/5,1]\)
it belongs to \((0.69,0.90)\).
The elementary Taylor bounds
\(\cos x\ge1-x^2/2\),
\(\cos x\le1-x^2/2+x^4/24\),
\(\sin x\ge x-x^3/6\), and
\(\sin x\le x-x^3/6+x^5/120\)
on these positive intervals, together with
\(1.30<R<1.31\), give

\[
3/5<\rho_f,\rho_g<4/5
\quad\text{on the respective bump supports}.
\tag{PJ-ADM.2}
\]

For \(\chi(t)=\sin^4(k(t-a))\), \(k=5\pi/2<8\),
direct differentiation gives
\(\chi''=4k^2(3\sin^2(k(t-a))\cos^2(k(t-a))-
\sin^4(k(t-a)))\). Hence
\(|\chi''+\chi|\le4k^2+1<257\).
For \(|\varepsilon|\le1/2000\), the change in either
curvature is \(<257/2000<13/100\), so

\[
0<47/100<\rho_{f_\varepsilon},\rho_{g_\varepsilon}
<93/100<1
\tag{PJ-ADM.3}
\]

on each affected interval. Outside the supports, the curvatures
are exactly those of Romik's reference, whose open-quarter values
lie strictly between zero and one. Since the perturbed support is
\(C^1\) across the patch boundaries and has nonnegative
curvature measure everywhere, it is a convex support. The
vertical and horizontal support axes are unchanged. QED.

**Interpretation.** PJ-MID and PJ-COUP still have a *separate*
exposed-contact-chart hypothesis; PJ-ADM.3 controls curvature,
not the global visibility of every nearby inner wall. But it
removes one avoidable numerical/proof ambiguity: every test at
\(|\varepsilon|\le1/2000\) is in the actual convex-support domain,
while tests at larger amplitudes can escape that domain and
cannot be used as a counterexample to the local formula.

**Unresolved.** Neither the unrestricted one-cap
\(P_J(U)\le M/2\) claim nor the actual full/partial ambidextrous
sharp-value theorem follows from this lemma. No Lean or CI was run.
