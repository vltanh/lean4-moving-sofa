# Symmetrizing the convex hull: an exact positive energy and the remaining niche bill

**Status.** This is a new *possible* full-turn reduction, not a proved symmetrization theorem. It differs fundamentally from RA1: RA averaged **the nonconvex body**, which fails feasibility even at the reference. Here we average only the **actual convex hull** with its horizontal reflection and then apply **both complete canonical forbidden sweeps** to the resulting convex hull. The reference hull is unchanged by this operation. The new positive hull-area identity below is exact. The necessary inequality for the *removed* niche area and, separately, connectedness of the resulting envelope remain unproved. Labels HS are local. The partial-turn problem is not considered.

## 1. Operator and reflection parity

Let \(S\) be a compact connected body possessing both complete conventional turns in the common unit incoming strip. Write \(K=\operatorname{conv}S\). Translate horizontally so the projection of K is the centered interval \([-W/2,W/2]\). Put
\[
J(x,y)=(-x,y),\quad K_{\mathrm s}=\tfrac12(K+JK),
\quad h=h_K,\quad h_{\mathrm s}=\tfrac12(h+Jh),\quad
h_{\mathrm a}=\tfrac12(h-Jh),
\]
where the action on support functions is \((Jh)(\theta)=h(\pi-\theta)\), with angles modulo \(2\pi\).

The support \(h_{\mathrm s}\) belongs to the genuine compact convex body \(K_{\mathrm s}\), and both axis supports are unchanged: the horizontal projection is still centered with width W, and the vertical projection is still \([0,1]\). Indeed \(h_{\mathrm a}\) vanishes at all four axis normals \(\theta=0,\pi/2,\pi,3\pi/2\), by centered horizontal supports and because J fixes the vertical normals.

For a convex K write \(E(K)\) for its entire full canonical two-turn envelope: intersect K with every support-tightened unit L-hallway over both closed quarter-turn intervals. This is a compact (possibly empty or disconnected) set. Whenever K is the actual hull of a full-turn S, the canonical tightening theorem gives \(S\subseteq E(K)\), and the component containing S is a feasible connected body. The same definition makes \(E(K_{\mathrm s})\) invariant under J, since the pair of handed turn constraints is exchanged by J. It need **not** be a Minkowski average of actual sofas. In particular it need not contain the forbidden central top-column points in RA1.

## 2. The exact area gained by convex-hull symmetrization

For any planar compact convex set with support h, the standard support-area formula reads
\[
|K|=\frac12\int_0^{2\pi}(h^2-h'^2)\,d\theta,
\]
with h Lipschitz and its a.e. derivative. The formula follows for nonsmooth hulls by polygon approximation; no open-quarter curvature density assumption is needed.

Reflection makes \(h_{\mathrm s}\) even and \(h_{\mathrm a}\) odd under \(\theta\mapsto\pi-\theta\), with the corresponding reflected derivative parities reversed. Thus their mixed \(L^2\) inner products vanish for both values and derivatives. Expanding the formula gives the **exact identity**
\[
\boxed{|K_{\mathrm s}|-|K|
=\frac12\int_0^{2\pi}\bigl(h_{\mathrm a}'{}^2-h_{\mathrm a}^2\bigr)\,d\theta.}
\tag{HS.1}
\]

Since \(h_{\mathrm a}\) vanishes at both ends of each coordinate quarter of length \(\pi/2\), the elementary Dirichlet inequality on each quarter gives
\(\int h_{\mathrm a}^2\le\frac14\int h_{\mathrm a}'{}^2\). Consequently
\[
\boxed{|K_{\mathrm s}|-|K|
\ge\frac38\int_0^{2\pi}|h_{\mathrm a}'|^2\,d\theta\ge0.}
\tag{HS.2}
\]
Equality holds only if \(h_{\mathrm a}\equiv0\), i.e. the hull was already left-right symmetric about its centered incoming axis. This quantitative result is stronger than merely invoking Brunn–Minkowski to say the convex hull gets larger.

## 3. What a real symmetrization theorem would have to pay

Define the ordinary **removed area**
\[
\mathscr R(K)=|K\setminus E(K)|.
\]
It subtracts the actual union of the two canonical forbidden sweeps *inside* K; overlap, clipping, and disconnected fibers are accounted for exactly. The identity \(|E(K)|=|K|-\mathscr R(K)\) and HS.1 give:
\[
\boxed{
|E(K_{\mathrm s})|-|E(K)|
=\frac12\int(h_{\mathrm a}'{}^2-h_{\mathrm a}^2)
-\bigl[\mathscr R(K_{\mathrm s})-\mathscr R(K)\bigr].
}
\tag{HS.3}
\]

Thus the following new, concrete **niche-increment budget** would suffice to prove that horizontal convex-hull symmetrization never decreases the *total* saturated envelope area:
\[
\boxed{
\mathscr R(K_{\mathrm s})-\mathscr R(K)
\le\frac12\int(h_{\mathrm a}'{}^2-h_{\mathrm a}^2).
}
\tag{HS.4, unproved}
\]
It cannot be inferred from hull-area monotonicity alone: making a support larger also moves inner forbidden quadrant thresholds, and can increase removed area. The earlier failures of naive averaging and of unqualified repair remain relevant.

Even if HS.4 were true for all actual full-turn hulls, a second step is necessary before applying the previously proved reflection-symmetric area theorem RS2: **\(E(K_{\mathrm s})\) must supply a connected J-invariant feasible body with area at least \(|E(K)|\)**. It is J-invariant as a set, but a union of exchanged disconnected components need not be an admissible sofa. Proving nonempty interval fibers, or an alternative single-component comparison, would supply this step. Do not drop it.

Under both these additional assertions, RS2 would give
\[
|S|\le|E(K)|\le|E(K_{\mathrm s})|\le M,
\]
closing the *full-turn* value. This final displayed implication is conditional, not a claimed proof.

## 4. Small noncertifying numerical screens

Short bounded diagnostics explicitly reconstructed full-angle support and niche roofs and compared the actual two-turn saturated envelope area before and after the hull-level operation. All tested families showed **an increase**, but no global statement follows:

- Seven one-sided and double-sided cut examples near Romik's hull, including independent positive/negative cap slopes: gains roughly \(8.2\times10^{-5}\) through \(2.93\times10^{-2}\) over the tested parameters.
- Fifty-four prescribed asymmetrically rounded two-radius stadium caps whose vertical-symmetric full envelope remained nonempty: sampled gains roughly \(0.0021\) through \(0.0453\).
- Thirty-seven sampled feasible sheared parallelograms: gains at least about \(0.0505\) on the chosen positive shear grid, with the original convex bodies providing exact source areas.
- Fifty-eight prescribed six-point opposite-end polygon hulls that passed a finite-angle extreme-vertex test and sampled nonempty-fiber test: gains at least about \(0.098\). These passage tests are **not** continuum feasibility certificates.
- Ten explicit middle-support plane-cut pairs of the reference, with sampled gains between about \(0.00248\) and \(0.01042\).
- Along one reflection interpolation \(K_\alpha=(1-\alpha)K_{\mathrm s}+\alpha K\), five prescribed \(\alpha\in\{0,1/4,1/2,3/4,1\}\) gave envelope areas decreasing numerically from \(1.636636\) at \(\alpha=0\) to \(1.632637\) at \(\alpha=1\), while the convex-hull areas decreased from \(1.994429\) to \(1.979446\).

These tests are discovery diagnostics only. In particular the reference computation has a nonzero discretization bias, and sampled vertex/angle feasibility is not an all-angle theorem. No interval-certified error, global functional covering, proof of HS.4, or proof that the symmetrized envelope always stays connected exists. The numerical evidence is a reason to investigate HS.4, not to mark it established.

## 5. Next exact gate

The task is now precise: either **prove or refute HS.4** for genuinely compatible full-turn hulls, while treating connectedness separately. It may be easier to control the removed-area increment via the antisymmetric support energy HS.1 than to compare two arbitrary weighted cap deficits and their clipping correction; this is a hypothesis, not a conclusion. A rigorous counterexample to HS.4 would discard this route even if the original full-turn conjecture remained true.

A useful negative control is the explicit near-reference tip-cut family in [near-reference-midline-obstruction.md](near-reference-midline-obstruction.md): it shows that half-height-rectangle admission and exact background-face matching cannot be assumed even at arbitrarily high subcritical areas. Horizontal **hull** symmetrization does not require those hypotheses at the outset.

All area identities in Sections 1–3 are pen-and-paper. The diagnostics used short invocations under five-second limits, with no optimizer campaign, CI, Lean/Lake compilation, dependency installation, or manuscript build. Full-turn optimality remains unproved.
