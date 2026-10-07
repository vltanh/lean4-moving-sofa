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


## 6. An exact normalization obstruction even if the area budget were proved

There is a **second independent missing implication** in any attempted global solution via hull reflection: after canonical saturation, the symmetrized envelope can lose its **entire unit vertical span**. Consequently the existing x-reflection symmetric optimality theorem RS2, which requires a common incoming **unit-span** normalization, cannot simply be applied to that saturated body.

This is already rigorous on the explicit symmetric-in-height double-tip cut family of [MCA](convex-cap-averaging-obstruction.md). For sufficiently small \(\tau>0\), let \(K_\tau\) be the actual convex hull of
\[
\Sigma\cap\{\tau(x+m/2)\le y\le1-\tau(x+m/2)\},
\]
in centered reference coordinates with horizontal projection \([-m,m]\), \(m>1\). The original reference hull \(K_*\) and the reference sofa \(\Sigma\) are invariant under the horizontal reflection \(J:(x,y)\mapsto(-x,y)\). The cut is vertically symmetric under \(\rho:(x,y)\mapsto(x,1-y)\), so \(K_\tau\) has that symmetry and so does its x-reflection average
\[
B_\tau=\tfrac12(K_\tau+JK_\tau).
\]

The top face of \(K_\tau\) is the **single point** \((-m/2,1)\), and its bottom face is the single point \((-m/2,0)\); these are the actual retained reference-tip points. The top face of \(JK_\tau\) is \((m/2,1)\), and analogously below. Support faces of a Minkowski sum add as sets. Consequently **both the top and bottom faces of \(B_\tau\) are the central singleton** at abscissa zero. The horizontal projection of \(B_\tau\) is still exactly \([-m,m]\), and its leftmost and rightmost points \((\pm m,1/2)\) are retained, since the original cuts leave those points unchanged.

Moreover \(B_\tau\subseteq K_*\): each summand lies in \(K_*\), which is convex and J-invariant. Since \(h_{B_\tau}\le h_{K_*}\), the canonical forbidden quadrants defined by \(B_\tau\) are contained in those defined by \(K_*\), pointwise in every turn orientation. Hence **both original extreme reference sofa points** \((\pm m,1/2)\), which survive the full reference motions, also survive all full canonical constraints of \(B_\tau\). Thus the envelope \(E(B_\tau)\) has horizontal projection containing \([-m,m]\), with a genuinely retained flank more than one horizontal unit to each side of zero.

Suppose \(E(B_\tau)\) retained a point at height one. Because the top face of \(B_\tau\) is just \((0,1)\), it would retain this exact point. The envelope is invariant under \(\rho\), because \(B_\tau\) is and the two complete handed turn families are interchanged by \(\rho\), so it would also retain \((0,0)\). Those two retained baseline points and the extreme flank points \((\pm m,1/2)\) contradict **UC1**, the previously proved simultaneous two-turn switching obstruction for a retained vertical unit chord with flanks farther than one on both sides. UC's pointwise switching argument only uses hallway containment and these retained points; it does not require the entire tentative envelope to be connected.

It follows that **neither** \((0,1)\) nor \((0,0)\) survives. No other points of \(B_\tau\) have those extreme heights. The envelope is compact, so
\[
\boxed{\max_{E(B_\tau)} y<1,\qquad
\min_{E(B_\tau)}y>0.}
\tag{HS.5}
\]
It is nonempty, since it contains the two outer reference tips (and in fact contains a nonempty middle portion for sufficiently small \(\tau\)); no empty-set convention is used.

This provides an exact counterexample to the premise that **hull symmetrization followed by canonical deletion automatically yields a symmetric *unit-span* full-turn sofa**. It does not refute the possible area monotonicity HS.4. Rather, it shows that *even if HS.4 were proved*, completing the route to M would additionally require either:

- a sharp x-reflection-symmetric theorem valid for full-turn sofas with *subunit* incoming vertical span (without an unjustified dilation), or
- a separate feasible area-preserving unit-span normalization for the symmetrized saturated envelope.

Neither statement is established here. The earlier RA failure of averaging actual nonconvex sets is not being recycled: \(B_\tau\) is a convex hull average, and its envelope correctly **deletes** the forbidden central top and bottom points instead of assuming they survive.

The top-face and retained-flank calculations are exact and use no numerical sampling. This example also explains why numerical area improvement after hull symmetrization, by itself, is not a proof of full-turn optimality.


## 7. The hull gain is almost entirely spent on forbidden material near the reference

A *quantitative obstruction* to a coarse proof of HS.4 can be obtained without any numerical computation. In the same double-tip cut family \(K_\tau\) from Section 6, denote its upper downward cap by \(U_\tau\), the reference cap by \(U_*\), and the symmetric average cap by \(C_\tau=(U_\tau+JU_\tau)/2\). Let \(B_\tau=(K_\tau+JK_\tau)/2\). The reference's central face interval has length \(m\).

**Lemma HS2 (linear hull gain, smaller surviving-area change).** As \(\tau\downarrow0\),
\[
\boxed{|B_\tau|-|K_\tau|=\frac{m^2}{2}\tau+O(\tau^{3/2}),}
\tag{HS.6}
\]
while both fully saturated full-turn envelope areas satisfy
\[
\boxed{|E(K_\tau)|=M+O(\tau^{3/2}),\qquad
|E(B_\tau)|=M+O(\tau^{3/2}).}
\tag{HS.7}
\]
In HS.7 the deviations are *nonpositive*, by the already proved reference-belt bound RB1. Consequently
\[
\boxed{\mathscr R(B_\tau)-\mathscr R(K_\tau)
=\frac{m^2}{2}\tau+O(\tau^{3/2}).}
\tag{HS.8}
\]
Thus the removed-area increase asymptotically consumes the **entire leading convex-hull gain**. No assertion of strict improvement, nor a fixed positive fraction of the hull gain remaining as sofa area, follows from HS.1 alone.

**Proof of HS.6.** Over the old horizontal face \([a,b]=[-m/2,m/2]\), the one-sided upper cut lowers the reference roof exactly by \(\tau(x-a)\), whose integral is \(\tau m^2/2\). The reference circular outer tail has a quadratic height deficit near its former top tip, so the additional loss on the right neighboring flank is \(O(\tau^{3/2})\); the cut is inactive on the left flank. Therefore
\[
|U_*|-|U_\tau|=\frac{m^2}{2}\tau+O(\tau^{3/2}).
\]
The exact mirrored-cap support calculation MCA.9 proves
\[
|U_*|-|C_\tau|=\frac{m^2}{4}\tau+O(\tau^{3/2}).
\]
Both \(K_\tau\) and \(B_\tau\) are vertically symmetric convex hulls with projection of width \(2m\), so their convex areas are \(2|U_\tau|-2m\) and \(2|C_\tau|-2m\), respectively. Subtract to obtain HS.6. QED.

**Proof of HS.7.** For sufficiently small \(\tau>0\), both \(K_\tau\) and \(JK_\tau\) are convex subsets of \(K_*\) that contain the entire central reference belt
\[
K_*\cap\{1/101\le y\le100/101\}.
\]
Their Minkowski midpoint \(B_\tau\) contains that belt as well (each point in the belt is the midpoint of itself in the two summands), and \(B_\tau\subseteq K_*\) by convexity and x-symmetry of \(K_*\). RB1 therefore gives
\[
|E(K_\tau)|\le M,\qquad |E(B_\tau)|\le M.
\]
For the first lower bound, the actual retained double-cut body \(S_\tau\subseteq E(K_\tau)\) has
\(|S_\tau|=M-O(\tau^{3/2})\) by MCA.4.

For the second lower bound, the intersection \(S_\tau\cap JS_\tau\) lies in \(K_\tau\cap JK_\tau\subseteq B_\tau\). Every point of that intersection belongs to the original reference sofa \(\Sigma\), whose canonical forbidden quadrants contain those of \(B_\tau\) because \(B_\tau\subseteq K_*\). Thus
\[
S_\tau\cap JS_\tau\subseteq E(B_\tau).
\]
Since \(\Sigma\) is J-invariant,
\[
|\Sigma\setminus(S_\tau\cap JS_\tau)|
\le|\Sigma\setminus S_\tau|+|\Sigma\setminus JS_\tau|
=O(\tau^{3/2}).
\]
Hence \(|E(B_\tau)|\ge M-O(\tau^{3/2})\). This proves both statements of HS.7. QED.

Finally the exact identity \( |E(B)|=|B|-\mathscr R(B)\) turns HS.6 and HS.7 into HS.8.

**Corollary HS3 (no uniform retained-energy fraction).** There is no positive constant \(c\) such that *every* genuinely full-turn, reference-belt-admitted hull K satisfies
\[
|E((K+JK)/2)|-|E(K)|
\ge c\bigl(|(K+JK)/2|-|K|\bigr).
\]
Indeed for \(K=K_\tau\), the numerator is \(O(\tau^{3/2})\), while the denominator is \((m^2/2)\tau+O(\tau^{3/2})>0\), making their ratio tend to zero. This conclusion does not refute the **sign-only** conjecture HS.4; it shows that proving it must use a sharp first-order cancellation, just as the successful TC reference-tail comparison did.

This is a pen-and-paper consequence of exact reference formulas and the already stated RB/MCA results. Neither a fresh computer certificate nor an independent continuum review is claimed.


## 8. Linear unit-span loss despite only three-halves-order area loss

The qualitative span obstruction HS.5 can be sharpened to an **explicit first-order bound**. Keep the double-tip cut family \(K_\tau\), and write \(b=m/2>1/2\) for the right endpoint of the reference horizontal top face. Let \(B_\tau=(K_\tau+JK_\tau)/2\), and \(E_\tau=E(B_\tau)\). By Section 7,
\[
M-O(\tau^{3/2})\le |E_\tau|\le M.
\]

**Theorem HS4 (linear span deficit).** For all sufficiently small \(\tau>0\),
\[
\boxed{\min_{E_\tau}y\ge b\tau/4,\qquad
\max_{E_\tau}y\le1-b\tau/4,}
\tag{HS.9}
\]
and hence
\[
\boxed{\operatorname{span}_y(E_\tau)\le1-b\tau/2.}
\tag{HS.10}
\]
Thus a symmetrized-hull envelope may have an incoming span defect of order \(\tau\) although its area deficit from \(M\) is only of order \(\tau^{3/2}\).

**Proof.** Fix \(\delta=\arctan\tau\) and the upper-right normal \(n=(\sin\delta,\cos\delta)\). The cut plane of \(K_\tau\) is
\[
\tau x+y\le1-\tau b,
\]
so
\[
h_{K_\tau}(n)\le\cos\delta-b\sin\delta.
\]
For \(\delta\) small, the original reference's right-upper tail has the exact support
\[
h_{K_*}(n)=\tfrac12+b\sin\delta+\tfrac12\cos\delta.
\]
The horizontally reflected cut hull \(JK_\tau\) is contained in \(K_*\), since \(K_*\) is J-invariant. Support additivity therefore gives the **exact support bound**
\[
h_{B_\tau}(n)
=\tfrac12\bigl(h_{K_\tau}(n)+h_{JK_\tau}(n)\bigr)
\le\tfrac14+\tfrac34\cos\delta.
\tag{HS.11}
\]
Every point \((x,y)\in B_\tau\) with \(x\ge b/2\) consequently satisfies
\[
y\le \frac{1/4+(3/4)\cos\delta-x\sin\delta}{\cos\delta}
=\tfrac34+\tfrac14\sec\delta-x\tau,
\]
so, using \(\sec(\arctan\tau)-1=\sqrt{1+\tau^2}-1\le\tau^2/2\),
\[
1-y\ge x\tau-\tfrac18\tau^2
\ge \tfrac b2\tau-\tfrac18\tau^2
\ge\tfrac b4\tau
\]
for all sufficiently small positive \(\tau\). Horizontal symmetry gives the same estimate whenever \(x\le-b/2\).

It remains to examine the *central* interval \(|x|\le b/2\). The reference lower positive niche roof \(n_*(x)\) is strictly positive throughout the interior of its nondegenerate top-face interval \((-b,b)\); this is the explicit reference geometry (or CW's strict baseline-sweep statement under curvature domination and width \(2m>2\)). On the compact interval \([-b/2,b/2]\) its lower bound is positive. More precisely, at every \(x\) choose an interior turn angle witnessing strictly positive lower niche height; continuity of the corresponding two wall bounds in \(x\) and in the support function gives a neighborhood and a fixed positive clearance. Finitely many such neighborhoods cover the compact interval. Since \(B_\tau\to K_*\) in Hausdorff distance and the cap supports converge uniformly, there exists \(\eta>0\), independent of sufficiently small \(\tau\), such that
\[
n_{B_\tau}(x)\ge\eta\quad (|x|\le b/2).
\]
Here \(n_{B_\tau}\) denotes the **actual full** lower forbidden roof of the convex hull \(B_\tau\), not a clipped niche. Because \(B_\tau\) is invariant under reflection \(\rho(x,y)=(x,1-y)\), any point of its full canonical two-turn envelope has \(y\le1-\eta\) on that central interval. For \(\tau\) sufficiently small, \(\eta\ge b\tau/4\).

Combining the central forbidden-roof estimate with the external supporting-line estimate proves \(\max_{E_\tau}y\le1-b\tau/4\). The envelope \(E_\tau\) is itself \(\rho\)-invariant, so its minimum ordinate is at least \(b\tau/4\) as well. It is nonempty by HS.7, and compact, so the extrema are attained. QED.

**Scope of the obstruction.** HS.9 does **not** disprove the sign-only hull-symmetrization conjecture HS.4. It does rule out assigning a negligible (e.g. \(O(\tau^{3/2})\)) cost to restoring exact unit vertical span by a generic width-preserving operation: the geometric span defect is order \(\tau\), while the original area deficit is smaller order. AN2 separately gives an exact low-area full-turn counterexample to the simplest determinant-one affine normalization. A successful full-turn symmetry proof would have to establish both an area comparison *and* a compatible sharp symmetric area theorem or genuinely feasible normalization, rather than invoke RS2 at the wrong span.


**Corollary HS5 (no linear vertical-span stability).** There is no constant \(c>0\) for which every **x-reflection symmetric, connected, full-turn** sofa \(S\) with vertical span \(h\le1\) necessarily satisfies
\[
|S|\le M-c(1-h).
\tag{HS.12, false}
\]
Indeed \(E_\tau\) contains the midline belt intersection \(S_\tau\cap JS_\tau\) and has nonempty interval fibers through that common retained middle region, hence is connected and full-turn feasible. By HS.7 it has area at least \(M-C\tau^{3/2}\); by HS.10 its span is at most \(1-b\tau/2\). For any fixed \(c>0\), choose \(\tau\) so small that \(C\sqrt\tau<cb/2\). Then \(|E_\tau|>M-c(1-h_\tau)\), contradicting the proposed bound.

This is an exact negative result about a possible **symmetric near-unit-span stability estimate**, not a counterexample to \(|S|\le M\). It makes clear that a sharp extension of RS2 to subunit spans cannot be bought by a fixed linear penalty in the missing span. The construction is genuinely connected: both \(K_\tau\) and \(B_\tau\) contain the reference central belt, whose middle horizontal segment is retained by the original reference's full canonical turns; support monotonicity makes that segment survive the smaller \(B_\tau\) sweeps, and vertical sections of \(E_\tau\) are intervals. Its horizontal projection is complete since the extreme reference tips also survive. These fibers share the retained horizontal midline, proving connectedness.
