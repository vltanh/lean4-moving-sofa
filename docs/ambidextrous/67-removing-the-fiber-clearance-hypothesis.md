# 67. Pinching fibers do not protect singular-continuous curvature at a clear outer point

This combines the preceding operations with a contact calculation at a stationary blocking corner. The result removes the fiber-clearance qualification from the singular-continuous exclusion at a general maximizing hull. It does not remove the requirement that the affected outer point be strictly clear of the two swept niches.

The proof handles pinches using their actual constraints. It does not assume a differentiable global roof, a finite contact partition, full quarter turns, or proximity to the candidate. The remaining outer/inner-corner coincidence problem and the sharp absolutely continuous density bound are not solved here.

## 67.1 Two elementary BV locality facts

**Lemma 127 (level-set locality with one-sided traces).**

(a) If u is a one-dimensional BV function, its derivative measure restricts to zero on any set where both traces of u equal a fixed constant.

(b) If v is locally Lipschitz with v' locally BV, the nonatomic part of D²v is zero on {v=0}. If v>=0, every atom of D²v on that set is nonnegative.

**Proof.** For (a), first take a compact subset F of the stated set. The measure Du has no atoms at points of F. If F has at least two points, its mass on the interval between its endpoints is zero by the common endpoint values. Every complementary interval of F has endpoints with the same value and also has zero Du mass. Subtract the countable sum of these interval masses; it converges absolutely because u has finite variation. Thus Du(F)=0. The same calculation on every compact subset, followed by regularity of the signed measure, gives the restriction identity. A singleton follows from continuity of u there.

For (b), one-sided derivatives of v exist as the one-sided traces of its regulated derivative v'. Except at a countable set of isolated level points and endpoints of complementary intervals, a point of {v=0} is approached by level points from both sides. The corresponding difference quotients show v'_-=v'_+=0 there. Apply (a) to v' and discard the countable set for the nonatomic measure. At a zero of a nonnegative v, v'_-<=0<=v'_+, so its derivative jump, the atom of D²v, is nonnegative. QED.

No semiconvexity is required for this version. It is a measure restriction, not a neighborhood assertion.

For the velocities p,q of (65.1), equation (65.2) and part (a) give

\[
\sigma_f|_{\{p_-=p_+=a\}}=(q+1)dt|_{\{p_-=p_+=a\}},
\]

\[
\sigma_g|_{\{q_-=q_+=b\}}=(1-p)dt|_{\{q_-=q_+=b\}}.
\tag{67.1}
\]

Thus singular first-source curvature cannot charge a continuous level set of p; singular second-source curvature cannot charge a continuous level set of q. In particular, a simultaneously stationary source p=q=0 carries no source singular curvature. This does not yet say what happens when a *different*, blocking corner is stationary.

## 67.2 A stationary blocking corner forces exact velocities at the other corner

Let P be a common lower and upper canonical corner at angles t and s, respectively. Use the lower frame mu_t,nu_t and the upper frame

\[
e_s=(\cos s,-\sin s),\qquad j_s=(-\sin s,-\cos s).
\]

Suppose one pair of one-sided traces of the lower velocities is p=q=0. The corresponding outer support contacts are then

\[
A=P+\mu_t,\qquad C=P+\nu_t.
\tag{67.2}
\]

Each is an exposed-face endpoint, or a singleton exposed point, of K. If K=conv(S) with S compact, both belong to S by Lemma 45. This remains true when the other traces at these normals differ: only the indicated face endpoints are used.

At the upper corner, their coordinates relative to P are

\[
(A-P)\cdot(e_s,j_s)=(\cos(t+s),-\sin(t+s)),
\]

\[
(C-P)\cdot(e_s,j_s)=(-\sin(t+s),-\cos(t+s)).
\]

For 0<t+s<pi, simultaneous avoidance of the open upper forbidden quadrant forces cos(t+s)=0. Hence t+s=pi/2, and these pairs of coordinates are (0,-1) and (-1,0).

Assume the upper angle s is in the interior of its motion interval. The fixed point A has its second inner inequality strictly violated at s, so its first inner-wall coordinate must be nonnegative for nearby parameters. That coordinate has value zero at s and one-sided derivatives -p_{upper,-}-1 and -p_{upper,+}-1. Its local minimum gives

\[
p_{upper,-}\geq-1,\qquad p_{upper,+}\leq-1.
\]

The support jump satisfies p_{upper,+}>=p_{upper,-}, so both equal -1. Testing the fixed point C against the other inner wall similarly gives q_{upper,-}=q_{upper,+}=1.

**Lemma 128 (stationary-corner reciprocity).** If one of two coincident opposite-turn corners has a stationary one-sided trace pair, and the other angle is interior, then the other corner has

\[
\boxed{p_-=p_+=-1,\qquad q_-=q_+=1.}
\tag{67.3}
\]

In particular neither source measure has an atom at that other angle. Its two source measures have no singular-continuous mass on the set of angles so obtained, by (67.1).

**Proof.** The preceding point and one-sided derivative tests prove the statement for a stationary lower corner. Reflect the strip and exchange the turns for the other case. The jumps of both p and q are the nonnegative source atoms, so equality of the traces excludes those atoms. Finally (67.1), on the joint level set p=-1,q=1, gives both source measures equal to 2dt there. QED.

The differentiation is in the *other*, interior motion angle. The stationary blocking corner itself may occur at an endpoint. No differentiability of curvature is used. At the axis endpoint cases that make t+s=0 or pi, the other angle cannot be an interior conventional angle; these are not applications of the lemma.

## 67.3 A pinch comparison only needs nonzero horizontal speed near each contact

The fixed velocity orthants in Note 65 can be weakened. Let two corner paths have bi-Lipschitz abscissae on compact interior parameter charts, with one-sided |a| bounded below and p,q bounded. They need not have opposite velocity signs throughout the charts. Define their lower and upper graphs F,G over an overlapping interval I in the body's projection.

Feasibility still gives v=G-F>=0. Their derivatives are BV, and the exact formulas (65.5)–(65.7) remain valid. At a point of Z={F=G}, the point lies in S and each selected corner is active. At a nonatomic parameter, the local-maximum test for min(R,L) gives

\[
p\leq0\leq q\quad\text{when }a<0,
\qquad q\leq0\leq p\quad\text{when }a>0.
\tag{67.4}
\]

Thus the curvature coefficients in those formulas are nonnegative **on Z**, even though they need not be nonnegative away from it.

At a jump with a<0 on both sides, the left limiting wall is L and the right one is R. Feasibility gives q_- >=0 and p_+ <=0. Since both velocity jumps are nonnegative, all traces have the standard signs. For a>0 the same argument gives the reverse signs. Formula (65.6), with its orientation factor, therefore also gives a nonnegative graph jump at Z.

By Lemma 127(b), the nonatomic part of D²v restricts to zero on Z. Its curvature terms there have negative sign and nonnegative coefficients, while all remaining terms have bounded Lebesgue density. Hence each positively weighted source curvature restricted to Z is absolutely continuous in the graph coordinate, and therefore in its bi-Lipschitz source parameter. Atoms of D²v on Z must be nonnegative by Lemma 127; the two graph jump contributions have the opposite sign, so both weighted jumps must vanish.

**Lemma 129 (nonstationary two-corner pinch comparison).** On these charts, singular first-source curvature is excluded from the zero-gap set wherever q is bounded away from zero. Singular second-source curvature is excluded wherever p is bounded away from zero. The atom statement uses the exact trace weights in (65.6).

**Proof.** Restrict the exact derivative-measure identities to Z and use the signs just proved and Lemma 127. A positive lower bound on a curvature coefficient gives measure domination by a constant times dx there. Pull back by the bi-Lipschitz graph parameter map. Bounds |q|>=1/n or |p|>=1/n and a countable cover exhaust the nonzero-coefficient sets. QED.

This argument does not claim that all graph second derivatives have a global sign. The positivity needed is only on the feasible contact set. It therefore includes a nonstationary blocking corner with a zero component or changing nearby contact type.

## 67.4 All clear singular-continuous contacts at a maximizer are excluded

Fix any normalized global maximizer and its correctly signed canonical motions, possibly partial. Replace the body by its same-hull saturation of equal area. On each floating support-normal interval, let the clear set consist of normals whose unique exposed point has positive distance from the closures of both swept niches.

**Theorem 130 (outer clearance alone excludes singular-continuous curvature).** The singular-continuous curvature measure of this maximizing hull gives zero mass to the clear set. No assumption on surviving-fiber clearance is required.

**Proof.** Work with one source quarter; reflection and exchange cover the others. Remove the countable sets of source or companion curvature atoms, and the null sets where the differentiation scales of Note 58 fail. The source support derivatives are then continuous at the remaining points.

For first-source singular curvature, (67.1) removes p=0. If q=0, Theorem 125 applies: p is nonzero and the clear exposed point supplies the retained gain, while the uniform-error scaling pays for any pinch. For second-source curvature exchange p and q. Thus it remains to treat source points with both velocities nonzero.

If the source corner is outside the horizontal projection or at its endpoints, Note 64 puts it strictly outside the incoming strip on the harmless side. If it is strictly inactive, Proposition 112 retains the old body. If its surviving fiber has positive length, roof continuity in Note 63 gives the neighborhood clearance used by Theorem 107. The corresponding actual improvements exclude all these cases at a maximizer.

The remaining source corner P is the sole point of its surviving fiber. It lies in the interior projection, and source feasibility makes it a local maximum of the lower min-wall roof. The first-order signs give opposite signs for its two nonzero velocities. Its abscissa is therefore locally bi-Lipschitz, and it supplies a lower graph F near P_x.

Consider what supplies the upper endpoint of that fiber.

* If it is the top boundary of K, a nonvertical supporting line there is an affine ceiling. If an upper-turn constraint has only one active wall at P, that wall likewise supplies an affine ceiling in a neighborhood. Its slope must equal F'(P_x), because it majorizes F and touches it there. The strict opposite source signs put this slope strictly between -cot(t) and tan(t). The oblique-ceiling measure theorem, Theorem 114, excludes the source singular measure on these contacts.

* Otherwise an upper corner equals P. Such an angle is attained: above a positive reflected roof height the axis-angle constraints have limiting height zero in the reflected lower-strip description, while the interior wall functions are continuous in their parameter. Compactness therefore supplies either an interior parameter or the partial terminal one. If P is on y=1, the top-hull case already applies.

There are only finitely many terminal angles and countably many upper support-jump parameters. Their corner images form a countable set. Each has at most one preimage in a source bi-Lipschitz chart, so source singular-continuous curvature gives them zero mass.

At each remaining blocking parameter, both support derivatives are continuous. If its horizontal corner speed is nonzero, it too has a local bi-Lipschitz graph. Lemma 129 excludes the source singular measure, since the current source coefficient is nonzero. If its horizontal speed is zero, the local maximum test at a differentiable corner forces its two velocities to have opposite weak signs. The equation p cos(t)-q sin(t)=0 then forces p=q=0. Lemma 128 makes the current source velocities exactly -1,1, a set carrying no source singular measure by (67.1).

All graph applications can be made on rational-ended parameter intervals and rational interior x-intervals with integer bounds on the speeds and derivative traces. This is a countable chart cover. The affine-ceiling theorem already handles its uniform ceiling families by a countable localization. The stationary case is contained in an explicit constant-velocity level set, not an uncountable union of individual null sets.

Every remaining case is therefore either null for the source singular measure or admits a strict area improvement. This proves the claim. A support normal used by no inner wall has an even simpler improvement: the outer circular enlargement does not change either niche. The finitely many pinned normals carry no singular-continuous mass. QED.

The key point is not that a collapsed fiber has negligible area. The proof either constrains its source measure by actual contact identities or pays a provably lower-order cost to restore feasibility.

## 67.5 What remains of the singular-continuous problem

**Corollary 131 (only outer/inner-corner coincidences remain).** Up to a null set, the singular-continuous curvature of a maximizing hull can be supported only at outer points that themselves coincide with a canonical inner corner of one of the two motions.

**Proof.** Theorem 110 classifies a nonatomic outer contact as strict clearance, a single-wall width-one contact, or an inner-corner coincidence. Theorem 130 eliminates strict clearance. The width-level identity in Theorem 109 eliminates singular-continuous curvature at width one. The remaining alternative is the claimed coincidence. QED.

This conclusion is about the *outer point belonging to the source normal*. It is different from the source inner corner being a pinching point elsewhere on the body. The latter no longer needs to be listed as an independent singular-continuous obstruction at a clear outer point.

Corollary 131 does not prove that the remaining coincidence set has zero curvature. Hidden/coincident exposed-edge atoms, the sharp bound on absolutely continuous density, full-quarter endpoints and the contact-order inequalities remain additional unrestricted obligations. The sharp conditional theorem is not promoted to an unrestricted result by this corollary.

## 67.6 An atomic extension of the zero-coefficient repair

The same-sign, nonzero companion-trace assumption in the atom version of Section 66.5 can be relaxed in its zero-coefficient case. For example, for a first-source atom assume q_-=q_+=0, but do not assume p is bounded away from zero. Then sup_J |q| tends to zero and the circular replacement has U=O(r).

On the corner band the unchanged L family has parameter derivative bounded by C(r+sup_J|q|). The new R value at any parameter is no larger than one of the two old endpoint R values, because its transformed family is affine with unchanged endpoints. Choose that endpoint, at distance at most 2r, instead of solving for an interior parameter as in Section 66.2. This gives a uniform roof error

\[
e_r\leq C(r+\sup_J|q|)r=o(r).
\]

A strictly clear outer-edge subsegment still gains area at least c r before scaling. Lemma 123 therefore yields a strict feasible improvement. The second-source version has p_-=p_+=0. This includes a stationary one-sided source trace with an atom on the other side, whenever the indicated companion traces vanish.

This does not remove all atomic pinch cases. In particular an opposite partial-terminal corner cannot be discarded merely because there are only finitely many such points: an atomic measure can charge their preimages. The countability step in Theorem 130 is deliberately confined to singular-continuous curvature.

Only written estimates, contact identities, and the standard measure inputs already cited in the preceding notes were used. No CI, Lean/Lake compilation, numerical experiment, or computer algebra was used. The proof chain remains subject to independent review.
