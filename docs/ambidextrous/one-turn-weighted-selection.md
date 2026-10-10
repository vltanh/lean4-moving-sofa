# Polygon selection and the correct balance for every weighted cap maximizer

This is a selection theorem for the **signed** objective Psi=A-W/2, not for the positive-part numerical objective or an unrestricted ambidextrous body. It derives the width-penalty endpoint term rather than importing unpenalized cap maximality. The finite variations need no smoothness, positive surviving fibers, or niche containment. Labels WP are local.

Dependencies: PA2 supplies attainment; [HV1--HV2](one-turn-height-and-approximation.md) extend the domain to height at most one and give uniform finite-angle approximation. The arguments below are pen-and-paper. The selection pattern is related to the repository's one-turn Selection/Variation proofs, but their unpenalized maximality hypotheses are not used.

## 1. Fix an arbitrary maximizer, not a favorable one

Let U_star be any global maximizer of Psi among normalized caps, with value P. Translate it horizontally and choose R so its entire horizontal projection lies strictly inside (-R,R). Let K_R be the compact downward-closed cap class of HV2. Height at most one is allowed; HV1 shows that this has the same global maximum P as the height-one problem.

For n=2^k>=2 put delta=pi/(2n), theta_j=j delta for 0<=j<=2n. Let P_n be the nonempty caps in K_R cut out by y>=0 and half-planes at precisely this finite allowed list of normals. Redundant sides are permitted. This is a compact class: its supports at the fixed finite list are bounded, and the corresponding nonempty bounded intersections converge with those offsets. One may also check this directly from the finite set of pairwise line intersections, retaining degenerate caps.

Let N_n use the interior lower-turn angles theta_j, 1<=j<n. Define

$$F_n(U)=|U|-|N_n(U)|-W(U)/2.$$

For any cap U its circumscribed grid polygon P_n(U) contains U and has exactly the same support values at all grid normals: U supplies a supporting point and the defining half-plane supplies the opposite inequality. It has the same width and height, and belongs to P_n. It tends to U as the mesh tends to zero. Its finite niche is exactly N_n(U).

## 2. A finite penalty with summable derivatives

Use positive sample weights

$$w_0=w_{2n}=1/4,\qquad w_j=\delta/(2\pi)\quad(0<j<2n),$$

whose total is less than one. Put

$$D_n(U,U_*)^2=\sum_{j=0}^{2n}w_j[h_U(\theta_j)-h_{U_*}(\theta_j)]^2.$$

Let e_n be the uniform niche error in HV.1 and choose

$$\eta_n=\sqrt{e_n}+1/n.$$

Continuity and compactness give a maximizer U_n in P_n of

$$F_n(U)-\eta_n D_n(U,U_*)^2.$$

**Theorem WP1 (selection of the prescribed maximizer).** Every such selected sequence satisfies U_n -> U_star in Hausdorff distance.

**Proof.** The circumscribed polygon of U_star has zero sample penalty and objective at least P: its area is no smaller, its width unchanged, and its finite niche no larger than the full niche. On the other hand HV.1 gives F_n(U_n)<=Psi(U_n)+e_n<=P+e_n. Thus

$$0\le D_n(U_n,U_*)^2\le e_n/\eta_n\longrightarrow0.$$

Every subsequence has a Hausdorff-convergent further subsequence in K_R. Its supports converge uniformly. The sample sums converge to the endpoint terms plus (1/(2pi)) times the integral of the squared support difference on [0,pi]. This follows from uniform convergence and elementary Riemann sums. Its value zero forces equality of the continuous upper support functions. A downward-closed cap is determined by those upper supports and y>=0. Therefore the only limit is U_star, proving full convergence. QED.

The sequence is eventually strictly inside the artificial vertical sides of the box and has positive area. No numerical rate for e_n is asserted; the selection is a mathematical existence argument, not an implemented optimizer.

## 3. Outward facet variations keep all other sampled supports fixed

Write h_j=h_(U_n)(theta_j), let ell_j be the length of its outer facet at theta_j, and suppose ell_j>0. Move only that supporting line outward by e>0, keeping all other grid half-planes and the floor fixed. For sufficiently small e the new cap lies in K_R, provided j is not the top normal j=n and the artificial side boundaries are inactive.

Its new actual support at theta_j is h_j+e. A relative-interior point of the old facet has strict slack in every other nonparallel constraint, so a small outward displacement witnesses attainment. Every other sampled support remains h_i: old attaining points are retained, and the unchanged half-plane prevents any increase. The height remains at most one because the top half-plane is unchanged. This works even when some other grid facets have zero length.

Consequently the derivative of the penalty along this one-sided variation is exactly

$$2\eta_n w_j(h_j-h_{*,j}).$$

This is not a Lipschitz estimate charged once for every facet; the weights are retained, so the errors will be summable.

## 4. Ordinary finite polygon area derivatives

For an interior normal 0<j<n, changing h_j moves just the first inner wall of the quadrant at theta_j. Let tau_j be the length of the portion of that inner wall, on the forbidden side of its companion wall and above the floor, which is exposed on the boundary of the **full** finite niche N_n.

The outer cap-area right derivative is ell_j; the full niche-area right derivative is tau_j. To verify the latter, subtract the parts already covered by other quadrants. The added strips have thickness e along exactly the exposed portions. Every correction at a line intersection has area O(e^2). All nonhorizontal inner-wall normals are distinct in this one-turn grid, and none is parallel to the floor, so there are no positive-length coincident moving/fixed walls. Empty triangles born at a zero-height corner also have area O(e^2). There are finitely many intersections for a fixed grid. Thus this calculation does not need a stable smooth contact description.

The same argument holds on n<j<2n for the second wall. At j=0 and j=2n there is **no inner-wall term**: endpoint angles are not in N_n. Moving one of these outer sides increases width at speed one, so the signed penalized objective has derivative ell_j-1/2.

**Theorem WP2 (weighted floating and endpoint inequalities).** Put B=R+1 and

$$b_{n,j}=4B\eta_n w_j\ge0.$$

For all sufficiently large n, at every non-top interior grid normal,

$$\boxed{\ell_j\le\tau_j+b_{n,j},}$$

and at each horizontal side normal,

$$\boxed{\ell_0,\ell_{2n}\le\tfrac12+b_{n,0}.}$$

Moreover the sum of all b_(n,j) is at most 4B eta_n and tends to zero.

**Proof.** For a positive-length facet, maximality and the preceding outward variation give the inequality with the exact error 2 eta_n w_j(h_j-h_*,j). Its absolute value is at most 4B eta_n w_j because every point of either cap has norm at most B, so both supports have absolute value at most B. A zero-length facet satisfies the upper inequality trivially since tau and b are nonnegative; no false two-sided variation at a redundant side is needed. At the two endpoints apply the separate derivative ell-1/2 and use w_0=w_(2n). Sum the weights. QED.

The endpoint conclusion is an **upper bound**, not a balance sigma=tau for an endpoint niche wall. The companion trimming theorem supplies the lower bound only after passing back to an actual maximizer.

## 5. What this establishes and what it does not

The selected polygons target an arbitrary specified weighted maximizer, with summable interior errors and the correct one-half endpoint term. They do not maximize the unpenalized cap area against all caps. The next note combines WP2 with elementary neighboring-wall geometry to obtain regularity and exact endpoint edges in the limit.

No result here establishes the sharp value P=M/2, bounds the two-turn clipping correction, or transfers this one-turn maximality to an arbitrary ambidextrous maximizer. The entire objective and domain have been kept explicit to avoid those substitutions.

No CI, Lean/Lake compilation, or numerical maximization was used. This is a written, self-reviewed proof, not a kernel-verification claim.
