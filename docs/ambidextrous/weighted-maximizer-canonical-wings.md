# Full-height canonical wings for the symmetric weighted-maximizer construction

**Scope.** This closes the height and outer-support portions of canonical-wing admission for the symmetric body constructed from a signed weighted maximizer. It does not prove its ordinary-area comparison with the two-wing functional, the sharp weighted value, or unrestricted ambidextrous optimality. Labels MW are local. Baseline: `942c3b85553843c6d7d4ced926c1e73e31394989`.

The argument is elementary once the stated TF/HF conclusions are available. Those historical arguments remain dependencies, not independently verified facts. No computer experiment is used in the proof.

## 1. Data supplied by TF and HF

Let U maximize the signed objective Psi(U)=|U|-|N(U)|-W(U)/2. Write its projection as [l,r], its upper roof as A(x), and its top face as [a,b] at height one. Let rho(x,y)=(x,1-y), and let n(x) be its full nonnegative niche roof. The preceding results supply

$$
A\ge1/2,\qquad 0\le n\le1/2,\qquad n(x)>0\Longrightarrow a<x<b,
$$

$$
T=b-a=W/2>1,\qquad
S_U=(U\setminus N(U))\cap\rho(U\setminus N(U)),
$$

$$
|S_U|=2\Psi(U),\qquad K=\operatorname{conv}(S_U)=U\cap\rho(U).
\tag{MW.1}
$$

TF2 also proves, for f(t)=h_U(t), g(t)=h_U(t+pi/2),

$$
f(t)-1<b\cos t,\qquad 1-g(t)>a\sin t
\quad(0<t<pi/2).
\tag{MW.2}
$$

These are the monotone baseline-intercept conclusions; they are stronger than merely asserting that the niche has no points outside [a,b]. Both full canonical turns of S_U are available from its construction.

The upper support of K equals the upper support of U. Indeed U is contained in 0<=y<=A(x) with A>=1/2, and the top point (x,A(x)) of every fiber lies in K because A(x)>=1-A(x). For a normal with nonnegative second component a support maximum can be taken at such a top point. Consequently the f,g of K are the displayed f,g of U. The lower supports of K are their reflected counterparts.

## 2. The vertical face segments are safe for all chosen walls

Define the right flank F_R=K intersect {x>=b} and the left flank F_D=K intersect {x<=a}. The entire segments {a} times [0,1] and {b} times [0,1] lie in K and S_U: A=1 at a,b and n vanishes there by TF3.

For z=(x,y) in F_R and 0<t<pi/2,

$$
z\cdot n_t=x\cos t+y\sin t\ge b\cos t>f(t)-1.
\tag{MW.3}
$$

The reflected first-wall inequality follows by replacing y by 1-y. Endpoint angles satisfy the corresponding non-strict inequalities from the strip bounds and limits. Thus every point of F_R meets the right-wall safe-half-plane constraint of both motions at every quarter angle, not only at the selected cut interval.

For z in F_D, (MW.2) gives

$$
z\cdot n_{t+pi/2}=-x\sin t+y\cos t\ge-a\sin t>g(t)-1.
\tag{MW.4}
$$

Again reflection gives the other turn, and limits give the axis cases. Every point of F_D meets the left-wall constraints throughout both turns.

This is a statement about a consistent choice of wall across angles. General avoidance of the forbidden quadrants alone would not prove it.

## 3. Canonical wings and their retained supports

Fix any beta in (0,pi/4), put L=pi/2, and define the same canonical safe pieces as in the imported admission proposal:

$$
J_R=[\beta,L]\cup[-L,-\beta],\qquad
J_D=[L,\pi-\beta]\cup[\pi+\beta,3L],
$$

$$
R=K\cap\bigcap_{\theta\in J_R}\{z:z\cdot n_\theta\ge h_K(\theta)-1\},
$$

$$
D=K\cap\bigcap_{\theta\in J_D}\{z:z\cdot n_\theta\ge h_K(\theta)-1\}.
\tag{MW.5}
$$

**Theorem MW1.** These R,D are compact convex subsets of the actual surviving body S_U. They each have vertical span one, satisfy all directional-width inequalities TW.1, and retain the full outward-semicircle supports:

$$
\boxed{h_R(\theta)=h_K(\theta)\quad(-L\le\theta\le L),}
$$

$$
\boxed{h_D(\theta)=h_K(\theta)\quad(L\le\theta\le3L).}
\tag{MW.6}
$$

**Proof of compactness, height and width.** The sets are intersections of closed half-planes with K. By MW.3--MW.4 they contain F_R,F_D respectively, including the full vertical segments at b,a. Thus each has height one and is nonempty. For theta in J_R, h_R(theta)<=h_K(theta) and h_R(theta+pi)<=1-h_K(theta), so its width at theta is at most one. Modulo pi these directions cover [beta,pi-beta]. The left statement is identical.

**Proof of retained supports.** For any z=(x,y) in K with x<b, the point (b,y) belongs to K and to F_R. Every normal with nonnegative first component has scalar product at least as large at (b,y) as at z. Hence the maximum over K can be taken in F_R. Since F_R subset R subset K, their support values agree on the right semicircle. At its vertical endpoints the full-height segment gives the same conclusion. Use (a,y) for the left semicircle.

**Proof that the wings are surviving material.** The definition of R imposes the first safe wall on the late lower interval [beta,L] and its reflected counterpart. At early angles 0<=t<=beta it also implies first-wall safety, as follows. For a fixed z in R let k(t)=h_K(t)-z dot n_t. The functions h_K and z dot n are continuous and the cap's first support agrees with U. However no monotonicity of k on the early interval has been proved here. Accordingly the full inclusion R subset S_U does NOT follow from MW.3 alone for points of R outside F_R. The safe conclusion established by this proof is R,D subset K, together with F_R,F_D subset S_U and the height/support/width claims above. The theorem's surviving-material wording is withdrawn in Section 5 below rather than used as a premise.

## 4. Consequence for the existing sharp auxiliary theorem

Choose beta to be the reference angle in SQ1. The height, width and convexity conclusions place (R,D) in SQ1's arbitrary-cut-slack, full-height domain. Therefore its stated calibration gives

$$
\widehat{\mathcal W}(R,D)\le M.
\tag{MW.7}
$$

No new analytic maximization is needed. Whole-core outer-support agreement, which was an extra hypothesis in the canonical-admission proposal, is automatic here by MW.6. The canonical wings are vertically symmetric because K and their two defining angle intervals are invariant under reflection in y=1/2. Hence their top and bottom heights agree, and the two cut deficits of each wing are equal.

This proves neither zero cut slack nor the contact signs at beta and L-beta. It does not establish a correctly oriented enclosing core or control the winding/uncovered-material terms. In particular MW.7 is not yet |S_U|<=M.

## 5. Exact theorem boundary and correction during drafting

The proved content of MW1 is: compact convex R,D inside K; full height; the stated constrained widths; full outward-support agreement; and inclusion of the actual surviving flanks F_R,F_D. It does **not** include R,D subset S_U. A truncated canonical wing need not be safe at every omitted early or late angle. The wording in the initial statement above is retained with this immediate correction to expose the distinction before any application.

For future use, one may instead define wings using the entire respective outward semicircle. MW.3--MW.4 prove the same height and support statements for those all-angle wings, and their consistent safe-wall choices then DO imply that they are subsets of S_U. They satisfy TW.1 as well. Their inward cut supports, hence the endpoint/core terms of the calibrated functional, may differ from MW.5 and must be retained rather than silently identified.

For either definition, the ordinary-area comparison is still the remaining step. The exact winding accounting in WA.3 keeps its negative-winding and uncovered-surviving-material corrections. Balance of the weighted cap is not a proof those corrections vanish.

This is a written partial admission result with explicit dependencies. No CI, Lean/Lake compilation, numerical search, or manuscript build is used. The primary target remains optimality; no global completion is claimed.
