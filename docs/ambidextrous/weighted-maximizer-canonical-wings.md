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

The upper support of K equals the upper support of U. Indeed the top point (x,A(x)) of every fiber belongs to K because A(x)>=1-A(x). For a normal with nonnegative second component a support maximum can be taken at a top point. Consequently the f,g of K equal those of U. The lower supports of K are their reflected counterparts.

## 2. The complete outer flanks satisfy consistent safe-wall choices

Define F_R=K intersect {x>=b} and F_D=K intersect {x<=a}. The entire segments {a} times [0,1] and {b} times [0,1] lie in K and S_U: A=1 at a,b and n vanishes there by TF3.

For z=(x,y) in F_R and 0<t<pi/2,

$$
z\cdot n_t=x\cos t+y\sin t\ge b\cos t>f(t)-1.
\tag{MW.3}
$$

Reflect y to 1-y for the other turn. Limits give the corresponding non-strict inequalities at the axis angles. Thus F_R satisfies the first safe wall of both motions throughout the full quarter.

For z in F_D, (MW.2) gives

$$
z\cdot n_{t+pi/2}=-x\sin t+y\cos t\ge-a\sin t>g(t)-1.
\tag{MW.4}
$$

Reflection and limits give the other turn and the axis cases. Thus F_D satisfies the second safe wall throughout both turns. In particular both flanks consist of actual surviving material.

General avoidance of forbidden quadrants would not by itself prove a consistent choice of one wall across angles. Here MW.2 is the additional input.

## 3. Truncated canonical wings: height, width and support, not global survival

Fix beta in (0,pi/4), put L=pi/2, and use the canonical wings from the imported admission proposal:

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

**Theorem MW1.** R,D are nonempty compact convex subsets of K. Each has vertical span one, satisfies all directional-width inequalities TW.1, and retains the full outward-semicircle supports:

$$
\boxed{h_R(\theta)=h_K(\theta)\quad(-L\le\theta\le L),}
$$

$$
\boxed{h_D(\theta)=h_K(\theta)\quad(L\le\theta\le3L).}
\tag{MW.6}
$$

They contain F_R,F_D respectively.

**Proof.** They are closed half-plane intersections inside K. MW.3--MW.4 imply F_R subset R and F_D subset D, so the vertical segments at b,a give nonemptiness and full height. For theta in J_R,

$$h_R(\theta)\le h_K(\theta),\qquad h_R(\theta+\pi)\le1-h_K(\theta),$$

hence width at theta is at most one. Modulo pi, J_R covers [beta,pi-beta]. The same proof works for D.

For any (x,y) in K with x<b, the point (b,y) lies in F_R and dominates (x,y) for every normal with nonnegative first component. A support maximum over K can therefore be taken in F_R. Since F_R subset R subset K, the supports agree on the right semicircle, including its endpoints. Use (a,y) for D. QED.

The theorem intentionally does not say R,D subset S_U. Their truncated angle definitions leave some wall constraints unchecked. The first committed draft briefly overstated that inclusion and immediately flagged it; this version removes the conflicting statement and gives the valid all-angle substitute below. No area comparison uses the overstatement.

## 4. All-angle wings are actual surviving material and have diameter one

Define

$$
\overline R=K\cap\bigcap_{-L\le\theta\le L}
\{z:z\cdot n_\theta\ge h_K(\theta)-1\},
$$

$$
\overline D=K\cap\bigcap_{L\le\theta\le3L}
\{z:z\cdot n_\theta\ge h_K(\theta)-1\}.
\tag{MW.7}
$$

**Corollary MW2.** These all-angle wings are compact convex subsets of S_U, each of height and diameter exactly one. They retain the outward supports in MW.6 and satisfy TW.1 for every choice of beta.

**Proof.** MW.3--MW.4 again give F_R subset overline R and F_D subset overline D. The proof of MW1 gives support agreement and full height. A point of overline R meets the first safe wall of every lower and upper hallway, so lies in S_U; a point of overline D meets the second safe wall. Every normal or its opposite belongs to the chosen semicircle. Pairing the outer and inner support inequalities therefore bounds every directional width by one. For any two points use the normal parallel to their difference to obtain distance at most one. The retained vertical segment has length one, so the diameter is exactly one. QED.

The all-angle and truncated wings need not coincide. They have identical outward supports, but their inward cut supports and the resulting connector points can differ. Those different endpoint terms cannot be silently identified.

## 5. Consequence for the existing sharp auxiliary theorem

Choose beta to be the reference angle in SQ1. Both pairs (R,D) and (overline R,overline D) satisfy SQ1's arbitrary-cut-slack, full-height hypotheses. Hence the already stated calibration gives

$$
\widehat{\mathcal W}(R,D)\le M,\qquad
\widehat{\mathcal W}(\overline R,\overline D)\le M.
\tag{MW.8}
$$

No new functional optimization is required. Whole-core outer-support agreement, previously an additional admission hypothesis, is automatic for both pairs. K and the defining semicircles are invariant under y -> 1-y, so the wings are vertically symmetric; their two cut deficits are equal and their actual inward cut vertices lie at height one half.

This proves neither zero cut slack nor the contact signs at the fixed reference cuts. It does not establish containment in a correctly accounted core or pay the winding/uncovered-material terms. Consequently MW.8 is not yet |S_U|<=M. The exact bookkeeping WA.3 remains necessary.

The result bridges the weighted-maximizer construction to the established two-wing data domain. It does not bridge arbitrary ambidextrous maximizers to weighted maximality. A sharp weighted value and unrestricted optimality both remain open.

No CI, Lean/Lake compilation, numerical search, dependency installation, or manuscript build was used. These are self-reviewed written arguments with their dependencies visible.
