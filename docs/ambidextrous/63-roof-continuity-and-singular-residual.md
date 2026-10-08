# 63. Continuous roofs and the precise residual support of singular curvature

This assembles the new contact classifications with the previously proved singular-curvature improvements. The first step supplies a needed fact that compactness alone would not give: a positive vertical fiber of a canonical common-hull envelope has a positive gap on a neighborhood of its horizontal coordinate.

No smoothness or curvature cap is used for this continuity statement. Endpoint angles may still be partial.

## 63.1 Truncating near axis angles has uniformly small positive height

Let K be contained in 0<=y<=1 and in a disk of radius R about the chosen origin. For a lower motion through [0,alpha], with 0<alpha<=L=pi/2, set

\[
q_t(x)=\min\left\{
\frac{h(t)-1-x\cos t}{\sin t},
\frac{h(t+L)-1+x\sin t}{\cos t}
\right\}\quad(0<t<L),
\]

and define its clipped roof

\[
F_\alpha(x)=\max\{0,\sup_{t\in[0,\alpha]\cap(0,L)}q_t(x)\}.
\tag{63.1}
\]

The axis-angle quadrants add no positive height because h(L)<=1. A partial endpoint alpha<L is included in the supremum and is not discarded.

Fix |x|<=D and 0<epsilon<pi/4. For 0<t<epsilon,

\[
q_t(x)\leq\frac{h(t+L)-1+x\sin t}{\cos t}
\leq2(R+D)\varepsilon.
\tag{63.2}
\]

Use h(L)<=1 and the R-Lipschitz bound of the support function on unit normals. At L-epsilon<t<L the first wall gives the identical bound. These estimates do not require differentiating h.

Let F_alpha,epsilon be (63.1) with the angular set further restricted to [epsilon,L-epsilon], retaining the maximum with zero. If the restricted set is empty, define that function to be zero. Then, with C=2(R+D),

\[
0\leq F_\alpha-F_{\alpha,\varepsilon}\leq C\varepsilon
\quad\text{on }[-D,D].
\tag{63.3}
\]

## 63.2 Continuity and a modulus

**Lemma 115 (continuous clipped roofs).** F_alpha is continuous. On [-D,D],

\[
|F_\alpha(x)-F_\alpha(z)|
\leq2C\varepsilon+\cot(\varepsilon)|x-z|
\quad(0<\varepsilon<\pi/4).
\tag{63.4}
\]

In particular it has a uniform local Holder modulus of exponent one half. The reflected upper ceiling has the same properties.

**Proof.** On the truncated angular set, each of the two affine walls has slope of absolute value at most cot(epsilon). Taking their minimum, the angular supremum, and the maximum with zero preserves this Lipschitz constant. The supremum is over a compact set of continuous functions depending continuously on the parameter, and is finite. Thus F_alpha,epsilon is continuous and satisfies the stated Lipschitz bound. Equation (63.3) proves uniform convergence to F_alpha and then (63.4). Choosing epsilon proportional to the square root of |x-z| gives the local Holder estimate. Apply the same argument to the reflected hull for the upper ceiling. QED.

This proof uses small **height**, not bounded wall slope, to control the nearly axis-parallel angles. Their individual slopes can diverge.

## 63.3 Positive fiber length supplies the needed neighborhood clearance

Let E_K be a feasible common-hull saturation for lower and upper endpoint magnitudes alpha,gamma. Over the interior of the horizontal projection of K its fiber is

\[
[\lambda(x),\upsilon(x)]
=[\max\{b_K(x),F_\alpha(x)\},
\ \min\{t_K(x),1-F^{\rho}_\gamma(x)\}],
\tag{63.5}
\]

where b_K,t_K are the lower and upper convex-hull graphs and F^rho uses rho K. The hull graphs are continuous, indeed locally Lipschitz, in that projection interior. Lemma 115 shows the same continuity for the two niche bounds. Therefore both endpoints in (63.5), and their difference, are continuous there.

**Corollary 116 (pointwise-to-uniform clearance).** If upsilon(x_0)>lambda(x_0) at an interior projection coordinate, some neighborhood of x_0 has a positive uniform fiber gap.

**Proof.** Apply continuity to the positive number upsilon(x_0)-lambda(x_0). QED.

Compactness and vertical convexity alone would not justify this: the union of [-1,1] times {0} with {0} times [0,1] is compact, connected, and vertically convex, but has a positive fiber at zero and collapsed fibers arbitrarily close to it. It is not asserted to be a canonical sofa envelope. The counterexample identifies why the roof argument is necessary.

## 63.4 A residual-support theorem for a maximizing hull

Let S be a global maximizing body in the posed problem, put K=conv(S), and replace S by its same-hull canonical saturation of equal area. Use the established correctly signed motions. Consider an open interval of source normals for one lower wall that avoids all axis and endpoint-pinned normals and actually occurs in that motion. Let sigma_sc be the singular-continuous part of that quarter's curvature measure.

The following statement concerns sigma_sc-almost every source normal. At those normals the exposed face is a single regular point P(t), after removing the curvature-null exceptions described in Note 60. Let c(t) be the corner driven by the changed support component.

**Theorem 117 (localization of the remaining singular-continuous obstruction).** Apart from a sigma_sc-null set, each such source normal belongs to at least one of the following residual classes:

1. P(t) is itself a canonical inner corner of some placement in either motion;
2. c_x(t) is an endpoint of the horizontal projection of K;
3. c(t) is an actual collapsed surviving fiber and admits no local affine ceiling touching there with slope strictly between the two lower inner-wall slopes.

The analogous statement holds for the other lower wall and for the upper motion after reflection.

**Proof.** First remove the width-one set, which carries no singular-continuous curvature by Theorem 109. If P(t) meets the closure of a sweep, Theorem 110 and (60.4) imply class 1, outside the stated null exceptions. We may therefore assume strict outer clearance.

At sigma_sc-almost every point the good singular-density scales used in Note 58 are available. If c_x(t) is outside the closed projection, Theorem 107 excludes maximality. Projection endpoints are retained as class 2. Thus take an interior projection coordinate x_0.

If its surviving fiber has positive length, Corollary 116 supplies the neighborhood gap needed in Theorem 107, again excluding that singular-density point. If the lower endpoint is strictly above c_y(t), Corollary 113 excludes it even when the fiber is collapsed. The only remaining possibility is lambda(x_0)=upsilon(x_0)=c_y(t): the changed corner itself is the pinching point.

Finally, the countable-chart result of Note 62 shows that source singular curvature gives zero mass to oblique affine-ceiling pinches. Outside that null set the remaining pinches have exactly the failure described in class 3. This proves the alternative. QED.

The pointwise improvement excludes any good density point satisfying its geometry; no unsupported passage from individually null sets to an uncountable union is used. Note 62 supplies a countable measurable cover for its contact class.

## 63.5 What the theorem does not say

The three residual classes have **not** been proved null. In particular:

- the corner in class 1 can use support normals well separated from the normal of the touched outer point; Note 60 quantifies this nonlocal dependence;
- class 3 still includes genuine corner/corner pinches and parallel limiting configurations;
- edge atoms are not part of sigma_sc and need their own argument;
- the sharp bound on the remaining absolutely continuous density is still missing.

Consequently Theorem 117 is a precise localization of the singular-continuous problem, not a proof of global curvature domination. It neither completes partial endpoint angles nor establishes the two contact-order inequalities.

The gain over the preceding ledger is that arbitrary pinching, arbitrary single-wall coincidence, and inactive-corner effects are no longer undifferentiated obstructions. The unresolved cases are explicitly stated and are the ones a further global variation must address.

All changes are pen-and-paper Markdown. No CI, Lean/Lake compilation, numerical experiment, or computer algebra was used.
