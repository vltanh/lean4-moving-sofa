# 21. Why the single-turn side-balance proof does not yet give the missing regularity

The restricted theorem now has no face-alignment gap. The remaining task is to control endpoint angles and the regularity/curvature/contact conditions for arbitrary maximizers. This note records a concrete obstruction to importing the existing single-turn polygon balance calculation unchanged. The strongest subsequent geometric statement is [Theorem 52](23-sobolev-geometric-theorem.md).

The source being compared is the repository's [single-turn variation section](../paper/sections/05-variations.tex). Its outer-side term is a full cap edge length. For a two-turn intersection the correct term is initially the **visible** part of that edge, and equality with the full length requires a geometric proof.

## 21.1 A finite-configuration derivative

Consider a convex polygon K described by outer supporting half-planes, together with finitely many forbidden quadrants for the two turn directions. Let E be K with their union removed. Raise one floating support height h(theta) by epsilon, keeping all other heights fixed. Suppose this height controls one outer edge of K and one parallel inner wall of a single forbidden quadrant; its companion inner wall is fixed.

Assume the relevant vertices and line intersections are transverse, no overlapping line segments occur at the moving interfaces, and the local combinatorics persist for small positive and negative epsilon. These hypotheses make all area changes piecewise differentiable and reduce the calculation to strips plus O(epsilon squared) vertex triangles.

Let sigma_visible(theta) be the length of the portion of the moving outer edge not covered by any forbidden quadrant. Let tau_visible(theta) be the length of the moving inner wall inside K, on the forbidden side of its companion wall, and not already covered by another forbidden quadrant.

**Proposition 48 (visible-side balance formula).** Under these hypotheses,

\[
\left.\frac{d}{d\varepsilon}|E_\varepsilon|\right|_{\varepsilon=0}
=\sigma_{\rm visible}(\theta)-\tau_{\rm visible}(\theta).
\tag{21.1}
\]

**Proof.** Raising the outer line adds a strip of normal thickness epsilon along the portions exposed to the surviving set. A portion already covered by another forbidden quadrant contributes no surviving area to first order. Raising the inner wall expands its forbidden quadrant and removes a strip along the portion not already removed by the others. Intersections of the moving strips with moving or fixed vertices have area O(epsilon squared) under the transversality assumptions. Sum the strip areas, divide by epsilon, and pass to zero. QED.

For a genuine maximizer the corresponding derivative is zero only if both signs of the perturbation are admissible. One-sided admissibility gives only the matching one-sided inequality. Connectedness of the surviving body, endpoint strip constraints, and preservation of the common-hull representation must also be verified before invoking maximality.

## 21.2 A canonical finite-angle example with a hidden outer-edge segment

Put

\[
d=\sqrt2-\tfrac12,
\qquad
K=\{(x,y):-d\leq x\leq d,\quad0\leq y\leq\tfrac34+\tfrac14x\}.
\tag{21.2}
\]

This compact convex trapezoid lies in the incoming unit strip: d<1, so its sloping upper edge stays strictly between y=0 and y=1, while its bottom edge is y=0. At the upper-turn dual angle -pi/4, take the frame

\[
u=(1,-1)/\sqrt2,\qquad v=(-1,-1)/\sqrt2.
\]

Its two support values are both d/sqrt(2), attained at the two bottom vertices. Therefore the canonical corner is (0,1/2), and the corresponding forbidden quadrant is

\[
W=\{(x,y):y>\tfrac12+|x|\}.
\tag{21.3}
\]

The sloping top edge of K lies in W precisely where

\[
-\tfrac15<x<\tfrac13.
\tag{21.4}
\]

Indeed, compare 3/4+x/4 with 1/2+|x| separately on x<=0 and x>=0. Both endpoints of the top edge lie outside W, as do both bottom vertices. The set E=K minus W is compact and connected, because its vertical sections are the nonempty intervals

\[
[0,\ \min\{3/4+x/4,\ 1/2+|x|\}].
\]

All four vertices survive, so conv(E)=K. Nevertheless a positive-length middle portion of a **nonhorizontal** outer edge is hidden in the opposite-turn quadrant. Its visible length is strictly smaller than its full length.

This is a finite-angle canonical configuration, not a claimed complete ambidextrous motion. Its role is exact and limited: connectedness, common-hull retention, and canonical placement alone do not identify the visible outer-edge length with the whole edge length. A full-motion or maximizing argument could impose more conditions, but those conditions need proof.

## 21.3 Consequence for the attempted regularity reduction

The single-turn floating-height argument compares the cap's outer edge length with an inner-wall length. Equation (21.1) is the quantity obtained directly in the two-turn setting. Replacing sigma_visible by sigma_K without justification can overstate the first-order gain, so it cannot currently establish the desired curvature-measure bound.

A valid continuation must do one of the following:

- prove that every relevant floating edge is fully visible for the selected maximizing configurations;
- retain both visible and hidden edge measures in the balance argument and show that the resulting system still yields the needed regularity;
- use a different relaxation with a proved sharp geometric comparison.

The finite example does not refute the desired regularity theorem. It records why the immediate transplantation of the existing proof does not establish it. Likewise, the full-angle extension has not been derived from the width-only argument rejected in Note 15.

## 21.4 Current stopping point of the derivation

The exact adaptive maximum, its equality kernel, and the geometric theorem on the stated regular class are proved in writing; Notes 22–23 further weaken that class's assumptions. The unrestricted conclusion is not proved because a justified reduction of arbitrary competitive bodies or maximizers to that full-turn support-function class is still missing. The missing step is now a concrete geometric/variational theorem, rather than an unspecified search for the sharp constant or for an equality argument.
