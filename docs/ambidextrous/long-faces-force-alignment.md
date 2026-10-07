# Two long horizontal faces force alignment

**Scope.** This combines the initial floor-trace geometry of the imported one-turn proposal with FL1 and the newly established weighted bound. It gives an ordinary-area theorem without assuming face alignment in advance. It does not prove that both faces of every maximizer are long. Labels LF are local.

Use the branch's common incoming strip 0<=y<=1 and K=conv(S), where S is a compact connected ambidextrous body. Assume K has vertical span one. Write its horizontal projection as [l,r], its top face as [a_+,b_+] at height one, and its bottom face as [a_-,b_-] at height zero.

## 1. Initial angles force the left endpoints to agree

Suppose |S|>8/5, so the earlier canonical/sign reduction supplies conventional lower and upper motions starting at angle zero. Only arbitrarily small positive angles are needed in this section.

For the lower motion, take the upper support h of K. The rightmost support tends to r as t decreases to zero, while the right derivative at the vertical normal is h'(pi/2+)=-a_+. Thus for a floor point (x,0) with a_+<x<r-1, the two inner-wall gaps are

$$h(t)-1-x\cos t\longrightarrow r-1-x>0,$$

$$h(t+pi/2)-1+x\sin t=(x-a_+)t+o(t)>0.$$

The point is forbidden by some sufficiently small positive angle. Consequently no retained bottom-face endpoint lies in (a_+,r-1). For the upper motion, reflection in y=1/2 gives the counterpart: no retained top-face endpoint lies in (a_-,r-1). These statements require no curvature or smooth support assumption; convex supports have the stated one-sided directional derivatives.

Now suppose both face lengths are strictly greater than one. Then

$$a_+\le r-(b_+-a_+)<r-1,\qquad a_-<r-1.$$

The retained bottom endpoint (a_-,0) cannot lie in (a_+,r-1), so a_-<=a_+. The retained top endpoint (a_+,1) gives the reverse inequality. Hence

$$\boxed{a_-=a_+=a.}\tag{LF.1}$$

The endpoints are retained because endpoints of an exposed face are extreme points of K and extreme points of the convex hull of a compact set belong to that set.

## 2. The full turns and right endpoints

The common portions of the two faces now have length greater than one. Their convex hull contains an axis-aligned unit square. As in FL Section 2, its width cos(omega)+sin(omega)>1 excludes a partial outgoing angle omega in (0,pi/2). Thus both conventional turns are full.

For the lower motion near t=pi/2, put epsilon=pi/2-t. The upper support expansion is h(t)=1+b_+ epsilon+o(epsilon). At a floor point with l+1<x<b_+,

$$h(t)-1-x\cos t=(b_+-x)\varepsilon+o(\varepsilon)>0,$$

$$h(t+pi/2)-1+x\sin t\longrightarrow x-l-1>0.$$

So no retained bottom-face endpoint lies in (l+1,b_+). Reflection gives the same exclusion of top-face endpoints from (l+1,b_-). Both b_+,b_- are strictly greater than l+1 because their face lengths exceed one. It follows that b_->=b_+ and b_+>=b_-, hence

$$\boxed{b_-=b_+=b.}\tag{LF.2}$$

Both faces therefore coincide and their common length exceeds one.

## 3. Ordinary-area consequence

**Theorem LF1.** If both horizontal exposed faces of the unit-span common hull have length strictly greater than one, then

$$\boxed{|S|\le M.}\tag{LF.3}$$

For |S|<=8/5 this is immediate. Otherwise Sections 1--2 force the aligned long-face geometry, and FL1 proves the ordinary-area bound using WV2. No symmetry, curvature, contact-order or prior full-turn assumption is made.

Equivalently, any feasible body in this normalization with area greater than M must have at least one horizontal face of length at most one. This is a necessary condition for a counterexample, not a proof that the short-face class is strictly suboptimal. In particular, it does not dismiss the known near-candidate point-face families.

The endpoint strictness matters. The argument used both left endpoints strictly below r-1 and both right endpoints strictly above l+1. Replacing the two assumptions >1 by >=1 requires separate boundary analysis and is not done here. FL1 still covers already aligned faces of length exactly one.

This is a pen-and-paper application of the floor-trace idea already recorded in OT3. No novelty claim is made for that elementary classification. The new payoff is the curvature-free ordinary-area theorem supplied by the weighted value. Unrestricted optimality still requires a sharp comparison for the remaining short-face class or a valid maximality-based reduction excluding it.

No computer calculation, CI, Lean/Lake compilation, dependency installation, or manuscript build was used.
