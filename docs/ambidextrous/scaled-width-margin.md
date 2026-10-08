# The existing analytic width gap survives a small width enlargement

**Scope.** This is a direct consequence of AW-W, useful in the short-face comparison. It uses only uniform scaling of a feasible body, not an anisotropic deformation or a new computation. Labels SW are local. It does not prove unrestricted optimality.

## 1. Uniform shrinking preserves both motions

Use a standard unit hallway

$$L=\{(x,y):x\le1,\ y\le1,\ x\ge0\ \text{or}\ y\ge0\}.$$

For 0<lambda<=1, lambda L is contained in L. If R_t S+b_t lies in L, then R_t(lambda S)+lambda b_t lies in lambda L, hence in L. The starting and terminal straight strips remain of width at most one, and their far translations can be extended as usual. This applies separately to both turns. Compactness and connectedness are preserved.

This is uniform Euclidean scaling. Compressing only the horizontal coordinate would not be justified by this argument.

## 2. Scaling the width-at-most-two theorem

AW-W states that every compact connected ambidextrous body in a common incoming strip of height at most one and horizontal width at most two has area strictly less than 41/25. The allowance of height at most one is essential here.

For a body of width W>2 choose lambda=2/W. Then lambda S has width two and incoming height at most lambda<1. Applying AW-W and scaling area gives

$$\boxed{|S|<\frac{41W^2}{100}.}\tag{SW.1}$$

For W<=2 the original bound applies without scaling.

**Lemma SW1.** Every body in that normalization with

$$W\le\frac{1001}{500}$$

satisfies

$$\boxed{|S|<\frac{41082041}{25000000}<M.}\tag{SW.2}$$

**Proof.** The rational bound is (41/25)(1001/1000)^2 and is larger than 41/25. Use SW.1 when W>2 and AW-W otherwise.

For the exact comparison, z=149/500 satisfies 4z^3+3z-1<0 and hence z<Y, the positive candidate root. Integration of 1/(1+t^2)>1-t^2 gives

$$M>1+4z^2+z-z^3/3=616648051/375000000.$$

The latter exceeds the displayed area bound by

$$104359/93750000>0.$$

No rounded approximation to M is used. QED.

The conclusion does not change the optimal value or require a new search. It simply spends part of AW-W's existing strict gap. In particular a potential body of area at least M has W>1001/500, not merely W>2.

## 3. Dependency boundary

This is a pen-and-paper corollary of the branch's analytic AW-W theorem and its stated height-at-most-one domain. It does not depend on the historical width certificate, TE's terminal-angle computation, matching certificates, weighted optimality or any curvature hypothesis. The prior AW-W proof still requires its own independent mathematical review. No CI, Lean/Lake compilation or numerical search is used.
