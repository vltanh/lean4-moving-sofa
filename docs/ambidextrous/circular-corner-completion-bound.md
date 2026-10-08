# A circular-corner bound for the cost of completing partial turns

**Statement and scope.** This strengthens the supplied PC2--PC4 localization. For a missing lower rotation epsilon and upper rotation epsilon', the completion allowance is

$$\lambda(\varepsilon)=\tan(\varepsilon/2)-\varepsilon/2,$$

rather than the larger triangular allowance in PC. Its leading term is epsilon^3/24 instead of epsilon^3/8. The comparison is an ordinary-area statement with signed empty-fiber corrections retained; it does not assert that deleting the missing quadrants leaves a connected competitor or that the remaining sharp margin has been proved. Labels CC are local.

Attribution: the two-strip corner-localization and signed-fiber strategy comes from the user-supplied `partial-turn-completion-package.zip`; see `partial-turn-package-audit.md` for its hashes, replay and qualifications. The exact circular-corner calculation below is the new strengthening. No computational result is a mathematical premise.

## 1. Two strips and their tangent wedge

Write L=pi/2 and alpha=L-epsilon, with 0<epsilon<L. A compact body with incoming vertical strip width at most one and outgoing strip normal n_alpha of width at most one lies in the parallelogram

$$P=\{0\le y\le1,\quad0\le z\cdot n_\alpha\le1\}$$

after translating the intersection A of the two lower supporting strip lines to zero. Put k=tan(epsilon/2). The common upper corner is D=(k,1). The lower cone is

$$C_A=\{z=u e_1+v n_{\alpha+L}:u,v\ge0\}.$$

The two tangent points

$$E=k e_1,\qquad F=k n_{\alpha+L}$$

satisfy D-E=n_L and D-F=n_alpha. Thus the unit circle centered at D is tangent to the two lower strip lines at E,F.

For every t in [alpha,L], n_t is a nonnegative linear combination of n_alpha,n_L. Hence D maximizes its scalar product over P. For the actual hull K contained in P,

$$h_K(t)\le D\cdot n_t.$$

Define the missing-first-wall region

$$\Omega_\varepsilon=\{z\in C_A:\ (D-z)\cdot n_t>1\text{ for some }t\in[\alpha,L]\}.$$

If z is forbidden by a late canonical quadrant of K and satisfies the two lower strip inequalities, then z lies in Omega_epsilon. This discards the second inner-wall condition only for an upper enclosure; no change of the original motion is assumed.

## 2. The entire union, not just an enclosing triangle

**Lemma CC1.** Omega_epsilon lies in the triangle AEF. Up to boundary sets of area zero, it is precisely the portion of this triangle outside the closed unit disk centered at D. Its area is

$$\boxed{|\Omega_\varepsilon|=k-\varepsilon/2=\lambda(\varepsilon).} \tag{CC.1}$$

**Proof of triangle containment.** If z=u e_1+v n_(alpha+L) has u+v>=k, write it as a convex combination of E,F plus a vector of C_A. For all t in [alpha,L], the scalar product of that last vector with n_t is nonnegative. Also

$$(D-E)\cdot n_t=\cos(L-t)\le1,\qquad
(D-F)\cdot n_t=\cos(t-\alpha)\le1.$$

Therefore (D-z) dot n_t<=1 for every t, and z is not in Omega_epsilon. This argument works for all 0<epsilon<L; the auxiliary epsilon<pi/3 convexity estimate in PC2 is unnecessary.

**Proof of the disk description.** For z in triangle AEF, D-z belongs to the cone spanned by n_alpha,n_L. Indeed D-E=n_L, D-F=n_alpha, and D-A=(k,1) has the bisector direction. A convex combination of these three vectors has an angle in [alpha,L]. Consequently

$$\max_{\alpha\le t\le L}(D-z)\cdot n_t=|D-z|.$$

Thus z is in Omega_epsilon exactly when |D-z|>1.

**Area.** The triangle AEF has area k^2 sin(epsilon)/2, the PC allowance. Its intersection with the disk is the small circular segment between the chord EF and its near arc, of central angle epsilon and area (epsilon-sin(epsilon))/2. Subtracting gives

$$|\Omega_\varepsilon|
=\tfrac12 k^2\sin\varepsilon-\tfrac12(\varepsilon-\sin\varepsilon)
=\tfrac12(1+k^2)\sin\varepsilon-\varepsilon/2
=k-\varepsilon/2.$$

All boundaries are finite line or circle arcs and have zero area. QED.

The equality describes the sharp region allowed by this *first-wall/two-strip relaxation*. It is not a claim that a connected ambidextrous body can fill all of Omega_epsilon while satisfying every other visited hallway.

## 3. Elementary size bounds and a rational form

Since epsilon/2=arctan(k),

$$\lambda(\varepsilon)=k-\arctan k=\int_0^k\frac{t^2}{1+t^2}\,dt.$$

Therefore

$$\boxed{\frac{k^3}{3(1+k^2)}\le\lambda(\varepsilon)\le\frac{k^3}{3}.} \tag{CC.2}$$

For 0<k<1 the alternating expansion gives

$$k^3/3-k^5/5\le\lambda\le k^3/3-k^5/5+k^7/7,$$

and further alternating terms yield entirely rational enclosures when k is rational. In terms of epsilon,

$$\lambda(\varepsilon)=\varepsilon^3/24+\varepsilon^5/240+O(\varepsilon^7).$$

The difference from PC's triangular allowance is exactly

$$\tau(\varepsilon)-\lambda(\varepsilon)
=\tfrac12(\varepsilon-\sin\varepsilon)>0.$$

For the previously established TE cutoff epsilon_0=L-2 arctan(29/50), the half tangent is exactly

$$k_0=\frac{1-29/50}{1+29/50}=\frac{21}{79}.$$

The illustrative per-turn values are lambda(epsilon_0) approximately 0.006008415 and tau(epsilon_0) approximately 0.017543826. The crude exact rational upper bound k_0^3/3 is already enough to bound the sum of both completion allowances by

$$\boxed{2\lambda(\varepsilon_0)<\frac{6174}{493039}.} \tag{CC.3}$$

This last numerical range uses TE as a separate, previously computer-certified premise. The geometric theorem CC1 and the next transfer theorem do not use TE, Gerver's theorem, or any computational certificate.

## 4. From the missing quadrants to an area comparison

Let S be a compact connected ambidextrous body in the unit incoming strip, with conventional turn magnitudes alpha=L-epsilon and gamma=L-epsilon', both in (0,L]. Let K=conv(S), with vertical hull fibers [B(x),A(x)] over I. The two full positive niche roofs are n_U,n_V; the actually visited ones are n_U^vis,n_V^vis. The upper cap roof is A_U=A, and the reflected-lower cap roof is A_V=1-B. Write d_U=1-A_U and d_V=1-A_V=B.

Because S is connected, it projects onto all of I; its visited canonical envelope has nonempty fibers of length

$$\ell_{vis}=1-\max(d_U,n_V^{vis})-\max(d_V,n_U^{vis})\ge0.$$

Define the possibly negative full signed length

$$\ell=1-\max(d_U,n_V)-\max(d_V,n_U).$$

There is an exact pointwise equality

$$\ell_{vis}=\ell+\xi_-+\xi_+,$$

where

$$\xi_-=\max(B,n_U)-\max(B,n_U^{vis})\ge0,$$

and xi_+ is its upper counterpart.

Every point counted by xi_- is above the actual hull floor B(x), not reached by the visited lower niche, and reached by some late lower quadrant. The floor point (x,B(x)) belongs to the two incoming/outgoing strips. Raising its y coordinate preserves their two lower inequalities, since both normals have nonnegative vertical component. Therefore the point belongs to C_A and then to Omega_epsilon by Section 1. Fubini gives

$$\int_I\xi_-\le|\Omega_\varepsilon|=\lambda(\varepsilon).$$

The reflected argument gives the upper bound. At epsilon=0 set lambda=0; there is no added angular interval.

**Theorem CC2 (signed-fiber completion transfer).** With the above data,

$$\boxed{|S|\le\int_I\ell\,dx+\lambda(\varepsilon)+\lambda(\varepsilon').} \tag{CC.4}$$

Equivalently, using only AS's pointwise algebra, the signed integral is C(U,V)-R(U,V). It follows also that

$$\boxed{|S|\le|E_{full}(K)|+\lambda(\varepsilon)+\lambda(\varepsilon'),} \tag{CC.5}$$

because the actual full envelope has fiber length ell_+=max(ell,0). CC.5 is a weaker consequence, not an identification of the signed integral with ordinary area.

These estimates count actual missing material. They do not require background curvature, contact topology, matching faces or convexity of S. They also do not claim the completed set is connected.

## 5. Exact empty-fiber and completion accounting

Put

$$Z=\int_I(-\ell)_+\,dx,\qquad \Xi=\int_I(\xi_-+\xi_+)\,dx.$$

Then

$$|E_{full}(K)|=\int_I\ell+Z,\qquad
|E_{vis}(K)|-|E_{full}(K)|=\Xi-Z.$$

The right side is nonnegative, since E_full is contained in E_vis. In particular 0<=Z<=Xi<=lambda(epsilon)+lambda(epsilon'). This separates signed empty-fiber overcount from the actual completion loss.

For a proof of optimality it would suffice to show, on the relevant partial-turn hulls,

$$\int_I\ell\,dx\le M-\Xi,$$

or the stronger sufficient uniform condition with Xi replaced by lambda(epsilon)+lambda(epsilon'). Neither inequality is proved here. For epsilon=epsilon'=0 this reduces exactly to the current full-turn target, which is also not closed.

If the full-turn theorem is eventually proved only for connected full-turn bodies, it cannot be applied to the total area of a potentially disconnected E_full without an additional component argument. The signed-fiber criterion above avoids that false implication but requires its stated larger-domain comparison.

## 6. Dependency and closure boundary

The PC package's main contribution is the localization and transfer, not its unproved PC6 margin. CC replaces its enclosing triangle by the exact tangent-circle corner region and removes an unnecessary small-angle restriction from that localization. The supplied numerical family is not a proof of genuine non-completion; the audit records its mesh and tolerance limitations.

This gives a quantitative bridge between the two problems, with a smaller cubic allowance. It is not a proof that every partial motion completes in place, that every completed set is connected, or that all the necessary cubic margins are available. Those remain explicit mathematical obligations. All newly asserted continuum statements above are hand proofs and remain subject to independent review. No CI, Lean/Lake compilation, dependency installation, manuscript build or long search was used.
