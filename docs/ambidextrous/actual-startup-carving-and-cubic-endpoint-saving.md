# Actual startup carving versus recoverable area: a general cubic endpoint theorem

**Status:** Self-contained geometric proofs for arbitrary compact convex outer hulls, without assuming that the sofa itself is convex, symmetric, smooth, close to Romik, or has a prescribed contact pattern. These results address the proposed saving from avoiding early corner intrusion. They do **not** prove Romik optimality or exhibit a larger sofa.

The important distinction is between (i) all hull material touched by early corner positions and (ii) material touched **only** by those positions and not by any later position. The first can be linear in the initial angle. The second has a **uniform cubic upper bound**, proved below, even before imposing outgoing straight-arm strips. Consequently an apparent large startup cut is not an equally large recoverable area saving.

The exact ordinary startup coefficient also generalizes [IW.6](initial-corner-activation-and-face-asymmetry.md) beyond its common-face-rectangle assumption. In particular, all four coefficients vanish for opposite-end faces, and strictly opposite-end faces have entire endpoint intervals with **no actual hull carving**. Positive ambient corner height is not the same as lost material.

## 1. Geometry and the two quantities being compared

Let K be a compact convex body of positive area contained in R x [0,H], where 0 < H <= 1. Its horizontal projection is [l,r], of width W=r-l. Set

\[
u_t=(\cos t,\sin t),\quad v_t=(-\sin t,\cos t),\quad L=\pi/2,
\]
\[
Q_t(K)=\{p:p\cdot u_t<h_K(u_t)-1,\ p\cdot v_t<h_K(v_t)-1\}.
\]

This is the open quadrant forbidden by the two inner-wall rays when the outer walls support K. All areas below are ordinary set areas, with unions counted once and intersections with K retained.

For 0 < tau < T <= L, define

\[
A_K(\tau)=\left|K\cap\bigcup_{0<t\le\tau}Q_t(K)\right|
\tag{EC.1}
\]

and let E_[a,b](K) be the intersection of K with the complements of all Q_t(K), a <= t <= b. The area gained by deleting the initial angle interval is

\[
G_K(\tau;T)=|E_{[\tau,T]}(K)|-|E_{[0,T]}(K)|\ge0.
\tag{EC.2}
\]

Intersecting both envelopes with any additional fixed constraints, including the other handed motion, only reduces the gained set. Thus every upper bound below for G remains valid with those constraints present. Deleting angles is a geometric relaxation, **not** permission to skip orientations in a continuous physical motion.

## 2. One rotating inner wall: an exact circular bound

**Lemma EC1.** Let n_t rotate through an angle tau in (0,pi), and let K be any compact convex set. The set of points satisfying

\[
p\cdot n_0\ge h_K(n_0)-1,\qquad
p\cdot n_\tau\ge h_K(n_\tau)-1
\]

but violating p dot n_t >= h_K(n_t)-1 at some intermediate angle has area at most

\[
\lambda(\tau)=\tan(\tau/2)-\tau/2.
\tag{EC.3}
\]

**Proof.** Let z be the intersection of the two outer support lines z dot n_0=h_K(n_0), z dot n_tau=h_K(n_tau). Every intermediate normal is a nonnegative linear combination of the endpoint normals. Sublinearity of support functions therefore gives h_K(n_t) <= z dot n_t. Writing w=z-p, the exceptional set is contained in

\[
\{w:w\cdot n_0\le1,\ w\cdot n_\tau\le1,
       \max_{0\le t\le\tau}w\cdot n_t>1\}.
\]

An interior maximum greater than one requires the direction of w to lie between the two normals. The set is the region outside the unit circular arc and inside its two endpoint tangent lines. The two triangles from the origin to the tangent intersection have combined area tan(tau/2); the intervening circular sector has area tau/2. Their difference is EC.3. No tangency or smoothness of K is assumed. QED.

This circular geometry is related to [CC1](circular-corner-completion-bound.md). The new use here is pointwise safe-wall branching: we do **not** assume the whole body occupies an outgoing strip at angle tau.

## 3. Uniform cubic bound on recoverable startup area

Write

\[
V=(W-1)_+,\qquad Z=\tan\tau,\qquad k=\sec\tau-1,
\]
\[
X(V,\tau)=\frac Z2\left[V^2-\frac{(V-k)_+^2}{1+Z^2}\right],
\]
\[
\boxed{B(W,\tau)=2\lambda(\tau)+X(V,\tau).}
\tag{EC.4}
\]

**Theorem EC2 (all-hull endpoint bound).** For every K as in Section 1 and every 0 < tau < T <= pi/2,

\[
\boxed{0\le G_K(\tau;T)\le B(W,\tau).}
\tag{EC.5}
\]

In particular, for fixed W,

\[
\boxed{B(W,\tau)=
\left[\frac1{12}+\frac{V(V+1)}2\right]\tau^3+O_W(\tau^5).}
\tag{EC.6}
\]

This is uniform over all hulls of that width in the incoming unit strip. There is no regularity, face-position, actual-hull retention, or nonempty-envelope-fiber hypothesis.

**Proof.** Every newly admitted point p=(x,y) belongs to an early forbidden quadrant but avoids Q_tau. At angle zero its v-depth is H-y <= 1.

If its v-depth at tau is also <=1, it belongs to the exceptional set for the rotating v-wall in Lemma EC1, of area at most lambda(tau).

Otherwise it must have u-depth <=1 at tau. If its u-depth at zero is <=1 as well, the u-wall version of EC1 gives another area allowance lambda(tau).

The only remaining points switch safe walls: their u-depth at zero is >1, and their u-depth at tau is <=1. Put

\[
\xi=r-1-x>0.
\]

Such points exist only when W>1. Since K is contained in its bounding rectangle,

\[
h_K(v_t)\le-l\sin t+H\cos t.
\]

An early v-wall violation therefore implies, for some 0<t<tau,

\[
y<H-\sec t+(x-l)\tan t\le(x-l)Z=(V-\xi)Z.
\tag{EC.7}
\]

Also h_K(u_tau) >= r cos(tau), using an actual rightmost point whose height is nonnegative. The final u-wall safety inequality gives

\[
x\cos\tau+y\sin\tau\ge r\cos\tau-1,
\quad\text{hence}\quad \xi\le k+yZ.
\tag{EC.8}
\]

All cross-branch points thus lie in the explicit polygon

\[
0\le\xi\le V,\quad 0\le y\le(V-\xi)Z,
\quad\xi-Zy\le k.
\tag{EC.9}
\]

The first two inequalities describe a triangle of area V^2 Z/2. When V>k the last inequality removes a triangle of area (V-k)^2 Z/[2(1+Z^2)]; otherwise it removes nothing. The remaining polygon has exactly the area X(V,tau) in EC.4. Adding the two single-wall allowances and this cross-branch allowance proves EC.5. Possible overlaps only make the estimate more conservative. Expanding tan and sec proves EC.6. QED.

A simpler, slightly weaker form follows by integrating 0<=y<=VZ and 0<=xi<=k+yZ:

\[
G_K(\tau;T)\le2\lambda(\tau)+VZk+\tfrac12V^2Z^3.
\tag{EC.10}
\]

**Exact rational version.** For rational q=tan(tau/2) in (0,1), both Z=2q/(1-q^2) and k=2q^2/(1-q^2) are rational. Moreover lambda(tau)=q-arctan q <= q^3/3. Hence

\[
\boxed{G_K(\tau;T)\le\frac{2q^3}{3}+X(V,\tau)}
\tag{EC.11}
\]

is a fully rational, whole-angle upper bound when W is rational or bounded above by a specified rational width. No finite angle sample is being treated as a proof of continuous coverage.

### Both hands and both ends

Horizontal reflection exchanges the start and finish of a conventional quarter turn; vertical reflection exchanges handedness. Thus EC2 applies separately at all four axis endpoints. If E_core imposes only t in [tau,L-tau] for each handed turn, and E_full imposes both full quarters, then for 0<tau<L/2,

\[
\boxed{0\le |E_{\rm core}(K)|-|E_{\rm full}(K)|\le4B(W,\tau).}
\tag{EC.12}
\]

The statement concerns total ordinary envelope areas even if an envelope is disconnected. It does not claim E_core is a feasible full-turn sofa. Unlike CC's stronger bound with actual outgoing-strip hypotheses, EC12 needs only the retained corner placements and the incoming strip.

## 4. The cubic order cannot be replaced by a smaller universal order

Take K=[0,1]^2. For q=tan(t/2), the positive single-angle forbidden triangle has baseline interval

\[
[q,\ 2q/(1+q)]
\]

and exact area

\[
\boxed{|K\cap Q_t|=
\frac{q^3(1-q)^3}{(1+q)(1+q^2)^2}.}
\tag{EC.13}
\]

This follows either by elementary integration or from corner height (1-sin t)(1-cos t) and triangle area height^2/(2 sin t cos t).

Fix q_tau=tan(tau/2)<=1/2 and choose an early angle t_0 with tan(t_0/2)=q_tau/4. The whole early triangle has x<q_tau. Every later quadrant, at t>=tau, meets y>=0 only at x>tan(t/2)>=q_tau. Therefore none of that early triangle is carved by **any** later lower-turn angle. Its area is greater than q_tau^3/128, since

\[
\frac{(1-q_0)^3}{(1+q_0)(1+q_0^2)^2}>\frac12
\quad(0<q_0\le1/8).
\]

Since q_tau>=tau/2,

\[
\boxed{G_K(\tau;L)>\tau^3/1024.}
\tag{EC.14}
\]

The same lower witness remains valid with the other full handed sweep imposed: the early triangle is below the midline, whereas the upper forbidden sweep is above it. In fact E_full(K) is a genuine connected full-turn sofa with actual hull K. The lower corner height is (1-sin t)(1-cos t) <= (sqrt(2)-1)^2/2 <1/2; the reflected upper sweep is separated, the entire midline survives, and all four square vertices survive every pose. Thus the cubic order is necessary even on an **actual feasible full-turn hull**, not only on arbitrary inconsistent support data.

The larger relaxed envelope obtained by deleting early angles is not claimed to execute a continuous full turn. This is sharpness of the endpoint-relaxation rate, not a larger-sofa construction.

## 5. General actual startup coefficients: all clipping included

Now assume H=1. Write the exposed top and bottom hull faces as

\[
[a,b]\times\{1\},\qquad[c,d]\times\{0\}.
\]

Either face may be a singleton. The supports satisfy

\[
h_K(u_t)=r+O(t),\qquad h_K(v_t)=1-at+o(t).
\]

**Theorem EC3 (actual startup law).** The early swept area EC.1 and the single-angle carved area have the same first-order coefficient:

\[
\boxed{\lim_{\tau\downarrow0}\frac{A_K(\tau)}\tau
=\lim_{\tau\downarrow0}\frac{|K\cap Q_\tau(K)|}\tau
=\int_c^d (x-a)_+\,\mathbf1_{\{x<r-1\}}\,dx.}
\tag{EC.15}
\]

**Proof.** Scale height by y=tau*z. Any early forbidden point satisfies 0<=y<=W tan(tau), by the bounding-box estimate in EC.7, so the rescaled sets lie in a fixed bounded rectangle for all small tau. Except at a null set of x and z, their indicators converge to the indicator of

\[
c<x<d,\quad a<x<r-1,\quad0<z<x-a.
\]

Indeed the first inner-wall inequality is eventually strict when x<r-1 and impossible when x>r-1. The second wall divided by tau tends to z<x-a when t=tau. Uniformity of the one-sided support expansion over 0<t<=tau gives the matching upper bound for the entire early union. Finally, a point (x,tau*z) belongs to K for every sufficiently small tau when x is in the interior of its bottom face; outside that face its lower hull boundary is strictly positive and it eventually does not belong. Singleton faces and face endpoints affect no area in x. Dominated convergence proves EC.15. QED.

Reflecting gives the other three endpoint coefficients:

| Hand and endpoint | First-order actual carved area |
| --- | --- |
| Lower, start | integral from c to d of (x-a)_+ times 1_{x<r-1} dx |
| Lower, finish | integral from c to d of (b-x)_+ times 1_{x>l+1} dx |
| Upper, start | integral from a to b of (x-c)_+ times 1_{x<r-1} dx |
| Upper, finish | integral from a to b of (d-x)_+ times 1_{x>l+1} dx |

These are per-endpoint coefficients, **not** an additive formula for the union of early and late sweeps, which may overlap. EC15 reduces to IW.6 when the common bottom/top rectangle is present. It does not subtract a forbidden triangle lying outside K.

**Opposite-end consequence.** If W>2 and

\[
[a,b]\subseteq[l,l+1],\qquad[c,d]\subseteq[r-1,r],
\]

all four coefficients are zero. For Romik's aligned reference faces they are positive; for example the lower-start coefficient is one half of (3m/2-1)^2. Yet EC2 says that the portion of that linear-size startup cut recoverable by omitting early angles is only cubic: almost all of it is also removed at later angles.

## 6. Strict opposite-end faces have genuinely corner-free endpoint intervals

**Theorem EC4.** If

\[
b<l+1<r-1<c,
\tag{EC.16}
\]

then there exists epsilon>0 such that **the entire convex hull** K avoids the inner forbidden quadrants for both handed motions throughout both endpoint intervals [0,epsilon] and [L-epsilon,L]. Its canonical complete-turn carving can therefore be computed from a compact interior angular interval alone.

**Proof.** Define the maximum simultaneous support depth

\[
D_K(t)=\max_{p\in K}\min\{h_K(u_t)-p\cdot u_t,
 h_K(v_t)-p\cdot v_t\}.
\]

At t=0 its value at p=(x,y) is min(r-x,1-y). Every point with y>0 has this minimum <1. All bottom-face points have x>=c>r-1, so their minima are also <1. Compactness gives D_K(0)<1. Since D_K is diameter(K)-Lipschitz in t, K avoids every initial lower quadrant on a positive interval. The reflected argument using b<l+1 gives a positive interval at the upper finish.

For the other two endpoints, put w(t)=width_K((sin t,cos t)). The one-sided support derivatives give

\[
w(t)=1+(b-c)t+o(t)<1
\]

for all sufficiently small positive t. That entire directional strip protects K at the lower finish and upper start. These four intervals have a common positive subinterval, proving the claim. QED.

**Subunit-height generalization.** If H<1, no face condition is needed. Every relevant near-vertical directional width is at most H cos t+W sin t <= H+Wt. Thus all four endpoint carve-outs are empty whenever 0<=t<=min(L,(1-H)/W), with the zero-width degenerate case treated separately.

**Boundary warning.** Zero coefficients in EC15 do not by themselves imply a positive interval of zero carving. The unit-square calculation EC13 has zero linear coefficient but positive carved area at every nonzero angle. EC16 is a sufficient strict condition, not an asserted classification of all endpoint degeneracies.

For an exact no-carving test at an arbitrary angle, the depth above also has the support-only dual form

\[
D_K(t)=\min_{0\le z\le1}
\left[z h_K(u_t)+(1-z)h_K(v_t)
+h_K(-z u_t-(1-z)v_t)\right].
\tag{EC.17}
\]

This follows by minimax for the two affine depth functions on compact convex K and the interval of weights z; it can alternatively be proved by separating the two-dimensional depth image from a northeast open quadrant. The hull avoids Q_t exactly when D_K(t)<=1. For polygons both the edge-based primal maximum and the piecewise-affine dual minimum are finite rational calculations at rational normal pairs.

## 7. Verification and the precise remaining optimality question

[The standard-library exact checker](computer-assisted/check_actual_endpoint_carving.py) was executed locally. It checks 20 rational small-angle/coefficient regressions, 18 exact primal/dual identities, 18 exact three-angle union comparisons against EC11, 20 independent clipped-triangle evaluations of the cross-branch area X, and the exact positive cubic square witness. It also demonstrates positive ambient corner height with **zero actual carved hull area** on a strict opposite-face polygon. These finite tests audit formulas and implementation; they are not substituted for the all-angle proofs above.

The user's proposed efficiency is real in the limited geometric sense of EC4. But waiting time or a large early triangle is not an area gain: the useful saving is the part not forbidden elsewhere, and EC2 bounds that saving uniformly by a cubic quantity for a small omitted angle interval.

What remains unproved is a comparison of **different complete hulls and their entire corner paths**: whether any increased middle-angle carving and lost outer area must offset all gains from an asymmetric opposite-face construction. EC2 holds for fixed K and cannot be applied as though the support function stayed fixed when K is changed. No theorem here bounds every sofa by M, eliminates all partial motions, or establishes uniqueness. No convex-only area constant was refined, no Lean was formalized, and no CI was invoked.
