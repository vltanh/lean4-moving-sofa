# Completing two turns across an interval of feasible straight strips

**Scope.** This is an exact angle-coverage reduction for the same body, with no area-changing operation. It removes a stated partial-turn case. It does not prove that all relevant strip directions belong to one connected component, nor that a reoriented body's faces are aligned. Labels SI are local. Baseline: `b8e78964127ec7115706016addec0682426f96dd`.

## 1. Canonical hallways indexed by one normal angle

Put L=pi/2, n_t=(cos t,sin t), and let h be the support function of a nonempty compact body S. Write w(t)=h(t)+h(t+pi). Define

$$
H_S(t)=\{z:z\cdot n_t\le h(t),\ z\cdot n_{t+L}\le h(t+L),
\ z\cdot n_t\ge h(t)-1\ \text{or}\ z\cdot n_{t+L}\ge h(t+L)-1\}.
$$

The two full conventional motions in a horizontal incoming strip correspond to

$$S\subset H_S(t)\quad(t\in[0,L]\cup[\pi,3L]).\tag{SI.1}$$

For the upper motion this follows by exchanging its two ordered normals: at magnitude s they are n_{-s},n_{-s-L}, so its right-handed index is 3L-s. Exchanging the two arms does not change the hallway set. A reflected motion of the *body* is not performed.

**Lemma SI1 (one safe strip supplies two hallway orientations).** If w(theta)<=1, then S is contained in H_S(theta) and H_S(theta-L). By pi-periodicity of w, the two opposite-index counterparts are also available.

**Proof.** Every z in S has z dot n_theta>=-h(theta+pi)>=h(theta)-1. Thus its inner-wall disjunction is automatically satisfied whenever n_theta is either member of the frame. Both outer bounds are actual support bounds. QED.

## 2. Transport of already full turns

Suppose SI.1 holds. Let eta be another normal direction with |eta-L|<=L, and assume

$$w(t)\le1\quad\text{for every }t\text{ between }L\text{ and }\eta.\tag{SI.2}$$

**Theorem SI2.** The same S has both full conventional turns with incoming normal n_eta. In the original coordinates the required hallway intervals are

$$[\eta-L,\eta]\quad\text{and}\quad[\eta+L,\eta+\pi].\tag{SI.3}$$

**Proof.** Put delta=eta-L. If delta>=0, the first interval's new portion beyond [0,L] is [L,L+delta], and its first normal is a safe-strip normal by SI.2. The second interval's new portion beyond [pi,3L] is [3L,3L+delta], with the opposite safe-strip normal. Apply SI1. All remaining angles are supplied by SI.1.

If delta<=0, the new portions are [delta,0] and [pi+delta,pi]. Their second normals range respectively in [L+delta,L] and its pi translate, so SI1 again applies. QED.

The statement transports along any connected interval of safe-strip normals by finitely many steps of length at most L. No bound on the strip's actual width other than <=1 is needed during the transport.

These pointwise containments give actual continuous motions. The canonical corner vector `(h(t)-1)n_t+(h(t+L)-1)n_(t+L)` is continuous. Rotate and translate S through that family. At its two ends a safe unit strip contains S, so the straight incoming/outgoing translations can be appended, exactly as in Proposition 19 and Lemma 20 of Note 8. Different initial positions for the two motions are reconciled by translations within their common straight strip.

## 3. Complete two partial turns when their strip directions connect

Suppose the canonical lower and upper motions have conventional magnitudes alpha,gamma in (0,L], respectively. The known hallway index intervals are

$$[0,\alpha],\qquad[3L-\gamma,3L].$$

Their outgoing strip normals, modulo pi, are alpha and pi-gamma; the incoming normal is L. Assume

$$\boxed{w(t)\le1\quad(\alpha\le t\le\pi-\gamma).}\tag{SI.4}$$

**Theorem SI3 (safe-strip bridge).** The same S admits two full conventional quarter turns with incoming normal n_alpha.

**Proof.** The desired lower interval is [alpha-L,alpha]. Its nonnegative part was already visited; on its negative part the second normal lies in [alpha,L], covered by SI.4.

The desired upper interval is [alpha+L,alpha+pi]. Its part at or above 3L-gamma is already in the original upper interval. For its remaining part, the second normal, reduced modulo pi, ranges in [alpha,pi-gamma]. Apply SI1. The canonical continuity and endpoint-strip argument in Section 2 give both full motions. QED.

This is a change of incoming orientation, not an unjustified extension of the original partial path. It preserves S and its ordinary area exactly.

## 4. Recover a unit-span incoming representative

Suppose additionally that |S|>1 and SI.4 holds. There is some normal with w>1: otherwise widths in two orthogonal directions would both be at most one, placing S in a rectangle of area at most one. Since w is continuous and pi-periodic, the connected component of `{t:w(t)<=1}` containing the bridge interval is a closed bounded interval in a suitable lift of the angle circle. Its endpoints have width exactly one.

Start with the full motions at normal alpha from SI3 and transport them along that component using SI2. Choosing an endpoint produces a common incoming representation with vertical span exactly one and both full turns. No dilation or anisotropic stretching is used.

**Corollary SI4.** A competitive body satisfying the safe-strip bridge can be placed in the unit-span full-turn class without altering its area. Thus it may be tested against FAS/FD/UC in the new coordinates. It is not known that those coordinates have an already covered face type.

Consequently a partial-turn body not reducible in this way must have an angle between its two outgoing strip normals where w>1. Knowing width<=1 at the three individual normals alpha,L,pi-gamma does not establish SI.4; a continuous width function can rise between them. That additional inequality must be proved or tested from actual support data.

## 5. How this interacts with opposite-end faces

At a unit-span orientation, write the top and bottom face intervals as [a,b] and [c,d]. The one-sided derivatives of width at the vertical normal are

$$w'(L-)=c-b,\qquad w'(L+)=d-a.\tag{SI.5}$$

These follow from the standard one-sided support derivatives: h'(L-)=-b, h'(L+)=-a, h'(3L-)=c, h'(3L+)=d.

If the top face is strictly to the left of the bottom face, then c>b, so w'(L-)>0. It follows that w(L-epsilon)<1 for every sufficiently small positive epsilon. Full turns can therefore be transported into these nearby narrower-strip orientations by SI2. The reversed ordering gives the opposite tilt.

This supplies orientation freedom in the asymmetric opposite-face case. It does not prove an area gain, preservation of face lengths, or alignment at the other endpoint of the safe-strip component. In particular it cannot be combined with a unit-span theorem at an interior orientation whose actual span is less than one without the endpoint step of Section 4.

All steps are pen-and-paper. No computer-assisted search, CI, Lean/Lake compilation, dependency installation or manuscript build is used. The unrestricted optimal value remains unproved.
