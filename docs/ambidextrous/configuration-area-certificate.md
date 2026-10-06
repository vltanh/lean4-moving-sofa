# Direct ordinary-area certificates from forbidden triples

This is a different route from curvature repair and auxiliary support-energy enclosure. It gives a finite, rationally checkable upper bound on **ordinary area** using only incompatibilities among occupied spatial cells. No curvature, smoothness, saturation, or candidate-neighborhood hypothesis is used. The finite certificate does not by itself solve the unrestricted problem; each result needs an explicitly covered parameter range and an accepted certificate.

Labels CF are local. The finite-position viewpoint is related to Kallus and Romik, *Improved upper bounds in the moving sofa problem*, arXiv:1706.06630, but the certificate here eliminates hallway translations through forbidden triples rather than optimizing their offsets. No priority claim is made.

## 1. Exactly eliminate the two hallway offsets

Let S be nonempty and compact and let (u,v) be an ordered orthonormal frame of either handedness. A placed unit hallway is

$$
L(A,B)=\{x:x\cdot u\le A,\ x\cdot v\le B,
\quad x\cdot u\ge A-1\ \text{or}\ x\cdot v\ge B-1\}.
$$

**Lemma CF1 (forbidden-triple equivalence).** There exist A,B with S contained in L(A,B) if and only if no ordered triple p,q,r in S satisfies

$$
(q-p)\cdot u>1,\qquad(r-p)\cdot v>1.
\tag{CF.1}
$$

Repeated points are allowed in this equivalence.

**Proof.** If S fits, a point p obeys one inner-wall inequality. In the first case every q obeys (q-p) dot u<=1; in the second every r obeys (r-p) dot v<=1. Conversely take A=h_S(u), B=h_S(v). The outer bounds are automatic. If some p violates both inner inequalities, compactness supplies q and r attaining those two supports, contradicting the absence of (CF.1). QED.

This statement concerns the actual points of S. It does not identify a signed curve integral with area, and it remains true when the hull has atoms, the surviving body has a pinched fiber, or a proposed hull repair would remove material.

## 2. Use the terminal strip as a spatial coordinate

Suppose the lower conventional motion ends at alpha<pi/2. Translate the incoming and terminal lower supports to zero, and set

$$
u=x\cos\alpha+y\sin\alpha,\qquad v=y.
$$

Here u in the next formulas is this scalar coordinate, not a frame vector. Both unit-strip conditions imply that the transformed body T is contained in [0,1]^2, and

$$
|S|=|T|/\cos\alpha.
\tag{CF.2}
$$

For a physical normal n=(n_x,n_y), differences of points transform as

$$
n\cdot(q-p)=A_n(\alpha)\Delta u+B_n(\alpha)\Delta v,
\quad A_n=n_x/\cos\alpha,\quad B_n=n_y-n_x\tan\alpha.
\tag{CF.3}
$$

The coordinate choice depends on alpha, but all following bounds hold uniformly on its specified interval. There is no assertion that the sofa remains physically inside its original strip during the motion; these are body-frame constraints.

Parameterize angles by r=tan(alpha/2). Rational r in [0,1) gives rational cosine (1-r^2)/(1+r^2) and sine 2r/(1+r^2). On a rational interval [r_0,r_1], bound A_n and B_n by their endpoint extrema. They are monotone in alpha for each fixed sign of n_x. Thus rational intervals [A_0,A_1], [B_0,B_1] contain their exact values throughout the interval.

Partition [0,1]^2 into n by n closed cells. Cell (i,j) is [i/n,(i+1)/n] times [j/n,(j+1)/n]. For two cells P,Q, their coordinate differences belong to

$$
\Delta u\in[(i_Q-i_P-1)/n,(i_Q-i_P+1)/n],
$$

and similarly for Delta v. Let ell_n(P,Q) be the sum of the minima of A*Delta u and B*Delta v over the corresponding two rational rectangles. Each minimum is the least of four endpoint products. Then

$$
n\cdot(q-p)\ge\ell_n(P,Q)
\tag{CF.4}
$$

for every alpha in the interval and every p in P,q in Q, mapped back by (CF.3). Treating the A and B extrema independently only weakens this lower bound; it never assumes that they occur at the same angle.

## 3. Finite incompatibilities give a rational dual certificate

For a hallway frame (u_t,v_t) known to be visited throughout the endpoint interval, declare three **distinct** cells P,Q,R incompatible if

$$
\ell_{u_t}(P,Q)>1,\qquad\ell_{v_t}(P,R)>1.
\tag{CF.5}
$$

Every transformed feasible body must miss at least one of those cells, by CF1. Let z_i be one or zero according as the body meets closed cell i or not. Then

$$
z_P+z_Q+z_R\le2,
\qquad 0\le z_i\le1,
\qquad |T|\le n^{-2}\sum_i z_i.
\tag{CF.6}
$$

Boundary overlaps of closed cells have zero area and can only increase the occupation count. The strict inequalities in CF.5 make the exclusion valid even for cells meeting only at their boundaries.

Choose any finite list of verified triples e and any nonnegative rational weights lambda_e. Write c_i for the sum of lambda_e over triples containing i. Summing CF.6 and paying for uncovered coefficients with z_i<=1 gives:

**Theorem CF2 (ordinary-area dual bound).** Throughout the endpoint interval,

$$
\boxed{
|S|\le\frac{2\sum_e\lambda_e+\sum_i(1-c_i)_+}
{n^2\cos\alpha_1},
\qquad \alpha_1=2\arctan r_1.
}
\tag{CF.7}
$$

**Proof.** Since c_i+(1-c_i)_+>=1,

$$
\sum_i z_i\le\sum_e\lambda_e\sum_{i\in e}z_i
+\sum_i(1-c_i)_+z_i
\le2\sum_e\lambda_e+\sum_i(1-c_i)_+.
$$

Use CF.2 and cos(alpha)>=cos(alpha_1). QED.

No LP solver is trusted in this theorem. A floating-point optimizer can propose triples and weights; a checker must reconstruct each visited frame, verify CF.5 with exact rational arithmetic, require distinct in-range cell indices and nonnegative weights, and evaluate CF.7. It does not need all possible triples, an LP optimality status, or an integral solution of a combinatorial optimization problem. Any accepted subset gives a valid upper bound.

## 4. Prove that each frame was actually visited

For a putative body of area greater than 8/5, the canonicalization and wrong-sign argument of AW-W give conventional endpoint magnitudes alpha,gamma in (arccos(5/8),pi/2]. The two-strip determinant estimates give

$$
|S|\le1/\cos\alpha,\quad |S|\le1/\cos\gamma,
\quad |S|\le1/\sin(\alpha+\gamma)
\tag{CF.8}
$$

when the respective determinant is nonzero. Their sum alpha+gamma exceeds pi/2.

A lower frame at angle t<=alpha_0 is therefore visited throughout the endpoint interval. An upper frame of magnitude t is guaranteed if either cos(t)>=5/8, or

$$
\alpha_1+t\ge\pi/2,
\qquad\sin(\alpha_1+t)>5/8.
\tag{CF.9}
$$

For the second claim, if gamma<=t, then pi/2<alpha+gamma<=alpha_1+t<=pi and sin(alpha+gamma)>=sin(alpha_1+t)>5/8. The last bound in CF.8 contradicts area greater than 8/5. All tests in CF.9 are rational for the chosen directions: the first is equivalent to cos(alpha_1+t)<=0.

The lower frames are ((cos t,sin t),(-sin t,cos t)); the upper frames are ((cos t,-sin t),(-sin t,-cos t)). Reflecting the whole problem exchanges the two endpoint roles. Thus a proved lower-endpoint exclusion also applies to the upper endpoint, without inserting a reflection into either physical motion.

## 5. Coverage and trust boundary

To exclude a whole interval of endpoint angles, certificates must cover it by rational half-tangent intervals with no gaps. Angles below 2 arctan(12/25) are already bounded by 769/481<8/5 using CF.8. For each remaining interval one may use a different grid and different verified triples. If every resulting rational upper bound is below a feasible candidate's area, no global maximizer has an endpoint in that covered interval.

This is a direct configuration/ordinary-area route, not a new curvature theorem. Partial endpoint intervals not covered, endpoint pi/2, and unrestricted sharp equality are not resolved merely by supplying a certificate for some smaller range. Extending a completed covering requires new accepted certificates, not extrapolation from sample values.

The only inputs beyond this note are the elementary canonical motion reduction and strip-area bounds, repeated in AW-W. In particular neither AF3, curvature domination, PR #8's qualitative entry, nor a conjectured Romik optimum is used in the upper-bound mechanism. All new commits use `[skip ci]`; no CI or Lean/Lake execution is part of this method.
