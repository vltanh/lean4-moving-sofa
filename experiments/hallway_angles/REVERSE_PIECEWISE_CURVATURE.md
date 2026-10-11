# Full piecewise curvature bound from the two neighboring reverse wedges

Status: continuation of REVERSE_LOCAL_VARIATION.md. This derives the continuum bound suggested there, including the facet-length self term. It is the arbitrary-bend analogue of the piecewise kappa bound in the right-angle maximality argument. It does not yet close the endpoint/arm bootstrap.

Retain q=sin e and the oblique arms a,b.

Define for z>=0

    kappa0(z)=max{z,(1+z)/2}.                           (1)

## 1. Why the current facet length enters

At a plus facet of mesh size delta, let sigma be its length. With the orientation conventions of REVERSE_LOCAL_VARIATION.md,

    a^+-a^-=sigma.                                      (2)

When the limiting plus arm a is negative, the next-wedge cutoff T_+ is controlled by the same-family threshold

    tan(delta/2)-a^+,

whereas the preceding wedge covers up to

    U_-=-tan(delta/2)-a^-.

The uncovered gap between these two thresholds is therefore

    2 tan(delta/2)-sigma

when positive. This is the exact source of the self term; replacing a^+,a^- by a common point value before taking the limit would lose it.

The lower endpoint of the preceding-wedge covered interval contributes

    max{0, [1-cos(delta)-b^+ sin(delta)]/sin(e+delta)}.

After division by delta its limit is

    (-b/q)_+.

Consequently the exposed plus-wall length obeys, at almost every limiting point with a<0,

    tau_+/delta <= (-b/q)_+ + (1-rho_+)_+ + o(1).       (3)

The selected-maximizer floating variation gives rho_+<=limsup tau_+/delta. Therefore

    rho_+ <= c+(1-rho_+)_+,    c=(-b/q)_+.             (4)

Solving this scalar inequality yields

    rho_+ <= kappa0((-b/q)_+)       when a<0.           (5)

Indeed if rho_+>=1 then rho_+<=c; if rho_+<1 then 2rho_+<=1+c.

## 2. Positive and zero arm cases

If a>0, the preceding-wedge endpoint U_- is negative for all sufficiently fine meshes. The first-neighbor estimate from the previous note gives

    rho_+ <= (b/q)_+.                                   (6)

At almost every point of the level set a=0, absolute continuity gives zero approximate derivative of a. The one-sided arm values are therefore o(delta), apart from the facet jump already represented by rho_+ delta. Repeating the threshold calculation gives the safe bound

    rho_+ <= max{1/2,(b/q)_+}.                          (7)

One may instead avoid assigning a value on {a=0}: (5)-(6) on the two open sign sets, together with weak upper semicontinuity, are enough for most integral arguments.

Reflection gives the complete minus-family bounds by swapping a and b.

## 3. The resulting maximality inequality

For a selected positive-area reverse maximizer, away from pinned endpoint atoms the expected continuum bound is

    rho_+ <=
      (b/q)_+                         if a>0,
      max{1/2,(b/q)_+}                if a=0,
      kappa0((-b/q)_+)                if a<0,            (8)

and

    rho_- <= the same expression with a,b interchanged. (9)

The explicit reverse optimizer lies entirely in the first case and saturates rho_+=b/q, rho_-=a/q.

## 4. Horizontal tangencies of the canonical corner

Formula (8) has an immediate geometric consequence useful for a no-backtracking proof. At an interior horizontal tangent y'=0, write X=x'. Then

    a=sin(phi) X,       b=-sin(e-phi) X.                (10)

If X>0, then a>0>b, so (8) gives rho_+=0 and (9) gives rho_-<=1/2. If X<0, then b>0>a, so rho_-=0 and rho_+<=1/2.

Differentiating q y'=sin(e-phi)a+sin(phi)b and using the arm equations gives at such a tangent

    q y'' = -2q X + rho_+ sin(e-phi)-rho_- sin(phi)
             +sin(phi)-sin(e-phi).                      (11)

Therefore:

- on the first half phi<=e/2, every right-moving horizontal tangent X>0 has y''<0;
- on the second half phi>=e/2, every left-moving horizontal tangent X<0 has y''>0.

These are strict statements. They show that one entire orientation of potentially harmful local extrema is impossible on each half. The two remaining tangent orientations are the residual obstruction to a complete monotonicity theorem.

## 5. Remaining endpoint/bootstrap task

The full all-obtuse theorem can now be attacked as a one-dimensional maximum-deficit problem for the coupled arms. What is still missing is a bend-uniform argument excluding:

- a left-moving local maximum on the first half, and
- a right-moving local minimum on the second half,

or, equivalently, proving that those extrema only generate clockwise loops whose signed corner area is no larger than the actual forbidden union.

This is substantially narrower than the original arbitrary-support crossing problem.

## Verification boundary

The discrete thresholds are exact line geometry. The passage from polygon defects to (8)-(9) requires the persistent-penalty selection and weak curvature convergence to be instantiated for reverse caps. The scalar solution of (4) and the tangent identity (11) are elementary. No numerical optimization is used.