# Conditional all-obtuse reverse theorem from nonnegative maximizer arms

Status: exact reduction. The only unproved hypothesis is a maximality property of arbitrary reverse caps; all scalar and variational ingredients already exist on the full obtuse interval.

## Theorem

Fix pi/2<beta<pi and e=pi-beta. Suppose every positive-area maximizer of the aligned reverse class has canonical oblique arms a,b satisfying

    a(phi)>=0, b(phi)>=0 for almost every 0<phi<e.

Then

    M_-(beta)=V(e),

and the unique maximizing compact connected sofa, up to normalized horizontal translation, is the explicit convex S_e of REVERSE_GEOMETRIC_THEOREM.md.

Strict positivity is not needed as a separate assumption: unless the canonical corner is constant on a positive-length interval, formula

    sin(e) y'=sin(e-phi)a+sin(phi)b

gives increasing height almost everywhere. Constant pieces can be removed by the usual generalized-inverse/approximation argument in the corner integral; equality with the strictly concave quadratic maximizer subsequently makes both arms strictly positive.

## Proof

Existence of a reverse-class maximizer is supplied by HALLWAY_WELL_POSEDNESS.md.

Let S be one and K=conv(S). Normalize its actual vertical width to w<=1. By the arm hypothesis and the velocity identity in REVERSE_MAXIMIZER_ARMS.md, the canonical corner has nondecreasing height through the actual strip. Horizontal left rays from a corner point lie in that pose's forbidden wedge, so the standard section argument gives

    area(S)<=Cap - integral x dy

with the same outside-strip boundary corrections as REVERSE_GENERAL_MAJORANT.md. The integration-by-parts excursion estimates do not use e<=e_*; that restriction entered only through the old proof of increasing strip crossing.

Hence the corrected majorant

    area(S)<=F_e(w)

is valid for this maximizer at every 0<e<pi/2.

The exact scalar width certificate in REVERSE_EXTENDED_RESULTS.md already proves on the whole closed interval 0<=e<=pi/2 that

    F_e(w)<F_e(1)=V(e)  for every w<1

after combining the midpoint bound on w<=1/2 with the quadratic comparison on 1/2<=w<1. Since the explicit S_e is a feasible reverse sofa of area V(e), maximality forces w=1 and area(S)=V(e).

Equality in the strict quadratic theorem identifies the canonical corner with C_* up to horizontal translation. The cap/niche containment and regular-closed equality argument from REVERSE_MAIN_THEOREM.md then gives equality of the compact sofas, not merely equality almost everywhere.

## Significance

The earlier theorem beta>=114.4698 degrees proved increasing canonical crossing for every competitor by a crude support-point estimate. The present reduction shows that no angle-dependent scalar obstruction remains below that point. To cover every obtuse bend it is enough to prove the maximality-level arm sign

    a,b>=0.

REVERSE_LOCAL_VARIATION.md and REVERSE_PIECEWISE_CURVATURE.md derive the local stationarity inequalities intended for that final step.

## Review boundary

This note does not claim the arm hypothesis has been proved. It records that, once it is proved for maximizers, no new quadratic optimization, candidate feasibility, width certificate, or equality argument is required.