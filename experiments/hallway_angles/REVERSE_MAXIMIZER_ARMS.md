# Oblique arm coordinates for reverse maximizers

Status: analytic reduction for the aligned reverse class. This note does not yet prove that an arbitrary reverse maximizer satisfies the candidate stationarity law; it identifies the exact law and the maximality lemma needed to remove the 114.47-degree cutoff. No CI or Lean build is used.

Write e=pi-beta in (0,pi/2), phi in [0,e], psi=e-phi, q=sin e, d=cos e. Put

    n1=(sin phi, cos phi),       t1=(cos phi,-sin phi),
    n2=(sin psi,-cos psi),       t2=(cos psi, sin psi).

Let K be the convex hull of a reverse-class competitor, with support functions h_+(phi), h_-(psi), support contacts

    P_+=h_+ n1+h_+' t1,
    P_-=h_- n2+h_-' t2,

and canonical inner corner C defined by

    n1.C=h_+-1,   n2.C=h_--1.

At differentiability points define the oblique arms

    a=t1.(P_+-C),
    b=t2.(P_--C),

and support curvature densities rho_+=h_++h_+'', rho_-=h_-+h_-''.

These definitions are invariant under horizontal translation.

## 1. Corner velocity in arm coordinates

Differentiating the two corner equations gives

    n1.C'=a,       n2.C'=-b.                              (1)

Since

    n2=-d n1+q t1,       n1=-d n2+q t2,

one obtains

    x'=(cos psi a-cos phi b)/q,
    y'=(sin psi a+sin phi b)/q.                           (2)

Thus positivity of both arms immediately implies strict increasing height of the canonical corner throughout the open interval. This is exactly the geometric input needed by the original quadratic area majorant; no separate crossing estimate is then required.

The previous 114.47-degree cutoff arose because REVERSE_CROSSING_EXTENSION.md bounded y' using only the vertical positions of arbitrary support points. Formula (2) shows that a maximality proof of a,b>0 would remove that cutoff for all obtuse bends.

## 2. Arm differential equations

Differentiate

    P_+-C=n1+a t1,
    P_--C=n2+b t2.

Using P_+'=rho_+ t1, dP_-/dphi=-rho_- t2 gives

    a'=rho_+-1-d a/q+b/q,                                (3)
    b'=1-rho_- -a/q+d b/q.                               (4)

These are identities for any sufficiently regular convex cap; in the nonsmooth setting they hold in the natural absolutely-continuous/measure form once endpoint atoms are separated.

## 3. The explicit reverse candidate has a simple balance law

For the explicit optimizer S_e of REVERSE_GEOMETRIC_THEOREM.md, direct substitution into the closed formulas gives

    rho_+(phi)=b(phi)/q,
    rho_-(psi)=a(phi)/q.                                 (5)

Equation (5) is not a numerical fit. One derivation is to substitute the explicit support/corner formulas and use

    k q = eta(2+d),      k q eta = 2-d.

Equivalently, insert (5) into (3)-(4); the resulting first-order arm system is exactly the support-coordinate form of the Euler equation in REVERSE_QUADRATIC_THEOREM.md. Conversely the Euler equation implies (5).

The geometric theorem already proves

    a(phi)>0, b(phi)>0

for every interior phi, because its velocity inequalities are n1.C'>0 and n2.C'<0. Hence (2) recovers the candidate's strict height monotonicity.

## 4. The precise all-obtuse maximality target

To extend exact reverse-class optimality to every pi/2<beta<pi it is enough to establish the following maximizer-level statement.

> **Reverse active-arm theorem (target).** Every positive-area maximizing reverse cap has absolutely continuous arms a,b with the endpoint traces required by its strip normalization, and a(phi),b(phi)>0 on (0,e).

Indeed formula (2) then makes the canonical corner strictly increasing in height. REVERSE_GENERAL_MAJORANT.md applies with no e<=e_* restriction, while extended_width_certificate.py has already verified the width comparisons on the entire 0<=e<=pi/2 interval. The strict quadratic theorem and the explicit feasible S_e then give

    M_-(beta)=V(pi-beta)

and uniqueness for every obtuse bend.

A stronger and more natural statement would identify the first-variation balance (5) for every maximizing cap on its active curvature set. The specified-maximizer selection of PR #2 is designed for exactly this purpose: polygonal floating-facet defects have total error tending to zero. What remains is the arbitrary-bend local wall calculation converting niche-boundary variation into the oblique opposite-arm coefficient b/q (and its reflection a/q), including any nonexposed/contact-switch terms.

## 5. Why this is preferable to the old crossing estimate

The old estimate attempts to prove y'>0 for EVERY competitor from strip support bounds, which is false as a general convex-body principle and becomes wasteful near beta=pi/2.

The maximizer-first route needs y'>0 only for an attained maximizing cap. It can therefore use stationarity and curvature, exactly as PRs #2, #4 and #9 do in the right-angle/fixed-net-angle problem. This is a substantially weaker geometric obligation and does not require a new variational solution.

## Review boundary

The formulas (1)-(4) are elementary support differentiation. Equation (5) is an identity for the already explicit candidate. The unproved step is the maximality/contact theorem for arbitrary reverse caps. This file deliberately does not call that step completed.
