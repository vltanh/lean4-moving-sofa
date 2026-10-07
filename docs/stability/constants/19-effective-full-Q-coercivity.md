# The full Q deficit improves cap coercivity, with an effective Q threshold

This is a new analytic consequence of the existing exact wide-domain deficit
identity and four-arc reconstruction. The numerical operator inequalities below
are checked with exact integer/dyadic interval arithmetic. The mathematical
reduction still requires independent review; no Lean proof is claimed.

## Statement

Let xi=(K,B,D) be any feasible triple in the enlarged normalized right-angle
Q domain, and let Delta=M-Q(xi). Align the horizontal midpoints of K and Gerver's
cap. Then:

1. On the exposed face L(xi)=0,

       d_H(K,K_G+shift) <= (49/50)*sqrt(Delta).

2. For every such triple, not necessarily on that face, if
   0<Delta<=1/512,

       d_H(K,K_G+shift) <= (49/50)*sqrt(Delta)+8*Delta^(2/3).       (A)

3. Consequently, for 0<=Delta<=10^(-18),

       d_H(K,K_G+shift) <= (99/100)*sqrt(Delta).                  (B)

These are Euclidean distances between caps. They improve the cap-only residual
coefficient sec(phi)>1 by USING the first-variation slack and auxiliary energies,
not by contradicting its sharpness for E_cap alone. The number 10^(-18) is an
unconditional threshold for this Q-TRIPLE theorem, not for arbitrary sofa area.

If a Ki cap has sofa-area deficit at most 10^(-18), its canonical triple obeys
Q>=A(K), so (B) also applies with the larger area deficit. For arbitrary original
sofas, applicability of a canonical geometric certificate still requires the
separate global-entry argument. This note does not compute that entry threshold.

## 1. The rank-two inequality including nonzero slack

Use the notation of note 18. Put lB=-(f+B)>=0 and lD=-(f+D)>=0 on the constrained
arcs; write ellB=lB(c), ellD=lD(d). The endpoint relations hold for every feasible
triple, regardless of L. Weighted Cauchy--Schwarz therefore gives

    E_B >= [JB-ellB/cos(c)]^2/(2*DB),
    E_D >= [JD+ellD/sin(T-d)]^2/(2*DD).                          (1)

Let r be the four cap residuals, with E_cap=||r||^2/2. Define V1,V2 by
JB=<V1,r>, JD=<V2,r>, and let A_t=H_t-(cos(t)/2)*H_0 be the centered evaluation
kernel. Put D0=diag(DB,DD), Gij=<Vi,Vj>, S=D0+G, and w_i(t)=<A_t,Vi>.

The quadratic form in (1) and E_cap is

    (1/2)*(||r||^2+(V*r-e)^T D0^(-1)(V*r-e)),
    e=(ellB/cos(c),-ellD/sin(T-d)).

Completing the square in the Hilbert space, or using the rank-two inverse
identity, gives

    |<A_t,r>| <= sqrt(2*(||A_t||^2-w^T*S^(-1)*w))*sqrt(Delta)
                  + |w^T*S^(-1)*e|.                           (2)

The remaining constant after square completion is nonnegative; dropping it
and L only weakens the bound. This argument makes no finite-dimensional
approximation of the residual space.

## 2. A continuum interval certificate, not sampled eigenvalues

The program critical_cone/certify_critical_rank2.py checks uniformly over

    phi in [0.039177264,0.039177465],
    theta in [0.681301409,0.681301610],
    t in [0,pi],

that

    2*(||A_t||^2-w^T*S^(-1)*w) < (49/50)^2,
    |(S^(-1)w)_1/cos(c)|+|(S^(-1)w)_2/sin(T-d)| < 1/2.         (3)

These parameter enclosures are the existing Gerver.Bounds input, not fitted
values. The kernel norm ||A_t||^2 is the six-piece formula of note 11. All cross
inner products are integrated exactly via the primitives for sec^2, csc^2,
csc*cot, and cot^2. Possible uncertain overlaps of parameter-dependent pieces
are enclosed conservatively; a denominator enclosure containing zero causes
subdivision, not acceptance.

The successful exact-arithmetic run covers the domain by 821 accepted dyadic
angle cells after 1,636 visits. Every cell also covers the entire parameter
box. All comparisons are rational integer comparisons. The backend uses
90-bit dyadic outward rounding, Taylor's theorem with explicit remainder for
sin/cos, and Machin's formula with alternating rational arctangent bounds for
pi. There are no floating-point acceptance predicates or SciPy solvers.

The initial mpmath interval run independently found the same 0.98 conclusion.
An initial exact backend used separately rounded tiny factorial coefficients,
which made its intervals unnecessarily wide near pi and failed to certify.
The implemented term recurrence repairs that loss without changing the bound.
This was an enclosure-efficiency failure, not a mathematical counterexample.

Combining (2) and (3) gives

    |centered f(t)| <= .98*sqrt(Delta)+(1/2)*max(ellB,ellD).      (4)

In particular L=0 forces both endpoint slacks to vanish, proving assertion 1.
No sharpness of 0.98 is claimed. The full functional-space relaxation of note18
is numerically closer to 0.968, and still drops feasibility constraints.

## 3. Quantify closeness to the critical face

The density of each reference auxiliary measure is at least 1/8 on its active
arc. On the nonconstant phase the density is

    1+b1-s/2 >= 1-0.527624699-0.681301610/2 > 1/8,

and on the endpoint phase it is 1/2. Therefore

    integral_c^v lB <= 8L <= 8Delta,
    integral_v^d lD <= 8L <= 8Delta.                            (5)

Let w0=1/8. The following derivative estimates hold on [c,c+w0] for lB and
[d-w0,d] for lD:

    ||lB'||_2 <= 8*sqrt(Delta),
    ||lD'||_2 <= 8*sqrt(Delta).                               (6)

Here derivatives are almost everywhere derivatives of support functions. A
curvature atom does not prevent the support function from being locally
absolutely continuous. The intervals avoid the residual singular endpoints.

To verify the constants, use the OLD left-pinned cap estimate
|f|<=2.002*sqrt(Delta), valid on every wide triple. Choosing this gauge does not
change lB,lD or the energies. All residual L2 norms are at most sqrt(2Delta).

For B, integrate (B/cos)'=-rB/cos from phi, with B(phi)=-f(phi). On the interval
up to c+w0, tan(t)<2, sec(phi)<1.001, hence

    |B(t)| <= [2.002*1.001+2]*sqrt(Delta) < 5*sqrt(Delta),
    |B'| <= 10*sqrt(Delta)+|rB|.

This interval lies within the middle cap arc, so f'=f(t+v)-r2. Thus

    ||lB'||_2 <=12.002*sqrt(w0)*sqrt(Delta)+2*sqrt(2Delta)
               <8*sqrt(Delta).

For D, solve its integrating factor from v, using D(v)=0 and D(T)=-f(T).
On [v,d], DD<1 gives

    |D(t)| <= [2.002*1.001+sqrt(2)]*sqrt(Delta)<4*sqrt(Delta).

On [d-w0,d], sin(T-t)>7/10 and |cot(t)|<1. Hence

    |D'| <=9*sqrt(Delta)+|rD|,
    |f'| <=2.002*sqrt(Delta)+|r4|,

which gives the second estimate in (6). All numerical side inequalities follow
from the displayed parameter box; the companion checker verifies them with
rational/trigonometric interval enclosures.

For a nonnegative absolutely continuous function l on an endpoint interval of
length w<=w0, averaging the fundamental theorem and Cauchy--Schwarz gives

    l(endpoint) <= (1/w)*integral l + sqrt(w)*||l'||_2.

Take w=Delta^(1/3). When Delta<=1/512, w<=1/8, and (5)--(6) yield

    max(ellB,ellD) <=16*Delta^(2/3).                            (7)

This is the crucial improvement over a merely Lipschitz slack estimate: the
slope's L2 norm itself is controlled by sqrt(Delta). In particular the endpoint
slacks are o(sqrt(Delta)), so they cannot recover the discarded cap-only
extremizing direction at leading order.

## 4. Finish the bound

Insert (7) into (4), obtaining (A). The support estimate extends to the lower
semicircle by the cap's floor identities, giving Euclidean Hausdorff distance.
If Delta<=10^(-18), then Delta^(1/6)<=10^(-3), and

    .98+8*Delta^(1/6) <= .988 < .99.

For Delta=0 the original cap energy is zero and the centered support is zero,
so no division by Delta is required. This proves (B).

## 5. What this settles and what remains

The full deficit DOES control near-optimal feasible triples strictly better
than the sharp cap-residual coefficient. We have an explicit all-triple Q
threshold and a strict coefficient below one, not just a numerical critical
ray or a conjecture based on a Hessian spectrum.

The exact optimal critical-cone coefficient is not identified here. Formula(3)
of note18 describes a continuum relaxation; additional convexity, containment,
and inactive-wall inequalities may further improve its feasible value. The
computer certificate validates the displayed operator inequalities, not those
unimplemented feasibility or sharpness claims. No global original-sofa area
threshold is obtained by renaming this Q threshold.
