# Split the deficit before optimizing the global coefficient

This is an analytic derivation, not a report of Lean verification. Write
M=|G|, epsilon=M-|S|, U=K\N(K), and e=M-|U|. Work in the local neighborhood
where the canonical triple is feasible, N(K) is contained in K, and A(K)<=Q<=M.
Thus |U|=A(K) and e>=0.

## 1. A stronger missing-area budget

The terminal comparison supplies, for alpha=pi/2-omega,

    |S| <= |U|-c*alpha,
    g := |S\U| <= c*alpha.

Therefore

    0 <= e <= epsilon,
    c*alpha <= epsilon-e,
    g <= epsilon-e,
    m := |U\S| = epsilon-e+g <= 2*(epsilon-e).

The existing argument weakens the last bound to 2*epsilon. Keeping e matters:
the cap-shape error and the missing-area error spend the SAME deficit budget.
Their worst cases must not be added as if both could spend all of epsilon.
For a full-angle contained sofa, g=0 and m=epsilon-e exactly, an additional
improvement.

## 2. The exact erosion allowance is sqrt(2)*delta

Suppose the normalized cap supports differ by at most delta>=0. Then

    G eroded by a closed Euclidean disk of radius sqrt(2)*delta
        is contained in K\N(K).

To see this for delta>0, a point of the erosion satisfies every upper cap wall:
translate it by delta times the wall's unit normal and use that the resulting
point is still in G. It is also above the floor. If it belonged to a forbidden
quadrant of K at angle t, translate it by -delta*(u_t+v_t). The two normals are
orthonormal, so the translation has norm sqrt(2)*delta. Both reference inner
wall inequalities would then be STRICTLY violated. The translated point would
not belong to G, contradicting erosion membership. If it falls below the floor
it is likewise outside G. The delta=0 case follows directly from equality of
all cap supports and niches.

The factor 2 in the previous erosion lemma came from the triangle inequality;
orthogonality gives sqrt(2). This claim concerns erosion of the actual reference
sofa, not erosion of its convex hull.

## 3. Use the entire residual disk

Assume G has the interior-ball property with constants kappa,r0. At scale rho,
for each p in G it supplies Bbar(z,kappa*rho) contained in G intersect Bbar(p,rho).
If erosion radius is r and rho>r/kappa, the disk of radius

    a = kappa*rho-r

around z lies in the erosion and hence in U. If S has no point within rho of p,
this entire disk is missing from S. Its area is pi*a^2. Consequently

    m < pi*(kappa*rho-r)^2

implies directed distance G-to-S at most rho. There is no reason to reserve
half the radius for erosion and then replace the disk by a smaller square.
All area comparisons require measurability and finite measure, as in the
existing bookkeeping lemmas.

## 4. Combine the two square-root costs in quadrature

The improved cap certificate gives delta<=k*sqrt(e), with k=2/cos(phi)<2.002.
Take r=sqrt(2)*k*sqrt(e). The recovery condition is met whenever

    kappa*rho > sqrt(2)*k*sqrt(e) + sqrt(2/pi)*sqrt(epsilon-e).

Cauchy--Schwarz gives

    sqrt(2)*k*sqrt(e) + sqrt(2/pi)*sqrt(epsilon-e)
       <= sqrt(2*k^2+2/pi)*sqrt(epsilon).

Thus any coefficient

    Cback > sqrt(2*k^2+2/pi)/kappa

works for the reverse directed distance at all sufficiently small deficits.
Strict inequality leaves room for the strict area contradiction without a
limiting argument. Compactness of S can also recover the non-strict endpoint
coefficient by passage to the limit, but that is not needed for an explicit
integer coefficient.

For contained full-angle sofas, replace 2/pi by 1/pi. This is a genuinely better
subclass estimate, not a claim that arbitrary partial-angle sofas are contained
in their full-angle envelopes.

## 5. Do not put the terminal-angle constant into the leading coefficient

The forward estimate has the form

    d(S,G) <= F*(delta+B*alpha),
    alpha <= (epsilon-e)/c.

Therefore keep the two-scale result

    d(S,G) <= F*k*sqrt(e) + (F*B/c)*(epsilon-e).

The second term is linear, not square-root. For every Cfront>F*k, it is absorbed
by choosing a sufficiently small positive entry threshold. This does not
require a numerical value of B/c to make Cfront explicit; its value affects the
threshold instead. An explicit coefficient with an existential threshold is
not the same as an explicit, usable pair (C,epsilon0).

## Resulting reference-data formula

For arbitrary near-optimal sofas, any

    C > max(F*k, sqrt(2*k^2+2/pi)/kappa)

is admissible, once the reference geometry provides F,kappa and the existing
local-entry theorem applies. This improves the old formula involving 80,
4*(160+1)/kappa, and the terminal-angle coefficient in the leading term.

The next task is to give rational reference values of F and kappa. No numerical
global coefficient is being asserted solely from the scalar formula above.
