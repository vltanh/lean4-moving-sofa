# Analytic global bounds: 2.3 with midpoint alignment, 4.22 with the old pin

This strengthens the written analytic theorem in note 07. It uses the same
local cap/terminal certificates and qualitative-entry argument, together with
notes 11--13. No Lean formalization or independent proof review is claimed.
The coefficients below are conservative upper bounds, not optimal sofa constants.

## 1. Normalizations and statement

Let M=|G|, epsilon=M-|S|, and m(S)=(h_S(0)-h_S(pi))/2, the midpoint of the
horizontal projection. Put

    S_c = S + (m(G)-m(S), 1-h_S(pi/2)).

There is epsilon0>0 such that every original moving sofa with
0<=epsilon<epsilon0 satisfies

    d_H(S_c,G) <= (23/10)*sqrt(epsilon) = 2.3*sqrt(epsilon),
    |S_c symmetric_difference G| <= 50*sqrt(epsilon).              (A)

The same class of sofas, under the PREVIOUS left/top normalization S_l, satisfies

    d_H(S_l,G) <= (211/50)*sqrt(epsilon) = 4.22*sqrt(epsilon).       (B)

The angle estimate alpha=pi/2-omega<=3.1*epsilon is unchanged. All distances
are Euclidean distances of the actual compact sets. No smoothness, injectivity,
or monotonicity is assumed for S. Since S_c uses only a translation, (A) also
bounds the distance minimized over all rigid alignments.

The entry threshold is still existential. The old left/top pin and the new
midpoint pin are different statements; they must not be interchanged silently.
The faithful Baek theorem, original uniqueness proof, bridge, and Lean source
are not changed by these analytic conclusions.

## 2. Shared deficit budget

Work after qualitative entry into the fixed local certificate regime, using the
selected normalization. Let K be the right-angle cap completion, U=K minus N(K),
e=M-|U|, alpha=pi/2-omega, and m=|U minus S|. The earlier terminal analysis gives

    0<=e<=epsilon,
    m<=lambda*(epsilon-e),       lambda=10031/10000,
    alpha<=3.1*(epsilon-e).

There is no assumption S subset U. The stronger missing-area estimate retains
the small possible surplus S minus U. Both local certificates are invariant
under translating all the corresponding geometry; alternatively apply them
after midpoint normalization, which also tends to G in the qualitative-entry
argument. The completion cap has the same horizontal extreme supports as S.

The support bound is delta<=k*sqrt(e), where

    k=1001/1000 for midpoint alignment,
    k=1001/500 for the old left-support pin.

Note 11 justifies the first coefficient; it is not a replacement of the old
normalization by notation alone.

## 3. Exact optimization of sector recovery

Take beta=153/100, h=beta/2. Note 12 supplies uniform translated interior
sectors of aperture beta at every point of G. Orthogonal erosion supplies

    G eroded by radius r is contained in U,
    r=sqrt(2)*k*sqrt(e).

Set rho=C*sqrt(epsilon) for epsilon>0. For rho+r below the fixed sector scale,
the exact area forced missing if a reference point is not rho-close to S is

    rho^2*F_beta(u),  u=r/rho,
    F_beta(u)=h-asin(u)-u*sqrt(1-u^2)+u^2*cot(h).

Write z=e/epsilon, so u^2=2*k^2*z/C^2. Subtract the missing-area upper bound:

    [rho^2*F_beta(u)-lambda*(epsilon-e)]/epsilon
      = C^2*[F_beta(u)+q*u^2]-lambda,
    q=lambda/(2*k^2).

For 0<=u<=sin(h), the minimum of F_beta(u)+q*u^2 occurs at

    u_* = 1/sqrt(1+(cot(h)+q)^2).

Indeed its derivative is

    2u*(cot(h)+q)-2*sqrt(1-u^2),

which is strictly increasing and changes sign once. At the minimum the two
algebraic terms cancel, leaving exactly

    L = h-atan(1/(cot(h)+q))
      = atan(q*tan(h)^2/(1+q*tan(h)+tan(h)^2)).

It is therefore sufficient that

    C^2*L>lambda,
    C*sin(h)>sqrt(2)*k.                                         (1)

The second inequality keeps the entire possible range e/epsilon in the
nonempty-sector regime. The first has a strict margin and ensures that the
forced missing area exceeds m for EVERY split of the deficit, not just at
sampled values of e. For reference, the limiting coefficient of this sufficient
sector argument is

    C_sector(k)=sqrt(lambda/L).

It is about 2.299325 for centered k=1.001 and 4.216330 for pinned k=2.002.
The simpler inscribed-sector calculation in note 12 gave 2.34301 and 4.24558;
using the whole surviving region is the final improvement here.

## 4. Exact rational certificate for the chosen constants

No floating-point optimizer is needed to verify (1). Put x=153/200 and use

    s_lo = x-x^3/6+x^5/120-x^7/5040 <= sin(x),
    c_hi = 1-x^2/2+x^4/24-x^6/720+x^8/40320 >= cos(x)>0,
    t_lo=s_lo/c_hi <= tan(x).

The rational function Z(t)=q*t^2/(1+q*t+t^2) is increasing for t>0, since its
derivative has numerator q*t*(2+q*t)>0. Hence

    L>=atan(Z(t_lo))
      >=Z(t_lo)-Z(t_lo)^3/3+Z(t_lo)^5/5-Z(t_lo)^7/7.

These alternating Taylor bounds apply because 0<x<1 and 0<Z(t_lo)<1.
All inputs on the right are rational. Exact fraction arithmetic gives positive
margins C^2*L_lower-lambda:

    k=1001/1000, C=23/10:   margin > 0.0005885,
    k=1001/500,  C=211/50:  margin > 0.0017467.

The separate exact checks C^2*s_lo^2>2*k^2 verify the second inequality of (1).
Thus C=2.3 and C=4.22 are proved sufficient for the reverse direction under
the fixed local certificates, not selected solely from numerical samples.

## 5. Forward distance and the entry threshold

Note 13 gives

    directed_distance(S,G) <= (100/49)*(delta+B*alpha)
      <= (100/49)*k*sqrt(e)+(100/49)*3.1*B*(epsilon-e),

with B fixed. The leading coefficients are about 2.042858 and 4.085715,
strictly below 2.3 and 4.22 respectively. The linear remainder is absorbed by
reducing epsilon0. Also reduce epsilon0 until rho+r is below the sector scale,
the reference normal-slack estimate applies, and the original local area and
terminal certificates hold. Each requirement has a positive threshold, but
this proof does not compute their common minimum.

At zero deficit the existing uniqueness theorem gives equality. For positive
deficit, the two directed bounds prove (A) and (B). Uniqueness enters qualitative
entry exactly as it did in the preceding global theorem; this is not being
advertised as an independent proof of uniqueness.

## 6. Symmetric-difference coefficient 50 under midpoint alignment

Keep the direct roof-band/convex-layer method of notes 05--07, rather than
multiplying a Hausdorff constant by a boundary neighborhood constant. It gives

    |S_c triangle G|
      <= 2*A0*k*sqrt(e)+(3*epsilon-2*e)+8*k^2*e,
    A0=62307/2500,       k=1001/1000.

In particular

    |S_c triangle G| <= 49.8954456*sqrt(epsilon)+11.016008*epsilon.

For sqrt(epsilon)<=1/200 the latter is strictly less than 50*sqrt(epsilon).
This is another threshold restriction, not an asserted numerical global entry
threshold. The area improvement uses midpoint cap coercivity; it does not rely
on the new sector geometry or the 2.3 Hausdorff coefficient.

## 7. What has and has not been improved

* The abstract cap coefficient modulo horizontal translation improves from the
  pinned 2 sec(phi) to sec(phi), with a sharp quotient-space calculation.
* The same old globally pinned sofa conclusion improves from 30.5 to 4.22.
* Choosing midpoint alignment yields global sofa coefficient 2.3 and area
  coefficient 50. The angle coefficient remains 3.1.
* The effective global entry threshold, optimal feasible-triple coefficient,
  and optimal actual-sofa coefficient remain unresolved.

These are written analytic derivations using the existing global reduction,
not a new kernel-checked formalization. Independent review should check the
reference corner audit, uniform cone/normal charts, and the existing local
certificate inputs before changing paper verification claims.
