# A sharper canonical-corner crossing lemma

Status: analytic proof draft. This strengthens the geometric step of `REVERSE_GENERAL_MAJORANT.md`; it does not by itself extend the final optimality theorem until the scalar width comparisons are supplied on the larger interval. No numerical optimizer, Lean build, or CI is used.

Let e=pi-beta in (0,pi/2), let the actual strip height be w<=1, and use the canonical corner and support-point notation of the general majorant. Write phi+psi=e. When 0<phi<=psi and the corner height is inside the actual strip, that file's derivative identity implies

    sin(e) y' >= (sin psi/sin phi)(cos phi-w)
                      +(sin phi/sin psi)cos psi.       (1)

Thus a sufficient condition for positive crossing velocity is

    w < G_e(phi),
    G_e(phi)=cos phi + sin(phi)^2 cos(psi)/sin(psi)^2.  (2)

Reflection handles the other half of the angle interval. All these statements hold almost everywhere for Lipschitz support functions, which is enough for the clamping argument.

## 1. The full-width range extends beyond 120 degrees

Define

    e_* = arccos(sqrt(2)-1),
    beta_* = pi-e_* = 114.4698005207... degrees.

For w<=1 and 0<e<=e_*, the right side of (1) is strictly positive at every interior angle. Indeed, at w=1 its numerator after multiplication by sin phi sin psi is

    (1-cos phi) [cos(psi)^2+(1+cos phi)cos psi-1].       (3)

Let J(phi) denote the bracket with psi=e-phi. On 0<=phi<=e/2,

    J'=(2 cos psi+1+cos phi)sin psi - sin phi cos psi > 0,

since sin psi>=sin phi and all cosines are positive. Moreover

    J(0)=cos(e)^2+2 cos(e)-1 >= 0

exactly when e<=e_*. Therefore J(phi)>0 for every phi>0, including when e=e_*.

Consequently the actual-strip crossing, the outside-excursion integration, and the corrected area majorant of `REVERSE_GENERAL_MAJORANT.md` all remain valid for

    beta_* <= beta < pi.

This is a genuine extension of the geometric majorant, not an inference from numerical tests. The width-dependent quadratic F_e(w) itself was already derived for every e<pi/2; only its comparison with V(e) must still be verified on the extended range.

## 2. A uniform narrow-width criterion for every obtuse bend

For fixed phi, the function cos psi/sin(psi)^2 decreases on (0,pi/2). Because psi=e-phi < pi/2-phi,

    G_e(phi) > cos phi + sin(phi)^3/cos(phi)^2
             = (1+t^3)/sqrt(1+t^2),  t=tan phi in [0,1].

Let r=983/1000. For every t>=0,

    (1+t^3)^2-r^2(1+t^2)
      =1-r^2-r^2 t^2+2t^3+t^6
      >=1-r^2-r^6/27 > 0.                             (4)

The minimum of 2t^3-r^2t^2 is -r^6/27, attained at t=r^2/3. The last inequality in (4) is the exact integer assertion

    27*(1000^2-983^2)*1000^4 > 983^6.

Hence G_e(phi)>983/1000 throughout the relevant range. Every reverse-class sofa of actual height w<=983/1000 has a single increasing crossing for EVERY obtuse bend beta in (pi/2,pi). Its corrected quadratic majorant is therefore valid on that whole interval.

The best universal constant obtainable from (2) alone is

    r_*=(1+t_*^3)/sqrt(1+t_*^2),
    2t_*^3+3t_*-1=0,
    r_*=0.9836083... .

The rational 983/1000 was selected so that (4) has a short exact proof; it is not claimed sharp.

## 3. What the derivative estimate does not prove

For e>e_*, the lower estimate at w=1 becomes negative for sufficiently small phi>0, since J(0)<0. This is a failure of this particular sufficient estimate, NOT a constructed feasible sofa with decreasing canonical height, and NOT a counterexample to reverse optimality.

Similarly, the narrow-width criterion does not prove an unrestricted geometric majorant for height-one sofas at every obtuse bend. Uniformly shrinking a sofa makes the criterion applicable but loses area. That loss must be retained in any ensuing upper bound.
