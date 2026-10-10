# The initial below-floor interval strengthens the first-wing energy test

Written proof, independently checked within the research session, October 10, 2026. This gives a
stronger sufficient condition for first-source unit curvature at a
remaining tilted canonical maximizer. Its sufficient curvature criteria can be combined with the
[first-wing tilted exclusion](gate1-tilted-first-wing-exclusion.md);
the criteria alone are not a sharp scalar value theorem.

## 1. Notation and criterion

Use the actual first-quarter support f and low-wing surrogate support g,
with their regular densities u=f''+f and v=g''+g. Set

    p=f'-g+1, q=g'+f-1,
    d=3C, B=e_R-1+h,
    gamma0=acos(1-h), s0=sqrt(h(2-h)), c0=1-h.

The remaining canonical parameter range has C>1/2 and 0<h<17/50.
The following two inequalities suffice for u<=1 a.e.:

    d^2+B^2<=5,                                        (IE1)
    d^2+B^2+B(1-h)-d sqrt(h(2-h))<=4.                  (IE2)

This statement uses the established spatial same-sign source facts and
subsequent positive-component propagation. Their usual strict versions
give u<1 at the relevant first crossing when either bound is strict.

## 2. Both regular densities vanish on the initial same-sign floor interval

Before the central normal delta=atan(h/(2C)), actual high-point
quadrants make no positive niche in J, and u=v=0 is already proved.
On a compact later interval with p>0,q>0 and D_y<0, the same-sign
source theorem gives u=0. The actual corner is locally shadowed:
at the corner both physical wall heights strictly increase when the
angle increases, because their angle derivatives are respectively
p/sin(t)>0 and q/cos(t)>0.

Any sole second-wall contact contributing positive selected graph must
satisfy its angular stationarity equation, so it is the tangency D.
Its height is strictly negative. Thus no positive second-source piece
remains. The same local comparison excludes limiting floor exposure:
a nonstationary floor contact with strict companion slack is raised by
a nearby angle, and a floor corner in this sign region is raised on
both walls. Compact angle exhaustion and the exact selected source
equality therefore give v=0 as well.

Consequently, as long as the initial p,q-positive component continues
and D_y<0, both densities vanish. The exact zero-density solution is

    f=2C cos(t)+e_R sin(t),
    g=C sin(t)+(1-h)cos(t),
    D_y=1-h-cos(t),

    p-1=B cos(t)-d sin(t),
    q+1=d cos(t)+B sin(t).                            (IE3)

The first D_y zero of this solution is gamma0. The initial values
p(0)=e_R+h>0 and q(0)=3C-1>0 are strictly positive.

## 3. Stop the circle evolution at the floor or the first p-zero

Let alpha be the first p=0 crossing in the initial q-positive component,
if that crossing exists. If q leaves its positive component earlier,
u=0 on its entire positive-positive part; later positive-q components
obey the already proved small-component bound, so they cause no u>1.
We may therefore consider the case where q stays positive up to the
relevant stopping time

    tau=min(alpha,gamma0).

On the interval before tau, (IE3) is a rotation of a vector of squared
length R^2=d^2+B^2. The standard positive-positive energy is

    Epp=(p-1/2)^2+(q+1)^2
        =R^2+p-3/4.

If tau=alpha, p=0 and hence Epp(tau)=R^2+1/4-1.
If tau=gamma0, the same expression equals
R^2+1/4+B c0-d s0. In both cases it is bounded above by

    R^2+1/4+max(B c0-d s0,-1).                        (IE4)

For tau=gamma0 this is immediate. For tau=alpha only the -1 term is
needed; no extrapolation of the zero-density solution past alpha is
asserted. This formulation also avoids needing monotonicity of the
extrapolated circle after its stopping time.

Conditions (IE1)-(IE2) are exactly the statement that the right side
of (IE4) is at most 17/4. If the floor is reached first, the usual
same-sign estimate u=0,v<=1/2 makes Epp nonincreasing until alpha.
Therefore at the first p-zero,

    1/4+(q(alpha)+1)^2<=17/4,
    q(alpha)<=1.

On the rest of that q-positive component, p<0 and the arm bound make
q decrease. Every subsequent positive-q component has q<=1/8.
The established regularity bound u<=kappa(q), together with u=0 on
p,q>0 and the same-sign vanishing on the opposite sign regions,
therefore gives u<=1 a.e. This proves the criterion.

## 4. A small exact uniform consequence above C=2/3

In particular, the criterion holds throughout

    2/3<C<=18/25, 3/100<=h<=17/50.                    (IE5)

Indeed the box bound gives H(C)=1-sqrt(1-C^2)<31/100. The endpoint
laws and nonnegative niche heights place B in the enlarged interval

    -231/400+(5/4)h <= B <= -107/400+(5/4)h.           (IE6)

The sharper left-box estimate n_-<=(H(C)-h)_+ is available but is
not needed for this particular corollary.

For IE1, the maximum of B^2 on this rectangle of h and its two affine
B endpoints is (27/50)^2. Since d<=54/25,

    d^2+B^2 <= (54/25)^2+(27/50)^2
                =12393/2500<5.

For IE2 define

    Q(d,B,h)=d^2+B^2+B(1-h)-d sqrt(h(2-h)).

It increases with d on d>=2, because its derivative is
2d-sqrt(h(2-h))>0. It is convex in B, so for each h it suffices to
use the two affine endpoints in (IE6). At either endpoint B=A+5h/4,
the polynomial part B^2+B(1-h) has h^2 coefficient 5/16>0. Also
-d sqrt(h(2-h)) is convex in h. Each resulting function of h is
therefore convex, so only the endpoints h=3/100 and h=17/50 need
checking.

At h=3/100, sqrt(h(2-h))>243/1000. The two B values are
-27/50 and -23/100, respectively. Substituting d=54/25 and this
lower square-root bound gives

    Q<97713/25000<4,
    Q<99263/25000<4.

At h=17/50, sqrt(h(2-h))>3/4. The two B values are
-61/400 and 63/400, respectively. The same substitution gives

    Q<474913/160000<4,
    Q<507897/160000<4.

All radical comparisons follow by squaring positive rationals. Thus
IE1 and IE2 both hold strictly on (IE5), proving first-source unit
curvature there.

## 5. The remaining high-tilt strip is also first-unit

The same criterion holds for every remaining width when

    C<=37/50, 21/100<=h<=17/50.                       (IE8)

Use H(C)<33/100 and the improved low-wing box bound. On this strip they give

    -107/400<=B<=69/400.

Consequently

    d^2+B^2<=(111/50)^2+(107/400)^2
             =799993/160000<5,

with exact margin 7/160000. For IE2 the expression Q increases in B on
this entire enlarged rectangle, since 2B+1-h>=1/8. Use the affine upper
endpoint B=-101/400+5h/4 and d=111/50. The resulting expression is
convex in h. At h=21/100, sqrt(h(2-h))>61/100 gives

    Q<17911/5000<4.

At h=17/50, the bound sqrt(h(2-h))>3/4 gives

    Q<545121/160000<4.

These exact endpoint comparisons prove both conditions. The general
[first-wing exclusion](gate1-tilted-first-wing-exclusion.md) therefore
excludes all remaining tilted maximizers with h>=21/100.

## 6. Stronger parameter-dependent endpoint interval

For a sharper application one should retain the actual left-box
improvement. The exact allowed interval is

    -1/2+(5/4)h-(H(C)-h)_+/4 <= B
        <= -1/2+(5/4)h+3H(C)/4.                       (IE7)

The lower endpoint has slope 3/2 for h<=H(C) and slope 5/4 afterwards.
For fixed C the two expressions in IE1-IE2 are convex in B; on each
affine h segment their IE2 expressions are convex in h. Hence any
desired additional rational rectangle can be certified by a few exact
endpoint comparisons. Such a certificate proves a sufficient curvature
condition only; it must still be combined with the appropriate folded
companion/value theorem.
