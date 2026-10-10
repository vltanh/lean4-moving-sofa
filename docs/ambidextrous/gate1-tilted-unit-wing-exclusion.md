# No tilted global maximizer with two unit-curvature wings

**October 10, 2026. Written proof, independently audited within this research session. Gate 1 remains open.**

This note proves that a canonical global maximizer of the actual spatial
score cannot be tilted if both of its regular charged-wing curvature
densities are at most one. Every possible order of the floor and window
crossings is covered. The proof establishes the needed finite-source
projection and local flux identities explicitly, including portions that
disappear at height zero.

The geometric reductions and source-measure inputs are
[MID](gate1-global-middle-chord-canonicalization.md),
[TF](gate1-spatial-tilted-facet-pinning.md),
[RG](gate1-spatial-maximizer-wing-curvature-regularity.md),
[EP](gate1-global-endpoint-complementarity.md), and
[LH](gate1-global-positive-pressure-and-wing-identity.md).
The [tilted-width exclusions](gate1-tilted-width-exclusions.md) place every
remaining tilted maximizer in the range used below. The
[horizontal theorem](gate1-horizontal-maximizer-sharp-value.md) already proves
the sharp value for every horizontal canonical global maximizer.

**The extra hypothesis here is that both regular wing densities are at most
one.** [CH7](gate1-spatial-maximizer-curvature-and-horizontal-value.md) supplies
one such bound for tilted maximizers with C at most 2/3. It does not supply
the other bound, and this note does not infer it. Every remaining
above-reference maximizer must therefore have a genuinely nonunit regular
wing. That is the current obstruction to Gate 1.

## 1. Domain and exact dependencies

Let U be the MID-canonical, EP-selected global maximizer of the actual spatial
objective P. Assume its affine middle roof is positively tilted after
reflection if needed. Translate so that

    I=[-2C,2C], J=[-C,C], A(-C)=a=1-epsilon, A(C)=1,
    1/2<C<4/5, 1/2<a<1.

The bounds in this display are available for every remaining tilted
maximizer from the exact short-width, wide-width and low-endpoint exclusions.
The stronger current bounds C>1001/2000 and epsilon<17/50 are not needed here.
TF4 places the top face at [C,b] x {1}; define

    T=b-C >=0, eR=A(2C), eL=A(-2C), z=n_U(C).

In particular the argument does not assume that the top face is a point.
LH2 gives positive endpoint pressures, and therefore EP gives equality of
limiting finite positive source measures and actual charged wing-curvature
measures. RG supplies the regularity and excludes open-quarter wing atoms.
The only additional hypothesis of this note is the unit bound on both
charged-wing densities, made explicit below.

Write L=pi/2, mu=(cos t,sin t), nu=(-sin t,cos t), and use the **left-wing
surrogate support** rather than the actual companion support across the
central-facet switch:

    f(t)=h_U(mu_t),
    g(t)=max_{-2C<=x<=-C}[-x sin t+A(x)cos t].

The endpoint values and derivatives are

    f(0)=g(L)=2C, f(L)=1, g(0)=a,
    f'(0)=eR, f'(L)=-b, g'(0)=C, g'(L)=-eL.          (TU.1)

Assume, in addition to the proved W^(2,infinity) regularity,

    0<=u=f''+f<=1, 0<=v=g''+g<=1  a.e. on (0,L).     (TU.2)

The actual companion is max(g,-C sin t+cos t). Its second term gives the
inner-wall height

    1-sec t+(x-C)tan t <=0  for x in J.

Consequently the full actual **positive** niche on J is exactly the positive
part of the surrogate two-wall roof. This follows by distributing min over the displayed maximum and then
taking the positive part; it is an all-angle identity, not an assumed
contact pattern. The surrogate has no central-facet atom;
before delta=atan(epsilon/(2C)) its curvature is zero. Actual quadrants with
0<t<delta have no positive part in J, so the finite-source equality also
forces u=0 there. These observations permit all subsequent source statements
to be made with f,g, including angles below the central-facet switch.

## 2. Monotone wall tangencies and ordered contacts

Set

    p=f'-g+1, q=g'+f-1,
    c=(f-1)mu+(g-1)nu,
    B=c+p nu=(f-1)mu+f'nu,
    D=c-q mu=(g-1)nu-g'mu.

Then

    p'=u-1-q, q'=v-1+p,
    B'=(u-1)nu, D'=(1-v)mu.                         (TU.3)

Thus B_x and D_x are nondecreasing, B_y is nonincreasing, and D_y is
nondecreasing. Their endpoints are

    B(0)=(2C-1,eR), B(L)=(b,0),
    D(0)=(-C,-epsilon), D(L)=(1-2C,eL).              (TU.4)

Because C>1/2,

    q cos t-p sin t=B_x-D_x >=4C-2>0.                (TU.5)

The endpoint contact signs are

    p(0)=eR+epsilon>0, q(0)=3C-1>0,
    p(L)=1-3C-T<0, q(L)=-eL<0.

The differential inequalities p'<=-q and q'<=p, together with TU.5, imply
unique ordered sign changes alpha<eta:

    p>0 on (0,alpha), p<0 on (alpha,L),
    q>0 on (0,eta), q<0 on (eta,L).                  (TU.6)

For example, while p>=0, TU.5 makes q>0 and hence p strictly decreases.
After p becomes negative, q strictly decreases as long as it is nonpositive;
at p=0 the vector field points strictly into p<0 whenever q>0. A return
through either zero is therefore impossible. At a common zero TU.5 would
fail. This also handles possible weak-density degeneracies without an
assumed finite contact chart.

Let gamma be a crossing of D_y=0 and beta a crossing of B_x=C. If T>0 both
are interior. Crossing plateaus cause no integration ambiguity: 1-v=0 a.e.
on a D_y plateau, and 1-u=0 a.e. on a B_x plateau. Write

    x_zero=D_x(gamma), D(gamma)=(x_zero,0),
    B(beta)=(C,z).                                  (TU.7)

The following source-separation estimate holds throughout C<=4/5. For the
right-window statement, any B tangency with B_x>=C has k=cos t<=C and

    p <= 1-(2C+k)sqrt(1-k^2)+epsilon k <0.            (TU.8)

The expression is convex in k. Its value at k=0 is 1-2C<0; at k=C it is
strictly below 1-3C sqrt(1-C^2)+C/2<0. The last strict inequality follows
from

    9C^2(1-C^2)-(1+C/2)^2>0  on [1/2,4/5].

Its derivative is (2-3C)(24C^2+16C-1)/2, and its endpoint values are
1/8 and 71/625, so its minimum is positive. Hence B(alpha)_x<C and
beta>alpha. Also B_y>=0, with B_y(alpha)>0: if it were zero, monotonicity
would make B constant at (b,0) from alpha to L, contradicting TU.8 and
p(alpha)=0. On the core interval (alpha,eta),

    c_y=B_y-p cos t>0,
    c_x'=p cos t-q sin t<0.

Its endpoints are c(alpha)=B(alpha), c(eta)=D(eta). Since D_x>=-C and
B(alpha)_x<C, the entire corner arc lies strictly inside J. Its positive
height at eta proves gamma<eta.

Global monotonicity of the two wall tangencies gives the signed envelope
graph: D up to eta, the corner c traversed in reverse from eta to alpha,
and B from alpha onward. In particular its negative part occurs before
x_zero, its positive part is exactly (x_zero,b), and n_U(-C)=0. Its positive
graph inside J is precisely

    D[gamma,eta], reverse c[alpha,eta], B[alpha,beta]. (TU.9)

This graph description follows from the signs and monotonicity in TU.3--6;
it is not imposed on the initial cap. For an explicit verification, the two wall derivatives are

    partial_t R_t(x)=(x-B_x(t))/sin^2 t,
    partial_t S_t(x)=(x-D_x(t))/cos^2 t.

At a D tangency with q>0, S is the global second-wall maximum and its
first companion lies strictly higher, so the full two-wall envelope equals
D there. At a B tangency with p<0 the reflected argument applies. At a
corner with p<0<q, every earlier second wall and every later first wall
is strictly below the corner, so the full envelope equals that corner.
The three spatial intervals meet at D(eta)=c(eta) and c(alpha)=B(alpha),
and cover [-C,b]. Their endpoint-angle limits supply the constant signed
heights -epsilon to the left and zero to the right. This verifies the
claimed graph directly from the full wall families.

## 3. Exact projection balance, with the zero-height limit issue resolved

Let U_n be the EP-selected finite polygons and Z_n={x in J_n:n_n(x)>0}.
The exact finite graph projection identity and the limiting source equality
give

    lim |Z_n| = integral_0^L [u sin t+v cos t]dt
              = (2C-b)+C=2C-T.                       (TU.10)

The last equality uses TU.1 and the horizontal projections of the two
outer source curves. It excludes the charged horizontal top segment T.

It is not legitimate to identify this limit merely from uniform roof
convergence. Here is the needed separate argument. The continuum roof is
positive on (x_zero,C], so uniform convergence gives the corresponding
lower bound liminf |Z_n|>=C-x_zero. On a compact K strictly inside
(-C,x_zero), the **surrogate signed** roof is strictly negative. For every
fixed angular cutoff h>0, every surrogate quadrant height on
K x [h,L-h] is therefore bounded strictly below zero. The added actual
high-point wall is also strictly negative there: x<C and t>0 in its
displayed height formula. Thus all actual quadrants with turning angle in
[h,L-h] have strictly negative height on K, uniformly. The converging
finite quadrants cannot contribute positive graph there for large n.

Any finite positive graph left over K must consequently come from source
normals within h of one of the endpoint directions. EP.22 (the uniform
O(grid spacing) finite source-exposure bound) bounds their total source
mass, and hence their horizontal projection, by O(h)+o(1). Exhaust K toward
(-C,x_zero), then let h decrease to zero. This proves

    lim |Z_n|=C-x_zero.

Together with TU.10 it gives the exact relation

    boxed: T=C+x_zero.                                (TU.11)

In particular T>0. Indeed D_y rises from -epsilon to zero before the
interior angle eta, so integral_0^gamma(1-v)sin t=epsilon>0. On this
interval cos t>0, and its horizontal projection
integral_0^gamma(1-v)cos t=T cannot vanish.

## 4. Exact local source equations, without assuming arclength convergence

On strict compact pieces of the positive graph TU.9, finite active-angle
localization gives the following lower bounds on limiting source measures:

    sigma_f=[(1-u)1_(alpha,beta)+q1_(alpha,eta)]dt,
    sigma_g=[(1-v)1_(gamma,eta)-p1_(alpha,eta)]dt.       (TU.12)

Here B and D have ordinary tangent lengths (1-u)dt and (1-v)dt. On the
strict corner arc, the two vector projection equations for the finite
alternating source edges give q dt to the first source and -p dt to the
second. All those corners have positive height and lie strictly in J, as
proved above. This is exactly the local finite-wall flux calculation used
in the horizontal branch, with its spatial hypotheses verified here.

More explicitly, for a compact strict corner interval, the two source
edge directions are -nu and mu. Their positive lengths a_f dt,a_g dt must
sum to the forward corner displacement after choosing the graph orientation;
comparing coefficients of mu,nu gives a_f=q and a_g=-p. The strict signs
in TU.6 make these lengths positive. Uniform localization to that interval
passes the resulting local finite lower bounds to the limiting measures.
Exhaustion extends them over the open graph pieces. Flat B or D parameter
intervals map to one spatial point and have zero ordinary tangent length,
so the displayed tangency contributions remain valid there.

At this stage assert only nu_f>=sigma_f and nu_g>=sigma_g. This avoids an
unproved global niche-arclength convergence statement. Their weighted total
is already determined by the actual positive graph projection:

    integral sin t d sigma_f + integral cos t d sigma_g
       = C-x_zero.

By EP and TU.10--11, the same weighted total for nu_f=u dt and nu_g=v dt
equals C-x_zero. Their nonnegative differences have zero weighted total;
both weights are strictly positive in (0,L), and EP.22 excludes endpoint
mass. Therefore the differences vanish. We obtain the exact equations

    boxed: u=(1-u)1_(alpha,beta)+q1_(alpha,eta),
           v=(1-v)1_(gamma,eta)-p1_(alpha,eta)  a.e.   (TU.13)

This conclusion also removes all residual floor/plateau mass. It does not
postulate that every weak finite exposure limit is ordinary continuum
arclength.

## 5. Endpoint pressures and the two clipped strip moments

Since n_U(-C)=0 and n_U(C)=z, EP's actual moving-window laws read

    eR=1/2+epsilon/4+3z/4,
    eL=1/2-3epsilon/4-z/4.                            (TU.14)

From D'= (1-v)mu, B'=(u-1)nu, TU.7 and TU.11,

    T=integral_0^gamma(1-v)cos t dt,
    epsilon=integral_0^gamma(1-v)sin t dt,
    T=integral_beta^L(1-u)sin t dt,
    z=integral_beta^L(1-u)cos t dt.                    (TU.15)

All four quantities are nonnegative. Also 0<=z<=eR<=1 and 0<epsilon<1/2,
so epsilon+z<2. The first-source box yields cos beta<=C, hence

    beta>=acos C, sin beta>=3/5, cot beta<=4/3.        (TU.16)

No relative order between gamma and beta, or between either of them and
the opposite contact switch, is assumed anywhere below.

## 6. A continuous contact energy and its exact derivative

Define a continuous, piecewise quadratic function of the ordered contact
state (p,q):

    H=(p-1/2)^2+(q+1)^2+3/4,       if p>=0,q>=0;
    H=(p-1)^2+(q+1)^2,             if p<=0,q>=0;
    H=(p-1)^2+(q+1/2)^2+3/4,       if p<=0,q<=0.     (TU.17)

The formulas match at p=0 and q=0. The reverse sign sector is absent by
TU.5. The composition H(p(t),q(t)) is absolutely continuous. Substitution
of TU.3 and the exact source equations TU.13 gives

    H'=-(q+1)(1-v)1_(0,gamma)
         +(1-p)(1-u)1_(beta,L)   a.e.              (TU.18)

For verification, without either clipping flag the three regimes are

    (++): u=0, v=1/2;
    (-+): u=(1+q)/2, v=(1-p)/2;
    (--): u=1/2, v=0,

and each makes H'=0. In the core, floor clipping replaces v=(1-p)/2 by
v=-p, contributing -(q+1)(1-v); window clipping replaces u=(1+q)/2 by
u=q, contributing (1-p)(1-u). In the initial regime floor clipping gives
v=0 and the same first contribution. In the final regime window clipping
gives u=0 and the same second contribution. If both clips occur in the
core, their contributions add. The conditions gamma<eta and beta>alpha
already exclude the other cases. Thus TU.18 covers every event order.

Endpoint substitution from TU.1 and TU.14 gives

    H(L)-H(0)
      =6CT+T^2-(epsilon+z)(epsilon+z/2).              (TU.19)

Indeed q(0)+1=3C, p(L)-1=-3C-T,
p(0)-1/2=(5epsilon+3z)/4, and q(L)+1/2=(3epsilon+z)/4.

## 7. Evaluate the two energy fluxes exactly

Write

    I_D=integral_0^gamma(q+1)(1-v)dt,
    I_B=integral_beta^L(1-p)(1-u)dt,

    R_D=integral_0^gamma(1-v(t))
              integral_0^t u(s)sin(t-s)ds dt >=0,
    R_B=integral_beta^L(1-u(t))
              integral_t^L v(s)sin(s-t)ds dt >=0.     (TU.20)

Variation of constants from the initial endpoint gives

    q(t)+1=3C cos t+(eR+epsilon)sin t
          -integral_0^t(1-v(s))cos(t-s)ds
          +integral_0^t u(s)sin(t-s)ds.

For any integrable d, symmetry of the cosine kernel gives

    integral_0^gamma d(t) integral_0^t d(s)cos(t-s)ds dt
      =1/2[(integral_0^gamma d cos)^2
             +(integral_0^gamma d sin)^2].

Apply this with d=1-v and TU.15. The result is

    I_D=3CT-T^2/2+eR epsilon+epsilon^2/2+R_D.         (TU.21)

Backward variation of constants from the final endpoint similarly gives

    1-p(t)=(3C+T)sin t+eL cos t
           -integral_t^L(1-u(s))cos(s-t)ds
           +integral_t^L v(s)sin(s-t)ds,

and therefore

    I_B=3CT+T^2/2+eL z-z^2/2+R_B.                   (TU.22)

Integrate TU.18, so H(L)-H(0)=I_B-I_D. Combine TU.19--22, cancel T^2,
and substitute the moving-window pressures TU.14. All terms simplify to
the exact identity

    boxed: 6CT=(z-epsilon)(2-epsilon-z)/4+R_B-R_D.     (TU.23)

For clarity, the endpoint algebra before its final factorization is

    6CT=eL z-eR epsilon+epsilon^2/2
                      +3epsilon z/2+R_B-R_D,

and TU.14 turns the first four terms into
(z-epsilon)/2+(epsilon^2-z^2)/4. There is no discarded sign term and no
symmetry assumption.

## 8. The contradiction is uniform over every event order

Because v<=1,

    integral_t^L v(s)sin(s-t)ds <=1-sin t.

Use TU.15--16 to bound

    R_B <= integral_beta^L(1-u)(1-sin t)dt
         <= [(1-sin beta)/sin beta] T <=2T/3,

    z <=cot beta T <=4T/3.                           (TU.24)

Since epsilon,z>=0 and epsilon+z<2,

    (z-epsilon)(2-epsilon-z)/4 <=z/2.

Dropping the nonpositive term -R_D in TU.23 now gives

    6CT <=z/2+R_B <=4T/3.

But C>1/2 and T>0 imply 6CT>3T>4T/3, a contradiction.

**Conclusion.** No positively tilted canonical spatial global maximizer in
the remaining width/height range can have both charged-wing curvature
densities at most one. Reflection excludes negative tilt under the same
condition. Coupled with the already proved horizontal sharp-value branch,
this closes the scalar value problem as soon as a global two-unit-wing
theorem, or a valid extension of the present argument to the remaining
nonunit branch, is supplied. The first-quarter-only theorem for C<=2/3
does not yet supply that missing hypothesis.

## 9. Exact scope and remaining obligation

The argument uses the true spatial endpoint pressures, the complete niche,
and the selected finite source identities. It does not use concavity of P,
a fixed-width optimization or a numerical screen. The event ordering is deduced from the two unit bounds;
gamma and beta may occur in any order compatible with gamma<eta and
beta>alpha. A putative nonunit companion phase can invalidate monotonicity,
the source graph TU.9, or the estimate on R_B, and must be analyzed before
this conditional exclusion is used in an unrestricted Gate 1 conclusion.

The proof received independent adversarial written checks of its geometry,
limiting measures, event orders, and exact algebra. No external refereeing,
Lean formalization, Lake build, or CI run is claimed. Gate 1 remains ACTIVE
until the remaining nonunit branch is resolved.
