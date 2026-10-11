# Geometric realization of the exact reverse-turn extremizer

## Theorem

For every 0<e<pi/2, the explicit stationary corner C_* in `REVERSE_QUADRATIC_THEOREM.md` bounds a compact convex sofa S_e of area V(e) that completes a reverse passage through the hallway of bend beta=pi-e. It has full strip height, is symmetric about the horizontal axis, and realizes the quadratic area bound exactly.

This feasibility theorem does not by itself assert optimality over all reverse sofas; the full-class upper bound for e<=pi/3 is assembled in `REVERSE_MAIN_THEOREM.md`.

Use L,s,c,d,q,m,k,K,eta,r,A,B,z0 as defined in the quadratic theorem, and let D0=cos K+eta sin K>0. In particular z0<0, B<0, and 0<K<pi/2.

## 1. Two endpoint inequalities

Let x,y be the components of C_*, and let h(phi)=1+n1(phi).C_*(phi-L). Direct substitution gives

    h(phi)=1/m+A sin phi-C0[cos(k(phi-L))-eta sin(k(phi-L))],
    C0=d/(2m D0)>0,
    rho(phi):=h+h''=1/m+(3C0/q^2)[cos(k(phi-L))-eta sin(k(phi-L))].

The two inequalities required below are

    rho(e)>0,              x''(L)>0.                    (1)

They reduce, after multiplication by strictly positive factors, to R(e)>0 and X(e)>0, where

    R=(2q^2+3d)cos K+eta(2q^2-3d)sin K,
    AC=2(1-d)+3d(3-2d)/q^2,
    AS=2(1-d)-3d(2d+3)/(1+d)^2,
    X=q^2(1+d)^2[AC cos K+eta AS sin K].

More precisely,

    rho(e)=R/(2m q^2 D0),
    x''(L)=c X/[2m s D0 q^2(1+d)^2].

### Small angles: 0<e<=pi/6

Here d>=sqrt(3)/2>4/5 and eta<2/3. Monotonicity of K gives K<=pi sqrt(13)/12<19/20. For v=19/20, the alternating Taylor bounds give

    cos K-eta sin K
      >=1-v^2/2-(2/3)(v-v^3/6+v^5/120)
      =3675901/576000000>0.

Thus rho(e)>0. Also AC>=12 because q^2<=1/4 and d(3-2d)>=1; AS>=-15/4 because 3d(2d+3)/(1+d)^2<=15/4 for 0<=d<=1. Since eta<1 and tan K<2, AC+eta AS tan K>0. This proves x''(L)>0.

### Middle angles: pi/6<=e<=4pi/9

`parameter_certificate.py` proves R>0 and X>0 on this whole closed interval using exact-integer dyadic interval arithmetic. Sixty-four cells in e/pi suffice; their common lower bounds are R>3/5 and X>2/5. These are parameter intervals, not point samples.

The computation uses Machin's identity for pi with rational alternating-series remainders, interval Taylor polynomials for sin and cos, and integer square roots. Every operation is outward rounded with integer division at scale 2^96. The degree-73/72 trigonometric remainders are bounded by exact rational inequalities. No binary64 arithmetic, numerical optimizer, or polygon package is in the proof checker.

### Large angles: 4pi/9<=e<pi/2

Here 0<d<=sin(pi/18)<1/5. Both coefficients in R are positive. Moreover

    AS=-(d+2)(2d^2+4d-1)/(1+d)^2>0,

and AC>0. This proves (1). The three ranges cover all 0<e<pi/2.

## 2. The corner is a strictly convex graph

For t>=0, differentiation of the explicit formula gives x'(t)>=0, y''(t)<=0, and x'''(t)<=0, with strict inequalities in the interior where appropriate. To check the signs, put

    U=k^2+1+2rk>0, W=2k+r(k^2+1)>0.

Then

    y''=z0 sin t+B[W sin(kt)cos t+U cos(kt)sin t],
    x'''=z0 sin t+B[(kU+W)sin(kt)cos t+(U+kW)cos(kt)sin t].

Every bracketed summand is nonnegative on [0,L], while B,z0<0. Direct substitution also gives

    y'(L)=q rho(e)>0.

Consequently y'(t)>=y'(L)>0 and x''(t)>=x''(L)>0 on [0,L]; reflection gives the same positivity on [-L,L]. Therefore y is a bijection onto [-1/2,1/2], and the corner defines x=g(y), with

    g''(y(t))=[x''y'-x'y'']/(y')^3>0.

Since x is even, increases on [0,L], and vanishes at the endpoints, g<=0.

## 3. Every inner wedge is avoided

Let phi=t+L and psi=e-phi. The corner velocities obey

    n1(phi).C_*'(t)
      =-c z0-B[s(k+r)sin(kt)+c(1+rk)cos(kt)]>0,
    n2(phi).C_*'(t)<0.                                 (2)

For t>=0 the first sign is immediate. On [-L,0] its bracket is increasing, so its minimum is at -L, where the first expression equals y'(-L)>0. The second sign follows by reflection.

At an interior pose, (2) is equivalent to

    -cot phi < g'(y(t)) < cot psi.

The forbidden wedge at that pose is the region to the left of both lines through (g(Y0),Y0) with slopes -cot phi and cot psi. Convexity of g places its graph above its tangent line, and the tangent slope lies between these two slopes. Thus every point with x>=g(y) avoids the forbidden wedge. This is a global all-heights argument, not a check only at the matching corner height. At phi=0,e the entry-strip inequalities give the inner-wall condition directly.

## 4. The right boundary is a genuine convex cap

The function cos(kt)-eta sin(kt) has no interior minimum on [-L,L], and its smaller endpoint value is at L. Thus rho(phi)>=rho(e)>0. The upper support arc is

    P_plus(phi)=(h sin phi+h' cos phi, h cos phi-h' sin phi),
    0<=phi<=e.

It starts at (h'(0),1/2), moves strictly right and down, and ends on y=0. The lower arc is its reflection. The terminal identity is

    h(e)cos e-h'(e)sin e=0.

It follows algebraically from kq=eta(2+d) and kq eta=2-d. The top contact has h'(0)=y'(-L)>0. Hence the cap's right boundary F(y) is strictly positive throughout the strip, while g(y)<=0. The two arcs, their terminal tangent vertex, and the strip halfplanes define a compatible convex cap; no support inequality cuts off either arc.

Define

    S_e={(x,y): -1/2<=y<=1/2, g(y)<=x<=F(y)}.

It is a compact convex body with nonempty interior. Its outer support values on the two relevant angular arcs are exactly h, since the displayed contact arcs belong to S_e.

## 5. Motion, area, and endpoints

Outer-wall containment follows from h=1+n_j.C_*. Inner-wall containment was proved in Section 3. Thus S_e fits every hallway pose along the explicit continuous corner path. At the start and end it lies in the corresponding unit-width strips; translations arbitrarily far along the incoming and outgoing arms attach without collision. This is a complete passage, not merely a rotation inside a bounded box.

Finally,

    area(S_e)=integral(F-g)dy
             =Cap(h,h)-integral x y' dt
             =Q(C_*)=V(e).

This proves feasibility and exact attainment. The body is regular closed, which is useful for set equality in the optimizer classification.

## Reproduction and trust boundary

```sh
python parameter_certificate.py --cells 64 --output parameter-proof.json
python -m unittest -v test_parameter_certificates test_reverse_exact
```

The parameter lemma is computer-assisted using exact integers, not Lean checked. The ODE solution, area identity, convexity argument, and wedge-avoidance proof are ordinary mathematical derivations and require independent mathematical review. Floating-point polygon tests are supplementary regression tests, not part of the certificate proof.
