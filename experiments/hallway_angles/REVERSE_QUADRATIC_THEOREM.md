# Exact maximization of the reverse-turn quadratic functional

This is an analytic theorem about the functional derived in `REVERSE_VARIATIONAL.md`. Its interpretation as an optimality theorem for sofas requires that file's geometric area-majorant hypothesis. No numerical maximization is used in this proof. No Lean or CI verification is claimed.

## 1. Statement and explicit stationary path

Fix 0 < e < pi/2. Write

    L=e/2, s=sin L, c=cos L, d=cos e,
    a=2s^2=1-d, b=2c^2=1+d, m=2-d,
    k=sqrt(1+3/sin(e)^2), K=kL,
    eta=sqrt((2-d)/(2+d)), r=(s/c) eta,
    z0=-2s/m,
    B=-d/[2m s (cos K+eta sin K)],
    A=(c/2+r B sin K)/s.

For -L <= t <= L put

    z_x(t)=z0+A cos t+B cos(kt),
    z_y(t)=A sin t-r B sin(kt),
    C_*(t)=R_{-t} z(t).

Then C_*(-L)=(0,-1/2), C_*(L)=(0,1/2). The denominators are positive: K increases from sqrt(3)/2 to pi/2 as e increases from 0 to pi/2, hence 0<K<pi/2.

**Theorem.** On H^1 paths C=(x,y) with y(-L)=-1/2 and y(L)=1/2, the functional Q from `REVERSE_VARIATIONAL.md` has a unique maximizer modulo horizontal translation, namely C_*. Endpoint abscissae are free. Reflection symmetry is a conclusion, not an assumption.

The support functions used to define Q are

    h_plus(phi)=1+n1(phi).C(phi-L),
    h_minus(e-phi)=1+n2(phi).C(phi-L).

For arbitrary H^1 paths these need not be support functions of a convex body. Enlarging to this space is a quadratic relaxation. The theorem does not assert that every feasible sofa is bounded by this relaxation without the geometric hypothesis.

## 2. The functional in rotating coordinates

Horizontal translation leaves Q unchanged. Fix the gauge x(-L)+x(L)=0 and write x(-L)=u, x(L)=-u. Put z(t)=R_t C(t), D=diag(a,b), J(x,y)=(-y,x), and H=1+d/2. Direct substitution gives

    Q(C)=H^2 cot e-u^2 sin(e)^2 tan e
      + integral_{-L}^L [1+(2s,0).z
          + (z^T(D+I)z-z'^T D z'-cross(z,z'))/2] dt.       (1)

Without the gauge, the rotating-coordinate expression additionally contains the endpoint term -(x(-L)+x(L))/4; using the gauge avoids that term. Equation (1) follows from the cap-area formula and

    integral x dy = 1/2 integral cross(C,C') dt
                    + (x(-L)+x(L))/4,
    cross(C,C') = cross(z,z')-|z|^2.

The Euler equation for the integral is

    D z''+J z'+(D+I)z+(2s,0)=0.                           (2)

Its characteristic determinant is

    (lambda^2+1)[sin(e)^2 lambda^2+sin(e)^2+3].

The symmetric solution of (2) with the stated endpoints is exactly z above. The frequency-1 mode is horizontal translation in the original frame.

## 3. Strict negativity for zero-endpoint variations

Let v in H^1_0([-L,L];R^2), and let q0(v) be the quadratic integral in (1). Set R=e/pi<1/2, X=||v_x'||_2, Y=||v_y'||_2. Poincare's inequality on an interval of length e and integration by parts give

    2 q0(v) <= -[a-(a+1)R^2] X^2
                -[b-(b+1)R^2] Y^2 + 2RXY.              (3)

Here integral cross(v,v')=2 integral v_x v_y', so the last term follows from Cauchy-Schwarz and ||v_x||_2<=R||v_x'||_2.

The matrix on the right is strictly negative definite. Indeed, a>=2R^2, a<1, so its first positive diagonal coefficient is positive. Its determinant is

    (1-R^2)[sin(e)^2(1-R^2)-3R^2] > 0.

To see the strict inequality, use sin e >= 2e/pi=2R and R<1/2; the bracket is at least R^2(1-4R^2)>0. Thus q0(v)<0 unless v=0.

## 4. Free endpoint abscissae do not introduce an asymmetric maximizer

Reflect paths by C(t) -> (x(-t),-y(-t)). In rotating coordinates this sends z(t) to (z_x(-t),-z_y(-t)). The quadratic form splits into reflection-even and reflection-odd subspaces, and the linear term is reflection-even.

The even variations have zero endpoints after the horizontal gauge. For an odd variation with endpoint parameter u, solve the homogeneous equation (2) with endpoints

    v(-L)=(uc,-us), v(L)=(-uc,-us).

Its solution is

    v_x=P sin t+T sin kt,
    v_y=-P cos t+r T cos kt,
    T=-u/[c sin K+r s cos K],
    P=u s(sin K-eta cos K)/[c sin K+r s cos K].

Any other odd variation with these endpoints differs by a zero-endpoint function. The cross term vanishes by integration by parts and the homogeneous Euler equation. Hence it suffices to evaluate the quadratic form on this solution. Including the endpoint term in (1), it equals u^2 E(e), where

    E(e) = (sin e/d)
      * [(2d-1) sin K-eta(2d+1) cos K]
      / [(1+d) sin K+eta(1-d) cos K].                    (4)

This is strictly negative for 0<e<pi/2:

- If e>=pi/3, then d<=1/2, so the numerator in (4) is negative.
- If 0<e<=pi/4, then K<=pi sqrt(7)/8<pi/3, while
  eta(2d+1)/(2d-1)>=sqrt(3). The latter inequality follows on squaring from
  (2-d)(2d+1)^2-3(2+d)(2d-1)^2=4(1-d)(4d^2+6d-1)>=0.
- If pi/4<=e<pi/3, then d<3/4, eta>1/2 and (2d+1)/(2d-1)>5, so the same ratio is greater than 5/2. Meanwhile K<=pi sqrt(5)/6<3pi/8, hence tan K<1+sqrt(2)<5/2.

All denominators in these comparisons are positive. Thus every nonzero odd variation decreases Q. Together with (3), this proves strict concavity modulo horizontal translation.

The displayed stationary solution therefore is the global maximizer of Q, including nonsymmetric competitors. Equality implies only a horizontal translate of C_*.

## 5. Exact value

An explicit elementary expression for the maximum is obtained without quadrature. With the constants in Section 1, define

    V(e) = H^2 cot e + e + e s z0 + 2s A sin L
           + (2s B/k) sin K
           - [A(a s^2+b c^2)
                + Bk(a s sin K-b c r cos K)]/2.          (5)

This is Q(C_*). To check (5), multiply (2) by z and integrate by parts. The integral in (1) becomes e+s integral z_x - [z^T D z']/2 at the endpoints. Substitute the explicit sine/cosine solution. The expression may suffer floating-point cancellation as e tends to zero; that numerical issue does not affect the identity.

For example, V(pi/6) is approximately 2.64102508165, V(pi/4) approximately 1.80376416705, and V(pi/3) approximately 1.39997951197. These decimal displays are not used in the proof.

## 6. Remaining geometric work

To turn this into a sharp sofa theorem, establish that the displayed support arcs form a convex cap, the corner graph is increasing in height and lies on the left boundary of a continuously feasible region, and the region realizes Q(C_*). The support-arc terminal contacts should meet at the symmetry axis. All of these are explicit one-variable inequalities for C_*.

Separately, extending the majorant from regular increasing-height canonical corners to every reverse-class sofa remains open in this research round. In particular, arbitrary canonical corner paths may have excursions outside the entry strip. The functional theorem must not be described as unrestricted moving-sofa optimality.
