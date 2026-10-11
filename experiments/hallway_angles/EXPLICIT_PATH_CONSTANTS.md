# Explicit uniform canonical-path stability

**Proof draft with exact-integer scalar assistance.** This quantifies the path theorem without using the actual-set stability or the universal limit-body theorem. Let 0<e<=1/10, and use the established reverse-class majorant, strict quadratic maximization, and explicit feasible S_e. Their geometric derivations remain dependencies requiring independent review.

For a reverse sofa R of actual width w, normalized deficit

    d=e[V(e)-area(R)]<1/3,

center its actual strip and impose the horizontal canonical gauge. Write C for its canonical corner, C_w for the stationary path with the same endpoint heights, and C_*=C_1 for the candidate. Then

    1-w <= 10d,                                      (1)
    sup |e(C_x-C_*x)| <= (5/2)sqrt(d)+(7/2)d,          (2)
    sup |C_y-C_*y| <= (17/10)sqrt(d)+5d.               (3)

All suprema are over the full parameter interval [-e/2,e/2]. These estimates allow nonsmooth, asymmetric, and nonconvex competitors. The constants apply simultaneously to the whole stated e interval.

## 1. Scalar bounds

`explicit_cutoff_certificate.py --cells 256` proves the following strict bounds on the CLOSED interval 0<=e<=1/10, with removable endpoint values interpreted by continuity:

    27/20 < eV(e) < 34/25,
    143/500 < ell_e < 1/3,
    -E(e)/e > 59/250,
    e F_e'(1) > 1/10,
    2e[V(e)-F_e(1/2)] > 1/10,
    eV(e)-e/[2sin(e/2)] > 1/3.                        (4)

Here ell_e=e h_e'(0), E is the free-endpoint Jacobi coefficient, and F_e is the corrected width-dependent majorant. The code also checks the endpoint-field and width-field bounds proved below from one-dimensional monotonicity.

The certificates use fixed-denominator outward integer intervals, bounded Taylor series, and integer square roots. All cells are intervals, including the first cell containing e=0. Neither floating-point optimization nor tests establish (4).

The last inequality in (4) and midpoint slicing imply w>1/2. The two width-slope inequalities and the quadratic nature of F_e imply

    e[V(e)-F_e(w)] >= (1-w)/10.

The majorant then proves (1) and the nonnegative decomposition

    d >= e[V(e)-F_e(w)] + e[F_e(w)-Q_corrected(C)].     (5)

## 2. A sharper trace estimate than using the minimum eigenvalue

Decompose the rotating-coordinate variation into its endpoint Jacobi field and a zero-endpoint variation v_0. Put U=e u for the endpoint abscissa parameter u. With rescaled time t=e z, define P(z)=e v_0x(ez), Q(z)=v_0y(ez), and X=||P'||_2, Y=||Q'||_2 on [-1/2,1/2]. The previous Poincare calculation gives

    2[-e q_0(v_0)] >= A X^2+B Y^2-2rXY,
    A=35/96, B=43/24, r=1/3.                         (6)

The matrix M=[[A,-r],[-r,B]] has determinant 1249/2304>0. The exact zero-endpoint trace inequality is |f(z)|<=sqrt(1/4-z^2)||f'||_2<=||f'||_2/2. Transforming back to rescaled physical coordinates uses rows (cos t,e sin t) and (-sin t/e,cos t). Their componentwise absolute bounds are (1,1/200) and (1/2,1), respectively, because e<=1/10.

For a row bound l and d_0=-e q_0(v_0), Cauchy-Schwarz in the positive matrix M gives

    |row(v_0)|^2 <= (l^T M^(-1)l/2) d_0.

The two exact coefficients are

    tau_x=4135701/2498000,
    tau_y=1320/1249.                                  (7)

Keeping this anisotropic trace estimate is important: the earlier coarser common 1/8 estimate loses too much in the vertical coordinate for a useful explicit cutoff.

## 3. The free-endpoint field on the whole time interval

Retain s,c,k,K,eta,r from the reverse quadratic theorem, and set

    D_J=c sin K+r s cos K,
    P_J=s(sin K-eta cos K)/D_J, T_J=-1/D_J.

After undoing rotation, the unit endpoint field is

    J_x(t)=T_J[sin(kt)cos t+r cos(kt)sin t],
    J_y(t)=-P_J+T_J[r cos(kt)cos t-sin(kt)sin t].

Its rescaled contribution is U*(J_x,J_y/e). For t>=0, J_y is increasing, from its nonpositive value at 0 to 0 at e/2, because its derivative is -T_J times a sum of positive sine/cosine products. J_x is decreasing from 0 to -1 provided

    (k+r)cos K cos(e/2)-(1+rk)sin K sin(e/2)>0.

The checker verifies the latter after multiplication by e. Reflection covers t<0. It also verifies 0<-J_y(0)/e<16/25. Consequently

    sup |J_x|<=1,    sup |J_y/e|<=16/25.              (8)

The orthogonal quadratic splitting gives endpoint energy at least (59/250)U^2, in addition to d_0. Combining (5), (7), and (8) by Cauchy-Schwarz in the TWO energy components gives

    |e(C_x-C_wx)| <= sqrt(250/59+tau_x) sqrt(d)
                    <(5/2)sqrt(d),
    |C_y-C_wy| <= sqrt((16/25)^2*250/59+tau_y) sqrt(d)
                    <(17/10)sqrt(d).                 (9)

The last comparisons are exact rational checks, not rounded square-root computations.

## 4. Varying the actual width

The stationary coefficients are affine in w, with

    B_w=1/[2s(cos K+eta sin K)],
    A_w=-c/(2s)+(r/s)B_w sin K.

Therefore

    partial_w C_x=A_w+B_w[cos(kt)cos t-r sin(kt)sin t],
    partial_w C_y=-B_w[cos(kt)sin t+r sin(kt)cos t].

On [0,e/2] the first is decreasing from its maximum at 0 to 0 at the endpoint. The second decreases from 0 to -1/2 if

    (1+rk)cos K cos(e/2)-(k+r)sin K sin(e/2)>0.

This scalar inequality is also certified. The maximum at t=0 has

    0<e partial_w C_x(0)<7/20.

Thus uniformly in w and t,

    |e partial_w C_x|<=7/20,  |partial_w C_y|<=1/2.    (10)

Equations (1), (9), and (10) prove (2)-(3).

## Dependency and verification boundary

This proof uses the cap/crossing/excursion majorant and the exact quadratic functional, not the fourth-round Hausdorff proof. Positivity of the displayed scalars is computer-assisted over a whole parameter interval; their geometric meanings and the trace calculation are analytic. The code does not certify its own correspondence to the mathematics. No Lean build or CI is used.
