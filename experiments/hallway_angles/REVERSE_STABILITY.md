# Quantitative reverse-class stability

Status: analytic proof draft, dependent on the reverse cap majorant and quadratic theorem. This controls canonical paths and relevant supports. It does not silently infer Hausdorff stability of arbitrary sets from an area estimate alone; the set-level limiting argument is separate.

Fix 0<e<=e_* from `REVERSE_CROSSING_EXTENSION.md`. Let S be any reverse-class sofa, centered in its actual vertical strip of width w, with canonical corner C and horizontal gauge x(-e/2)+x(e/2)=0. Put

    Delta=V(e)-area(S)>=0,
    Delta_0=V(e)-1/[2 sin(e/2)]>0,
    a_e=min{F_e'(1),2[V(e)-F_e(1/2)]}>0.

The scalar positivity is established by `extended_width_certificate.py`.

## 1. Width deficit is controlled by area deficit

If Delta<Delta_0 then w>1/2, by the width-sensitive midpoint bound. Since F_e is quadratic,

    [F_e(1)-F_e(w)]/(1-w)

is affine in w. Its endpoint values on [1/2,1] are the two quantities defining a_e. Therefore

    V(e)-F_e(w)>=a_e(1-w),
    1-w<=Delta/a_e.                                   (1)

Let C_{e,w} be the explicit stationary path with endpoint heights +/- (1-w/2). The geometric majorant and strict quadratic maximization give the stronger decomposition

    Delta >= [V(e)-F_e(w)]
                 +[F_e(w)-Q_corrected(C)].             (2)

Both bracketed terms are nonnegative. The second is exactly the quadratic deficit relative to C_{e,w}, since the width correction is fixed when w is fixed.

## 2. Quantitative control of all path variations

Write t in [-e/2,e/2] and v(t)=R_t(C(t)-C_{e,w}(t)). Its endpoint abscissa parameter is u: v(-e/2)=(u cos(e/2),-u sin(e/2)) and v(e/2)=(-u cos(e/2),-u sin(e/2)). Let J_e be the homogeneous endpoint Jacobi field for u=1 in `REVERSE_QUADRATIC_THEOREM.md`, and write

    v=u J_e+v_0,  v_0 in H^1_0.

Integration by parts and the homogeneous Euler equation eliminate the mixed quadratic term. Consequently the deficit is

    F_e(w)-Q_corrected(C)=-E(e)u^2-q_0(v_0),            (3)

where E(e)<0 is the explicit endpoint coefficient of the quadratic theorem.

Put r=e/pi, a=1-cos e, b=1+cos e, and let mu_e be the smaller eigenvalue of

    [[a-(a+1)r^2, -r],
     [-r, b-(b+1)r^2]].

The original Poincare argument proves mu_e>0. Hence

    -q_0(v_0)>=(mu_e/2)||v_0'||_2^2.

The zero-endpoint estimate ||v_0||_infinity<=sqrt(e)||v_0'||_2 and (2)-(3) imply

    ||C-C_{e,w}||_infinity
      <=[||J_e||_infinity/sqrt(-E(e))+sqrt(2e/mu_e)] sqrt(Delta).

The explicit C_{e,w} is affine in w. If L_e=||partial_w C_{e,w}||_infinity, then (1) yields

    ||C-C_{e,1}||_infinity
      <= B_e sqrt(Delta)+(L_e/a_e)Delta.                (4)

Thus nearly optimal competitors, including asymmetric and nonsmooth ones, have canonical paths and relevant support values close to those of the exact optimizer. Reflection symmetry was not assumed in obtaining (3).

## 3. Uniform coercivity after the near-reversal rescaling

Ordinary physical-coordinate constants degenerate as e->0, so (4) alone is not enough for a changing-angle limit. Rescale time by t=e u, u in [-1/2,1/2]. For a zero-endpoint rotating-coordinate variation define

    P(u)=e v_{0,x}(e u), Q(u)=v_{0,y}(e u).

Direct substitution in q_0 gives

    2e q_0 = integral [(a+1)P^2+(b+1)e^2 Q^2
                       -(a/e^2)P'^2-b Q'^2-(P Q'-Q P')] du.

Let X=||P'||_2 and Y=||Q'||_2. Poincare on the unit interval and integration by parts yield

    2e q_0 <=-[a/e^2-(a+1)/pi^2]X^2
               -[b-(b+1)e^2/pi^2]Y^2+(2/pi)XY.

For 0<e<=1/2, the elementary Taylor bounds and pi>3 give

    a/e^2>=47/96, a+1<=9/8, b>=15/8, b+1<=3.

Thus the first positive coefficient is at least 35/96 and the second at least 43/24. Using (2/3)XY<=X^2/9+Y^2 proves the explicit uniform bound

    -e q_0 >= (X^2+Y^2)/8.                             (5)

For the free endpoint mode set U=e u. Its contribution is

    -e E(e)u^2=[-E(e)/e] U^2.

With T0=tan(sqrt(3)/2)/sqrt(3), the endpoint formula gives

    -E(e)/e -> (1/T0-1)/2 > 0.                         (6)

The rescaled fields (J_{e,x}(e u),J_{e,y}(e u)/e) converge uniformly and are bounded. This follows directly from their explicit sine/cosine formulas: k e -> sqrt(3), r/e ->1/(2sqrt(3)), and their denominator tends to sin(sqrt(3)/2)>0.

The width coefficient also stays uniformly positive after multiplying by e:

    e a_e -> min{3(1-T0)/[2(1+T0)],
                  (13-17T0)/[8(1+T0)]}>0.             (7)

For an elementary sign check, alternating Taylor bounds at x=sqrt(3)/2 give sin x<=563x/640 and cos x>=5/8, so T0<=563/800<13/17<1.

Equations (2), (5)-(7) imply: there exist fixed B,delta_*,e_1>0 such that for every e<e_1 and normalized deficit

    delta=e[V(e)-area(S)]<delta_*,

one has

    1-w<=B delta,
    sup_{|u|<=1/2} |(e C_x(eu),C_y(eu))
                       -(e C_{e,1,x}(eu),C_{e,1,y}(eu))|
       <=B(sqrt(delta)+delta).                         (8)

To convert back from rotating coordinates use the matrix with rows (cos(eu),e sin(eu)) and (-sin(eu)/e,cos(eu)); it and the width-dependent stationary-path coefficients are uniformly bounded. No unproved exchange of a vanishing spectral gap with the limit is used.

This uniform estimate is the main input to the universal set-shape limit, not merely uniqueness at each fixed angle.
