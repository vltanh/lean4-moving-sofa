# A continuum dual certificate for reverse contact kernels

**Analytic certificate specification.** The finite verifier described here proves inequalities for every density pair in an infinite-dimensional convex relaxation. Numerical linear programs propose dual functions only. Acceptance uses exact integer/rational arithmetic. The geometric link to a relaxed reverse maximizer is in REVERSE_RELAXED_SELECTION.md and REVERSE_TERMINAL_KERNEL.md; these analytic arguments remain separate review dependencies.

## 1. Normalize the angular variable

Let s=e t with 0<=t<=1, and abbreviate r_+(et), r_-(et) by r_+(t), r_-(t) in this note. Put R=1/(1-cos e), c=R/2. Define

    (K_e r)_+(t)=e integral_t^1 r_+(x)sin(e(x-t))dx
                  +e integral_(1-t)^1 r_-(x)sin(e(x+t))dx,

and obtain the minus component by interchanging the two families. The relaxation is

    r>=0, r+c K_e r<=R,
    983/1000 <= w=e integral_0^1 (r_++r_-)sin(et)dt <=1. (1)

In particular r<=R. The kernel is nonnegative for e<=pi/2.

There are two target linear functionals:

- the upper curvature moment J_+, with coefficient pair f=(e sin(et),0);
- the subtracted term F(eu)=1+cos e-sin(e)a(eu), with coefficients

    f_+(t)=e sin(e(t+1-u)) 1_(t>=u),
    f_-(t)=e sin(e(t-1+u)) 1_(t>=1-u), 0<=u<=1/2.     (2)

The second target has a jump at u. The partition explicitly includes u and 1-u; the verifier never interpolates across that jump.

## 2. Dual inequality, with its residual paid for

For a pair lambda>=0 and a real eta, suppose

    f <= lambda+c K_e^*lambda+eta e sin(et)             (3)

componentwise almost everywhere. Multiplication by r and integration give

    integral f.r <= R integral(lambda_++lambda_-)
                     +max{eta,(983/1000)eta}.           (4)

The adjoint consists of a one-sided sine convolution and a reflected cross term:

    (K_e^*lambda)_+(t)
       =e integral_0^t lambda_+(x)sin(e(t-x))dx
        +e integral_(1-t)^1 lambda_-(x)sin(e(t+x))dx.

If the left side of (3) minus its right side is at most epsilon>=0, adding the constant epsilon to BOTH components of lambda makes (3) valid, because K_e^* is positive. The resulting extra cost is 2R epsilon. This allowance is never discarded.

## 3. Piecewise-affine witnesses and exact integration

A record gives a symmetric rational partition of [0,1] and the two endpoint values of lambda on every cell, separately on both families. Values are nonnegative. Adjacent cells may have different one-sided endpoint values. Changes on the finite set of endpoints do not affect integrals; the verifier checks both one-sided residuals.

For an affine lambda of slope v on [l,t], exact primitives are

    e integral_l^t lambda(x)cos(ex)dx
      =lambda(t)sin(et)-lambda(l)sin(el)
         +(v/e)[cos(et)-cos(el)],

    e integral_l^t lambda(x)sin(ex)dx
      =-lambda(t)cos(et)+lambda(l)cos(el)
         +(v/e)[sin(et)-sin(el)].                       (5)

Prefix sums of (5) give the full adjoint value. No quadrature estimate or numerical integration is used.

## 4. Control between the finitely checked points

On an open cell, and its reflected companion, lambda is affine. Put Lambda=integral(lambda_++lambda_-), and write L0,L1 for upper bounds on the same-family and reflected-family lambda values, and V1 for the absolute reflected slope. The second derivative of the dual residual is bounded in absolute value by

    M=e^3[1+|eta|+c Lambda]
        +c e^2[L0+2cos(e)L1]+c e V1.                  (6)

To verify (6), the same-family adjoint term H has H''=e^2 lambda-e^2 H. The cross term satisfies

    Hcross''=-e sin(e)lambda_other'(1-t)
               +2e^2 cos(e)lambda_other(1-t)-e^2 Hcross.

Also H+Hcross<=e Lambda, and both target and moment coefficient have second derivative bounded by e^3 (times |eta| for the latter). All one-sided values are handled separately.

For a twice differentiable function with |f''|<=M on an interval of length h, its value lies below the larger endpoint value plus Mh^2/8. Thus checking the residual at eight equal subdivisions of each cell, using (6), gives a rigorous UNIFORM residual allowance epsilon_0. This proves a continuum inequality, not merely inequalities at eight samples.

## 5. One witness certifies a whole parameter box

Suppose the record is centered at rational (e0,u0), and the target box is e in [el,eh], u in [ul,uh]. Restrict throughout to e<=pi/2, even when the final rational box extends slightly beyond that endpoint. Set

    E=eh, Rmax=1/[1-cos(el)], cmax=Rmax/2,
    de=max(e0-el,eh-e0), du=max(u0-ul,uh-u0).

Pointwise differentiation in e gives the following sufficient residual Lipschitz constant:

    Le=1+2E+[cmax(1+2E)+E Rmax^2/2]Lambda
                 +|eta|(1+E).                         (7)

Indeed the derivative of e sin(ea) is bounded by 1+2E for 0<=a<=2, the adjoint kernel derivative by (1+2E)Lambda, |c'|<=Rmax^2/2, and the adjoint itself by E Lambda. The moment coefficient has the sharper 1+E bound.

The target's discontinuity moves with u, so a pointwise Lipschitz assertion would be false. Its L1 difference instead satisfies

    ||f_(e,u)-f_(e,u0)||_1 <= E(1+2E)|u-u0|.           (8)

The first coefficient contributes an interval of length |du| with height at most E and an interior derivative at most E^2; the second coefficient vanishes at its moving endpoint and contributes at most E^2|du|. Since r<=Rmax, the objective error is bounded by Rmax times (8).

Consequently the whole-box target is at most

    U=Rmax[Lambda+2(epsilon_0+Le de)]
        +max{eta,(983/1000)eta}
        +Rmax E(1+2E)du.                              (9)

For the moment cover du=0. The verifier accepts only if U<43/50 for the moment target, or U<1+cos(eh) for the arm target. At the last box it may replace cos(eh) by zero, since only its intersection with e<=pi/2 is asserted.

## 6. Turning a moment bound into crossing

For e in [57/50,123/100] the separate moment certificate targets J_+,J_-<43/50. Let phi<=psi=e-phi and suppose the canonical corner height lies inside its actual strip. The terminal identities and density ceiling give

    Y_-(psi)>=w/2-J_+-R[cos(psi)-cos(e)],

as well as Y_-(psi)>=-w/2. Insert these into the exact support-point formula for y'. Minimizing in the possible corner height and using w<=1 gives

    q y' >= [sin(phi)/sin(psi)] B(e,phi/e),

    B=cos(psi)-sin(psi)^2/[1+cos(phi)]
       +max{0,7/50-R[cos(psi)-cos(e)]}.                 (10)

For clarity, before setting w=1 the relevant lower expression is

    [sin(psi)/sin(phi)](cos(phi)-w)
       +[sin(phi)/sin(psi)]
          [cos(psi)+max(0,w-43/50-R(cos(psi)-cos e))].

It is nonincreasing in w on the first half, so w=1 is the conservative value. Equation (10) follows using (1-cos phi)=sin(phi)^2/(1+cos phi).

`reverse_crossing_gate.py` certifies B>0 on the whole rectangle [57/50,123/100] x [0,1/2] by exact interval bounds. Thus every interior crossing velocity is positive. Reflection uses J_- for the other half. Clamping the C1 corner height to the strip makes it nondecreasing, which is the condition required by the signed-area majorant. This does not require positive individual arms on this range.

## 7. Range joins and proof status

For e<=57/50, the old general crossing argument applies because cos(57/50)>sqrt(2)-1. For narrow widths w<=983/1000 its separate old crossing bound applies at every obtuse bend. For the remaining larger e, the arm certificate seeks F(eu)<1+cos e for 0<=u<=1/2; the terminal-kernel elementary bound handles the other half, and reflection handles b.

A complete theorem requires the accepted box sets to cover all stated ranges without gaps, AND the geometric relaxed-maximizer hypotheses. The builder's use of an optimizer, or a list of successful point tests, is not enough. The independent replay must recompute every dual inequality and check the exact rational cover rather than trust saved success flags. No CI or Lean build is part of this method.
