# Sharpness for actual caps, and why it is not yet sharpness for the Q deficit

Analytic argument with numerical diagnostics, not formal verification. The
reference is Gerver's cap. The result concerns the FOUR CAP residual energies,
not the full Q deficit or actual sofa-area deficit.

## 1. The raw extremizing ray is not feasible in either sign

Let A=sec(phi), and let C(t)=<H_t,H_0> be the covariance from note 11. It is the
pinned support reconstruction for the abstract extremizing residual r=H_0.
It has C(0)=2A^2, C(pi/2)=C(pi)=0, and E(C)=A^2.

A proposed support h_G+tau*C with tau>0 is not a cap support. On [0,phi],
h_G(t)=cos(t), while C(t)=2A^2*cos(t)-sin(t). Thus

    h(t)-h(0)*cos(t)=-tau*sin(t)<0.

But every cap contains (h(0),0), so its support must be at least h(0)*cos(t).
Equivalently, the proposed right supporting face has negative upper height:
C'(0+)=-1. Adding a horizontal translation cannot fix either violation.

For tau<0, the jumps of C' at phi and T=pi-phi are both A^2*sin(phi)>0.
The reference has no curvature atom at either cut, so multiplying these jumps
by tau gives negative curvature atoms. Hence the opposite raw ray is also
infeasible. Merely rejecting the two raw rays does NOT prove a strict improvement
over sec(phi): approximating feasible directions can still approach them.

## 2. Reference curvature is positive where smoothing is needed

On the upper outer contact A(t), the curvature density in normal angle is

    rho_A=b+1-a',       x'=-a*u+b*v.

The phase formulas give

    phase 1: rho_A=0,
    phase 2: rho_A=b,
    phase 3: rho_A=b,
    phase 4: rho_A=s/2-b1,       s=pi/2-t,
    phase 5: rho_A=1/2.

The source parameter bounds make the second- and third-phase b greater than
1/2 and the fourth-phase expression greater than 1/2. For example phase 3 uses
b=c1-t+1, c1>0.626, and t<1.571-0.68. The reflected contact C supplies the
same lower bound on the second quadrant. Consequently the reference curvature
measure has density at least 1/2 on (phi,pi-phi), plus the positive top-face
atom. It is zero on the two endpoint normal gaps. Its floor-face atom is the
positive horizontal width. These facts follow from the contact formulas, not
from sampled curvature of a polygonal approximation.

## 3. Smooth only toward the positive-curvature side

Fix a small eta>0, less than all distances to the other relevant cuts. Replace
C on [phi,phi+eta] by the cubic Hermite interpolant that matches its endpoint
values, its LEFT derivative at phi, and its ordinary derivative at phi+eta.
On [T-eta,T], interpolate the endpoint values, the derivative at T-eta, and the
RIGHT derivative at T. Leave C unchanged elsewhere. Denote the result C_eta.

Thus C_eta is C1 at phi and T, with no curvature atom there. It is unchanged
on the two zero-curvature normal gaps. The only remaining derivative jump is
the top-face jump 2*tan(phi), where the reference already has a positive atom.
On the smoothing intervals, C_eta-C=O(eta) and its derivative difference is
O(1); its second derivative is bounded by a finite M_eta=O(1/eta).

Now take

    h_tau,eta = h_G - tau*C_eta,       tau>0 sufficiently small.

On the upper central angles, choose tau*M_eta<1/4, preserving a curvature
density at least 1/4. Make tau smaller if needed so the top-face atom remains
positive. At angles 0 and pi the new endpoint face jumps are +tau, not negative.
Extend the lower support by the floor endpoints exactly as for an ordinary cap;
its bottom width is W-2*tau*A^2>0 for small tau. All other lower curvature is
zero. Therefore the full periodic support has nonnegative curvature measure
h''+h and defines a genuine convex body. Its floor support is zero and its top
support is still one, so it is a normalized right-angle cap.

This uses the standard planar support-function criterion h''+h>=0 as a measure.
It can also be checked by integrating the resulting counterclockwise supporting
curve: the density and all jumps just listed are nonnegative. The one-sided
choice of the smoothing intervals matters; symmetric smoothing across an
endpoint normal gap could introduce negative curvature where the reference
has no positive density available to absorb it.

## 4. Residual convergence and the lower bound

The changed supports and derivatives are confined to intervals of length eta.
All residual coefficients there are bounded, since phi and T are a positive
distance from their singular integration endpoints. Values at 0, phi, pi/2,
T, and pi are preserved. The shifted term in r2 changes only on another interval
of length eta and by O(eta). Therefore

    r(C_eta) -> H_0 in the four-arc L2 direct sum,
    E(C_eta) -> A^2.

For any horizontal translation s, the two extreme support values imply

    ||C_eta-s*cos||_infinity >= |C_eta(0)+C_eta(pi)|/2=A^2.

For the actual cap h_G-tau*C_eta, translation-invariant Hausdorff error is at
least tau*A^2 and its cap residual energy is tau^2*E(C_eta). The ratio is at
least A^2/sqrt(E(C_eta)), which tends to A. Combined with the upper theorem
in note 11, this proves that sec(phi) is the exact optimal coefficient for
cap-distance versus cap-residual-energy, even among actual normalized caps
arbitrarily close to Gerver and after optimizing horizontal translation.

This is a supremum/limiting sharpness statement. The infeasible raw ray does
not itself supply an attained extremum in the feasible cap class.

## 5. Numerical cross-check

The committed Hermite experiment uses eta=0.01, 0.003, 0.001, 0.0003, 0.0001.
It integrates the actual modified residuals, not a guessed quadratic form.
The endpoint lower ratios increase from about 1.000766899 to 1.000767914,
approaching sec(phi)=1.00076792405693346. A coefficient bound for the cubic
second derivatives gives an explicit positive perturbation amplitude that
preserves the analytic curvature margins for each chosen eta.

These computations check formulas and convergence behavior; they do not certify
Lean, area, a feasible auxiliary-body optimum, or a globally sharp sofa constant.
The proof of residual convergence is the support/derivative estimate above,
not extrapolation of the five samples.

## 6. The Q-deficit question remains different

For a feasible triple,

    M-Q = dual slack + E_cap + E_B + E_D.

Our cap construction does not show that the last three other contributions
are negligible compared with E_cap. In particular, a nonzero first variation
would produce a deficit of order tau, while cap energy is only order tau^2.
Then distance/sqrt(M-Q) tends to zero, not sec(phi).

The correct next feasible-Q experiment is therefore on critical directions:
linearized feasible wall constraints AND zero first-variation slack, with the
auxiliary energies optimized rather than discarded. The raw cap witness and
its smoothing do not by themselves answer that optimization problem.
