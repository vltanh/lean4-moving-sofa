# Centering the cap halves the coefficient: sec(phi), not 2 sec(phi)

This is an analytic calculation, not a Lean formalization. It uses the actual
four-arc reconstruction already present in SharpReconstruction/SharpKernelNorms.
It does not modify the older pinned theorem or assert that its constant was wrong.

## 1. Choose a different horizontal translation

Write Delta(t)=h_K(t)-h_G(t), v=pi/2, b=v-phi, T=pi-phi, and A=sec(phi).
The old gauge is f(t)=Delta(t)+Delta(pi)*cos(t), so f(pi)=f(v)=0.
Let r=(r1,r2,r3,r4) be its four residuals on [0,phi], [phi,b], [b,v], [v,pi],
and E=(1/2)*sum integral rj^2. Horizontal translations do not change r or E.

Replace the left-support pin by horizontal midpoint alignment:

    g(t)=f(t)-(f(0)/2)*cos(t)
        =Delta(t)-s*cos(t),   s=(Delta(0)-Delta(pi))/2.

Thus g(0)=g(pi)=f(0)/2. This aligns the midpoints of the horizontal projections
of the two caps; it does not force either left endpoint to match separately.

## 2. Evaluation kernels and covariance

Use the Hilbert direct sum of the four L2 arc spaces, with the ordinary sum of
square norms (equal to 2E). Write f(t)=<H_t,r>. The earlier calculation gives

    ||H_0||^2=2A^2.

Direct integration of the same trigonometric kernels gives C(t)=<H_t,H_0>:

    [0,phi]:       2A^2*cos(t)-sin(t)
    [phi,b]:       A+A^2*cos(t)-sin(t)
    [b,v]:         (A^2+A*sin(phi))*cos(t)
    [v,v+phi]:     A*(A-sin(phi))*cos(t)
    [v+phi,T]:     A+A^2*cos(t)-sin(t)
    [T,pi]:        -sin(t).

Endpoint formulas agree. One convenient check on the fourth-arc integration is

    J(t)=integral_v^t H_0,4(u)/sin(u) du
        = A*(A-sin(phi))*(-cot(t)),                  v<=t<=v+phi,
        = 1-A^2*cot(t)-A*csc(t),                    v+phi<=t<=T,
        = 1,                                        T<=t<=pi.

Then C(t)=-sin(t)*J(t) on the fourth arc. On the middle arc,
C'(t)=C(t+v)-A, with C(phi)=2A-sin(phi), supplies the displayed covariance
without an additional double integral. On the first and third arcs the already
established integrating-factor formulas give the other entries.

The centered evaluation kernel is Hbar_t=H_t-(cos(t)/2)*H_0. Its squared norm is

    D(t)=||H_t||^2-cos(t)*C(t)+(A^2/2)*cos(t)^2.

Substitution yields

    [0,phi]:       (A^2/2)*cos(t)^2
    [phi,b]:       A*cos(t)-(A^2/2)*cos(t)^2
    [b,v]:         sin(t)*cos(t)+B*cos(t)^2
    [v,v+phi]:     -sin(t)*cos(t)+B*cos(t)^2
    [v+phi,T]:     -A*cos(t)-(A^2/2)*cos(t)^2
    [T,pi]:        (A^2/2)*cos(t)^2,

where B=A*sin(phi)-A^2/2=-(tan(phi)-1)^2/2<=0.

On the first and last intervals D<=A^2/2. On the second and fifth it has the
form z-z^2/2=1/2-(z-1)^2/2<=1/2. On the two short intervals around v, B<=0 and
|sin(t)*cos(t)|<=1/2 give the same bound. Since A>=1, everywhere

    0<=D(t)<=A^2/2.

Consequently

    |g(t)|<=sqrt(D(t))*sqrt(2E)<=A*sqrt(E).

This holds for every 0<phi<pi/4, not only Gerver's numerical box.

## 3. Cap and Q consequences

Using the previous cap residual-to-deficit theorem E<=M-Q(xi),

    d_H(K,G_cap+(s,0)) <= sec(phi)*sqrt(M-Q(xi)).

Here the distance is Euclidean Hausdorff distance between convex caps. The
upper-half support estimate extends to the lower half by the cap/floor support
identities, exactly as in the earlier pinned argument. On Ki, substitute the
larger deficit M-A(K). In the source box,

    sec(phi)<=1250/1249<1001/1000=1.001.

Unlike changing 30.5 to another global-sofa coefficient, this IS an improvement
at the same cap level, with a different allowed translation. The old coefficient
2 sec(phi) is retained when the left-support pin is mandatory.

## 4. Sharp even after optimizing translations in the abstract residual space

Take the residual r=H_0. Then E=A^2 and f(0)=2A^2, f(pi)=0. For every real s,

    max(|f(0)-s|,|f(pi)+s|)>=|f(0)+f(pi)|/2=A^2.

The centered estimate achieves this lower bound. Thus the norm of the abstract
reconstruction map into the quotient by horizontal translations is EXACTLY
sec(phi). No nonlinear choice of translation can improve that abstract constant.
This does not prove sharpness for the Q-deficit over feasible triples: the
auxiliary energies and first-variation slack must also be considered there.

## 5. Checks and caveats

An independent 50-digit quadrature of Hbar_t^2 over all four residual intervals
agreed with the six D(t) formulas at 36 test points for three cut angles; the
largest absolute discrepancy was about 2.7e-51. This is a diagnostic, not an
interval certificate. The formulas above have elementary integral/algebraic
proofs and do not rely on those sample points.

The first test implementation tried to select the middle formula at phi+1e-60
while using 50-digit arithmetic. Rounding returned phi and caused recursion.
The repaired implementation writes the endpoint kernel explicitly. That failure
was a test implementation error, not evidence about the theorem.

The next global-sofa statement must specify the new midpoint normalization.
It is incorrect to insert 1.001 into a theorem that still pins the left support
without accounting for the additional translation.
