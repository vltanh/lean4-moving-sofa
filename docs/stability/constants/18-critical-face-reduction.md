# The critical face forces auxiliary energy: an exact continuum reduction

Analytic argument; no Lean, CI, or formal verification. Let p=phi, v=pi/2,
b=v-p, T=pi-p, c=v-theta, d=v+theta. Work with a support difference f on
[0,pi], pinned by f(v)=f(pi)=0. Horizontal translation does not affect any of
the energies. Let B(t),D(t) denote the differences of the auxiliary support
functions at angles pi+t.

## 1. The first variation is a positive weighted wall-slack integral

The actual deficit identity gives

    M-Q = L + E_cap + E_B + E_D,
    L = integral_[c,v] (-(f+B)) d beta
        + integral_[v,d] (-(f+D)) d delta.

The wall inequalities imply f+B<=0 and f+D<=0 on their constraint intervals.
The reference beta and delta curvature measures have strictly positive density
on the interiors of these arcs. This follows from Gerver/Structure.gv_tangents:
the active B and D contact curves have nonzero speed on each phase. Their
supports are the closures of the stated intervals; endpoints do not alter the
conclusion because support differences are continuous.

Consequently L=0 if and only if

    B=-f on [c,v],    D=-f on [v,d].                        (1)

This is an exact statement for a feasible point on the exposed zero-slack face,
not merely a scalar condition imposed on a guessed Hessian. It also describes
the zero-first-variation part of the tangent cone for differentiable feasible
rays. Full feasibility still includes convexity and all other inequalities.

## 2. Eliminate the unpenalized auxiliary portions

The endpoint constraints give B(p)=-f(p), B(v)=D(v)=0, D(T)=-f(T).
The auxiliary residuals are

    rB=-tan(t)*B-B',              p<t<v,
    rD=(D(T)-D*cos(T-t))/sin(T-t)-D',   v<t<T.

On [c,v], (1) therefore forces rB=tan(t)*f+f'. On [v,d] it forces

    rD=(-f(T)+f*cos(T-t))/sin(T-t)+f'.

On the remaining B interval [p,c], minimizing half the square integral with
its two fixed endpoint values gives exactly

    [f(p)/cos(p)-f(c)/cos(c)]^2 / [2*(tan(c)-tan(p))].       (2)

This is weighted Cauchy--Schwarz applied to (B/cos)'=-rB/cos. Equality is
attained in the relaxed function space by rB proportional to sec(t).

On [d,T] the remaining D energy has relaxed minimum zero: the homogeneous
solution D(t)=-f(T)*cos(T-t)+q*sin(T-t) can meet the value D(d)=-f(d), with
no prescribed derivative at T. Thus the exact infimum after dropping the other
convexity/wall constraints is

    E_rel(f)=E_cap(f) + (2)
      + (1/2)*integral_c^v (tan(t)*f+f')^2
      + (1/2)*integral_v^d [(-f(T)+f*cos(T-t))/sin(T-t)+f']^2.    (3)

Every continuously feasible zero-slack triple satisfies M-Q>=E_rel(f).
Conversely, arbitrary f and the minimizing auxiliaries in this relaxed problem
need NOT produce a feasible triple. Hence its operator norm is an upper-bound
problem for the feasible critical face, not an attained feasible sharp constant.

## 3. Two explicit rank-one penalties already capture most of the gain

Set DB=tan(c)-tan(p), DD=cot(T-d)-tan(p), both positive, and

    JB=f(p)/cos(p)-f(c)/cos(c),
    JD=f(d)/sin(T-d)-DD*f(T).

The second formula follows by integrating the D integrating factor from v to d.
For every feasible zero-slack triple,

    M-Q >= E_cap + JB^2/(2*DB) + JD^2/(2*DD).               (4)

This weaker estimate is convenient because the cap reconstruction is already
known by its Green kernels H_t. Both JB and JD are linear functionals of the
four cap residuals. Their penalty is a rank-two positive update of the cap
Hilbert-space energy. A 2-by-2 inverse, not a discretized nonlinear optimizer,
therefore gives the exact evaluation norm of the relaxation (4).

## 4. Initial Galerkin diagnostics

Piecewise trigonometric support interpolation with 32,64,128,256 angular
subdivisions was tested, with all arc/cut endpoints included and Gauss
quadrature split at shifted support knots. The cap-only midpoint norm approaches
sec(phi), as an independent calibration. The relaxed full-auxiliary norm is
about 0.968; the rank-two relaxation is about 0.971.

These are sampled finite-dimensional diagnostics only. Galerkin spaces provide
lower approximations to the unrestricted function-space norm, not certified
upper bounds. They do not establish sharpness for feasible critical triples.
The next step is an interval certificate for the rank-two continuum norm and
an estimate for nonzero dual slack. A numerical global sofa entry threshold is
still a separate problem.
