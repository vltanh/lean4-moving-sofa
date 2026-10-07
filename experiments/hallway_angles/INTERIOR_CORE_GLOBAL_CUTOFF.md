# A larger explicit interval of unrestricted optimality

**Sixth-round mathematical proof draft.** This strengthens `EXPLICIT_GLOBAL_CUTOFF.md`. It remains dependent on the analytic reverse-class proof and is not independently reviewed or Lean-checked. No CI or Lean build was used.

## Theorem

For every 0<e<=1/8 radians, the unrestricted moving-sofa supremum in a sharp unit-width hallway of bend beta=pi-e is

    M(pi-e)=V(e),

with the explicit candidate S_e as the unique maximizing compact connected set up to Euclidean congruence. In particular, every bend from 173 degrees to strictly below 180 degrees is covered.

The new sufficient cutoff is pi-1/8, approximately 172.83802756 degrees. This is not the actual onset of global reverse optimality and is not a phase-transition angle. The earlier cutoff pi-1/19 is superseded, not contradicted. No claim is added for an unrestricted optimum at 150 or 170 degrees.

The function V and the explicit shape/motion are unchanged from `REVERSE_MAIN_THEOREM.md` and `REVERSE_GEOMETRIC_THEOREM.md`.

## 1. Improved but explicit path constants

Assume an unrestricted competitor has area A>=V(e). Let n in [0,pi/2] be its unoriented entry/exit strip-normal mismatch. The strip-area bound, eV>27/20, and sin(3e/4)>20e/27 give

    n<=3e/4<=3/32.

Scaling by lambda=cos(n/2) gives an aligned sofa R. Its area is at least V/2>3, excluding the forward class whose midpoint bound is below 3. Thus R is reverse and has normalized deficit

    0<=d=e[V-area(R)]<=17n^2/50<=153/51200.

The previous width majorant first gives 1-w<=10d<3/100. Hence w>97/100. On this smaller actual-width interval the scalar derivative bound e F_e'(w)>1/4 improves the estimate to

    1-w<=4d.

The quadratic variation splits orthogonally into the endpoint Jacobi mode and a zero-endpoint mode as before. A sharper fixed Poincare matrix, valid throughout 0<e<=1/8, is

    [[39/100, -8/25],[-8/25,197/100]].

Indeed pi>25/8, 1-cos(e)>=e^2/2-e^4/24, and cos(e)>=1-e^2/2 imply both diagonal lower bounds. The determinant is 6659/10000>0. For the physical-coordinate trace rows (1,1/128) and (1/2,1), the squared zero-endpoint trace coefficients are

    80896975/54550528,  12025/13318.

The certified endpoint energy exceeds (59/250)U^2 and its coordinate magnitudes are at most |U| and (16/25)|U|. Cauchy-Schwarz in the two energies, together with the width derivative bounds 7/20 and 1/2, yields

    eta_x=(12/5)sqrt(d)+(7/5)d,
    eta_y=(41/25)sqrt(d)+2d.

These bound the canonical-corner differences from the full-width candidate after horizontal rescaling. They do not require symmetry or convexity of R. All trace and constant comparisons are exact rational checks in `path_constants()`.

The interval checker verifies the needed scalar bounds over the whole closed interval [0,1/8], including its removable endpoint. In particular it verifies the two endpoint width slopes for w in [1/2,1], then the derivative at w=97/100 and w=1. Affinity of F_e' fills the latter width interval.

## 2. Uniform interior rectangles

Use `CURVED_CONTACT_CORES.md`, rather than only the flat-contact rectangle. The checker constructs finitely many rational rectangles

    Q_j=[L_j,R_j] x [-H_j/2,H_j/2]

inside EVERY normalized candidate T_e=A_e S_e for 0<e<=1/8.

The candidate boundary points come from its explicit support and corner formulas. Their coordinates are enclosed over each whole e-interval by exact integer arithmetic. For an upper-arc point, a lower bound on X and on its positive Y gives a point in T_e, by symmetry and convexity with the segment X=0. For an inner-arc point, an upper bound X<=0 and a lower bound Y>=0 work the same way. Chords of these known interior points are also interior. Thus these are genuine common inscribed rectangles, not numerical polygon guesses.

Near the upper flat segment, cancellation is avoided using

    e^2 rho_e(phi)<=8/5,
    Y_e(u)>=1/2-(4/5)u^2,  phi=e*u.

The first bound follows from a scalar amplitude estimate and is checked over the whole e interval; the second follows by integrating the support-contact derivative. It is not inferred from sampled Y values.

The curved-core lemma places the shrunken rectangle of dimensions

    W_j-2eta_x, H_j-2eta_y,  W_j=R_j-L_j,

inside the majorant region Omega. The competitor misses area at most d from each such rectangle. Full Hausdorff stability is not used.

## 3. Exact covering of every mismatch direction

Suppose n>0 and put a=sin(n)/e, b=cos(n). Then

    0<a<=3/4, b>=99/100, n<=(501/500)e*a.

The last inequality follows from sin(n)/n>=1-n^2/6 and n<=3/32. Let z=(501/500)/8 and t=sqrt(a). It suffices to check t in [0,7/8], a slightly larger interval than required.

Since sqrt(17/50)<7/12, define

    X(a)=(7/5)z*a+(119/250)z^2*a^2,
    Y(a)=(287/300)z*a+(17/25)z^2*a^2.

These upper-bound eta_x and eta_y simultaneously at all e<=1/8. The missing-area rectangle lemma yields a contradiction to exit-strip width at most lambda if a rectangle has positive shrunken dimensions, satisfies both triangular-cap conditions, and has

    m_j(t)=W_j-(1-H_j)/t^2-2X(t^2)
             -(287/150)z-(34/25)z^2*t^2
             -(z^2*t^2*H_j)/2-(7/6)z*t > 0.          (1)

For a full-height rectangle the apparently singular term is identically zero. To derive (1), use b>=1-n^2/2, b<=1, lambda<=1, and 2sqrt(a*b*d)<=(7/6)n*sqrt(a), then divide the width excess by a>0.

For each exact rational t-cell [t0,t1], the checker uses t0 in the negative inverse-square term and t1 in all negative polynomial terms. It selects a rectangle for which this lower bound is positive. It separately checks positive dimensions and

    (W_j-2X)^2/2 > (17/50)z^2*a,
    (99/200)(H_j-2Y)^2 > (17/50)z^2*a^3.

These imply the horizontal and vertical triangular-cap conditions for every actual a in that cell. They are not omitted when the mismatch is tiny. The first cell uses a full-height rectangle and therefore covers all sufficiently small nonzero mismatches without a division by zero.

A run with 128 parameter cells, 128 boundary parameters per arc, and 1024 direction cells proves every inequality. It produces 255 common candidate rectangles and uses 65 of them; the minimum normalized directional margin exceeds 0.006. The stored exact rational margins, not this decimal, define the certificate.

## 4. Equality and scope

Every n>0 is impossible. Thus lambda=1 and the original competitor already belongs to the reverse class. Its area cannot exceed V, and equality implies S_e up to congruence by the reverse-class uniqueness theorem. The explicit S_e supplies attainment.

This argument does not require the existence theorem for unrestricted maximizers, the fourth-round set-Hausdorff stability theorem, or a theorem identifying the middle-angle phase transition.

## Reproduction and review

    python interior_core_certificate.py --parameter-cells 128 --points 128 \
      --direction-cells 1024 --output interior-core-proof.json

The certificate uses Python exact integers/rationals, bounded trigonometric series, and integer square roots. Its boundary parameters are construction witnesses; all corresponding e intervals and all mismatch directions are verified. Candidate feasibility and the area majorant remain analytic proof dependencies, not conclusions of the checker.

Independent review must still assess the cap identity, canonical crossing/excursions, width correction, strict quadratic optimization, and the alignment lemma. An exact arithmetic certificate alone cannot validate those geometric arguments or establish publication priority.
