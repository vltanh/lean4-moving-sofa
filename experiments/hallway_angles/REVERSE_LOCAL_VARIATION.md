# Local reverse-wall variation and positive-arm curvature domination

Status: analytic geometric lemma for polygonal reverse caps plus its continuum consequence under the specified-maximizer selection scheme. It does not yet prove global arm positivity. No CI or Lean build is used.

Fix e in (0,pi/2), q=sin e, d=cos e, and a mesh angle phi with neighbors phi-delta and phi+delta. Put psi=e-phi. Use

    n=n1(phi), t=t1(phi), m=n2(phi), s=t2(phi).

Thus m=-d n+q t and s.q? More explicitly m.t=q and s.t=d.

Let C be the current canonical corner. On the current plus inner wall, the current forbidden wedge occupies the ray

    p(r)=C-r t,   r>=0,

because m.(p(r)-C)=-q r<0.

Let a^-,a^+ be the one-sided plus arms at the current normal, so the current plus facet endpoints are C+n+a^- t and C+n+a^+ t. Let b^-,b^+ be the one-sided minus arms at the current minus normal, measured along s. For a polygon support fan, a^+-a^- is the current plus facet length and b^+-b^- is the current minus facet length.

Write u=tan(delta/2).

## 1. Exact neighboring-wedge thresholds

For the next pose phi+delta, direct scalar products with its two inner lines give

    n1(phi+delta).p(r) - [h_+(phi+delta)-1]
      = sin(delta)[u-a^+-r],

and

    n2(phi+delta).p(r) - [h_-(psi-delta)-1]
      = 1-cos(delta)+b^- sin(delta)-r sin(e-delta).

Hence the next forbidden wedge contains the whole tail

    r > T_+

where

    T_+=max{0, u-a^+,
       [1-cos(delta)+b^- sin(delta)]/sin(e-delta)}.       (1)

For the preceding pose phi-delta, the corresponding identities are

    n1(phi-delta).p(r) - [h_+(phi-delta)-1]
      = sin(delta)[u+a^-+r],

    n2(phi-delta).p(r) - [h_-(psi+delta)-1]
      = 1-cos(delta)-b^+ sin(delta)-r sin(e+delta).

Thus the preceding forbidden wedge contains the interval

    B_- < r < U_-

whenever it is nonempty, where

    B_-=[1-cos(delta)-b^+ sin(delta)]/sin(e+delta),
    U_-=-u-a^-.                                         (2)

These are exact polygon identities. They use only adjacency of the sampled support normals; no smoothness, contact ansatz or candidate formula is used.

## 2. An exposed-length bound

Let tau_+(phi) be the length of the exposed niche boundary lying on the current plus inner-wall ray. Every point covered by either neighboring forbidden wedge is nonexposed. Equations (1)-(2) therefore give

    tau_+ <= min{
      T_+,
      max(0,B_-)+max(0,T_+-U_-)
    }.                                                   (3)

The second term is simply the length left in [0,T_+] after deleting the interval guaranteed to be covered by the preceding wedge. The formula remains an upper bound when that interval is empty or overshoots [0,T_+].

The reflected calculation gives the analogous estimate for tau_-.

## 3. Continuum consequence on a positive-arm region

Consider polygon caps from the persistent-penalty selection of a specified reverse maximizer, on a compact parameter interval J contained in (0,e). Suppose the limiting plus arm satisfies

    a(phi)>=eta>0 on J.

Uniform support convergence and one-sided support-point convergence imply a^+-a^-=O(delta) and a^+- -> a almost everywhere. For sufficiently fine meshes U_-<0 on J, so the first term T_+ in (3) is the useful one. Since

    u/delta -> 1/2,
    [1-cos(delta)]/delta ->0,
    sin(delta)/delta ->1,
    sin(e-delta)->q,

division by delta and passage to the curvature measure gives

    rho_+(phi) <= max{b(phi)/q,0}    a.e. on J.          (4)

In particular, if both arms are positive on J,

    rho_+ <= b/q.                                       (5)

Reflection gives

    rho_- <= a/q                                        (6)

wherever both arms are positive.

The selection argument needed for (4) is the same one-sided floating-facet logic used in PR #2: moving a sampled outer line outward changes cap area by the facet length and niche area by at most the exposed inner-wall length, while the persistent support penalty contributes total error tending to zero. A full arbitrary-bend selection note still has to spell out compactness and the two pinned normals, but no new local geometry is hidden there.

## 4. Relation to the explicit candidate

The exact reverse candidate satisfies the stronger equalities

    rho_+=b/q,   rho_-=a/q.

Thus (5)-(6) recover the correct stationarity coefficient, rather than a bend-independent surrogate. Substituting them into the arm identities of REVERSE_MAXIMIZER_ARMS.md gives the candidate Euler system.

## 5. Remaining bootstrap problem

Equations (4)-(6) are conditional on positivity of the arm whose neighboring wedge removes the O(1) ray segment. If a becomes negative, the first threshold in (1) is O(1) and the simple one-neighbor estimate no longer yields a finite density bound. Equation (3), using BOTH neighboring wedges, remains finite in the limit and gives a different piecewise curvature bound; that bound is the natural arbitrary-bend analogue of Baek's kappa function.

Deriving and bootstrapping that full piecewise bound is the next step. The present lemma is already sufficient once endpoint positivity and a no-first-zero argument are established.

## Review boundary

The threshold identities and exposed-length estimate are elementary line geometry. The continuum passage uses the same kind of polygon-selection/weak-curvature limit as PR #2/#4 and still needs to be written in full for the reverse cap class before being called a theorem about every maximizer.