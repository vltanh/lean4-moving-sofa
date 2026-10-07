# A numerical cutoff for the 2.3 / 50 / 3.1 theorem

## Statement and verification status

Let P be Gerver's parameter solution in the source box, let G be its original
sofa, and write M=|G|. For an original moving sofa S, put epsilon=M-|S| and

    m(S)=(h_S(0)-h_S(pi))/2,
    S_c=S+(m(G)-m(S), 1-h_S(pi/2)).

The analytic arguments in notes26--31, combined with the centered coercivity
and exact sector budget of notes11--14, give the following explicit statement:

    0<=epsilon<=10^(-600)
      ==> d_H(S_c,G) <= (23/10)*sqrt(epsilon),
          |S_c symmetric_difference G| <= 50*sqrt(epsilon),
          0<=pi/2-omega <= (31/10)*epsilon                    (A)

for every admissible reduced angle omega of S. The distance is Euclidean
Hausdorff distance of the actual compact sets. Midpoint/top normalization,
not left-support pinning, is part of the statement. A translation suffices,
so the distance minimized over rigid alignments has the same upper bound.

This is a WRITTEN ANALYTIC theorem, not a Lean-verified result. The numerical
reference inequalities and scalar cutoff implications have an executed exact
arithmetic check. That computation does not verify the penalized-polygon
arguments in notes26--27, the reference contact classification, or the
arbitrary-set geometric arguments. Those analytic proofs still require
independent review. The very small cutoff is not asserted sharp or useful as
a practical optimizer tolerance.

## 1. Quantitative entry, before any local certificate is invoked

The global entry modulus of note27 gives

    d_H(S_c,G) <=3000000*epsilon^(1/12),  epsilon<=10^(-144),
    alpha=pi/2-omega <500*epsilon^(1/6),  0<epsilon<=10^(-30).

At epsilon<=10^(-600), monotonicity of positive powers gives

    d_H(S_c,G)<=3*10^(-44)<10^(-40),
    alpha<5*10^(-98)<10^(-20).                               (1)

Let K be the full right-angle cap completion of S_c, obtained by taking its
convex hull together with its vertical projections to the floor. Its upper
support values equal those of S_c. The same identity holds for Gerver and its
cap. Hence (1) gives

    sup_[0,pi]|h_K-h_Gcap|<10^(-40).                           (2)

This implication uses ordinary support continuity under Hausdorff distance;
it does not assume the local Q area certificate or the sharp square-root
bound being proved. K and S_c also have the same horizontal extremes, so K
is already midpoint-aligned with the reference cap.

## 2. Numerical hypotheses of the local geometric certificates

Here is the complete radius table supplied by notes29--31.

| Certificate | Sufficient numerical hypothesis |
| --- | --- |
| Canonical wide triple, core/cut separation, N(K) subset K, A(K)<=Q<=M | upper-support error <=10^-40 |
| Terminal floor trapezoid and omitted-wedge surplus | same support bound and alpha<=10^-20 |
| Euclidean normal-slack recovery | refined support error plus full-angle slack <=10^-10 |
| Uniform translated interior sector of aperture1.53 | radius at most10^-20 |
| Direct symmetric-difference remainder absorption | sqrt(epsilon)<=1/200 |

The top-face and niche-foot subradii are included explicitly in note29:
eta=10^-8 for the top face and eta=10^-5 for the niche windows, each with
support tolerance eta^3/2^24. The chosen10^-40 bound is smaller than both.
The terminal floor proof uses two fixed visited angles t0=1/1600000 and
pi/2-t0, not an unspecified finite cover. The normal proof uses depth10^-8,
and the sector chart proof uses an explicit curvature/angle reserve.

Apply the first two rows, already justified by (1)--(2). With

    U=K minus N(K), e=M-|U|, g=|S_c minus U|, m=|U minus S_c|,

we obtain

    0<=e<=epsilon,
    alpha<=(31/10)*(epsilon-e),
    g<=(31/10000)*(epsilon-e),
    m<=(10031/10000)*(epsilon-e).                             (3)

In particular the angle conclusion of (A) already follows. No containment
S_c subset U is assumed; the possible omitted-wedge surplus g is retained.
At alpha=0, the same formulas hold with g=0.

## 3. Refine the cap error and close the Hausdorff estimate

The local canonical Q certificate and centered cap coercivity now give

    delta=d_H(K,Gcap)<=k*sqrt(e),  k=1001/1000.

The normalized containing box bounds the full-angle slack of S_c by16alpha.
Combining with (3),

    delta+zeta <=1.001*sqrt(epsilon)+(248/5)*epsilon<10^(-10).  (4)

Thus note31's forward normal estimate applies. Its right side is at most

    (100/49)*[1.001*sqrt(epsilon)+(248/5)*epsilon]
      < (23/10)*sqrt(epsilon)

for every positive epsilon in the stated range. This uses the strict leading
coefficient inequality (100/49)*1.001<2.3; the remainder is linear.

For reverse distance, put rho=(23/10)*sqrt(epsilon) and let
r=sqrt(2)*delta be the orthogonal erosion allowance. The reference sector can
be used because

    rho+r <=(23/10+(3/2)*(1001/1000))*sqrt(epsilon)<10^(-20).   (5)

The full surviving-sector area calculation of note14 applies with beta=153/100
and lambda=10031/10000. Its exact rational certificate proves that, for EVERY
split e/epsilon in [0,1], the eroded sector inside the radius-rho disk has area
strictly larger than lambda*(epsilon-e)>=m. If a reference point were farther
thanrho from S_c, that whole sector would lie in U minus S_c, a contradiction.
This proves the reverse directed bound. Combining it with (4) gives the first
conclusion in (A).

No cap-only Q threshold, spectral approximation, or assumption of an attained
critical mode is used in this global argument.

## 4. Symmetric difference

The direct convex-layer and reference roof-band estimate yields

    |S_c triangle G|
      <= (62307/1250)*k*sqrt(epsilon)+(3+8*k^2)*epsilon.

Its leading coefficient is49.8954456. The exact inequality

    (62307/1250)*k+(3+8*k^2)/200<50

and sqrt(epsilon)<=10^-300<1/200 prove the second conclusion in (A).
The reference vertical slack threshold1/2040000 used by that roof-band estimate
is also satisfied by (4), since10^-10<1/2040000. This estimate does not multiply
the Hausdorff bound by a perimeter or a neighborhood-area constant. All set areas
are finite; |S_c triangle G|=epsilon+2|S_c minus G| accounts for arbitrary holes.

## 5. Zero deficit and what is now numerical

For epsilon=0, the existing normalized uniqueness theorem supplies S_c=G.
The published coarse-angle input puts any admissible reduced omega above
asin(84/85). If alpha=pi/2-omega>0, the four reference points
(a,0),(b0,0),(a,1),(b0,1) force width in the terminal normal omega to be at least
cos(alpha)+(b0-a)sin(alpha)>1, since0<alpha<1/4 and b0-a>1. That contradicts
the terminal unit strip. Hence alpha=0 as well. Only the four actual points
are used: the whole rectangle is in the convex hull, not in the nonconvex sofa.
The positive-deficit proof never divides by zero.

The old result had explicit leading coefficients but no common numerical
entry cutoff. Formula (A) now supplies a concrete one,10^-600. The large
exponent comes mainly from using the coarse epsilon^(1/12) entry modulus to
meet a deliberately conservative support radius10^-40. It is not evidence
that the sharp estimates fail above that deficit.

## 6. Replay and audit scope

Run, without Lean or Lake:

    python docs/stability/constants/effective_entry/replay_cutoff_radii.py \
      --expect docs/stability/constants/effective_entry/cutoff-radius-summary.json

This RECOMPUTES all inequalities with `check_cutoff_radii.py` before comparing
the invariant receipt. The compact summary stores exact reference enclosures,
the names of the41 positive margins, source hashes, and a hash of the complete
exact report. The full rational margins are regenerated rather than duplicated
in Git. Python version metadata is excluded from the invariant comparison.

The checker encloses reference formulas on complete phase intervals over the
entire parameter box, with90-bit outward dyadic arithmetic and Taylor/Machin
bounds. The cutoff10^-600 itself and all local scalar implications use exact
Fractions; it would be incorrect to round that number onto the90-bit grid.

The final run checks5440 inequalities/identities, including41 exact positive
local or cutoff margins, exact power identities, and two negative controls.
It recomputes the all-split sector coefficient inequality with rational
sine/cosine/arctangent bounds. The replay with the expected receipt passed.

Checker SHA256:
`4c2fbdf3464b95fe436786d9200cd8a45393680c8908ca9e0c79346a2002bec4`.
Full invariant report SHA256:
`5d1a503086145b5e521e81692f3dc79ba3f74eb0e81017bd0710b80a148b9061`.

The computation verifies only the inequalities it evaluates. Independent
mathematical review should particularly inspect the global penalized-entry
proof (notes26--27), exposed-face estimate (note29), fixed floor witnesses
(note30), and quantitative corner charts (note31). Formalization remains frozen;
no manuscript or kernel-verification claim is changed by this continuation.
