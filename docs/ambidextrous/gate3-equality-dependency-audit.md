# Gate 3: equality dependencies and recovery of the original body

**October 10, 2026. Written equality audit.** This note separates the
additional rigidity arguments from the sharp-value statements proved by
[Gate 1](gate1-sharp-full-turn-closure.md) and
[Gate 2](gate2-sharp-partial-turn-closure.md). It proves the exact equality
deficit in the actual original-body domain, records the quantifier needed
for canonical maximizer regularity, and supplies the inverse and
compact-set recovery lemmas. It does not infer uniqueness from a value
bound or from selection of one convenient maximizer.

The full-turn classification in
[CE](gate3-full-turn-cap-equality.md) and the proper-angle and body
rigidity in [TB](gate3-terminal-and-body-rigidity.md) have now passed
this independent equality audit. The controlling plan asks Gate 3 to
analyze the hull, terminal angles and
actual body at equality, to prove uniqueness separately if true, and to
expose the complete derivation in a manuscript for independent review.
External referee acceptance and Lean verification are separate matters.
Labels ED below are local to this note.

## 1. An exact deficit for the original two-cap partition

Let \(S\) be an actual compact connected admissible body of area greater
than \(\sqrt2\). Normalize its common incoming strip to
\(0\le y\le1\). The [Gate 0 audit](original-motion-global-bridge-gate0-audit.md)
supplies the actual hull \(K=\operatorname{conv}S\), its projection
\(I=[l,r]\), and two independent canonical terminal magnitudes
\(\alpha,\gamma\in[\pi/4,\pi/2]\). It retains the outgoing whole-body
strip for each motion.

Let \(U\) have the actual upper hull roof \(A_U=A_K\), and let \(V\)
have roof \(A_V=1-B_K\), where \(B_K\) is the actual lower hull roof.
These are the original downward caps; no cap replacement has yet been
made. For every upward normal, the downward upper cap has the same
support as \(K\), because maximizing that normal over each vertical
fiber selects its upper endpoint. The reflected statement identifies
the supports of \(V\) with those of the reflected hull.

Put

\[
J=[l+(r-l)/4,r-(r-l)/4],\qquad
d_U=1-A_U,\quad d_V=1-A_V,
\]
\[
N_U=N_{U,\alpha},\qquad N_V=N_{V,\gamma},
\]

where each \(N\) is the entire partial barrier from G2C.3, including
the whole terminal first wall. The exact signed fiber is

\[
\ell=1-\max(d_V,N_U)-\max(d_U,N_V).
\tag{ED.1}
\]

Define the partition defect

\[
\begin{aligned}
D_{\rm part}={}&
\int_J\bigl[(d_V-N_U)_++(d_U-N_V)_+\bigr]\,dx\\
&+\int_{I\setminus J}
\bigl[(N_U-d_V)_++(N_V-d_U)_+\bigr]\,dx.
\end{aligned}
\tag{ED.2}
\]

Subtract ED.1 from \(1-N_U-N_V\) on \(J\), and from
\(A_U+A_V-1\) on its complement. The identity
\(\max(a,b)-a=(b-a)_+\), together with
\(|J|=|I\setminus J|\), gives the exact formula

\[
\boxed{
\mathcal P_\alpha(U)+\mathcal P_\gamma(V)
-\int_I\ell\,dx=D_{\rm part}\ge0.}
\tag{ED.3}
\]

This is the signed version of
[SPB.4](spatial-half-partition-bound.md), with both terminal strips
included. It holds for arbitrary auxiliary convex hulls as well, even
when some signed fibers are negative.

For the actual connected body, Gate 0 gives a canonical envelope
\(E\supseteq S\). Connectedness implies
\(\operatorname{proj}_x S=I\), so every \(E\)-fiber is nonempty and
\(\ell\ge0\) everywhere. Thus \(|E|=\int_I\ell\), and

\[
D_{\rm fill}:=|E\setminus S|=\int_I\ell\,dx-|S|\ge0.
\tag{ED.4}
\]

**Theorem ED1 (exact original-body equality deficit).** With
\(M\) as in G2C.1,

\[
\boxed{
M-|S|
=\left(\frac M2-\mathcal P_\alpha(U)\right)
 +\left(\frac M2-\mathcal P_\gamma(V)\right)
 +D_{\rm part}+D_{\rm fill}.}
\tag{ED.5}
\]

Every term on the right is nonnegative by G2C1, ED.2 and ED.4.
Consequently \(|S|=M\) forces both **original** caps to be scalar
equality caps, both partition integrals to vanish, and \(|E\setminus S|=0\).
The pointwise partition conditions are, almost everywhere,

\[
\begin{array}{ll}
d_V\le N_U,\ d_U\le N_V,&x\in J,\\
N_U\le d_V,\ N_V\le d_U,&x\in I\setminus J.
\end{array}
\tag{ED.6}
\]

Their continuous representatives satisfy the same inequalities on the
interiors of the respective intervals. No assertion that \(S=E\) has
yet been made. For an auxiliary hull, ED.3 still holds, but ED.4 must
not be asserted without its actual-body hypotheses.

## 2. The finite selections can target any canonical equality cap

The headline statement of
[RG](gate1-spatial-maximizer-wing-curvature-regularity.md) is existential.
For rigidity, merely exhibiting one regular maximizer would be
insufficient. Its selection proof gives the following stronger
quantifier, which must be stated when used.

**Theorem ED2 (regularity of every prescribed canonical maximizer).**
Let \(U_0\) be any height-one global maximizer of the full-turn spatial
score whose entire middle roof is affine. The regularity and nonlinear
wing-curvature bounds in RG.15--RG.17 hold for this same \(U_0\).
The endpoint and exposure conclusions of
[EP](gate1-global-endpoint-complementarity.md) and
[LH](gate1-global-positive-pressure-and-wing-identity.md) can likewise
be obtained from selections converging to \(U_0\).

**Proof.** Translate \(U_0\) strictly inside the artificial box of RG.
Let \(P_n\) be the sampled spatial score and
\(e_n=\sup(P_n-P)\to0\), uniformly on that compact cap domain.
Use exactly RG's support-distance penalty centered at \(U_0\), and
let \(\eta_n=\sqrt{e_n}+1/n\). The grid circumscription of \(U_0\)
has zero penalty and sampled score at least \(P(U_0)=P_{\max}\).
For a penalized optimizer \(U_n\), therefore,

\[
P_{\max}\le P_n(U_n)-\eta_nD_n(U_n,U_0)^2
\le P_{\max}+e_n-\eta_nD_n(U_n,U_0)^2.
\]

Hence

\[
D_n(U_n,U_0)^2\le e_n/\eta_n\longrightarrow0.
\tag{ED.7}
\]

Compactness and the positive Riemann-sum support weights identify every
Hausdorff subsequential limit with \(U_0\). The whole sequence converges
to that prescribed cap. RG's neighboring-wall estimates, vanishing
middle-facet error away from its single normal, and measure domination
now apply to this sequence. They prove the stated regularity of
\(U_0\), not of a different replacement maximizer. EP uses the same
penalization and explicitly allows any prescribed global maximizer.
Its trimming and erosion arguments, followed by LH's strict
positive-pressure exclusion, concern this same target. \(\square\)

No such statement has been inferred for an arbitrary uncanonicalized
maximizer. Its middle roof must first be handled with an inverse
argument, as in Section 4.

## 3. What strict functional calibration does and does not require

The horizontal sharp branch gives

\[
P(U_0)\le F(f,g)-W/2\le M/2
\tag{ED.8}
\]

by [CH.25--CH.26](gate1-spatial-maximizer-curvature-and-horizontal-value.md).
This comparison is used only after its geometric hypotheses, including
both unit wing bounds and niche confinement, have been proved for the
prescribed canonical maximizer.

At equality in ED.8, the strict functional theorem
[AF3](adaptive-functional-global-calibration.md) identifies the upper
support pair. To see that its full-profile quantifier applies, define
the upper-half profile by \(h(t)=f(t)\), \(h(t+\pi/2)=g(t)\), and
extend by

\[
h(-t)=h(t)-\sin t\qquad(0\le t\le\pi).
\tag{ED.9}
\]

The endpoint conditions make this a periodic \(H^1\) profile with
\(h(\pi/2)=1\), \(h(3\pi/2)=0\), and horizontal width \(W>2\).
Its reflected upper pair is precisely \((f,g)\), so

\[
\widetilde{\mathcal Q}(h)=2F(f,g)-W=M.
\tag{ED.10}
\]

AF3's equality kernel is the reference profile plus horizontal
translation. It is a theorem on **all real \(H^1\) profiles**, so the
extension need not independently be proved convex or smooth. Strict
fixed-width concavity is already coercive on \(H^1_0\), and the
width-stationary classification is performed in that function space.
There is no inference that a geometric optimizer is smooth because an
unrelated auxiliary optimizer happens to be smooth.

The strict wide-horizontal exclusions and tilted-maximizer exclusions
in [G1C](gate1-sharp-full-turn-closure.md) use only global maximality,
the reference lower value and the necessary laws of ED2. Thus their
contradictions apply at value \(M/2\) as well as in the earlier
hypothetical-above-reference proof. They force a canonical equality
cap into the horizontal branch ED.8. This exposes the precise route to
canonical full-turn rigidity rather than assuming rigidity from G1C1.

## 4. Reversing the middle chord and height extrusion

**Lemma ED3 (exact inverse at the reference).** Suppose \(U\) is an
arbitrary cap of full-turn scalar value \(M/2\). Intersect it with
the halfplane under its middle chord to obtain \(V\), then extrude
vertically by \(\varepsilon=1-\max A_V\) to obtain \(U_c\).
If canonical equality classification gives
\(U_c=U_*\), after horizontal translation, then
\(\varepsilon=0\) and \(U=V=U_*\).

**Proof.** Both maps are score-nondecreasing by MID and SD, and the
universal bound is \(M/2\). Hence
\(P(U)=P(V)=P(U_c)=M/2\). Vertical extrusion has the exact roof
identity

\[
A_V=A_*-\varepsilon.
\]

For every upward unit normal \(n\), maximizing over the translated
roof gives
\(h_V(n)=h_*(n)-\varepsilon n_y\). Both inner walls consequently
decrease by \(\varepsilon\), and

\[
n_V=(n_*-\varepsilon)_+.
\]

The two horizontal integration regions have the same length. Therefore

\[
\boxed{P(U_*)-P(V)
=\int_J(\varepsilon-n_*(x))_+\,dx.}
\tag{ED.11}
\]

The reference niche is continuous and vanishes at both endpoints of
its middle window. If \(\varepsilon>0\), a one-sided interval inside
\(J\) has \(n_*<\varepsilon\), so ED.11 is strictly positive.
This contradicts equality of the scores. Thus \(\varepsilon=0\) and
\(V=U_*\). Chord clipping leaves \(U\) unchanged outside \(J\).
Inside \(J\), it gives \(A_U\ge A_V=1\), while the original strip
gives \(A_U\le1\). Hence the original cap equals the reference
everywhere. \(\square\)

This also recovers exact height one; no separate strict-height theorem
for all caps is needed. The argument uses the vanishing reference niche
at the window endpoints, not injectivity of canonicalization in
general.

For an exact check of that distinction, let
\(I=[-1/4,1/4]\) and \(A(x)=1/2-|x|\). Its middle chord clips the
roof to \(\min(1/2-|x|,3/8)\), a different cap. Both full positive
niches vanish: for either cap, every corner height is at most

\[
\frac12+\frac12\sin t\cos t-\sin t-\cos t\le-\frac14.
\]

The exterior roofs coincide and their common score is \(5/64\).
Thus equal score through chord clipping alone is not a general
geometric equality statement. ED.11 is the additional sharp-reference
argument that makes its inverse valid here.

## 5. A largest-angle choice is not an equality theorem

Gate 2's value proof may select a largest terminal angle among global
maximizers. That is enough to rule out an above-reference global value.
It does not, on its own, rule out another global maximizer at a smaller
angle after the sharp value has been proved.

The logical distinction is already visible for the continuous function
\(F(x,a)=-x^2(1-a)^2\) on \([0,1]^2\): all largest-angle maximizers
have \(a=1\), but \((0,a)\) is a maximizer for every smaller angle.
This is a quantifier counterexample, not a proposed sofa.

The additional geometric lemma is now proved as
[TB1](gate3-terminal-and-body-rigidity.md), using
[TP, Section 3](gate2-terminal-facet-and-prefix-reduction.md).
If a canonical equality cap has terminal facet length \(m>w_H\),
that argument, before appealing to the largest-angle choice, produces
a strictly larger angle with the **same cap and unchanged barrier**.
The old positive charged terminal facet then lies at an interior used
normal. [PS1](gate2-partial-endpoint-source-and-green.md) applies to any
prescribed canonical joint maximizer without a largest-angle
hypothesis and forbids such an interior charged atom. This fixed-cap
contradiction extends \(m\le w_H\) to every equality pair. The remaining
MP/RX/AC contradiction therefore applies with that stronger quantifier.

The negative-completion alternative needs its own equality check:
completion gives full-turn scalar equality for the same canonical cap;
full-turn rigidity identifies it with \(U_*\). The reference has
positive charged circular curvature on first normals arbitrarily close
to \(\pi/2\), whereas PD5 forbids charged curvature on the unvisited
open arc of a proper partial maximizer. These statements are
incompatible. Merely saying that completion does not lose value would
not be enough.

The proved consequence [TB2](gate3-terminal-and-body-rigidity.md) is strictness
\(P_\alpha(U)<M/2\) for every \(\alpha<\pi/2\), while the full-turn
equality caps are horizontal translates of \(U_*\) by
[CE3](gate3-full-turn-cap-equality.md). Both the fixed-cap extension
and equality classification have received independent mathematical
checks in this audit; they are additional results beyond the original
value-only Gate 2 proof.

## 6. Original hull alignment and literal compact-set recovery

Apply the now-proved full-turn scalar rigidity CE3 and strict
proper-angle scalar inequality TB2. ED1 then gives
\(\alpha=\gamma=\pi/2\), and both original caps are translates of
\(U_*\). They have the same actual interval \(I\). Since the
reference cap has fixed positive width, equality of these intervals
forces the two horizontal translation parameters to coincide. Thus

\[
A_K=A_*,\qquad B_K=1-A_*,\qquad K=K_*.
\tag{ED.12}
\]

This is equality of the **original hull**, not of a hull produced by
area-preserving compression or independent cap replacement. Gate 0's
support tightening changes the hallway witnesses while retaining the
body and its hull. Its auxiliary-envelope connectedification is not
used for this equality implication.

Now \(S\subseteq E_{\pi/2,\pi/2}(K_*)=\Sigma_*\), and ED1 gives
\(|\Sigma_*\setminus S|=0\). The reference envelope is regular closed.
Here is the property needed for that assertion. Its roofs are
continuous, \(A_*>1/2\) on the interior of its projection by concavity
between the endpoint values \(1/2\) and the middle plateau value one,
its niche is zero outside the plateau, and its niche has a strict
height ceiling below \(1/2\) by
[the reference separation calculation](04-romik-candidate.md).
Consequently its vertical fiber has strictly positive length at every
interior abscissa. Points of every boundary fiber are limits of points
in the interior of the envelope; the two extreme fibers are limits
from interior abscissae. Hence
\(\Sigma_* = \overline{\operatorname{int}\Sigma_*}\).

**Lemma ED4 (literal body recovery).** If a compact regular-closed set
\(F\) contains a closed set \(S\) and \(|F\setminus S|=0\), then
\(S=F\).

**Proof.** A point of \(F\setminus S\) has a neighborhood disjoint
from \(S\), since \(S\) is closed. Regular closedness places an
interior point of \(F\) in that neighborhood, and then a positive-area
ball in \(F\setminus S\), a contradiction. \(\square\)

This is [Lemma 4](01-two-motion-envelopes.md), with its larger-set
hypothesis explicitly verified at the identified reference envelope.
It rules out zero-area deletions. Zero-area appendages are excluded
earlier, by the recovered original hull and canonical containment.

Even connectedness, equal area and the same hull do not replace that
last argument. Let \(D\) be the closed disk of radius \(1/4\), and set

\[
S_0=D\cup([0,3/8]\times\{0\})
       \cup(\{0\}\times[0,3/8]),
\]
\[
S_1=S_0\cup[(3/8,0),(0,3/8)].
\tag{ED.13}
\]

These are distinct compact connected sets with the same convex hull
and area \(\pi/16\). They are both genuine two-full-turn bodies:
both fit in a disk of radius \(3/8\), which can be translated into
the unit-square corner, rotated there, and translated along either
unit outgoing arm. The new segment adds no area and lies in the old
convex hull, but its midpoint \((3/16,3/16)\) is outside \(S_0\).
This low-area example invalidates an unqualified almost-everywhere to
compact-set inference, without challenging sharp-reference recovery.

Body uniqueness does not mean uniqueness of motion witnesses. The
canonical angle conclusion says that each original equality motion
must reach its correctly handed quarter turn; otherwise Gate 0 would
supply a proper equality pair. It does not prohibit pauses, upstream
translations or backtracking in a supplied witness.

## 7. What a manuscript must expose

A self-contained derivation of the new reductions can be assembled
from the accepted proofs, but a list of closure notes is not that
manuscript. The following items must appear with their hypotheses and
proofs, or as explicitly stated external inputs:

| Part | Required material |
|---|---|
| Original domain | The two independent motions, correct-handed angle reach, actual outgoing strips, common hull, signed fibers and connected projection. |
| Scalar domain | Height extrusion, middle chord, width coercivity, moving-window continuity, attainment, top insertion and used-support saturation. |
| Source selection | Penalization targeting the prescribed cap, zero-end-face complementarity, inward trimming, erosion, finite source occupation and removal of charged singular curvature. |
| Full-turn value | The unit-wing geometric comparison, the \(H^1\) calibration, all strict horizontal/tilted exclusions, and the exact feasibility argument before the ordinary one-turn bound is applied. |
| Partial-turn value | One-sided angle derivatives with historical ties, the genuine finite-angle bounds, terminal facet mass, weighted companion comparison, reflected impulse and both error-payment ranges. |
| Equality | The all-canonical quantifier ED2, strict calibration, inverse ED3, fixed-cap terminal extension contradiction, original two-cap deficit ED.5 and literal set recovery ED4. |
| Reference and inputs | Exact reference functions, matching and area, the reference feasibility input, and the precise ordinary one-turn theorem and rational area enclosure used by Gate 1. |

The external ordinary one-turn theorem is used to strictly exclude
nonreference full-turn branches. No equality classification for that
external theorem is required. The present rigidity argument must not
claim that theorem's uniqueness as an unstated input.

The manuscript should describe itself accurately as a complete
derivation from its explicitly stated external theorems if their
proofs are not reproduced. Its exact rational checks are reproducible
arithmetic evidence; they do not replace the continuum source or
compactness arguments. Historical statements that a gate was then
open, and historical conditional routes no longer used, must not be
mixed into its current proof without clear scope labels.

No external acceptance, kernel verification or uniqueness of motions
is implied by completion of this written equality audit.
