# Gate 2: dependency, boundary and original-domain coverage audit

**October 10, 2026. Audit accepted; Gate 2 PASS at the written-proof
level.** This document checks the chain assembled in
[the partial-turn closure](gate2-sharp-partial-turn-closure.md). Separate
reviews within this research session accepted the final curvature
envelope, weighted payment, all sign and angle boundaries, and the
original-motion deduction. Every result in the chain concerns the actual
partial spatial objective or an explicitly identified geometric input.

## 1. The exact target and the required contradiction

The scalar target is

\[
\mathcal P_\alpha(U)
=\int_{I\setminus J}A_U-\int_J
\max\{0,\sup_{0<t<\alpha}\min(R_t,S_t),R_\alpha\}
\le M/2,
\]

for every compact downward convex cap of height at most one and every
\(\alpha\in[\pi/4,\pi/2]\), using its own moving middle half.
At the full-turn endpoint the terminal wall is redundant and Gate 1
applies. The proper-angle terminal term is a whole first wall, not a
two-wall corner or an outgoing half-ray.

If any cap violates this inequality, PD gives an attained joint global
maximizer. Select the largest terminal angle among maximizing pairs and
canonize at that fixed angle. The final argument excludes this selected
pair; it does not assert that each intermediate maximizer exclusion was
already an individual-cap theorem at every fixed angle.

## 2. Noncircular dependency order

| Step | Proven input and its role | Premises retained |
|---|---|---|
| 1 | [PD](gate2-partial-cap-domain-reductions.md): height extrusion, middle chord, width coercivity, joint continuity, attainment, top insertion and unused-support saturation | All caps, both middle-slope signs, exact outgoing wall |
| 2 | [PS](gate2-partial-endpoint-source-and-green.md): partial finite-source selection, actual endpoint complementarity, positive pressures, wing/source and Green identities, regular used-wing bounds | The selected partial maximizer; the possible first terminal atom is retained |
| 3 | [AT](gate2-all-width-terminal-angle-exclusion.md): universal bound below M/2 for alpha at most atan(8/3) | All widths, all floor/window clips, actual support compatibility |
| 4 | [TP](gate2-terminal-facet-and-prefix-reduction.md), Section 1: transfer short-width and tilt exclusions using the three visited tents and partial endpoint pressures | Reflection only of the comparison and barrier together |
| 5 | [WC](gate2-three-angle-width-cut.md): C<37/50 at every remaining angle | Exact partial endpoint identities and a joint positive-floor loss bound; no endpoint niche box |
| 6 | [NT](gate2-negative-tilt-completion.md): bound the completed negative-tilt alternatives by Gate 1 | Completion proved only when h_R is at least 1−sin(alpha), or the central normal is visited |
| 7 | [TV](gate2-terminal-angle-variations.md) and TP, Sections 2–3: terminal facet m<=w and top projection T_L+2T_R<=d | Largest-angle choice, both one-sided derivatives with ties, actual terminal tail height |
| 8 | [MP](gate2-companion-moment-prefix-exclusion.md): weighted companion support and exact terminal margin | Only the early weighted excess E_theta must be paid; no whole-wing unit premise |
| 9 | [RX](gate2-reflected-tail-cot-one-eighth.md): E_theta=0 for cot(alpha)<=1/8 | The endpoint boxes are proved valid on this small-deficit interval |
| 10 | [AC](gate2-all-angle-reflected-cubic-exclusion.md): E_theta<6517/6400000 for cot(alpha)>=1/8 | Uses the outgoing wall explicitly in the endpoint bound; keeps its terminal impulse |
| 11 | MP plus PS terminal occupation | Strict exposure has length greater than w>=m, contradicting the total terminal source mass |
| 12 | G2C1 plus [Gate 0](original-motion-global-bridge-gate0-audit.md) and G2C.23–24 | Both independent angles, actual connected-body fibers and the signed auxiliary domain |

AT needs the domain reduction but does not depend on the terminal angle
law or the final curvature estimate. WC uses TP's initial finite-angle
and endpoint facts, not MP or the reflected error payment. MP uses WC;
RX and AC then supply MP's separate weighted-excess premise. There is
no circular appeal to the desired partial-cap value.

The earlier positive first-unit exclusion PU, short positive-width
energy criterion IM, very-small-deficit exclusion RP, and all-angle
short-width prefix SW are valid supporting results. Their separate case
exclusions are not needed to cover a missing interval in the final
RX/AC argument. The local source laws and reflected support identities
used from PU/RP are identified explicitly in AC.7–12; their conclusions
about whole branches are not assumed as curvature hypotheses.

## 3. All angle boundaries are covered

| Angle case | Bound or contradiction |
|---|---|
| alpha=pi/2 | Gate 1 universal cap theorem, including subunit height |
| pi/4<=alpha<=atan(8/3) | AT's universal strict bound 5259/6400<M/2 |
| atan(8/3)<alpha<pi/2, 0<cot(alpha)<=1/8 | RX unit companion prefix, then MP with zero weighted excess |
| atan(8/3)<alpha<pi/2, 1/8<=cot(alpha)<3/8 | AC reflected envelope and cubic payment, then MP |

The two proper-angle curvature ranges overlap at cot(alpha)=1/8.
The AT boundary cot(alpha)=3/8 is included in its strict exclusion.
The limiting cot(alpha)=0 is handled by Gate 1 itself, not by a
singular partial-wall formula. No two-angle diagonal or equal-angle
assumption appears in this coverage.

## 4. All middle-slope signs and exceptional facets are covered

| Original middle | Support convention and terminal handling |
|---|---|
| Positive slope | First support is actual; companion support is the low-left-wing surrogate. Every omitted high-point second wall is nonpositive on J. The removed central interval has no regular charged sources. H=1. |
| Horizontal | Both supports are actual. Both top overhangs are allowed, including either or both equal to zero. H=1. |
| Negative slope, completed branch | NT proves full-niche domination only in its stated two alternatives, and Gate 1 pays the value. Equality at h_R=1−s or at the central normal is included. |
| Remaining negative slope | 0<h_R<1−s and the first central normal is unvisited. Remove that unused atom with the right-wing first-support surrogate; all used first supports remain actual. H=1−h_R>s. |

PS excludes singular curvature on proper regular used arcs. It does
not remove the first terminal facet: its reflected impulse has size
\(j=m/s\), and RX/AC pay it through the exact energy identity.
The companion terminal atom is absent by the separately proved PS
source law. The first terminal facet is not hidden inside an
almost-everywhere curvature bound.

The initial reflected Q-component remains positive throughout the
unused gap. P is strictly decreasing there, so a first zero before the
terminal impulse cannot return before that impulse. The proofs handle
the zero before, at or after the impulse, a component ending before the
zero, and every later positive-Q component. After P becomes nonpositive,
Q decreases on the remaining positive component; it cannot create a
second excess episode by re-entering Q>1.

The source law and the local arm equations are used on the actual used
interval, or on a surrogate interval where equality of the relevant
supports is proved. No stationarity of a reflected partial objective is
assumed. The apparent reflection only exchanges these local equations.

## 5. Weighted moment, exposure and exact payment

The shifted companion curve obeys
\(D_x'=(1-v)\cos t\), \(D_y'=(1-v)\sin t\). A positive
global second-wall maximum is attained in the used interior and satisfies
\(D_x=x\). Its actual outer support point has horizontal coordinate
at least \(-2C\), which forces \(\sin t\le C+z\) when
\(x=-C+z\). In particular a terminal maximum is not silently
discarded; the second wall is strictly decreasing after this cutoff.

With \(\theta=\arcsin(C-T_L)\), the weighted kernel changes sign
at \(\theta\). Before that angle its only adverse contribution is
\((v-1)_+\); afterwards nonnegativity of v gives the required upper
bound. Thus whole-wing curvature exceeding one is allowed. The exact
error is

\[
\mathcal E_\theta
=\int_0^\theta(v-1)_+
\frac{\sin(\theta-t)}{\cos\theta}\,dt.
\]

MP's support comparison is uniform on the entire interval
\([-C,-C+w]\), and its strict terminal margin is greater than
\(39c/4400\). RX makes the error zero in its range. In AC's range,
the reflected excess ends before 91/100 and has slope bound 19/25.
The relevant interval has length less than 7/40, and
\(\cos\theta>2/3\). Hence

\[
\mathcal E_\theta
<\frac{6517}{6400000}
<\frac{117}{110000}
<\frac{39c}{4400}.
\]

The middle strict gap is exactly \(3193/70400000\). No floating-point
root, angle grid, optimization run, contact-chart guess or unexplained
numerical allowance occurs in this payment.

The strict exposure continues beyond the interior right endpoint of
\([-C,-C+w]\), so its measure is strictly greater than w. PS gives
full terminal occupation on this strict set and total occupation m.
This contradicts m<=w. The contradiction requires no identification of
weak finite-source measures with the ordinary arclength of the full
continuum niche, and no common terminal occupation for separate shape
and angle perturbations. Historical ties may remain elsewhere.

## 6. The independent-motion and signed-domain deduction

For an actual above-sqrt(2) body, Gate 0 retains the two whole-body
outgoing strips and independent alpha,gamma in [pi/4,pi/2], even when
the physical rotations backtrack. Its upper and reflected-lower caps
have a common projection and middle half. On J the exact signed fiber
is bounded by 1 minus the two partial barriers; off J it is bounded
by the two cap roofs minus 1. Equal lengths cancel the constants.

This proves
\(\int\ell\le\mathcal P_\alpha(U)+\mathcal P_\gamma(V)\le M\)
on the entire auxiliary signed domain. For the actual connected body,
Gate 0 also proves \(|S|\le\int\ell\), using nonempty projected
fibers. For auxiliary hulls with negative fibers, no positive-part
replacement is made. Bodies of area at most sqrt(2) are below M by
the exact Gate 1 reference comparison. The genuine Romik construction
supplies the matching lower bound.

The final implication does not require arbitrary in-place completion,
full-niche domination for all partial caps, symmetry of the two angles,
or an independent width multiplier on a restricted scalar domain.

## 7. Verification record and remaining scope

PD, PS, NT, TV, AT, PU, IM, TP, WC, RP, RX and MP received separate
written mathematical checks within the research session. SW also
received an independent exact-boundary audit. Root and two separate
audit streams accepted AC's all-sign pressure and impulse bounds,
clipped W monotonicity, episode envelope and cubic payment. The
assembled closure and its independent-motion deduction were separately
reviewed. The used-interval scope of the surrogate arm inequalities,
zero-overhang equality, and no-reentry argument are explicit in the
final documents.

The standalone
[exact checker](computer-assisted/check_gate2_final_exact.py) uses
Python's Fraction arithmetic and passes 83 final rational and squared
comparisons. Those checks are arithmetic evidence only. The source
selection, geometric identities, compactness arguments and external
ordinary one-turn theorem remain mathematical dependencies.

This audit concerns the sharp area value in the original compact
connected motion domain. It makes no equality classification,
uniqueness, external referee acceptance, or Lean-kernel claim. Gate 1's
explicit external theorem and area enclosure are retained as inputs.
