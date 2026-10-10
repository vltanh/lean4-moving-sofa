# Gate 1 dependency and coverage audit

Completed integration audit, independently checked within the research session,
October 10, 2026. This update has checked the complete coverage against
[FR](gate1-tilted-final-height-reduction.md) Sections 1--5 and
[SH](gate1-tilted-small-height-exclusion.md), including the earlier IE8
high-tilt strip. It finds no remaining coverage gap or circular dependency.
All separate final proof audits have been accepted. The
[closure theorem](gate1-sharp-full-turn-closure.md) records Gate 1 as passed
at the written-proof level; external refereeing and Lean verification remain outstanding.

## 1. Exact theorem obtained

The target is the spatial one-cap inequality

    P(U)=integral_(I\J) A_U-integral_J n_U <= M/2

for every downward compact convex cap of height at most one, with its own
middle-half window J and the full continuous-angle two-attached-wall
positive niche. This is the stronger sufficient theorem SD.3. Its domain
has no curvature, symmetry, contact-pattern, polygon-count, or physical
cap-survivor-feasibility restriction.

SD3 gives attainment after translation and width coercivity. MID2 maps an
attained maximizer to a height-one global maximizer whose entire middle
roof is affine, without lowering P. The penalized polygon selection in
RG targets this particular canonical maximizer; it does not replace it
by a different finite optimizer whose canonicality would be unproved.
Thus excluding every tilted canonical maximizer, while bounding every
horizontal canonical maximizer by M/2, computes the unrestricted scalar
supremum. SD2 then covers every subunit-height cap as well.

For any common full-turn hull K, the Gate 0 signed fiber length is

    ell=1-max(d_V,n_U)-max(d_U,n_V).

Inside the common J, ell<=1-n_U-n_V. Outside J,
ell<=A_U+A_V-1. The two pieces have equal horizontal measure, so their
constants cancel and

    integral_I ell<=P(U)+P(V)<=M.

This also holds for arbitrary auxiliary hulls with negative signed
fibers; nonempty fibers are needed only to identify the signed integral
with ordinary envelope area for a genuine connected sofa. Consequently
SD.3 gives the full-conventional-two-turn Gate 1 theorem and the stronger
signed full-turn charge. It does not give the independent partial-turn
and outgoing-strip theorem of Gate 2.

## 2. The dependency order is acyclic

| Stage | Inputs actually used | Output and scope |
|---|---|---|
| SD | Actual attached walls, height extrusion, convex-body compactness | Height-one attainment and a compact width range on the entire cap domain |
| MID, TF | Support monotonicity, uncharged middle area, genuine cap variations | An affine middle roof; tilted endpoint pinning; high middle endpoint at height one |
| FE, RG, EP | Penalized finite selections, corrected floating-facet inequalities, actual trimming/erosion, adjacent-wall geometry | Bounded regular wing curvature, exact endpoint complementarity, limiting finite-source measure balances |
| LH | A direct charged-roof and full-niche tent upper bound | Low middle height >1/2; strictly positive endpoint pressures and source equalities; clipped Green wing-length identity |
| HW | Spatial regularity/source laws, separately proved horizontal feasibility, direct calibration and exact rational leakage/wide bounds | Every horizontal canonical global maximizer has P<=M/2 |
| Tilted width/height cuts | Genuine charged-roof majorants and actual full-niche lower bounds | Every surviving tilt has 1001/2000<C<37/50 and 0<h<17/50 |
| CH7 and GF | Spatial arm bounds plus the first-good source/energy argument | All tilted C<=2/3 are excluded; more generally any first-unit tilted maximizer in .5<C<.8 is excluded |
| CG | Width/height cuts, cap support boxes, positive endpoint pressures, wing identity | Positive-corner confinement and a compact connected genuine one-turn cap survivor; only now may the ordinary one-turn bound be used |
| IE and ET | Same-sign spatial source laws and the actual initial floor interval; no full first-unit assumption | A sufficient first-unit criterion and a terminal first-unit interval at every possible positive right endpoint tangency |
| RT | EP, boxes, high pinned point, reflected arm estimate under T=0; no full unit assumption | Exact middle positive projection, T>0, n(-C)=0; optional support-point bounds on T |
| Final scalar alternatives | Actual n(-C)=0 pressures, IE, ET leakage, CG feasibility and the ordinary one-turn bound | The high-strip reduction and both IE failure cases exclude all remaining wider tilted maximizers |

The endpoint complementarity does not use an invalid two-sided isolated
axis variation. Its lower inequality comes from actual inward trimming;
axis-face convergence follows from the floating-facet bound, not from
the pressure equality being proved. Positive faces are obtained only
after LH. Likewise the selected finite source measures are kept distinct
from ordinary limiting niche arclength. The no-ghost projection and the
fractional B/D/c occupation disintegration are additional proved steps,
not consequences silently imported from uniform roof convergence.

GF has no dependence on CG or Gerver feasibility. Its full source
classification and fold-energy budget concern the actual spatial niche,
even before it is shown to lie under the cap. CG in turn has no
first-unit hypothesis, so using it later on the wider nonunit branch is
legitimate. IE and ET similarly use the regularity/arm bounds, not GF's
conclusion. RT's global projection works at C>=2/3 by the elementary
high-point inequality (3C-1)cos t+sin t>1; it does not borrow the
first-good positive-interval theorem outside its valid scope.

## 3. Width and height coverage, including boundaries

The exact reference gives P_max>=M/2>41/50. The global tilted cuts therefore
leave strict bounds

    1001/2000<C<37/50, 0<h<17/50.

At the lower and upper cut boundaries the direct upper bounds are
already strictly below the reference. CH7 applies through C=2/3, and
GF excludes that entire first-good branch. The only remaining interval
is therefore

    2/3<C<37/50.

CG, forward ET, RT, and their endpoint/leakage consequences all apply
there without assuming u<=1 or v<=1 on a whole quarter. RT also includes
C=2/3, so there is no uncovered joining endpoint.

The complete remaining coverage is as follows.

| Width and tilt range | Exclusion |
|---|---|
| Every remaining width, 21/100<=h<17/50 | IE8 proves both first-unit conditions; GF excludes the cap |
| 2/3<C<=73/100, 1/20<=h<=21/100 | FR4--FR5 prove both first-unit conditions; GF excludes the cap |
| 73/100<=C<37/50, 1/20<=h<=21/100 | FR6--FR13 give the strict actual spatial bound P<41/50 |
| 2/3<C<37/50, 0<h<=509/10000 | SH1--SH24 exclude failure of either IE condition by a genuine ordinary-area contradiction; if neither fails, IE and GF apply |

Thus the final high-strip argument leaves h<1/20, and the last row covers
it with positive overlap because 1/20<509/10000. The last row splits on
the two IE inequalities:

    d^2+B^2<=5,
    d^2+B^2+B(1-h)-d sqrt(h(2-h))<=4,
    d=3C, B=eR-1+h.

If both hold, IE gives u<=1 and GF contradicts a tilted maximizer.
If either fails, its ordinary-area lower bound exceeds G0. Non-strict
equality in either IE inequality belongs to the first-unit side, so no
equality case is lost. The joining widths 2/3 and 73/100 and joining
heights 1/20 and 21/100 are included in at least one closed-side estimate.

The prior IE8 radius bound was checked explicitly:
(111/50)^2+(107/400)^2=799993/160000<5. It uses the earlier endpoint
boxes, not n(-C)=0 or a whole-quarter unit premise. Its IE2 test is
monotone in B and convex in h, with both listed endpoints below four.
The newer FR strip has the analogous exact radius 798001/160000<5 and
the two IE2 endpoint values 634973/160000 and 553949/160000.

The FR triangle extension lowers FT's old base width a=37/25 to a=73/50.
The requisite crossover lower bound becomes stronger:
M-h/2>=363/400>179/200. The apex remains positive and in J, and the
two full gain triangles remain disjoint and inside J. The improved
asymmetric floor losses are added back explicitly. The critical point is
inside the unclipped region, and the same negative-semidefinite Hessian
and supporting plane control every other clipping pattern. The final
bound is 7550393/9240000<41/50.

This audit also checked the fixed exact rational identities behind the
last small-height cases: the SH18 monotone-bracket value is
11102231813/13507522880000>0, and the SH23 lower bound is
666488123/300000000>22199/10000. These checks evaluate the stated
certificates; they perform no parameter search or angle sampling.

## 4. The ordinary one-turn dependency is explicit

The external area theorem used by HW and CG is Baek's [*Optimality of
Gerver's Sofa*](https://arxiv.org/html/2411.19826v1), arXiv:2411.19826, Theorem 1.1.1. Its stated class is a
nonempty connected closed planar shape that admits an actual continuous
rigid motion through the unit right-angle hallway. CG constructs such a
shape: n<=A, the vertical fibers meet the continuous top graph, and the
full canonical placements provide the motion. The cap is never assumed
to maximize ordinary one-turn area.

The exact numerical relaxation is the already recorded

    G0=22199/10000.

It is obtained from the six existing [Gerver/AreaBounds.lean](../../MovingSofaOptimality/Gerver/AreaBounds.lean) enclosures
for the stated Gerver parameter solution by the signed combination

    (7202+13340+8069-6013-30-369)/10000.

This audit checked that the six named enclosure declarations and their
`IsSolution`/`Bounds` premises are present in the repository and that the
signed sum is correct. The assembled `gerverSofa_area_mem` declaration in
[Main.lean](../../MovingSofaOptimality/Main.lean) gives the same upper endpoint;
`romik_exists` and `romik_bounds` in
[External/Romik.lean](../../MovingSofaOptimality/External/Romik.lean) supply
the solution and its bounds in the existing source chain. This inspection
does not claim a new Lean compilation or a new proof of Baek's theorem. Only this external ordinary area upper bound is
imported; no weighted-maximizer stationarity, weighted contact chart, or
weighted unit-curvature theorem is transferred to the spatial objective.

## 5. Final status and scope

Gate 1 passes as a written mathematical proof
within this research chain, conditional on its explicitly cited ordinary
one-turn theorem and existing Gerver area enclosure. The spatial scalar
bound and the full-conventional-two-turn bound are then proved in that
sense. No Lean verification, external refereeing, arbitrary partial-turn
optimality, equality classification, or uniqueness conclusion follows
from this checkpoint alone. Gate 2 remains a distinct unresolved step.
