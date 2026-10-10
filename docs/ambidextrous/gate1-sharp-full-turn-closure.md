# Gate 1 closure: the sharp spatial cap value and full-turn area theorem

**October 10, 2026. Gate 1: PASS as a written mathematical proof.** The
last tilted-maximizer alternatives are excluded below, completing the
universal scalar theorem SD.3 and the full-turn acceptance inequality
G1.2 / G1.5. The constituent arguments and the complete dependency order
received separate mathematical checks within this research session. They
have not been externally refereed or verified by a Lean kernel.

The ordinary one-turn area theorem and its exact numerical enclosure are
explicit dependencies, recorded in Section 6. **Gate 2, concerning two
independent partial turns and their actual outgoing strips, remains
unproved.** The present result establishes the sharp value for complete
conventional turns; it does not establish unrestricted ambidextrous
optimality, equality classification, or uniqueness.

## 1. Exact statements

Let

\[
M=1+4Y^2+\arctan Y,
\qquad 4Y^3+3Y-1=0,\quad Y>0.
\tag{G1C.1}
\]

For a nonempty compact downward convex cap
\(U\subset\mathbb R\times[0,1]\), write its horizontal projection as
\(I=[l,r]\), its roof as \(A_U\), its width as \(W=r-l\), and set

\[
J=[l+W/4,r-W/4].
\]

The positive ambient niche is the full two-attached-wall envelope

\[
n_U(x)=\left[\sup_{0<t<\pi/2}
\min\left\{
\frac{h_U(\cos t,\sin t)-1-x\cos t}{\sin t},
\frac{h_U(-\sin t,\cos t)-1+x\sin t}{\cos t}
\right\}\right]_+.
\tag{G1C.2}
\]

Define

\[
\mathcal P(U)=\int_{I\setminus J}A_U(x)\,dx
-\int_J n_U(x)\,dx.
\tag{G1C.3}
\]

**Theorem G1C1 (SD.3, sharp scalar value).** Every such cap satisfies

\[
\boxed{\mathcal P(U)\le M/2.}
\tag{G1C.4}
\]

The supremum equals \(M/2\), attained by Romik's reference cap. The
statement includes caps of height below one, arbitrary asymmetry,
nonsmooth boundaries, unbounded polygon complexity, and caps whose
ordinary one-turn survivor is not known to be connected or feasible.
A zero-width cap has score zero and is immediate.

**Theorem G1C2 (Gate 1, sharp full-turn value).** Every compact connected
body that can make both complete conventional quarter turns through the
two unit right-angle corridors, from a common incoming orientation, has

\[
\boxed{|S|\le M.}
\tag{G1C.5}
\]

Romik's construction attains equality. The same upper bound holds for
the signed full-turn envelope functional on every auxiliary convex hull
in Gate 0's domain. This last assertion concerns the signed integral;
it does not identify that integral with ordinary area when an auxiliary
hull has empty survivor fibers.

## 2. The global maximizer reduction

The proofs in [SD](gate1-spatial-dual-height-width-compactness.md) and
[MID](gate1-global-middle-chord-canonicalization.md) apply to the entire
cap domain of G1C1. Vertical Minkowski extrusion to height one cannot
decrease \(\mathcal P\): it raises each charged exterior roof by the
extrusion amount, and raises each positive middle niche roof by at most
that amount. The two regions have equal horizontal measure.

The actual 45-degree two-wall niche gives width coercivity, and the
whole-angle niche is continuous under Hausdorff convergence. Consequently
the scalar maximum is attained by a height-one cap with \(8/5<W<6\).
Replacing its uncharged middle roof by its chord and then saturating the
height preserves global maximality and makes the entire middle roof
affine. The polygon selections used for regularity target this chosen
maximizer, rather than a different finite optimizer.

The reference score is \(M/2\), and \(M/2>41/50\). This strict rational
comparison needs no decimal approximation: if \(a=297/1000\), then
\(4a^3+3a<1\), so \(Y>a\), while

\[
M>1+4a^2+a-a^3/3
=\frac{1641103309}{1000000000}>\frac{41}{25}.
\tag{G1C.6}
\]

Here \(\arctan a\ge a-a^3/3\) follows by integrating
\(1/(1+t^2)\ge1-t^2\).

The [regularity theorem](gate1-spatial-maximizer-wing-curvature-regularity.md),
[facet-pinning theorem](gate1-spatial-tilted-facet-pinning.md),
[endpoint complementarity](gate1-global-endpoint-complementarity.md), and
[positive-pressure theorem](gate1-global-positive-pressure-and-wing-identity.md)
then apply to the canonical global maximizer. They prove bounded regular
wing curvature, the necessary corner locations, positive endpoint
pressures, exact limiting finite-source balances, and

\[
2\mathcal P=L_{\mathrm{wing}}.
\tag{G1C.7}
\]

The wing length includes any horizontal top overhang and excludes the
vertical end faces. These are necessary conditions for the spatial
objective itself. Ordinary niche arclength is not silently identified
with a weak limit of finite source measures.

If the affine middle roof is horizontal, the complete
[horizontal theorem HW1](gate1-horizontal-maximizer-sharp-value.md)
already proves G1C.4 at every width. It remains to exclude tilted
canonical global maximizers. The following sections exhaust them.

## 3. Tilted normalization and the first-unit exclusion

Reflect horizontally if needed so that the higher middle endpoint is on
the right. Put

\[
I=[-2C,2C],\quad J=[-C,C],\quad
A(-C)=1-h,\quad A(C)=1,
\]

and write the top face as \([C,C+T]\times\{1\}\). Here \(h>0\) is
the tilt height and \(T\ge0\) is the top overhang. To fix the two wing
conventions explicitly, put

\[
f(t)=h_U(\cos t,\sin t),\qquad
g(t)=\max_{x\in[-2C,-C]}\{-x\sin t+A_U(x)\cos t\},
\]

\[
u=f''+f,\qquad v=g''+g
\quad\text{almost everywhere on }(0,\pi/2).
\]

Thus the first density \(u\) belongs to the high-right wing, and \(v\)
uses the low-left-wing surrogate, excluding the central-facet atom.
The extra high-point second wall is nonpositive on \(J\); the tilted
source notes justify this convention for the actual positive niche.

The [short, wide, and intermediate cuts](gate1-tilted-width-exclusions.md)
and the [full-triangle width bound](gate1-tilted-full-triangle-width-cut.md)
give

\[
\frac{1001}{2000}<C<\frac{37}{50},\qquad
0<h<\frac{17}{50}.
\tag{G1C.8}
\]

The general [first-unit theorem GF](gate1-tilted-first-wing-exclusion.md)
excludes any tilted canonical global maximizer in this domain for which
\(u\le1\) almost everywhere. It places no unit bound on \(v\).
Its [structural argument](gate1-tilted-first-wing-structure.md) and
[joint-source occupation audit](gate1-tilted-folded-source-occupations.md)
retain companion folds and measurable contact ties. The exact energy
inequality ends with

\[
6CT\le\frac{97}{48}T<3T,
\]

where the geometry has forced \(T>0\), contradicting \(C>1/2\).
The first companion-floor crossing has displacement at least \(T\);
it is not assumed to be the global niche minimum.

[CH7](gate1-spatial-maximizer-curvature-and-horizontal-value.md) supplies
\(u\le1\) whenever \(C\le2/3\), including the endpoint. Hence only

\[
\frac23<C<\frac{37}{50}
\tag{G1C.9}
\]

remains. For this entire wider range, the
[initial-floor energy test IE](gate1-tilted-initial-floor-energy.md)
gives a sufficient condition for \(u\le1\). With

\[
d=3C,\quad B=e_R-1+h,\quad s=\sqrt{h(2-h)},
\]

the two conditions are

\[
d^2+B^2\le5,
\qquad d^2+B^2+B(1-h)-ds\le4.
\tag{G1C.10}
\]

IE8 proves both throughout \(21/100\le h<17/50\), without using the
later zero-niche endpoint result. GF excludes that strip, leaving
\(h<21/100\).

## 4. Endpoint geometry and the final height reduction

The next three results assume neither whole wing has curvature at most
one. This order matters for the remaining branch.

[CG](gate1-tilted-corner-confinement.md) proves that all positive inner
corners lie in \(J\), the actual niche lies below the cap, and
\(\mathcal S=U\setminus N(U)\) is a nonempty compact connected body
with a genuine continuous one-turn motion. Thus the established ordinary
one-turn bound

\[
|\mathcal S|\le G_0:=\frac{22199}{10000}
\tag{G1C.11}
\]

may be applied to this body.

The [early-excess theorem ET](gate1-tilted-first-excess-ends-early.md)
shows \(u\le1\) for \(t\ge11/15\), before every possible positive
right endpoint tangency because \(\cos(11/15)>37/50\). It also bounds
the earlier excess moment by \(J_f<1/40\).

The new [reflected-tail and projection theorem RT](gate1-tilted-reflected-tail-and-projection.md)
uses the high pinned point, the actual finite-source horizontal moment,
and a reflected arm estimate under \(T=0\). It proves

\[
T>0,\qquad n_U(-C)=0,
\qquad T=C+x_{\rm zero}.
\tag{G1C.12}
\]

Here \(x_{\rm zero}\) is the unique zero of the low-wing second-wall
envelope. Passing through its zero-height interval is justified by the
finite source mass estimate, rather than by an invalid continuity claim
for zero-set lengths.

Writing \(z=n_U(C)\), the actual endpoint laws and ET/RT now give

\[
e_R=\frac12+\frac h4+\frac{3z}{4},\qquad
e_L=\frac12-\frac{3h}{4}-\frac z4,
\]

\[
0<T\le s,\quad 0\le z\le KT,\quad
K=\frac{C}{\sqrt{1-C^2}}<\frac{10}{9},\quad
N_{\rm out}\le\frac{(T+J_f)z}{2}.
\tag{G1C.13}
\]

The [final height reduction FR](gate1-tilted-final-height-reduction.md)
uses these pressure identities to exclude \(h\ge1/20\). For
\(C\le73/100\), both IE conditions hold throughout
\(1/20\le h\le21/100\); the exact radius bound is
\(798001/160000<5\), and the two extremal energy bounds are
\(634973/160000<4\) and \(553949/160000<4\).

For \(C\ge73/100\), the zero left endpoint niche sharpens the
positive-floor loss in the full-triangle proof. The joint concave support
relaxation retains every clipping pattern. Its supporting-plane bound
decreases in \(h\) over this strip and at \(h=1/20\) is

\[
\mathcal P<\frac{7550393}{9240000}
=\frac{41}{50}-\frac{26407}{9240000}<\frac{41}{50}.
\tag{G1C.14}
\]

Both subranges contradict maximality. Every remaining tilt therefore
has \(0<h<1/20\).

## 5. Every small-tilt alternative is impossible

The [small-height theorem SH](gate1-tilted-small-height-exclusion.md)
covers the slightly larger interval

\[
\frac23<C<\frac{37}{50},\qquad
0<h\le\frac{509}{10000}.
\tag{G1C.15}
\]

It combines G1C.7, the two actual wing chord lengths, and G1C.13 to obtain
an ordinary-area lower bound. Set

\[
C_0=\frac{\sqrt{17}}6,\quad
S_0=\frac{2\sqrt{17}+\sqrt{26}}6,\quad
\lambda=\sqrt{\frac{17}{26}},\quad
m=\frac{3}{4\sqrt{26}},\quad a_0=\frac{1-\lambda}{2}.
\]

The tangent inequality for the Euclidean norm gives

\[
|\mathcal S|\ge S_0+(2+\lambda)(C-C_0)
-Ch-m(h+z)+a_0T-\frac{(T+J_f)z}{2}.
\tag{G1C.16}
\]

If the second inequality of G1C.10 fails, completion of squares gives

\[
\left(3C-\frac s2\right)^2+\frac9{16}(h+z)^2>\frac{17}{4},
\]

and therefore

\[
C-C_0>\frac s6-\frac3{64}(h+z)^2.
\]

Substitution into G1C.16 and the exact endpoint bounds reduce the area
surplus to a decreasing cubic bracket. Its value at the rational endpoint
\(s_*=63/200\) is

\[
\frac{11102231813}{13507522880000}>0.
\tag{G1C.17}
\]

Thus \(|\mathcal S|>S_0>2669/1200>G_0\), contradicting G1C.11.

If the first inequality of G1C.10 fails, then
\(C>\sqrt{19}/6>29/40\) and \(B<-4/15\). These force the improved
endpoint bound \(z<27/100\). The same chord estimate yields

\[
|\mathcal S|>\frac{666488123}{300000000}
=G_0+\frac{518123}{300000000}>G_0,
\tag{G1C.18}
\]

again a contradiction. If neither inequality fails, IE gives \(u\le1\)
and GF excludes the cap. These alternatives include equality in either
energy criterion. They exhaust G1C.15.

Since \(1/20<509/10000\), this excludes every tilt left by Section 4.
The complete coverage is recorded explicitly below.

| Canonical maximizer branch | Complete bound or exclusion |
|---|---|
| Horizontal middle, every width | HW1 proves \(\mathcal P\le M/2\) |
| Tilted, outside G1C.8 | Actual short/wide/intermediate and full-triangle bounds |
| Tilted, \(C\le2/3\) inside G1C.8 | CH7 followed by GF |
| \(2/3<C<37/50\), \(h\ge21/100\) | IE8 followed by GF |
| \(2/3<C\le73/100\), \(1/20\le h\le21/100\) | FR's IE strip followed by GF |
| \(73/100\le C<37/50\), \(1/20\le h\le21/100\) | FR's actual full-triangle bound |
| \(2/3<C<37/50\), \(0<h\le509/10000\) | SH: either IE failure contradicts ordinary area; otherwise IE and GF |

The selected canonical maximizing cap is therefore horizontal. HW1 bounds its
value by \(M/2\); the reference attains \(M/2\). Attainment, the
score-preserving canonical reduction, and height extrusion prove G1C1
for the entire original cap domain. No global curvature hypothesis has
been imposed on that domain.

## 6. Ordinary one-turn dependency and verification record

The external input in G1C.11 is Baek's
[*Optimality of Gerver's Sofa*, Theorem 1.1.1](https://arxiv.org/html/2411.19826v1),
which bounds every nonempty connected closed planar shape admitting a
continuous rigid motion through the unit right-angle hallway by Gerver's
area. CG constructs a body in exactly that class before the theorem is
used. No optimality premise for the spatial cap under the ordinary-area
objective is imported.

The rational relaxation \(G_0=22199/10000\) is the existing exact
enclosure recorded in [SE.1](one-turn-single-excess-quarter.md).
Its six component bounds occur in
[Gerver/AreaBounds.lean](../../MovingSofaOptimality/Gerver/AreaBounds.lean),
with their stated Gerver parameter solution and bounds hypotheses. Their
signed upper sum is

\[
\frac{7202+13340+8069-6013-30-369}{10000}
=\frac{22199}{10000}.
\]

The assembled declaration `gerverSofa_area_mem` in
[Main.lean](../../MovingSofaOptimality/Main.lean) gives the same upper
endpoint. The declarations `romik_exists` and `romik_bounds` in
[External/Romik.lean](../../MovingSofaOptimality/External/Romik.lean)
supply a solution in the stated box and its parameter bounds in the
existing source chain. Those declarations and their premises were
inspected; they were not recompiled or newly proved in this work. The
external theorem and this existing enclosure are explicit dependencies
of the written result.

The [dependency and coverage audit](gate1-dependency-coverage-audit.md)
checks that the source arguments, corner confinement, forward and
reflected terminal estimates, and final energy alternatives have no
circular unit-curvature or ordinary-feasibility premise. The
[fixed exact checker](computer-assisted/check_gate1_final_scalar_exact.py)
reproduces the final rational certificates using Python's `Fraction`
only. Its checks are arithmetic certificates, not a substitute for the
continuum geometric proofs. No angle sampling, optimization campaign,
Lean/Lake command, CI run, or Lean source edit is part of this checkpoint.

## 7. Deduction of Gate 1 and the remaining gate

For a genuine connected both-full-turn sofa, let \(U,V\) be the upper
and reflected lower downward caps of its common convex hull. They share
the same projection \(I\) and middle half \(J\). With
\(d_U=1-A_U\) and \(d_V=1-A_V\), the
[Gate 0 fiber formula](original-motion-global-bridge-gate0-audit.md) is

\[
\ell(x)=1-\max\{d_V(x),n_U(x)\}
-\max\{d_U(x),n_V(x)\}.
\]

On \(J\), \(\ell\le1-n_U-n_V\); on \(I\setminus J\),
\(\ell\le A_U+A_V-1\). The constants cancel after integration because
the two regions have equal length. Connectedness supplies nonempty
projected fibers for the actual canonical envelope, so

\[
|S|\le\int_I\ell(x)\,dx
\le\mathcal P(U)+\mathcal P(V)\le M.
\tag{G1C.19}
\]

For arbitrary auxiliary hulls the same pointwise inequalities bound the
signed integral, without assuming its fibers are nonempty. At Romik's
reference hull, the middle roofs equal one, both niches are confined to
the middle window, and the
[exact reference calculation](spatial-half-partition-bound.md)
gives equality throughout G1C.19. Thus the complete full-turn supremum
is exactly \(M\), and the original coupled ordinary niche-loss inequality
G1.2 / G1.5 follows as well. This meets the controlling plan's Gate 1
acceptance condition.

The unresolved theorem is now Gate 2: the sharp joint charge with
independent terminal angles \(\alpha,\gamma\in[\pi/4,\pi/2]\) and
their two actual outgoing whole-body strips. The proof above uses both
full angle intervals. It supplies no no-loss completion theorem for
partial turns. The research branch therefore continues to distinguish
**Gate 1 passed** from **unrestricted ambidextrous optimality unproved**.
