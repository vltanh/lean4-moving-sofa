# Optimality for left-right reflection-symmetric bodies

**Scope.** This proves the ordinary-area bound for ambidextrous bodies invariant under reflection in a line perpendicular to their common incoming strip. The two motions themselves need not be symmetric or full quarter turns. Reflection supplies missing angles, and the new geometric face results supply the area comparison. It is not a proof that an unrestricted optimizer has this symmetry. Labels RS are local.

The geometric completion argument below is independent of weighted optimality and curvature. The final value comparison depends on the branch's written AW-W and WV2 chains through FAS1; those historical arguments remain subject to independent review. No computer-assisted certificate or numerical calculation is used.

## 1. Reflection supplies complementary hallway angles

Translate the reflection axis to x=0, and let J(x,y)=(-x,y). A lower supporting hallway at angle t is specified by the ordered normals

$$\mu_t=(\cos t,\sin t),\qquad\nu_t=(-\sin t,\cos t),$$

and the actual supports f=h_S(mu_t), g=h_S(nu_t). Its conditions are

$$x\cdot\mu_t\le f,\quad x\cdot\nu_t\le g,\quad
x\cdot\mu_t\ge f-1\ \text{or}\ x\cdot\nu_t\ge g-1.$$

The hallway is unchanged if its two normals and corresponding supports are exchanged. For L=pi/2,

$$\boxed{J\mu_t=\nu_{L-t},\qquad J\nu_t=\mu_{L-t}.}\tag{RS.1}$$

If JS=S, applying J to a supporting hallway containing S therefore gives a supporting hallway containing the same S at angle L-t, with the supports exchanged. The reflected supports are the actual supports because J is an orthogonal symmetry of S.

**Lemma RS1 (completion from more than half a quarter).** If a left-right symmetric compact body fits its canonical lower supporting hallways at every angle in [0,alpha], where alpha>=pi/4, then it fits them throughout [0,pi/2].

**Proof.** Reflection supplies [L-alpha,L]. The two intervals cover [0,L] when alpha>=L/2. QED.

There is an actual continuous motion, not just a collection of unrelated placements. Put

$$c_S(t)=(f(t)-1)\mu_t+(g(t)-1)\nu_t.$$

Support continuity makes t -> c_S(t) continuous, and the canonical hallway equals c_S(t)+R_t L_0, where L_0 is the standard unit hallway. Thus t -> R_{-t}(S-c_S(t)) is a continuous feasible rigid motion. At the two axis angles it lies in the incoming and outgoing unit strips, so the free straight-arm translations can be appended. No interpolated placement is assumed feasible without the pointwise supporting-hallway inequalities.

Reflect vertically in y=1/2 to reduce an upper turn to the lower-turn statement. The vertical and horizontal reflections commute. Hence RS1 completes both turns independently whenever their original conventional magnitudes are at least pi/4.

## 2. Competitive symmetric bodies have both full turns

Suppose S is a compact connected ambidextrous body in the common incoming normalization 0<=y<=1, with vertical span one, and JS=S. If its area were greater than M, it would in particular exceed 8/5. The existing motion reduction supplies conventional endpoint magnitudes

$$\alpha,\gamma>\arccos(5/8)>\pi/4.$$

Here the last strict inequality is elementary: 5/8<1/sqrt(2), since 25/64<1/2. All intermediate angles in the two reduced motions are visited by continuity, and canonical support tightening preserves containment of S. RS1 then gives full canonical motions for both turns.

This uses only the earlier elementary strip/sign reduction, not the computer-assisted endpoint theorem TE1. It does not require the originally supplied motions to respect the reflection or have equal endpoints.

## 3. Central point faces are impossible above width two

The analytic width theorem AW-W excludes width at most two for a body of area greater than M. Write W>2 and projection [-W/2,W/2]. Reflection invariance of K=conv(S) makes both its horizontal exposed faces centered intervals about zero.

If either face were a single point, its abscissa would be zero. But

$$-W/2+1<0<W/2-1,$$

so the point lies strictly between the two unit end intervals. UC2 in [full-turn-unit-chord-obstruction.md](full-turn-unit-chord-obstruction.md) forbids such a central point face under both full turns. Therefore both horizontal faces have positive length.

No continuity of face length under small perturbations is used. The point-face case is excluded directly by the two-turn switching argument.

## 4. Positive centered faces must align

FD1 classifies two nondegenerate horizontal faces of a full-turn body with W>2. They either coincide, or lie in opposite unit end intervals.

Both reflection-symmetric faces contain zero. Neither end interval contains zero when W>2. The opposite-end alternatives are therefore impossible, leaving identical positive-length top and bottom faces. FAS1 applies and gives |S|<=M, contradicting the putative excess.

**Theorem RS2 (reflection-symmetric optimality).** Every compact connected ambidextrous body in the common incoming unit-span normalization, invariant under reflection in a line perpendicular to that strip, satisfies

$$\boxed{|S|\le M.}\tag{RS.2}$$

The reference construction has this symmetry and attains M. Thus the optimal value within this stated symmetry class is M. No curvature, contact-order, face-length, full-turn or symmetric-motion assumption is added.

## 5. What symmetry has not been proved

The conclusion is a theorem about actual bodies with the stated reflection symmetry, not a license to symmetrize an arbitrary competitor. Neither Minkowski averaging S with JS, taking their union or intersection, nor recentering individual vertical fibers has been shown to preserve both hallway motions and not decrease area. In particular, invariance of the optimization problem under J does not imply existence of a J-invariant maximizer in a nonconvex feasible class.

Consequently an unrestricted counterexample must break left-right symmetry in the common incoming coordinates. This does not eliminate the asymmetric end-point-face, opposite-end-positive-face or partial-turn configurations. The known near-reference asymmetric clipping families remain relevant.

The theorem does not claim that every shape possessing some reflection axis can be placed with that axis perpendicular to a valid common incoming strip. The symmetry is imposed on the specified incoming representation, which is the one used by the motion and width reductions.

This closes a natural geometric class and shows exactly where a symmetry-reduction proof could finish the unrestricted value. Such a reduction is not supplied here. All new steps are pen-and-paper; no CI, Lean/Lake compilation, long script, dependency installation or manuscript build is used.
