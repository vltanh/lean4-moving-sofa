# Active roadmap: a sharp opposite-face bound, not a uniform exclusion gap

**Unrestricted optimality is not proved.** The newest RR/PD/PS hand proofs show that the saturated positive opposite-end-face class carries the entire full-turn supremum. They remove point faces as a separate upper-value obligation, but do not bound that supremum. Remaining partial-turn bodies with an unsafe strip bridge still need an additional argument. Unrestricted uniqueness stays deferred.

Read [HANDOFF.md](HANDOFF.md) and [positive-face-density-review.md](positive-face-density-review.md). All written results are self-reviewed; the historical proof chain has not been independently refereed or kernel-verified.

## 1. Target and runtime policy

Prove the ordinary area of an attained unrestricted ambidextrous maximizer is at most

$$M=1+4Y^2+\arctan Y,\qquad4Y^3+3Y-1=0,\quad Y>0.$$

One attained maximizer suffices for the value. Do not impose unrestricted uniqueness first. Prefer pen-and-paper proofs, with short checks to reject faulty premises or verify explicit algebra. Maximum 30 seconds per invocation, preferably external five/ten-second limits. No long optimizer campaign or repeated refinement without a new instruction. **No CI, Lean/Lake compilation, dependency installation or manuscript build.** Commit substantial positive and negative findings with `[skip ci]`, under docs/ambidextrous.

## 2. New full-turn reduction: positive opposite faces suffice

[RR1](rounded-strip-regularization.md) proves that

$$R_\lambda=\lambda S+\frac{1-\lambda}{2}B$$

preserves every canonical hallway containing S. The same rounding preserves the exact set of straight-strip normals whose width is at most one. Shaving each of two opposite supports by less than the rounding radius leaves the connected center set lambda S intact and creates two actual positive-length support chords. Connectedness follows from a union of convex disk portions attached to those centers.

[PD2](full-turn-positive-face-density.md) chooses a width-record normal just outside the safe-strip component. Semiconvex width estimates control the entire bridge after shaving; a further shrink makes that whole interval safe. SI2 transports the full motions to the new unit-span incoming orientation. The positive left derivative of width makes the two horizontal faces strictly separated. Their areas converge to the original area, and can be chosen strictly below it.

For competitive bodies, AW-W and FD1 place those positive faces in opposite unit end strips. Therefore

$$\boxed{\sup_{\rm full\ turns}|S|=\sup_{\rm positive\ opposite\ faces}|S|.}$$

PS1 in [the review](positive-face-density-review.md) additionally saturates every approximant at its actual hull. The fibers remain nonempty intervals, the envelope is connected, its hull and faces are unchanged, and area does not decrease. Thus the same supremum is obtained over **saturated positive opposite-end-face bodies**.

This is a genuine value reduction: a full-turn body above M would give a positive opposite-face body above M. It is not a theorem that every full-turn maximizer can be chosen with those positive faces. The approximating face lengths can vanish, and this subclass need not attain its supremum.

## 3. A negative result that prevents the wrong computer strategy

Applying the from-below approximation to the reference gives actual positive opposite-end-face full-turn bodies with

$$|S_j|<M,\qquad |S_j|\to M.$$

Thus a fixed epsilon>0 cannot make the whole remaining positive-face class satisfy |S|<=M-epsilon. Saturation does not restore such a gap. Excluding literal point faces does not make the remaining geometry a uniformly suboptimal exception.

This is stronger than merely finding point-face perturbations near the reference. The unresolved positive-face class itself carries the whole full-turn supremum. A sharp hand theorem, a valid limiting argument, or a computer/local combination with its exact residual class is still needed. Counting fewer face alternatives is not evidence that a small final estimate will finish the proof.

FD3 is not contradicted: it excluded aligned positive-face approximants at fixed unit span; PD constructs separated faces and changes the incoming orientation through a proved safe-strip bridge.

## 4. Exact full-turn acceptance target

It now suffices to prove

$$\boxed{|E|\le M}$$

for every compact connected full-turn canonical envelope E whose unit-span hull has positive faces in opposite unit end strips, at competitive widths. A proof on this class covers point-face limits by PD/PS. A statement only about an attained maximizer inside the positive-face subclass is insufficient unless such attainment is separately justified.

For actual cap pairs with the same hull and nonempty fibers, the exact accounting is

$$|E|=\Psi(U)+\Psi(V)+G,\qquad G\ge0.$$

The written weighted theorem supplies

$$\Psi(U)\le M/2,\qquad\Delta(U)=M/2-\Psi(U)\ge0.$$

Thus one sufficient sharp comparison remains

$$\boxed{G\le\Delta(U)+\Delta(V).}$$

This is a target, not a theorem that the clipping is paid. An ordinary-area comparison avoiding the cap decomposition, or a justified reduction to an admitted class, would also suffice. No signed-area replacement can omit positive clipping, negative winding or uncovered surviving material.

The main missing upper bound has not been supplied by RR/PD. The new construction keeps feasibility and limiting area, but does not increase the area of an actual maximizer at a finite step.

## 5. Partial turns remain a separate obligation

[SI3--SI4](strip-interval-completion.md) transport a partial-turn body to full turns when its entire interval of relevant outgoing strip normals has width at most one. These are actual motions of the same body, followed to a unit-span endpoint of that safe component.

The remaining partial-turn case has a width bump above one on that interval. Width at most one at three separate directions does not establish a safe bridge. RR's unshaved safe-strip set is unchanged, and PD starts from already full motions. Neither is a universal partial-turn completion theorem.

Therefore unrestricted closure still requires both the full-turn sharp target in Section 4 and a value bound or full-turn reduction for the uncovered partial-turn configurations. A theorem on one attained unrestricted maximizer may combine these tasks, but cannot assume its motion endpoints.

## 6. Previously established written inputs and classes

**Weighted one-turn value WV2.** The cap problem subtracts the entire positive niche. PA/WP/WR give attainment, selected polygons and regularity; AR/PT/TS/EB give same-sign estimates, a positive top, half-height niche and exact limiting exposure. TF/HF give confinement and a stationary core. CG/SE force one good quarter using the known ordinary Gerver area bound on a feasible one-turn body. VE's visible-source lower bound and WV's energy contradiction force the other good, then SR1/AF3 give the value. VE's continuum source-flux limit remains a principal independent-review point. No arbitrary two-turn cap is assigned weighted maximality.

**Aligned faces and symmetry.** FAS bounds every full-turn aligned positive-face body. SCG/CSF give additional conditions forcing full turns; FL/LF cover long faces without assuming them. RS bounds the left-right reflection-symmetric common incoming class using complementary-angle completion, UC and FD. None proves the existence of a symmetric unrestricted optimizer.

**Width/angle restrictions.** AW-W and SW give competitive width >1001/500; AL gives width <=2999/1020. AM/TE retain scoped exact computational exclusions, including the endpoint-angle bound beyond sixty degrees. They are not a global sharp covering and are not inputs to RR/PD beyond the explicitly cited analytic width localization.

## 7. Failure controls

RA1 rules out naive reflection averaging of actual nonconvex bodies. MCA1 rules out the analogous convex-cap averaged enclosure on a feasible double-cut reference family: its actual area loss is smaller-order than its averaged weighted loss. RR differs because its rounding budget is paid by shrinking; no finite area monotonicity is assumed.

The earlier controls AF4, GR1, AX1/SAT1, SAC2, SC3, TR1 and AO1 remain relevant. The canonical-wing identity keeps both negative winding and uncovered material. Saturation and auxiliary data admission do not by themselves prove an area inequality. A finite support grid is not a C1 neighborhood. Small extreme-height difference does not center the endpoints at one half.

The occupancy relaxation's fractional barriers still prevent a resolution-only fix of the unconditioned LP. Do not launch a long search for the uniform opposite-face gap that Section 3 now disproves.

## 8. Execution record and next-session discipline

`computer-assisted/check_positive_face_density.py` ran under a five-second cap in about 0.007 seconds internally. Its 93 named checks include 80 depth budgets, 101 rational convex-strip samples and four negative controls. The JSON record matches the executed Git blob. These regressions do not verify the continuum approximation, saturation connectivity or the historical motion/width chain.

Two earlier exploratory five-second-capped rectangle/parallelogram tests supplied neither a sharp bound nor a continuum feasibility certificate. They are recorded as unsuccessful discovery, not proof inputs. No large search was run.

Read RR/PD/PS with the review. If a specific implication is wrong, state and repair it. Otherwise pursue the sharp saturated opposite-face bound or a genuinely uncovered partial-turn comparison. Do not reopen solved auxiliary optimization merely to generate more lemmas. Keep supremum-versus-attainment, actual support witnesses, safe-angle coverage and correction signs explicit. The PR remains open and draft; unrestricted optimality and independent verification remain unfinished.
