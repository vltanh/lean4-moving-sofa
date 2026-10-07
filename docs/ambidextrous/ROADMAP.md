# Active roadmap: extend a proved clipping budget to the full opposite-face class

**Unrestricted optimality is not proved.** The new TC/RB/STW hand arguments pay the positive clipping correction on explicit reference-tail domains. They bound fully saturated arbitrary convex boundary-layer cuts and permit some outward tail changes. Middle supporting data remain fixed. These restrictions are not known for every competitor or every maximizer. Unrestricted uniqueness remains deferred.

Read [HANDOFF.md](HANDOFF.md) and [tail-pairing-review.md](tail-pairing-review.md). The global supremum reduction is in [positive-face-density-review.md](positive-face-density-review.md). All written proofs are self-reviewed, not independently refereed or kernel-verified.

## 1. Acceptance criterion and execution policy

For one attained unrestricted ambidextrous maximizer, prove its ordinary area is at most

$$M=1+4Y^2+\arctan Y,\qquad4Y^3+3Y-1=0,\quad Y>0.$$

Do not require unrestricted equality classification first. Prefer hand proofs and brief checks that can reject an incorrect premise or confirm explicit arithmetic. New script invocations are capped at 30 seconds, preferably external five/ten-second limits. No long optimization or repeated refinement without a new instruction. **No CI, Lean/Lake compilation, dependency installation or manuscript build.** Commit substantive findings, positive and negative, with `[skip ci]` under docs/ambidextrous.

## 2. A sharp clipping comparison now proved on a stated domain

The full-turn two-cap identity, for nonempty surviving fibers, is

$$|E|=\Psi(U)+\Psi(V)+G,\qquad G\ge0,$$

where Psi(U)=|U|-|N(U)|-W(U)/2 subtracts the full positive niche. With Delta(U)=M/2-Psi(U), the sharp target is G<=Delta(U)+Delta(V).

[TC](tail-paired-cut-deficit.md) proves a stronger per-cap estimate for arbitrary inward support changes near the top normal, retaining the reference middle supports:

$$\boxed{\Delta(U)\ge\int_a^b(1-A_U(x))dx.}$$

Here [a,b]=[-m/2,m/2] is the reference face interval, not a presumed face of U. The pointwise mechanism is

$$n_*(b-d)-n_U(b-d)\le\frac{h_*(t)-h_U(t)}{\sin t}
\le A_*(b+d)-A_U(b+d),\quad t=\pi/2-\arcsin(2d).$$

A single known reference parameter lower-bounds the new niche, while an outer supporting line upper-bounds the new cap roof. The companion wall is checked. Pairing the two abscissae preserves measure and pays niche savings by outer-flank losses. Cap loss beneath the old face remains to pay clipping. No moved-face derivative energy or assumed new contact pattern is used.

### Concrete boundary-layer theorem RB

Set eta=2 arctan(1/10), so cos eta=99/101 and sin eta=20/101. [RB1](reference-belt-saturation-bound.md) proves

$$\boxed{K_*\cap\{1/101\le y\le100/101\}\subseteq K\subseteq K_*
\quad\Longrightarrow\quad |E(K)|\le M.}$$

E(K) is the full canonical saturation, not merely K intersected with the old reference. It is compact, connected and full-turn feasible. Its actual hull need not equal K, and that equality is not assumed. Arbitrary independent upper/lower convex shavings in those layers are allowed, including point faces and nonsmooth changes.

A separately given body S with hull K still needs both full turns to infer S subset E(K). The theorem does not erase missing-angle restrictions on an arbitrary partial-turn S.

### Signed extension STW

[STW](signed-tail-window-comparison.md) allows outward support changes as well. The cap contains the full half-height rectangle, lies in the unit-height strip, equals the reference support outside the top-normal window, and satisfies

$$h_U(\theta)\le1+(m/2)|\cos\theta|$$

inside it. The same independent conditions apply to V. The possible upward first-wall displacement is at most 1/99 while its fixed companion clearance is at least 19/8. The paired inequalities therefore hold with signed cap/niche differences. Niche confinement and the half-height bounds give nonempty fibers, and the full positive correction is paid:

$$\boxed{G\le\Delta(U)+\Delta(V),\qquad |E|\le M.}$$

Nontrivial outward smooth bumps are explicitly admitted. These proofs use the reference construction only, **not WV, its source-flux limit, Gerver's theorem, or the earlier large certificates**.

## 3. What the new domain does not cover

Neither TC nor STW permits arbitrary changes of the middle supports. RB fixes a whole central belt and prohibits outward hull changes; STW relaxes the latter only within an angular window and under explicit barriers. Arbitrarily small perturbations of the middle arcs can violate these exact conditions.

Thus this is not a complete Hausdorff or C1 neighborhood theorem. No compactness or proximity argument has put every maximizing body into this class. PD's approximation changes incoming orientation and preserves limiting area, but does not impose reference-based middle supports.

A genuine next extension must pay for changing the middle supports, or prove a separate admission/replacement theorem that yields these hypotheses while preserving the required area inequality. Repeating the clipping identity or renaming the remaining class would not supply that step.

## 4. Global full-turn target and the no-uniform-gap obstruction

RR preserves existing hallway motions by shrinking and disk rounding with budget lambda+2r=1. Connected shallow strip shavings produce actual positive face chords. PD chooses a nearby record width and a further small shrink to justify a full safe-strip bridge, then transports full motions to a new unit-span orientation. Areas converge from below and the two positive faces separate.

The existing width and face restrictions put competitive approximants in opposite unit end strips. PS1 permits full same-hull saturation. Therefore

$$\boxed{\sup_{\rm full-turn}|S|=\sup_{\rm saturated\ positive\ opposite-face}|S|.}$$

Point faces no longer need an independent upper-value theorem if that positive-face class is bounded. The restricted class is not claimed to attain its supremum; face lengths can vanish in an extremizing sequence.

The reference itself has positive opposite-face approximants with areas below M tending to M. There is no fixed epsilon>0 bounding that whole class by M-epsilon, even after requiring saturation. Do not launch a search for such a gap. The class carries the full unresolved full-turn supremum.

The remaining full-turn acceptance theorem is still |E|<=M for every member of that class, with all actual-area and angle hypotheses checked. TC/RB/STW prove it only for the admitted portions described above.

## 5. Partial turns remain separate

SI3--SI4 complete partial motions when the interval of required outgoing strip normals is entirely safe, meaning width at most one throughout. An intervening width bump above one remains unhandled. Three separate safe normals do not imply the bridge.

RR preserves the old safe-strip set exactly, and PD begins with full turns. RB constructs a full-turn E(K), but an arbitrary partial-turn body with the same hull need not be contained in it. A proof of full-turn optimality therefore still requires an additional partial-turn reduction or upper bound for unrestricted closure.

## 6. Earlier results retained, with their hypotheses

WV2 gives the signed weighted cap maximum M/2 in the written PA/WP/WR, AR/PT/TS/EB, TF/HF, CG/SE, VE/WV, SR/AF chain. SE uses the established Gerver area bound on a genuine one-turn body. VE's limiting two-source exposure argument remains a principal independent-review point. No arbitrary two-turn cap is assigned weighted maximality.

FAS bounds every full-turn aligned positive-face body. SCG/CSF force full turns in additional retained-point regimes; FL/LF cover long faces. FD/UC classify positive full-turn faces and exclude central point faces. RS bounds the left-right reflection-symmetric common incoming class, not arbitrary maximizers by an unproved symmetrization.

Analytic AW-W/SW and AL restrict competitive width; AM/TE retain their scoped exact computational exclusions. They are not complete global coverage or premises of TC/RB/STW.

## 7. Failed shortcuts and bounded tests

RA1 and MCA1 reject naive averaging of actual sets and the analogous convex-cap enclosure. Earlier AF4, GR1, AX1/SAT1, SAC2, SC3, TR1 and AO1 controls remain in force. Repair, saturation, data admission or proximity alone do not pay actual-area corrections. Canonical-wing formulas retain negative winding and uncovered surviving material.

The new [FF](face-filling-budget-obstruction.md) rejects the universal claim that filling a cap's top segment increases Psi by at least the convex cap area added. A disk cap with no positive niche becomes a square with a positive niche triangle. That intermediate inequality fails exactly. The narrower final deficit comparison TC/STW is not refuted by this example.

A separate, more restrictive filling conjecture had no sampled violation among 12 prescribed cuts and 32 prescribed convex-hull point sets. This is inconclusive and is not a theorem. The scripts use finite quadrature with no certified error sign and were bounded by five-second limits. No global search or complete covering was run.

The exact checker `computer-assisted/check_tail_pairing.py` passed 12 named checks, 72 signed local-line cases, 144 paired-fiber identities and three negative controls under a five-second cap; internal time was about 0.0064 seconds. Its executed source hash matches the committed blob. These checks do not verify the continuum proof or cap admission. See [the review](tail-pairing-review.md) and the JSON execution record for provenance.

## 8. Next-session discipline

Read the handoff and review before invoking the new clipping budget. If an actual gap is found, identify and repair that implication. Otherwise pursue middle-support control or a specific uncovered partial-turn comparison. Keep actual points, nonempty fibers, full-turn premises, all signs and supremum-versus-attainment distinctions visible.

No unproved global localization, symmetric-maximizer existence or reference support agreement is supplied by the latest theorem. Commit substantive findings frequently, including failed proposed inequalities. The PR remains open and draft; unrestricted optimality and independent verification remain unfinished.
