# 7. Proof ledger and next mathematical obligations

This ledger describes the first pen-and-paper research pass. "Written proof" means a proof supplied in these notes and self-reviewed for its stated hypotheses. It does not mean independent refereeing, a computer-assisted proof, or Lean verification.

## 7.1 Results and their actual domains

| Result | Status | Scope and limitation |
|---|---|---|
| Propositions 1–3: two-motion envelope, connected saturation, largest component | Written proof | Fixed witnesses and a compact box. Does not prove existence of a globally optimal motion pair. |
| Lemma 4: exact recovery from area equality | Written proof | The larger set must be regular closed; the smaller set must be closed. |
| Proposition 5: common convex outer set minus two swept niches | Written proof | Arbitrary witness motions. Does not make the common outer set a canonical one-turn cap. |
| Proposition 6 and Corollary 7: overlap identity and budget | Written proof | Finite-area measurable sets; no injectivity assumption. |
| Lemma 8: niche ceiling and overlap slab | Written proof | The stated quarter-turn quadrant representation only. No universal separation theorem. |
| Theorem 9 and Corollary 10: partition majorant and exact slack | Written proof | Arbitrary measurable niches. A sharp global analytic majorant is still missing. |
| Lemma 11: local mask tightness | Written proof | A restricted angular representation with a strict separation margin. |
| Lemma 12: exact candidate root bounds and area-parameter identity | Written proof | The connection between the benchmark area and the geometric candidate is cited from Romik. |
| Theorem 13: exact candidate corner-height maximum below 1/2 | Written proof from cited path formulas | Establishes candidate niche separation and zero mask loss, not optimality. |
| Proposition 14: common incoming pose | Written proof | May prepend pure translations; does not give monotone angular motion. |
| Lemma 15: masked finite variation | Written proof | Measurable envelopes; directly identifies the missing second-motion mask. |
| Proposition 16 and common-arc calculation | Written proof under smooth hypotheses | Not a differentiability theorem for arbitrary swept envelopes or a proof of admissibility of shape variations. |
| Theorem 17: optimality and uniqueness from the five-defect certificate | Conditional theorem, with proof | Coverage, clipped-area estimates, sharp bound, geometric rigidity, and regular-closed recovery hypotheses must be supplied. |
| Lemma 18: quadratic comparison identity | Written proof | No ambidextrous quadratic form satisfying its sign assumptions has been constructed here. |

## 7.2 The dependency graph

The following parts are already established within their stated domains:

```text
arbitrary posed two-turn body
  -> common incoming pose (14)
  -> exact two-motion envelope (1)
  -> common convex outer set and two swept niches (5)
  -> globally valid partition majorant with exact mask loss (9)

Romik's specified path formulas [external input]
  -> exact root bounds (12)
  -> strict candidate ceiling (13)
  -> zero candidate mask loss, robust under small independent path perturbations
```

The missing chain is:

```text
explicit clipped-niche estimates a,b
  + a sharp global bound Q <= M on a covering normalized witness class
  + rigidity of simultaneous equality
  + regular-closedness of the identified envelope
  -> optimality and exact body uniqueness (17)
```

Theorem 17 does not assume a global maximizer exists. A feasible candidate of area M, together with a pointwise upper bound, supplies attainment. Thus a global compactness theorem need not be the first research task on this route.

## 7.3 Self-review checks performed

**Set algebra and sign.** The removed region is a union. Its overlap enters surviving area with a plus sign. The partition identity was checked on all four membership cases: neither niche, lower only, upper only, and both. The all-overlap example and the constant-weight example detect incorrect double subtraction.

**Representation.** Endpoints are included, motions are independent, initial body orientations are specified, and connectedness is recovered via components rather than assumed for an intersection. A compact box is chosen per witness; it is not a hidden uniform diameter estimate. The exact common outer-set representation works before any reduction to monotone motion.

**Normalization.** A fixed midline is used only after common-pose normalization for a proposed global comparison. The raw set identities hold in any coordinates. No separate transverse alignment or symmetric motion assumption is hidden in the normalization proof.

**Candidate algebra.** The sign test at 2-sqrt(3), the upper root bound 1/3, and the identity X=1+4Y^2 are exact. In the height proof the first-phase coefficient is nonpositive, so replacing cos(t) by its lower bound reverses neither inequality. The middle-phase derivative has the required strict sign because R>2sqrt(2)/3. The late phase is a reflection of the first. The resulting separation margin is positive by R<sqrt(2).

**Equality.** Zero area loss is not identified with equality of compact sets without the regular-closed hypothesis. Scalar-parameter uniqueness, equality of envelopes, and uniqueness of motion witnesses are distinct statements. Only body uniqueness is targeted.

**Variations.** The exact finite-difference identity counts only changes surviving the opposite envelope. The smooth derivative is restricted to transverse finite intersections. Co-oriented shared arcs use min/max one-sided derivatives; generic sofa differentiability and variation admissibility remain unproved.

## 7.4 Three next proof tasks

### A. A two-path first-order diagnostic at the candidate

Use the explicit candidate paths, but allow independent perturbations of both witnesses. The strict separation margin means the mask loss vanishes locally in the fixed angular representation. Derive the remaining first variation of the common outer-set/clipped-niche functional, including shared outer-boundary arcs and any one-sided terms. A symmetric one-parameter contact calculation is not sufficient.

Deliverable: a stated admissible variation class and a proved first-order inequality (or a specific countervariation to the proposed majorant). Do not call it global optimality.

### B. An explicit clipped-niche lower bound

Construct functions a(z) and b(z) that lower-bound the appropriate half-plane portions of the swept niches. Candidate equality must be proved, not inferred from the full-niche area formula. Any sweep integral must account for multiplicity, clipping endpoints, and intersections with the common outer set. Avoid applying a full-niche bound unchanged after clipping.

Deliverable: a written geometric inequality, its precise witness domain, and its equality conditions. If the domain is narrower than the full normalized class, record the coverage theorem needed to reach it.

### C. The sharp global certificate and its kernel

Investigate whether the resulting Q admits a global comparison with candidate value M, for example through Lemma 18. Check the joint quadratic form in symmetric and antisymmetric directions and any cross terms. The global comparison must cover the entire stated domain, not just the candidate's contact cell.

Deliverable: either a proved comparison and a characterized equality kernel, or an explicit obstruction showing this particular relaxation is too large. Extra disconnected envelope components, mask slack far from the candidate, and unreduced angular histories are legitimate obstruction tests. None alone disproves optimality of Romik's body.

## 7.5 Provenance and execution record

The foundational set/measure lemmas are elementary and carry no novelty claim. The candidate is Romik's construction; the majorant/rigidity organization is motivated by Baek and the repository's uniqueness work. This pass is not a comprehensive priority or literature audit, and no claim is made that the candidate separation calculation is new.

All changes are Markdown under `docs/ambidextrous/`. The existing manuscript, Lean source, dependency files, and workflow definitions are unchanged. No CI run was requested, inspected, or used. No Lean/Lake compilation, dependency installation, numerical experiment, CAS calculation, or manuscript build was performed. Commits carry `[skip ci]`.

Global optimality and uniqueness remain unproved in this branch because the sharp clipped-niche certificate and its rigidity have not yet been established, not because a stationary candidate or a formal theorem statement was unavailable.
