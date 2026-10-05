# Paper integration: a parallel proof, presented in a side subsection

**Status.** PR #5 now preserves both original formalizations. Its earlier
changes to `MovingSofaUniqueness/Main.lean` and `scripts/Audit.lean` were
reverted exactly. The new route is implemented in three added modules, with
an independent audit script; it has **not been compiled or kernel-audited**
in this work. The manuscript TeX and `main.pdf` are unchanged.

These notes supersede the earlier proposal to make the new route the
backbone of the manuscript. The policy is **complete parallel formalization,
minimal paper integration**. The main uniqueness proof may continue to use
Baek's original optimality theorem.

## 1. Where to add the discussion

Add a compact subsection, **"Optimality revisited"**, at the end of Section 8,
after the equality analysis and `thm:caps`. Give a proposition and its proof,
not merely an assertion that dependencies could be rearranged. Explain that
this is a second logical route sharing the same intermediate mathematics,
not a replacement for the main proof.

Only small accompanying changes are needed:

- In `01-introduction.tex`, add one paragraph near the end of the proof
  strategy, pointing to the alternative route and retaining Baek's priority.
- In `08-equality.tex`, add the subsection outlined below. Identify the exact
  maximality-level inputs rather than citing corollaries that already assume
  Baek's global bound.
- In `10-formalization.tex` and `a3-lean.tex`, describe the separate entry point
  and audit, and add the new declarations to the dictionary. Update the
  verification commit/status only after they have actually been checked.

Do not restructure Sections 2--3 or 6--9 solely to add this observation.
In particular, `fact:optimal`, the original envelope reduction, and the main
uniqueness assembly may stay as they are. Their use in the main proof is
legitimate; the side subsection explicitly does not use them as inputs to
its alternative bound.

Do not update the PDF or claim that it contains the subsection until the TeX
has been intentionally edited and the paper regenerated in a later pass.

## 2. The circularity boundary for the subsection

The alternative proof may use:

1. Gerver's explicit feasibility and `M = |G| > 11/5`, including
   `A_(pi/2)(K_G) = M`.
2. Baek's fixed-angle existence and comparison theorems, 3.5.2--3.5.6: there
   is a maximizing cap whose cap-minus-niche set is a monotone moving sofa,
   and its area dominates every moving sofa with that angle.
3. Baek's initial angle theorem 1.5.1 and the ordinary monotonization facts.
4. The restricted-domain quadratic comparison
   `A(K) <= Q(x_K) <= Q(x_G) = M` for caps in the injectivity domain.
5. The new selection, variation, curvature, pinned-bound, and Mamikon
   equality results at their actual-maximality or restricted-domain level.

It must not use Baek's Theorem 1.1.1, the universal upper bound in
`fact:optimal`, or a wrapper that depends on those results. In particular,
do not simply cite `cor:Ki` or the existing proof of `thm:caps` to justify
injectivity or classification of an actual maximizer: their equality-area
formulations use the old bound. Use the primitive maximality statements
spelled out below instead.

The existence input remains explicit. "Every maximizer is Gerver" alone
would not imply that a maximum exists. The selected maximizing sofa in the
optimality comparison need not contain the original sofa; containment is
proved separately for the equality case.

## 3. Suggested mathematical content

The following is a prose draft for the subsection, not a claim that the
manuscript or the new Lean code has already been verified.

### Optimality revisited

The main proof uses Baek's optimality theorem to turn equality with Gerver's
area into maximality. The maximality-level results also give an alternative
proof of that upper bound. In this paragraph we use Baek's fixed-angle
existence and comparison theorems and the restricted-domain quadratic
bound, but not his final optimality theorem or its consequences.

**Proposition.** The maximizer principles, together with those intermediate
results, imply that every moving sofa has area at most `M = |G|`. Moreover,
a right-angle cap maximizes `A_(pi/2)` if and only if it is a horizontal
translate of Gerver's cap.

**Proof.** Let `K` actually maximize `A = A_(pi/2)`. Gerver's cap is a
competitor, so `A(K) >= M > 11/5`. Apply the selection and curvature theorems
using actual maximality and positive area. They give the injectivity
condition. Since `|K| >= A(K) >= M`, the cap also meets the area threshold
in the injectivity domain. Thus

```math
M\leq\mathcal A(K)\leq\mathcal Q(\xi_K)
 \leq\mathcal Q(\xi_G)=M.
```

Both comparisons are equalities. The Mamikon equality analysis gives
`h_K(t)-h_(K_G)(t)=a cos(t)` on `[0,pi]`, hence

```math
K=K_G+(a,0),\qquad
K\setminus\mathcal N(K)=G+(a,0).
```

A right-angle maximizing cap exists. Comparing any right-angle cap with it
therefore gives `A(C) <= M`. Horizontal translations of `K_G` attain `M`,
which proves the converse classification. The fixed-angle comparison
property then bounds every sofa with a right-angle motion by `M`.

Now let `S` be any moving sofa with `|S| >= 11/5`. The initial angle theorem
gives an angle `omega` in `[arcsec(11/5),pi/2]`. Choose a fixed-angle
maximizing monotone sofa `T`, so `|T| >= |S| >= 11/5`. The pinned-bound
argument applies to its maximizing cap without requiring `|T| = M`; it
gives `R_(pi/2-omega) T` a right-angle motion. Consequently

```math
|S|\leq |T|=|R_{\pi/2-\omega}T|\leq M.
```

Sofas of area less than `11/5` satisfy the bound because `M > 11/5`.
Gerver's sofa is feasible, so this proves global optimality. The all-angle
cap bound follows by comparison with a fixed-angle maximizing monotone
sofa. Finally, using this newly proved bound in the own-envelope and
regular-closedness arguments recovers every equality-case sofa as a rigid
image of Gerver's sofa, as a set. This last argument preserves the given
sofa through its own envelopes; it does not assert that the numerical
comparator `T` contains it. QED.

The paper may omit that last recovery sentence from the proposition and
refer to the parallel formal development instead, since set recovery is
already the main subject of Section 9. It must not suggest that concavity
alone supplies uniqueness: the Mamikon-kernel and recovery arguments are
substantive.

## 4. Suggested introduction and verification wording

After the new route has been compiled and its transitive dependencies
checked, a suitable introduction paragraph is:

> Although the main proof uses Baek's optimality theorem, the maximality-level
> arguments also recover optimality from his intermediate results without
> invoking his final theorem. The same comparison determines the value and,
> through its equality case, identifies all right-angle maximizing caps.
> We describe this parallel proof in the subsection "Optimality revisited"
> and formalize it separately, leaving the original proof route unchanged.

Until verification, use wording such as "the repository contains an
uncompiled Lean implementation of this parallel route" rather than
"Lean has verified its independence". A checked base commit does not
certify declarations added afterward.

Use "an alternative assembly from Baek's intermediate results" or
"a maximizer-first strengthening of Baek's argument". Avoid "independent
of Baek's methods", "a solution from first principles", or "uniqueness
for free". The fixed-angle existence construction and the quadratic
functional remain Baek's central contributions.

## 5. The parallel formalization

The added modules are:

| File | Purpose |
| --- | --- |
| `MovingSofaUniqueness/Maximizers.lean` | Actual maximality gives geometry, value, and cap rigidity |
| `MovingSofaUniqueness/Optimality.lean` | Right-angle cap classification and global optimality |
| `MovingSofaUniqueness/Alternative.lean` | Independent envelope assembly and exact-set uniqueness |
| `scripts/AuditMaximizerRoute.lean` | Separate axiom/dependency audit and negative controls |

Import `MovingSofaUniqueness.Alternative` for the complete route. All names
in the following dictionary are in `MovingSofaUniqueness.MaximizerRoute`:

| Mathematical step | Declaration |
| --- | --- |
| Fixed-angle existence/comparison | `exists_maximizing_cap` |
| Gerver as a competitor | `gerver_le_of_maximizes` |
| Injectivity from maximality | `isKi_of_maximizes` |
| Determine the right-angle maximum value | `right_angle_maximizer_value` |
| Identify the cap and sofa | `right_angle_maximizer_eq_gerver` |
| Both directions of cap maximality | `right_angle_maximizes_iff_translate_gerver` |
| Right-angle inequality with equality cases | `right_angle_optimality_and_rigidity` |
| The fixed-angle maximizing sofa's motion | `maximizing_monotone_has_right_angle` |
| Global optimality | `gerver_sofa_optimal` |
| All-angle cap bound | `cap_area_le_gerver` |
| Preserve the specified sofa | `equal_area_envelope`, `maximizer_contained_in_gerver` |
| Exact-set equality case | `image_eq_gerver_of_volume_eq`, `volume_eq_gerver_iff` |
| Optimality and uniqueness together | `gerver_sofa_optimal_and_unique` |
| Global maximizer classification | `isMaximal_iff_image_eq_gerver` |

The full prefix is important: for example,
`MovingSofaUniqueness.image_eq_gerver_of_volume_eq` is the original theorem,
whereas `MovingSofaUniqueness.MaximizerRoute.image_eq_gerver_of_volume_eq`
is the new parallel proof. Do not conflate their dependency claims.

## 6. Verification obligations and preservation

No compilation, Lean audit, Comparator, or CI was attempted for this work.
For a later authorized pass:

- Build the new entry point and run the separate audit. It checks all new
  module declarations for standard axioms and for transitive dependence on
  `MovingSofaOptimality.theorem1_1_1`, `gm_area_le`, or any declaration owned
  by the original uniqueness `Main`. It traverses numbered results and
  helpers, and must pass its negative controls on the original proofs.
- Review the actual theorem types and the prose correspondence. Keep the
  feasibility, positive-area, angle, cap, and moving-sofa hypotheses.
- Confirm the cumulative PR diff leaves every pre-existing file untouched.
  The original proof routes, audit, Challenge/Solution, bridge, and paper
  section line numbers therefore remain intact.

`Solution.lean` intentionally continues to use the original optimality and
uniqueness proofs. The original audit intentionally does not import the new
modules; it is not a substitute for the added audit. No registry or original
verification claim should be silently extended to cover the parallel route.
