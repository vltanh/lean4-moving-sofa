# Four-direction first pass: results, rejected shortcuts, and priorities

**All four requested directions were attempted. Neither general optimality frontier is closed.** This review distinguishes the new hand arguments, the exact finite calculations, and the mathematical work still needed. Baseline: `80fb626e5672d9bb66a52c88d4b1b027b6c62e11`. The initial plan is `four-direction-research-plan.md`.

## 1. Actual maximizers: second-order rejection and critical-face reduction

Read [Direction 1](direction-1-critical-face-reduction.md).

Review found that the repository already has the intended finite two-turn balance equations in Notes 21, 53 and 54. Their unresolved terms are geometric constraint multipliers and hidden outer boundary, not missing elementary differentiation. Note 67 also leaves specific outer/inner-corner and density obstructions. None was silently discarded.

The first attempt therefore used second-order information: a feasible critical direction v with grad F dot v=0 and v^T H v>0 proves an area improvement on its actual finite chart. More generally, a quadratic polynomial on a compact polytope has a global maximizing representative either at a vertex or at the unique stationary point of a face with negative definite restricted Hessian. Singular stationary ridges can be followed to smaller faces without changing value. With rational fixed-angle geometry this gives a finite rational candidate list for the bounded finite problem.

The exact test rejects a stationary saddle in a connected two-position unit-hallway envelope. Its area is 25/98 at the balanced point and 125/392 at the two maximizing box vertices. Four additional quadratic fixtures test interior concavity, a singular ridge, convexity and a linear objective.

**Outcome:** useful finite structural rejection/candidate mechanism, not the desired continuum curvature theorem. **Next gate:** apply it to actual unresolved geometric charts, retaining all constraints, or prove a uniform family of feasible critical directions at noncandidate maximizers. Merely enumerating an abstract finite list does not make its potentially enormous size manageable.

## 2. Coupled duality: scalar weights fail; spatial allocation remains

Read [Direction 2](direction-2-overlap-safe-duality.md).

The tested dual subtracts weighted forbidden area from a genuine outer enclosure and requires the total charge at every point to be at most one. It includes both turns from the start. On an exact four-hallway configuration with actual finite hull [0,3/2] times [0,1], each triangle has area 8/75 and each same-turn overlap has area 37/448. The true remaining area is 20807/16800.

Unweighted swept-area subtraction incorrectly gives 161/150, below the actual envelope. The exact optimal constant-weight dual instead gives 193/150, above it by 809/16800. Thus neither unweighted subtraction nor one scalar weight per quadrant gives sharp area accounting. The reference's common finite lower-quadrant overlap forces all its scalar lower weights to sum to at most one, so refining the angle list does not remove that particular obstruction.

A spatial priority allocation counts each point once and retains every exclusive forbidden piece. Robust subsets of the quadrants make such allocations valid across parameter boxes; Direction 3 implements that option.

**Outcome:** reject the unsplit constant-weight proposal, not all coupled duality. **Next gate:** a spatial allocation valid and sharp enough over every relevant placement branch. No universal certificate is claimed.

## 3. Finite-angle global exclusion: one whole parameter box certified

Read [Direction 3](direction-3-robust-finite-angle-box.md).

Four selected hallway frames use rational normal coordinates 3/5,4/5 and their reflected counterparts. All eight offsets vary independently by up to 1/20 around the stated rectangular support values, and the body lies in [0,49/20] times [0,1]. Shrinking the forbidden quadrants to their offset lower bounds gives a fixed robust removal region. Its complement has exact area

$$709/480<8/5<M.$$

The note integrates the three left-lobe pieces by hand, reflects them, and includes the extra horizontal strip. Thus the result excludes **every parameter in the stated box**, not just sampled offsets. It does not assume that the relaxed remaining set is connected. Polygon clipping/inclusion-exclusion and independent vertical line-order integration agree exactly on this fraction.

Increasing the same offset radius to 1/10 gives 117/70, which does not exclude the enlarged box. This failed test is retained. No complete global covering, near-reference localization, or improvement of the earlier unrestricted two-diagonal bound has been proved.

**Outcome:** a complete small branch certificate and exact evaluator, rather than another floating-point cap screen. **Next gate:** specify the entire residual parameter domain and prove covering/local sharpness. A list of successful boxes alone is not a proof.

## 4. Joint area/angle: actual strip widths reduce completion cost

Read [Direction 4](direction-4-width-aware-completion.md).

For endpoint strip widths p,q<=1 separated by a missing angle e<pi/2, the first-wall missing region has exact allowance Lambda(p,q;e). Write a=arccos p, b=arccos q. If a+b>=e, no points are lost by the first-wall relaxation and the whole interval is safe. Otherwise

$$\Lambda=\frac12\left[\frac{2pq-\cos(e)(p^2+q^2)}{\sin(e)}-p\sqrt{1-p^2}-q\sqrt{1-q^2}-e+a+b\right].$$

A polar-coordinate proof supplies the whole interval, with no sampled contact pattern. At p=q=1 it equals CC's tan(e/2)-e/2. It is monotone in each strip width and never exceeds that unit-strip allowance.

The actual CC signed-fiber transfer now uses the incoming width and each outgoing width separately. It retains empty-fiber/component qualifications. If both allowances are zero, the original body completes without deletion and without a connectedness problem. Positive allowances still need payment by a geometric area deficit.

Examples, as approximate diagnostics of the analytic formula: at e=0.3, the unit-strip allowance is about 0.001135218; widths (0.98,1) reduce it to about 0.000124620; widths (0.98,0.98) give zero by the exact angular criterion. The nine prescribed formula/quadrature checks have residuals below 2e-16, but these floating-point agreements are not interval-certified error bounds.

**Outcome:** a general width-aware completion theorem, not another reference-scale theorem. **Next gate:** combine it with actual parameter branches carrying an area bound, or prove that all relevant terminal widths satisfy its zero-loss criterion. Neither holds automatically.

## 5. Execution and provenance

`computer-assisted/check_four_directions.py` uses standard-library Fraction arithmetic for Directions 1--3. It computes finite areas twice by different methods. Direction 4 uses floating-point elementary functions and independent Simpson quadrature strictly as a diagnostic of a hand-proved formula.

The retained run exited with code zero under an external five-second timeout. Its recorded internal test time was 0.010549032999961128 seconds; total subprocess wall time was 0.6050302799999372 seconds. Python was 3.13.5. Executed bytes match the committed Git blob

`65a619e742b44eeea3ebb0ed0bb544ec845f0566`

and SHA-256

`9b1cb59505291dbf2dc862d9a597b38eab60c19e4fc5f0f0d51221867d9a489b`.

The compact committed record is `computer-assisted/four-direction-checks.json`. The conversation reproduction bundle also contains full stdout, stderr, the execution command and all 22 exact vertical-integration bands for the robust box. Two earlier short prototypes compared prescribed box widths and offset radii; they suggested the reported exact fixture rather than supplying any unrecorded global search result.

No optimizer, numerical eigenvalue certification, broad parameter sweep, CI, Lean/Lake compilation, dependency installation, or manuscript build was used. These are self-reviewed written arguments; agreement of finite implementations is not independent verification of the entire historical continuum chain.

## 6. Priority after trying all four

The most concrete next experiment is **Directions 1 and 3 together**, using Direction 2's overlap-safe spatial accounting: derive actual finite arrangement charts for a specified unresolved placement region, reject saddle candidates exactly, and certify complete boxes or list a precise residual. This offers falsifiable outputs without assuming unknown curvature or symmetry.

Direction 4 is ready to be inserted when those branches include partial endpoints; its formula avoids paying the worst-case unit-strip cost when actual widths are smaller. It should not become another standalone sequence of special-family refinements.

The continuum maximizer-structure route remains important, but the present attempt did not eliminate its multipliers or prove injectivity. The alternative finite route likewise still needs a complete domain covering and a sharp limiting/residual theorem. Both are substantial obligations, not routine assembly.

Primary methodological context checked in this continuation: Jineon Baek, *Optimality of Gerver's Sofa*, arXiv:2411.19826 (balancing, injectivity and concave upper comparison), and Yoav Kallus and Dan Romik, *Improved upper bounds in the moving sofa problem*, arXiv:1706.06630 (finite-position outer bounds). No unverified claim from a separate ambidextrous repository is used as an input.
