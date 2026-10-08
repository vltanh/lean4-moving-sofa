# Direct geometric area research — new successful gate and a decisive obstruction

**Branch:** research/ambidextrous-pen-and-paper, draft PR #3.
**Scope:** mathematical research only, no Lean formalization.

## Certified result

[TS-CERT1](two-switch-global-wide-area-certificate.md)
gives the new complete-two-turn ordinary-area theorem

\[
W\ge1411/500=2.822
\quad\Longrightarrow\quad
|S|\le4198376550651309/2560000000000000
<41/25=1.64<M.
\]

It uses two **actual unknown** safe-wall switching angles at a retained
midpoint point, their true outer-wall upper bounds, and true
inner-wall necessary bounds from three retained horizontal anchors
at 18 rational frames. The unknown anchor heights are eliminated
on rational angle/width parameter boxes.

[check_two_switch_wide_area.py](computer-assisted/check_two_switch_wide_area.py)
is the deterministic stand-alone exact checker. The local rational
replay of the equivalent algorithm passed: 5,393 visited boxes,
1,410 exact-infeasibility leaves, 1,287 strict exact-area leaves,
maximum depth 19, no unresolved leaves. The exact maximum accepted
upper bound and exact margin are in the theorem. The independently
authored committed replay script includes assertions for these counts;
it is not claimed that CI/Lean checked the geometric proof.
The hand derivation of each interval relaxation remains self-reviewed
and would benefit from independent scrutiny before publication.

The already proved TSW width theorem bounds W by 2sqrt(2), so
the entire full-turn width interval [2.822,2sqrt(2)]
is excluded for a sharp-area counterexample, not just a tiny
reference-shape neighborhood.

## The new stop rule: why the same approach cannot settle the interior

[AR3-NEG](three-anchor-continuum-obstruction.md)
constructs a completely explicit **compact connected polygonal
region of area 167/100=1.67>M**, with the same left/midpoint/right
anchors P,C,Q used in the upper certificate, satisfying:
- the anchored **inner-wall disjunction at every real quarter-turn
  angle in both handed directions**, not just at 18 samples;
- the four **anchored outer-wall inequalities at 45 degrees**.

It is **not** a feasible full-turn sofa: its actual points
p=(31/20,1/20), q=(21/10,1), r=(0,7/10)
give at the proper (3/5,4/5) frame
(q-p)·u=109/100>1 and (r-p)·v=163/100>1.
Those extra points raise the true support beyond the anchors.
This explicit configuration rules out an unqualified attempt
to prove the sharp M bound by refining only this three-anchor
continuous-angular relaxation at intermediate widths.

**Do not** spend another long session merely squeezing the
W>=2.822 threshold toward the candidate width while keeping
the same independent pointwise anchor constraints.
For the interior class the relaxation is structurally too large.

## Next genuinely different route

Use **actual forbidden triples among occupied spatial regions**
as in [CF1/CF2](configuration-area-certificate.md), combined
with width/angle branching and two-handed simultaneous constraints.
Every accepted condition should involve real additional points
of a possible sofa, not a support lower bound from the fixed three
anchors alone.

A worthwhile initial acceptance gate is to derive a
**nontrivial exact dual certificate** that excludes a
positive-area family of multi-point configurations in a
moderate-width box, with an area bound strictly improving the
best currently *available* general upper bound on that box.
A numerical LP solution alone is not such a certificate.
Test both feasible reference geometry and AR3's explicitly
forbidden triple as positive/negative controls.

The work remains **unfinished**: the broad width range
2<W<2.822, especially around Romik's width about 2.334,
has no globally sharp ordinary-area bound in these notes.
The partial-turn class also retains independent angular
reach and completion obligations. No global value/uniqueness
proof has been obtained.
