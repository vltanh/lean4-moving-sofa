#!/usr/bin/env python3
"""Compile the Gate 3 manuscript from explicit, reviewable proof sections.

This performs text assembly and integrity checks only. It runs no mathematical
search, Lean, Lake, CI, or source arithmetic checker.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[1]
OUTPUT = ROOT / "GATE3-MANUSCRIPT.md"
MANIFEST = ROOT / "gate3-manuscript-manifest.json"

# Each range has an inclusive heading start and an exclusive heading end.
# None at the start includes the mathematical preamble after the document title.
SPECS = [
    ("main-introduction", "The theorem, construction and external inputs",
     "gate3-manuscript-introduction.md", [(None, None)]),
    ("main-motions", "Original continuous motions and actual-hull reduction",
     "original-motion-global-bridge-gate0-audit.md", [("## 1.", "## 6.")]),
    ("main-full-turn", "Integrated full-turn value and equality proof",
     "gate3-manuscript-full-turn.md", [(None, None)]),
    ("main-partial-turn", "Integrated partial-turn and strict-angle proof",
     "gate3-manuscript-partial-turn.md", [(None, None)]),
    ("main-equality", "Original equality caps, actual hull and exact body",
     "gate3-sharp-equality-and-uniqueness.md", [("## 1.", "## 6.")]),
    ("proof-reference-matching", "Reference matching, stationarity and exact value (Note 14)",
     "14-sharp-quadratic-calibration.md", [("## 14.1", "## 14.4")]),
    ("proof-reference-height", "The exact global reference corner-height ceiling (Note 4)",
     "04-romik-candidate.md", [("## 4.2", "## 4.4")]),
    ("proof-contact-identity", "The contact integral and its boundary identity (Note 13)",
     "13-contact-quadratic.md", [("## 13.1", "## 13.3")]),
    ("proof-adaptive", "The unrestricted H1 calibration and all equality cases (AF)",
     "adaptive-functional-global-calibration.md", [("## A.1", "## A.8")]),
    ("proof-signed-roof", "Unit-curvature signed-roof identity (SR)",
     "curvature-only-signed-roof.md", [("## S.1", "## S.4")]),
    ("proof-arm", "Support area, reference cap and local arm geometry (AR)",
     "one-turn-arm-reduction.md", [("## 1.", "## 5."), ("**Discrete lemma.**", "**Proof of AR7.**")]),
    ("proof-neighboring-walls", "Neighboring-wall geometry and exact threshold identities (WR)",
     "one-turn-weighted-regularity.md", [("## 1.", "## 2."), ("## 4.", "Put kappa(z)")]),
    ("proof-visible-flux", "Actual visible-source flux and its finite limit (VE)",
     "one-turn-visible-exposure-bound.md", [("## 3.", "## 4.")]),
    ("proof-full-domain", "Full-cap height, width, continuity and attainment (SD)",
     "gate1-spatial-dual-height-width-compactness.md", [("## 1.", "## 5.")]),
    ("proof-middle-chord", "The exact middle-chord and height reduction (MID)",
     "gate1-global-middle-chord-canonicalization.md", [("## 1.", "## 5.")]),
    ("proof-finite-exposure", "Finite exposure and the moving spatial window (FE)",
     "gate1-spatial-exposure-moving-window-variation.md", [("## 1.", "## 6.")]),
    ("proof-prescribed-regularity", "Prescribed-cap approximation and wing regularity (RG)",
     "gate1-spatial-maximizer-wing-curvature-regularity.md", [("## 1.", "## 6.")]),
    ("proof-full-endpoints", "Actual full-cap endpoint complementarity (EP)",
     "gate1-global-endpoint-complementarity.md", [("## 1.", "## 7.")]),
    ("proof-full-pressures", "Positive endpoint pressures, source balance and Green identity (LH)",
     "gate1-global-positive-pressure-and-wing-identity.md", [("## Theorem LH1", "## 9.")]),
    ("proof-facet-pinning", "Pinning the affine middle facet (TF)",
     "gate1-spatial-tilted-facet-pinning.md", [("## 1.", "## 4.")]),
    ("proof-full-curvature", "Spatial source curvature and the horizontal calibration (CH)",
     "gate1-spatial-maximizer-curvature-and-horizontal-value.md", [("## 1.", "## 9.")]),
    ("proof-horizontal-short", "Strict short-width horizontal bound (SW)",
     "gate1-horizontal-short-width-exclusion.md", [(None, None)]),
    ("proof-horizontal-complete", "Complete horizontal width coverage and exact certificates (HW)",
     "gate1-horizontal-maximizer-sharp-value.md", [("## Part I.", "## Conclusion")]),
    ("proof-tilted-width", "Tilted short, wide and intermediate width exclusions",
     "gate1-tilted-width-exclusions.md", [("## Part A.", "## Remaining")]),
    ("proof-full-triangle", "The full three-triangle tilted width cut (FT)",
     "gate1-tilted-full-triangle-width-cut.md", [(None, None)]),
    ("proof-first-wing-structure", "The tilted first-wing structure and projection",
     "gate1-tilted-first-wing-structure.md", [(None, None)]),
    ("proof-fold-occupations", "Fractional occupations for folded sources",
     "gate1-tilted-folded-source-occupations.md", [(None, "## Verdict")]),
    ("proof-two-unit-wings", "The two-unit-wing energy identities used in the first-wing argument",
     "gate1-tilted-unit-wing-exclusion.md", [(None, "## 9.")]),
    ("proof-first-unit", "The complete tilted first-unit-wing contradiction (GF)",
     "gate1-tilted-first-wing-exclusion.md", [(None, None)]),
    ("proof-initial-energy", "The tilted initial-floor energy conditions (IE)",
     "gate1-tilted-initial-floor-energy.md", [(None, None)]),
    ("proof-corner-confinement", "Constructing a genuine feasible one-turn survivor (CG)",
     "gate1-tilted-corner-confinement.md", [(None, None)]),
    ("proof-early-excess", "Forward curvature excess and endpoint leakage (ET)",
     "gate1-tilted-first-excess-ends-early.md", [(None, None)]),
    ("proof-reflected-projection", "Reflected tail and exact zero-height projection (RT)",
     "gate1-tilted-reflected-tail-and-projection.md", [(None, None)]),
    ("proof-final-height", "The final tilted height reduction (FR)",
     "gate1-tilted-final-height-reduction.md", [(None, None)]),
    ("proof-small-height", "The last small-height alternatives (SH)",
     "gate1-tilted-small-height-exclusion.md", [(None, None)]),
    ("proof-full-closure", "Full-turn assembly and explicit external input record (G1C)",
     "gate1-sharp-full-turn-closure.md", [("## 1.", None)]),
    ("proof-partial-domain", "Actual partial-cap domain and used-support saturation (PD)",
     "gate2-partial-cap-domain-reductions.md", [("## 1.", "## 7.")]),
    ("proof-partial-sources", "Prescribed partial-cap source theorem and terminal mass (PS)",
     "gate2-partial-endpoint-source-and-green.md", [("## 1.", "## 10.")]),
    ("proof-negative-completion", "Same-cap completion of the negative-tilt alternatives (NT)",
     "gate2-negative-tilt-completion.md", [(None, None)]),
    ("proof-angle-variation", "Exact one-sided angle derivatives with contact ties (TV)",
     "gate2-terminal-angle-variations.md", [("## 1.", "## 2.")]),
    ("proof-initial-angle", "The all-width initial-angle certificate (AT)",
     "gate2-all-width-terminal-angle-exclusion.md", [(None, "## 8.")]),
    ("proof-terminal-geometry", "Terminal facet geometry, width cuts and projection (TP)",
     "gate2-terminal-facet-and-prefix-reduction.md", [(None, None)]),
    ("proof-partial-width", "The all-sign partial three-angle width cut (WC)",
     "gate2-three-angle-width-cut.md", [(None, None)]),
    ("proof-positive-local-laws", "Local positive-tilt source and support laws (PU)",
     "gate2-positive-tilt-first-unit-exclusion.md", [(None, "## 5.")]),
    ("proof-reflected-local-laws", "The all-sign reflected source system and energy calculation (RP)",
     "gate2-small-deficit-companion-prefix.md", [(None, "## 5.")]),
    ("proof-weighted-moment", "The weighted companion moment and exact terminal margin (MP)",
     "gate2-companion-moment-prefix-exclusion.md", [(None, None)]),
    ("proof-near-full", "The near-full reflected-tail estimate (RX)",
     "gate2-reflected-tail-cot-one-eighth.md", [(None, None)]),
    ("proof-cubic-payment", "The complementary reflected envelope and cubic payment (AC)",
     "gate2-all-angle-reflected-cubic-exclusion.md", [(None, None)]),
    ("proof-partial-closure", "Universal partial-cap value and original-motion deduction (G2C)",
     "gate2-sharp-partial-turn-closure.md", [("## 1.", None)]),
    ("proof-full-equality", "Every original full-turn equality cap and inverse canonicalization (CE)",
     "gate3-full-turn-cap-equality.md", [("## 1.", None)]),
    ("proof-terminal-equality", "Strict proper angles and literal compact-body recovery (TB)",
     "gate3-terminal-and-body-rigidity.md", [("## 1.", None)]),
    ("proof-equality-audit", "Exact body deficits, equality dependencies and counterexamples (ED)",
     "gate3-equality-dependency-audit.md", [("## 1.", None)]),
]

# These are source navigation, historical context, or optional arithmetic artifacts;
# none is an unembedded mathematical premise. Missing proof destinations outside
# this explicit routing are retained in the manifest for review.
CONTEXT_ROUTES = {
    "GATE3-ROADMAP.md": "manuscript-guide",
    "GATE2-ROADMAP.md": "manuscript-guide",
    "SHARP-OPTIMALITY-EXECUTION-PLAN.md": "manuscript-guide",
    "CONSOLIDATED-RESEARCH-HANDOFF.md": "manuscript-guide",
    "ROADMAP.md": "manuscript-guide",
    "HANDOFF.md": "manuscript-guide",
    "gate1-dependency-coverage-audit.md": "verification-record",
    "gate2-dependency-coverage-audit.md": "verification-record",
    "18-restricted-optimality-and-uniqueness.md": "main-introduction",
    "one-turn-single-excess-quarter.md": "external-inputs",
    "spatial-half-partition-bound.md": "main-equality",
}

# These optional attributions are not premises: the required statements are
# proved in the selected sections. Pin them to the already published baseline.
HISTORICAL_SOURCE_REFS = {
    "midpoint-bound-general-motions.md": "The required motion coverage is rederived in GA.1--3.",
    "08-common-hull-tightening.md": "Actual-hull tightening is proved in GA.1--2.",
    "10-wrong-angle-exclusion.md": "Wrong-angle exclusion is proved in the original-motion chapter.",
    "exact-in-place-completion-obstruction.md": "Only the displayed, directly checked triangle support calculation is retained.",
    "candidate-functional-concavity-counterexample.md": "Historical warning about a discarded functional; no step uses it.",
    "one-turn-half-width-top-face.md": "Historical zero-set warning; FE proves the required source variation independently.",
    "romik-terminal-angle-outgoing-strip-rigidity.md": "Historical comparison of auxiliary cuts, after the direct reference-width proof.",
    "01-two-motion-envelopes.md": "Attribution for the envelope idea; ED4 and TB4 reproduce the required actual-body deduction.",
}
HISTORICAL_BASE = (
    "https://github.com/vltanh/lean4-moving-sofa/blob/"
    "b525305f344e635e6264cb470514d6b8bb7a8e43/docs/ambidextrous/"
)

# Explicit preludes restore notation or hypotheses whose old source documents
# introduced them outside the selected proof range. They are audited proof text,
# not implicit dependencies on the surrounding historical notes.
PRELUDES = {
    "04-romik-candidate.md": r"""
**Local notation and derivation.** In this chapter only, write
\(s=\sin\beta\), \(c=\cos\beta\), \(\beta=\beta_*=\arctan Y\),
and \(L=\pi/4-\beta\). Thus this local \(L\) is not the full-turn endpoint.
The root bound MS.2 gives \(2/7<Y<1/3\); also
\(2-\sqrt3<2/7\), because \(3>144/49\). Consequently
\(\pi/12<\beta<\arctan(1/3)\), the bound labeled (4.2) below.
The path ordinate \(q(t)\) in (4.6) is the vertical coordinate of the
canonical corner
\((f_*(t)-1)\mu_t+(g_*(t)-1)\nu_t\) from MS.11.
Horizontal centering does not change this ordinate. Thus the following
height proof uses the explicit construction in this manuscript and has
no additional external path or feasibility premise.
""",
    "13-contact-quadratic.md": r"""
**Local notation.** For a normalized support \(h\), put \(L=\pi/2\),
\(h^\rho(\theta)=h(-\theta)+\sin\theta\), and
\[
C(h)=\frac12\int_0^L(f^2-f'^2+g^2-g'^2)\,dt,\qquad
I(h)=\frac12\int_0^L\det(c(t),c'(t))\,dt,
\]
where \(f=h(t)\), \(g=h(t+L)\), and
\(c(t)=(f-1)\mu_t+(g-1)\nu_t\). These are the quantities \(C,I\)
used in AR.2 and AF.1. For a convex body \(K\) in the normalized unit
strip, AR1 identifies \(C(h)\) and \(C(h^\rho)\) with the upper and
reflected-lower cap areas. Their fibers sum to one plus the hull fiber,
so
\[
C(h)+C(h^\rho)-h(0)-h(\pi)=|K|.
\]
This proves the identity called (12.5) in the historical notation below.
For general \(H^1\) profiles, \(C,I,h^\rho\) retain the displayed
algebraic definitions; no convexity claim is made for those profiles.
""",
    "one-turn-arm-reduction.md": r"""
**Scope and notation.** The domain used here consists of compact
downward convex caps in \(0\le y\le1\), normalized to height one.
Let \(N(U)\) be the full positive two-wall niche,
\(\mathcal A(U)=|U|-|N(U)|\), and
\(\Psi(U)=\mathcal A(U)-W/2\). The notation PA.1 below refers to this
explicit domain, not to an additional attainment theorem.
The selected material proves the support-area identity, its
unit-curvature comparison, the reference value, and an elementary
finite neighboring-wall lemma. Weighted-maximizer propagation results
from the intervening historical sections are not used.
""",
    "one-turn-weighted-regularity.md": r"""
**Scope.** This excerpt contains only the geometric adjacent-wall
estimate WR.1 and its exact threshold refinements. It does not import
the historical weighted first variation or its limiting curvature
argument. RG3 supplies the full spatial limit with the uncharged
middle-facet errors accounted for, and PS supplies the partial spatial
limit with its actual-versus-circumscribed facet comparison. Those
complete proofs are included separately.
""",
    "one-turn-visible-exposure-bound.md": r"""
**Local visible-graph hypotheses.** Use the finite source sequences
from FE/RG with LH, or from PS: their first- and second-wall exposed
length measures converge weakly on the interval in question to
\(u(t)\,dt\), \(v(t)\,dt\). Supports converge uniformly and are uniformly
bounded and Lipschitz. Set \(L=\pi/2\), \(u=f''+f\), \(v=g''+g\),
\(p=f'-g+1\), \(q=g'+f-1\), and
\[
c=(f-1)\mu_t+(g-1)\nu_t,\qquad D=c-q\mu_t.
\]
Then \(c'=p\mu_t+q\nu_t\), \(D'=(1-v)\mu_t\).
The local application assumes positive-height Lipschitz roof graphs:
the corner graph has \(p<0<q\) and a unique maximizing angle;
the second-wall tangency graph has \(0\le v\le1\), a strict companion
gap, and a unique maximizing angle outside the images of its constant
parameter intervals. Each graph piece lies compactly inside the
charged middle window \(J\), and its source angles lie in a compact
regular visited interval avoiding omitted, terminal and exceptional
facet normals. Thus its physical exposure is counted by the spatial
source measures. The two graph images are disjoint when their
contributions are added. CH proves these visibility and separation
hypotheses in its application, as do the specified later local source
arguments. The following section proves the finite tangent-flux limit
under these stated hypotheses; it does not assert global visibility
for an arbitrary cap.
""",
    "gate1-spatial-maximizer-curvature-and-horizontal-value.md": r"""
**Local width threshold.** The constant labeled CH.1 is
\[
W_H=\frac4{35}\sqrt{523+2\sqrt{701}},\qquad C_H=W_H/4.
\tag{CH.1}
\]
The source laws below concern a prescribed canonical global maximizer
of the full spatial score. The horizontal value conclusion CH6 has
the stated hypothesis \(W\le W_H\); the later HW proof covers the
complement.
""",
    "gate1-horizontal-maximizer-sharp-value.md": r"""
**Scope.** The cap is a horizontal, middle-chord-canonical global
maximizer of the full spatial score, as defined in FTM and CH.
This chapter excludes the remaining widths for such a maximizer.
""",
    "gate2-terminal-angle-variations.md": r"""
**Local definitions.** Let \(U\) be a compact downward convex cap
of height at most one, with roof \(A\), projection \(I\), and middle
half \(J\). Put \(L=\pi/2\), \(f(t)=h_U(\mu_t)\),
\(g(t)=h_U(\nu_t)\), and use the wall functions \(R_t,D_t\) from MS.5.
For \(\pi/4\le a<L\), define
\[
n_a(x)=\max\{0,\sup_{0<t<a}\min(R_t(x),D_t(x))\},\quad
N_a=\max(n_a,R_a),\quad
\mathcal P_a(U)=\int_{I\setminus J}A-\int_JN_a.
\]
Thus \(n_a\) excludes the terminal whole wall, while \(N_a\) includes it,
as in PT.3. Horizontal reflection at fixed \(a\) is not assumed.
""",
    "gate3-terminal-and-body-rigidity.md": r"""
**Local maximizer convention.** A joint global maximizer means a pair
\((U,a)\) maximizing the full cap-and-angle objective over all compact
downward caps of height at most one and all
\(\pi/4\le a\le L=\pi/2\). Its value is \(M/2\) by G2C.
No largest-angle selection is assumed in this equality chapter.
""",
}

# Each exact replacement is listed in the manifest. These remove historical
# provenance or unused claims and make the retained local hypotheses explicit.
EDITORIAL_REPLACEMENTS = {
    "gate1-global-middle-chord-canonicalization.md": [
        (
            "\\{U:\\ U\\text{ is downward compact convex, has height 1, width }W>0,\\ \n",
            "\\{U:\\ U\\text{ is downward compact convex, has height 1, width }W>0,\\,\n"
        ),
    ],
    "original-motion-global-bridge-gate0-audit.md": [
        (
            " That triangle has the prescribed partial lower/full upper motions yet fails a late orientation; no in-place zero-loss completion is being smuggled into GA.8.",
            " The displayed support and strip equalities are all that this example uses."
        ),
    ],
    "04-romik-candidate.md": [
        ("For Romik's specified path, the vertical coordinate q(t) is",
         "For the canonical corner of the explicit reference support, the vertical coordinate q(t) is"),
    ],
    "13-contact-quadratic.md": [
        ("Keep the normalized support-function notation of Note 12 and put L=pi/2.",
         "Use the normalized support-function notation just defined and put L=pi/2."),
    ],
    "one-turn-arm-reduction.md": [
        (
            "For every maximizer, WR1 gives height one, W^(2,infinity) supports on each open quarter, and\n\n$$\np(0)=\\tfrac12,\\qquad q(L)=-\\tfrac12,\\qquad \\rho_f\\le\\kappa(q),\\qquad \\rho_g\\le\\kappa(p)\\quad\\text{a.e.},\n\\qquad \\kappa(z)=\\max\\{|z|,(1+|z|)/2\\}.\n$$\n\nThese are WR.4 and WR.5. In particular p and q are Lipschitz on (0,L) with one-sided traces at both ends, and",
            "Whenever the quarter supports are in W^(2,infinity), p and q are Lipschitz with one-sided traces and satisfy the kinematic identities"
        ),
        (
            "Use the grid polygons of WP1 with spacing delta",
            "Use any grid caps with spacing delta"
        ),
        ("the exposed length tau_j of WP2 is zero.",
         "the exposed length tau_j of the finite first-wall ray is zero."),
    ],
    "one-turn-visible-exposure-bound.md": [
        (
            "Let U_n be the WP sequence and let n_n be its finite positive niche roof. Denote by nu_n^f and nu_n^g the measures that assign to each grid angle the total exposed first- or second-wall length. EB1 gives weak convergence to u(t)dt and v(t)dt, respectively.",
            "Let U_n be a sequence satisfying the stated local hypotheses and let n_n be its finite positive niche roof. Denote by nu_n^f and nu_n^g the measures that assign to each grid angle the total exposed first- or second-wall length. By hypothesis they converge weakly to u(t)dt and v(t)dt, respectively."
        ),
        (
            "The following local facts justify reading part of those limiting measures from VE1.",
            "The following local facts justify reading part of those limiting measures from the positive unique-source graphs specified in the prelude."
        ),
    ],
    "gate1-tilted-unit-wing-exclusion.md": [
        (
            "**October 10, 2026. Written proof, independently audited within this research session. Gate 1 remains open.**",
            "**Written two-unit-wing lemma, independently audited within the research session.**"
        ),
    ],
    "gate1-tilted-width-exclusions.md": [
        (
            "does not close the remaining tilted comparison.",
            "is joined with the subsequent tilted source analysis in the integrated full-turn chapter."
        ),
    ],
    "gate2-positive-tilt-first-unit-exclusion.md": [
        (
            "Combine the bound with PS.11 and pass to the limit exactly\nas in WR.5.",
            r"""Write \(T_n=\tan(\delta_n/2)\), and let \(\ell_{n,j}\) be the
charged facet length at a paired first-source grid normal. The retained
WR threshold identities give
\[
\tau_{n,j}\le
\tan(\delta_n)(|q^+_{n,j}|+T_n)+(2T_n-L^{\rm circ}_{n,j})_+
\le\tan(\delta_n)(|q^+_{n,j}|+T_n)+(2T_n-\ell_{n,j})_+.
\]
Here \(q^+_{n,j}\) uses the forward companion secant support derivative.
Combining with PS.11 and separating
\(\ell_{n,j}\ge2T_n\) from \(\ell_{n,j}<2T_n\) gives
\[
\ell_{n,j}\le
\kappa(q^+_{n,j})\delta_n+O(\delta_n^2)+b_{n,j}
\]
uniformly on each compact regular interval. Outer-only normals have
charged length at most \(b_{n,j}\). Semiconvexity, uniform support
convergence and the \(C^1\) limit on that interval make these secant
derivatives converge locally to the companion derivative, in particular
in \(L^1\). Sum the estimate against nonnegative continuous angular
tests. The summed \(O(\delta_n^2)\) and \(b\)-errors vanish, while PS
identifies the weak charged-curvature limit. This proves
\(u\le\kappa(q)\). Interchanging the paired normal families proves
\(v\le\kappa(p)\)."""
        ),
    ],
}

RANGE_REPLACEMENTS = {
    "04-romik-candidate.md": [
        {
            "start": "Here is the reduction from the cited path formulas.",
            "end": "We have only rewritten the given path; this is not an independent verification of all its vector matching equations or its contact pattern.",
            "replacement": r"""Direct substitution from MS.11 proves (4.6). In the first phase,
\[
(f_*-1)\sin t+(g_*-1)\cos t
=\tfrac12+a\sin(2t)-\sin t-\tfrac12\cos t.
\]
In the middle phase the \(k\)-terms cancel, and the result is
\[
\tfrac12+R\sin(3t/2+\pi/8)-\sin t-\cos t
=\tfrac12+R\cos(3(t-\pi/4)/2)-\sqrt2\cos(t-\pi/4).
\]
The last phase is the reflected first expression. Matching at
\(t=\beta\) gives \(R\cos(3L/2)=c\), exactly (4.5).
Thus every identity required for the height proof follows from the
displayed reference support.""",
        },
    ],
}

def digest(text: str) -> str:
    return hashlib.sha256(text.encode()).hexdigest()

def excerpt(source: str, ranges: list[tuple[str | None, str | None]]) -> str:
    pieces = []
    for start, end in ranges:
        a = source.index(start) if start else 0
        b = source.index(end, a + (len(start) if start else 0)) if end else len(source)
        piece = source[a:b]
        if not start:
            piece = re.sub(r"\A# [^\n]*\n+", "", piece, count=1)
        pieces.append(piece.strip())
    return "\n\n".join(pieces)

def compile_manuscript() -> tuple[str, dict]:
    source_routes = {name: anchor for anchor, _, name, _ in SPECS}
    routes = dict(CONTEXT_ROUTES)
    routes.update(source_routes)
    records = []
    unresolved = {}
    historical_links = {}
    output = [
        "# Sharp area and exact uniqueness for the ambidextrous moving sofa problem",
        "",
        "<a id=\"manuscript-guide\"></a>",
        "## Reading guide",
        "",
        "This manuscript includes an integrated proof followed by the complete "
        "essential technical proof sections. The first five chapters give the "
        "theorem, original-motion reduction, full and partial cap arguments, and "
        "exact uniqueness. The subsequent chapters expose the source selections, "
        "calibration, geometric reductions and rational certificates in full.",
        "",
        "Equation labels are local to their stated proof families. Component "
        "results retain their hypotheses and distinctions between geometric "
        "identities and stationarity for a particular objective. The main "
        "theorem and the final review record govern the manuscript's status.",
        "",
        "The source-section manifest records exact input hashes and extraction "
        "boundaries. The assembly retains the selected proofs, restores "
        "explicit local definitions and hypotheses, and records every "
        "editorial replacement as well as heading and link changes.",
        "",
        "A few pinned historical links give optional attribution or "
        "counterexample context. They are not mathematical premises: "
        "the required arguments are reproduced in the selected proof sections.",
        "",
        "### Contents",
        "",
    ]
    for i, (anchor, title, _, _) in enumerate(SPECS, 1):
        kind = f"Chapter {i}" if i <= 5 else f"Technical proof {i-5}"
        output.append(f"- [{kind}: {title}](#{anchor})")
    output.extend(["- [Verification and review record](#verification-record)", ""])

    for i, (anchor, title, name, ranges) in enumerate(SPECS, 1):
        path = ROOT / name
        source = path.read_text()
        try:
            body = excerpt(source, ranges)
        except ValueError as exc:
            raise ValueError(f"Missing extraction heading in {name}: {ranges}") from exc
        source_excerpt = body
        editorial_changes = []
        for before, after in EDITORIAL_REPLACEMENTS.get(name, []):
            if body.count(before) != 1:
                raise ValueError(f"Editorial match is not unique in {name}: {before[:90]}")
            body = body.replace(before, after, 1)
            editorial_changes.append({"before": before, "after": after})
        for change in RANGE_REPLACEMENTS.get(name, []):
            a = body.index(change["start"])
            b = body.index(change["end"], a) + len(change["end"])
            before = body[a:b]
            body = body[:a] + change["replacement"] + body[b:]
            editorial_changes.append({"before": before, "after": change["replacement"]})
        prelude = PRELUDES.get(name, "").strip()
        if prelude:
            body = prelude + "\n\n" + body
        edited_excerpt = body
        def route(match: re.Match) -> str:
            label, target = match.group(1), match.group(2)
            if re.match(r"^[a-zA-Z][a-zA-Z0-9+.-]*:", target) or target.startswith("#"):
                return match.group(0)
            destination = target.split("#", 1)[0]
            filename = Path(destination).name
            # Bracketed mathematical factors can resemble Markdown links.
            # Only a destination naming an actual file is a relative reference.
            if not re.search(r"\.(?:md|lean|py|json|txt|csv|pdf|html)$", destination):
                return match.group(0)
            if filename in routes:
                return f"[{label}](#{routes[filename]})"
            if filename in HISTORICAL_SOURCE_REFS:
                historical_links.setdefault(name, []).append({
                    "destination": target,
                    "reason": HISTORICAL_SOURCE_REFS[filename],
                })
                return f"[{label}]({HISTORICAL_BASE}{target})"
            if destination.endswith(".lean"):
                return f"[{label}](#external-inputs)"
            if destination.startswith("computer-assisted/"):
                return f"[{label}](#verification-record)"
            unresolved.setdefault(name, []).append(target)
            return match.group(0)
        body = re.sub(r"\[([^\]]+)\]\(([^)]+)\)", route, body)
        body = re.sub(r"^(#{1,6}) ", lambda m: "#" * min(6, len(m.group(1))+1)+" ", body, flags=re.M)
        kind = f"Chapter {i}" if i <= 5 else f"Technical proof {i-5}"
        output.extend([
            "---", "", f"<a id=\"{anchor}\"></a>", f"## {kind}. {title}", "",
            body, "",
        ])
        records.append({
            "anchor": anchor, "title": title, "source": name,
            "ranges": [{"start": a, "end": b} for a, b in ranges],
            "source_sha256": digest(source),
            "excerpt_sha256": digest(source_excerpt),
            "excerpt_characters": len(source_excerpt),
            "excerpt_words": len(source_excerpt.split()),
            "prelude": prelude,
            "editorial_replacements": editorial_changes,
            "edited_excerpt_sha256": digest(edited_excerpt),
        })

    output.extend([
        "---", "", "<a id=\"external-inputs\"></a>",
        "## External-input cross-reference", "",
        "The ordinary one-turn theorem and the exact rational Gerver enclosure "
        "are stated in Chapter 1, Section 6 and detailed in the full-turn "
        "closure's dependency section. No equality case of that external "
        "theorem is imported. Every application constructs a genuine feasible "
        "compact connected one-turn body first.", "",
        "<a id=\"verification-record\"></a>", "## Verification and review record", "",
        "The continuum arguments and equality deductions received separate "
        "mathematical checks within this research session. The final equality "
        "audit is included above. External referee acceptance and Lean-kernel "
        "verification are not claimed.", "",
        "The existing fixed final arithmetic checkers report 74 exact rational "
        "checks for Gate 1 and 83 for Gate 2. They corroborate the displayed "
        "finite rational and squared comparisons. They do not check the "
        "continuum geometric proofs. No angle search, new numerical "
        "optimization, Lean/Lake command or CI run is part of this compilation.",
        "",
        "The reproducible assembly records every selected source section and "
        "its SHA-256 digest in gate3-manuscript-manifest.json. Its check mode "
        "verifies that this manuscript and the manifest match those source "
        "sections exactly after the recorded prelude, editorial, heading "
        "and link transformations. "
        "This is an integrity check, not a mathematical proof checker.",
        "",
    ])
    manuscript = "\n".join(output).rstrip()+"\n"
    anchors = set(re.findall(r'<a id="([^"]+)">', manuscript))
    local_links = re.findall(r"\]\(#([^)]+)\)", manuscript)
    broken = sorted(set(local_links)-anchors)
    manifest = {
        "title": "Sharp area and exact uniqueness for the ambidextrous moving sofa problem",
        "scope": "Written proof; internal mathematical review; external refereeing and Lean verification outstanding.",
        "assembly_policy": "Explicit heading ranges; selected proofs retained; local preludes and every editorial replacement recorded; headings and relative reference destinations adjusted.",
        "compiler_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        "manuscript_sha256": digest(manuscript),
        "manuscript_characters": len(manuscript),
        "manuscript_words": len(manuscript.split()),
        "section_count": len(records),
        "sections": records,
        "unresolved_relative_links": unresolved,
        "historical_context_links": historical_links,
        "broken_internal_links": broken,
        "local_link_count": len(local_links),
    }
    return manuscript, manifest

def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    manuscript, manifest = compile_manuscript()
    rendered_manifest = json.dumps(manifest, ensure_ascii=False, indent=2)+"\n"
    if args.check:
        if not OUTPUT.exists() or OUTPUT.read_text() != manuscript:
            raise SystemExit("FAIL: manuscript does not match the selected sources")
        if not MANIFEST.exists() or MANIFEST.read_text() != rendered_manifest:
            raise SystemExit("FAIL: manifest does not match the selected sources")
    else:
        OUTPUT.write_text(manuscript)
        MANIFEST.write_text(rendered_manifest)
    print(f"{'PASS' if args.check else 'Built'}: {manifest['section_count']} proof sections, "
          f"{manifest['manuscript_words']} whitespace words, "
          f"{manifest['local_link_count']} internal links.")
    print(f"Unresolved relative destinations: "
          f"{sum(len(v) for v in manifest['unresolved_relative_links'].values())}; "
          f"broken internal links: {len(manifest['broken_internal_links'])}.")
    if manifest["unresolved_relative_links"]:
        print(json.dumps(manifest["unresolved_relative_links"], ensure_ascii=False, indent=2))
    if manifest["broken_internal_links"]:
        raise SystemExit("FAIL: broken internal anchors")
    if manifest["unresolved_relative_links"]:
        raise SystemExit("FAIL: unresolved relative references")

if __name__ == "__main__":
    main()
