# Review: aligned short-face extension and the remaining geometry

**Unrestricted optimality is not proved.** This continuation closes the full-turn aligned-face case for every positive common face length, not only lengths at least one. It also gives short-face conditions forcing full turns, classifies the remaining positive-face full-turn cases, and rules out a false point-face approximation. The new reasoning is pen and paper, with short exact checks used to catch errors rather than supply a global certificate.

Baseline: `bbd0e986b988b5b2cb30e1ec81606f8e92584078`. All mathematical statements remain self-reviewed. The existing WV2 weighted-value and AW-W width proofs are inputs, not independently verified by this continuation.

## 1. What FAS1 actually proves

[full-turn-aligned-short-faces.md](full-turn-aligned-short-faces.md) proves |S|<=M for a compact connected ambidextrous body with two full conventional turns and identical nondegenerate top/bottom hull faces. No lower bound on their positive length T is assumed. Curvature, reflection symmetry and extreme-height conditions are also not assumptions.

The proof follows these explicit steps:

- [SW1](scaled-width-margin.md) uniformly shrinks a body of width W>2 to width two and applies AW-W, which allows incoming height at most one. It yields `|S|<41 W^2/100`. Therefore every body with W<=1001/500 has area below `41082041/25000000<M`.
- For a potential counterexample, W>1001/500. The case T>=1 is already FL. For 0<T<1, retained face endpoints force actual extreme-point flank inequalities on every t in `(0,2 arctan T)`.
- Those inequalities first imply T>2-sqrt(3); otherwise W<=2. The angle pi/6 is consequently available in their interval, and each flank width is at most sqrt(3)/2.
- Failure of either explicit SCG clipping condition makes the corresponding flank at most `cos(2 arctan T)`. Hence W is at most `T+cos(2 arctan T)+sqrt(3)/2`.
- An exact polynomial sum-of-nonnegative-terms identity bounds the latter expression by `1201/600<1001/500`, a contradiction.
- Thus both SCG conditions hold. They confine the two actual positive niches between the retained face endpoints, eliminate clipping, and permit the two universal WV2 bounds to add.

Neither a floating-point maximum of that elementary function nor any newly generated exclusion tree is used. The rational width margin is deliberately larger than the entire unresolved range of the intermediate flank test.

## 2. The six-point criterion is an ordinary-area comparison

[SCG1](short-chord-optimality.md) uses four *actual* points `(a,0),(a,1),(b,0),(b,1)` and two actual horizontal extreme witnesses `(l,y_L),(r,y_R)`. For T=b-a in (0,1), its two inequalities are

$$2T(r-a)+\min(y_R,1-y_R)(1-T^2)>1+T^2,$$

$$2T(b-l)+\min(y_L,1-y_L)(1-T^2)>1+T^2,$$

with r-a,b-l>1. A trigonometric strip lemma proves full turns; safe-wall alternatives at the four retained points then prove niche confinement directly. This does not require positive corner height at every angle or a connected family of positive triangles.

The distinction between hull membership and actual retention is essential. The rectangle between the four points may be absent from S; its corners, however, cannot merely be assumed from a rectangle inside the hull.

[CSF1](central-short-face-optimality.md) supplies geometric conditions making the certificate automatic even before full turns are known. If both face intervals contain `[l+1,r-1]`, initial floor traces force a common left endpoint. Support widths then force full turns at explicit width/height thresholds, and final traces force right-endpoint agreement. Thresholds include W>1+sqrt(2) without extra extreme-height information, W>7/3 with extreme witnesses in [1/4,3/4], and W>sqrt(5) with mid-height extremes.

These thresholds are not asserted for every maximizer. CSF is a sufficient partial-angle admission result; FAS is the stronger already-full-turn aligned-face result.

## 3. The actual short-face example and a discarded parameter tuple

The CSF note verifies a genuine feasible body using an ellipse of semiaxes 7/10 and 1/2, horizontally added to a segment of length 9/10. Its common hull has width 23/10, face length 9/10 and mid-height extremes. Exact support inequalities confine both niches to the face interval, and a Cauchy--Schwarz estimate puts their heights below one half. The surviving fibers are connected through the midline and all hull extreme points survive. This checks both feasibility and actual hull identity.

The first draft instead displayed W=12/5,T=2/5 as parameters passing the six-point algebra. It did not verify a feasible realization. The later flank bound proves that those parameters are incompatible with full-turn feasibility, since W>T+sqrt(3). The example was replaced in both notes. No conditional theorem depends on the discarded tuple. This is why numerical support parameters alone must not be called a feasible body.

## 4. Exact remaining full-turn classes

[FD1--FD2](full-turn-face-dichotomy.md) use only the initial and final retained-point exclusions. For W>2, two nondegenerate faces must either coincide and span `[l+1,r-1]`, or lie in opposite unit end intervals `[l,l+1]` and `[r-1,r]`.

The first case is now covered by FAS regardless of its positive face length. Thus a full-turn counterexample would have either at least one point face, or two positive faces in opposite end intervals. This is a smaller and more explicit remainder than the prior blanket class 'one face has length at most one'. It is not an exclusion of either remaining alternative.

FD3 proves that an aligned point-face hull of width W>2 cannot be a Hausdorff limit of aligned positive-face, full-turn, unit-span hulls of converging width. Each approximant's common face must have length at least W_j-2, and the endpoints preserve that positive length in the limit. Adding an arbitrarily small horizontal segment at fixed height therefore cannot supply the hoped-for approximation. Uniform shrinking creates a subunit-height body instead, outside the exact unit-span face theorem unless another operation is justified.

## 5. A retained-point negative control

There is a simple actual-envelope model illustrating why a hull-only version of SCG's argument is false. Let K be a radius-one-half disk centered at (0,1/2), added to `[-3/5,3/5] x {0}`. Its horizontal faces are `[-3/5,3/5]`, and its support is

$$h(t)=1/2+(1/2)\sin t+(3/5)|\cos t|.$$

Its canonical niches are confined strictly to that face interval by the explicit intercept formulas. Their corner height is

$$(3/5)\sin(2t)+(1/2)(1-\sin t-\cos t).$$

Writing z=sin t+cos t, this is `(3/5)z^2-z/2-1/10`, whose endpoint maximum on [1,sqrt(2)] is `11/10-sqrt(2)/2<1/2`. Thus the symmetric canonical envelope is compact, connected through the midline, feasible for both full turns and has actual hull K.

The four points at x=plus or minus 9/20 and y=0,1 lie in K, but not all in the actual body. At the rational lower-turn direction (c,s)=(20/101,99/101), the point (9/20,0) has both forbidden gaps strictly positive:

$$f-1-(9/20)c=2/101,\qquad g-1+(9/20)s=1269/2020.$$

Meanwhile the narrower rectangle's six-point algebra passes with margin 43/40. Thus simply replacing 'the four points are in S' by 'the four points are in K' would license a false niche-confinement conclusion. The new proofs never make that replacement: CSF explicitly postpones use of its right endpoints as retained points until alignment is proved.

No claim that this stadium model beats M or violates the valid weighted theorem is made.

## 6. Checks actually executed

The standard-library [checker](computer-assisted/check_short_face_extension.py) ran under an external five-second limit. The final recorded internal time was about 0.030 seconds. Its 19 named checks include:

- a coefficient-by-coefficient verification of the complete FAS polynomial identity;
- 1,805 exact rational strip tests and 985 failed-certificate flank tests;
- 27 central-threshold polynomial regressions;
- all 6,084 pairs of nondegenerate face intervals on a quarter-unit grid in [0,3], with 225 passing the initial/final tests and exactly matching the three proved alternatives;
- four negative controls: reversed cubic sign, forgetting the reflected extreme height, false point-face thickening, and hull-only retention.

The [record](computer-assisted/short-face-checks.json) gives Python version, hashes and explicit scope. Executed local source matches the fetched Git blob `65ab585aa3c29f5596f00bd2569c7103c1030529`, SHA-256 `9d038e0a6346a89cb8b0a3ec7c6d4da018c7815bb31b759d4eaaf5bb8d9b3b19`.

These are arithmetic and finite regression checks, not independent verification of the continuum geometry or WV2. Two exploratory calculations under five-second limits evaluated a few stadium integrals and their symbolic antiderivative; those observations were not used as proof premises. No optimization campaign, interval search, or global parameter covering was run.

## 7. What remains and what must not be claimed

Unrestricted optimality still requires a valid ordinary-area comparison for the remaining point-face and opposite-end-face classes, plus actual angular coverage for unhandled partial-turn bodies. The general clipping identity still has its positive correction; FAS removes it only in the stated admitted class.

There is no proved reduction of every maximizer to the new aligned class, no uniform strict gap below M for all point-face bodies, and no local theorem inferred from a grid. The new result closes one substantive geometric case, not the entire problem.

All substantive findings and corrections are committed with `[skip ci]`. No CI, Lean/Lake compilation, dependency installation or manuscript build was used. The PR remains open and draft. The primary goal remains optimal value, with unrestricted uniqueness deferred.
