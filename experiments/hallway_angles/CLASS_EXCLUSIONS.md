# Excluding whole motion classes

These consequences use the midpoint bounds in `CLASS_BOUNDS.md`, explicit elementary constructions, and (for the 150-degree numerical improvement) the independent interval certificate. They do not use uniqueness or Mamikon rigidity. No novelty claim is made for these elementary comparisons.

**Scope:** the forward and reverse classes mean the full-rotation, aligned-endpoint descriptions in `Motion`. The forward angle changes from 0 to beta, the reverse angle from 0 to beta-pi, and the sofa lies in the normalized entry strip. The midpoint argument also applies to nonmonotone continuous motions in these descriptions, because they still pass through the required midpoint orientation. It does not cover every conceivable entry/exit alignment or partial-rotation motion.

## 1. A semicircle excludes the reverse class on an interval

The upper unit semicircle has area pi/2 and can follow the fixed-inner-corner forward rotation through every beta in (0,pi). Here is a direct verification.

Write a point of the semicircle as r(cos(phi),sin(phi)), with 0<=r<=1 and 0<=phi<=pi. At a hallway pose theta in [0,beta], its two wall coordinates relative to the fixed corner are

    f1 = r sin(phi-theta),
    f2 = r sin(phi+beta-theta).

Both are at most 1. If phi>=theta, then 0<=phi-theta<=pi, so f1>=0. Otherwise 0<=phi+beta-theta<beta<pi, so f2>=0. Hence the point remains in the hallway at every pose. Entry and exit translations attach as explained in `INTERVAL_CERTIFICATES.md`.

Every reverse-class sofa has area at most sec(beta/2). Therefore, whenever

    beta < 2 arccos(2/pi),

its area is strictly smaller than pi/2, so no reverse-class sofa can be globally optimal. The threshold is approximately 100.9195525 degrees (the exact expression, not the rounded decimal, defines the interval).

This is an analytic comparison: it does not depend on numerical optimization or the interval checker.

## 2. A translation-only parallelogram excludes the forward class near pi

At theta=0 let n1,n2 be the two unit wall normals. The parallelogram

    P = {x : 0 <= n1.x <= 1 and 0 <= n2.x <= 1}

has area csc(beta), since the absolute determinant of the two normals is sin(beta).

It can enter by translation along the first strip to the junction, and leave along the second strip. More explicitly, keeping n1.x in [0,1] while decreasing the second wall coordinate preserves hallway containment; the analogous statement with the two coordinates exchanged gives the exit. Thus this is a feasible moving sofa without any rotation.

Every forward-class sofa has area at most 2 csc(beta/2). The strict comparison

    csc(beta) > 2 csc(beta/2)

is equivalent to cos(beta/2)<1/4. Hence no forward-class sofa can be globally optimal for

    beta > 2 arccos(1/4),

approximately 151.0449756 degrees. Again the exact expression determines the range.

## 3. The checked reverse construction improves this exclusion at 150 degrees

At beta=150 degrees, the forward-class bound is

    2 csc(75 degrees) = 2(sqrt(6)-sqrt(2)) < 2.070553.

The connected reverse construction in `results/interval-manifest.json` has interval-checked area

    190058468799968251 / 72057594037927936 > 2.637591.

Consequently **every forward-class sofa at 150 degrees is strictly suboptimal**, not merely the forward path found by the local solver. This conclusion is conditional on the lower certificate and the arithmetic trust boundary documented in `INTERVAL_CERTIFICATES.md`; it is not a Lean-checked theorem.

`class_exclusion.py` compares the exact lower fractions to outward rational upper bounds derived from integer trigonometric enclosures. Run:

```sh
python class_exclusion.py
python -m unittest -v test_class_bounds
```

The same comparison excludes the reverse class at 30,60,90 degrees, consistent with the stronger analytic interval in Section 1. The crude midpoint bounds do **not** select a class at 120,135,137 degrees; the script retains those inconclusive results. In particular, the observed crossing of two locally optimized paths near 136.5--136.8 degrees is not promoted to a classification of all maximizers.
