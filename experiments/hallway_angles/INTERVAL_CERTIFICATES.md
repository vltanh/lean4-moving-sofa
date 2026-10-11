# Continuous-motion interval certificates

This checker does not depend on the uniqueness proof or a sharp concave area majorant. It verifies explicit lower-bound constructions. It is **not a Lean proof** and does not certify global optimality. Independent review of this small checker and its arithmetic assumptions is still appropriate.

## Three different quantities

1. The local optimizer maximizes a finite sampled hallway intersection. Its value can exceed the continuously feasible area, even when the solver reports success.
2. `enclose_fast` implements a continuous-motion inner construction using floating-point polygon operations. Its decimal areas are not interval certificates.
3. `interval_verify.py` checks a union of dyadic rectangles through the entire motion using outward-rounded intervals. Its accepted shape has an exactly computed rational area. The polygon generator and local optimizer are outside this checker's trust boundary.

## Exact certificate meaning

A `hallway-dyadic-rectangles-v1` certificate specifies:

- An exact decimal rational bend in degrees: beta = (bend_degrees/180) pi. The turn angle is beta for forward motion, beta-pi for reverse motion.
- Corner coordinates in hexadecimal binary64 notation, interpreted as exact dyadic rationals. Consecutive corners are joined by straight segments at equally spaced motion parameters. The checked path is piecewise linear, including paths discovered using a cubic interpolation basis.
- Closed rectangles `[x0,x1] x [y0,y1]` with integer coordinates divided by 2^30. The checker validates that row interiors are disjoint, rectangles within each row do not overlap in area, and 0 <= y0 < y1 <= 1.

The checker may discard rectangles it cannot prove safe. It selects a connected component using exact integer tests for positive-length common horizontal edges, and sums the areas of its rectangles using integers. This test can underestimate connectivity but cannot falsely connect separated rectangles. The selected finite union is compact, connected, and regular closed. Boundary overlaps have zero area.

## Hallway containment at every time

For inner corner c and unit wall normals n1,n2, write fj = nj dot (x-c). The hallway is

    f1 <= 1, f2 <= 1, and max(f1,f2) >= 0.

On a time interval, the checker bounds the corner and normals, then bounds each fj on every whole rectangle. The outer-wall test is upper(fj) <= 1 for both j.

For the inner corner it either proves lower(f1) >= 0 or lower(f2) >= 0, or finds fixed nonnegative weights a,b, not both zero, and proves

    lower((a n1 + b n2) dot (x-c)) >= 0.

This last inequality excludes f1 < 0 and f2 < 0 simultaneously. The weights are merely proposed with ordinary arithmetic; their validity is established by their signs and the subsequent interval inequality. They need not be exactly normalized or optimal. Coordinate-axis separating directions are useful for axis-aligned rectangles.

If an interval test is inconclusive, the time interval is bisected. Every knot interval is processed. Reaching the depth limit discards the unresolved rectangles; it never treats successful point samples as a proof. Therefore every retained rectangle is safe for every real time in [0,1], conditional on correctness of the implementation and stated arithmetic operations.

## Completing entry and exit

The tested motion is not just a rotation in a truncated box. Entry and exit translations can be attached in the unbounded hallway.

At entry, theta=0 and c_y=0, so f1=y is in [0,1]. Increasing c_x decreases f2 by sin(beta) times the increase. The outer inequalities remain satisfied, and f1 remains nonnegative. For sufficiently large c_x, the bounded sofa lies entirely in the incoming arm. Reversing this translation attaches the entry motion.

At a forward exit, theta=beta and c_y=0, so f2=y is in [0,1]. Decreasing c_x decreases f1, attaching a collision-free exit translation. At a reverse exit, theta=beta-pi and c_y=1, so f2=1-y is in [0,1]; increasing c_x decreases f1 and attaches the exit. Since sin(beta)>0, each can be translated arbitrarily far into the corresponding arm.

No completeness theorem for the forward/reverse search classes is needed for these *lower* bounds. Such a theorem would be needed to infer unrestricted *upper* bounds or optimality from searches limited to these classes.

## Arithmetic assumptions

The checker does not call the platform sine or cosine, SciPy, Shapely, GEOS, or the optimizer. It uses NumPy for vectorized basic arithmetic and `nextafter`.

- The pi enclosure is computed from the Machin formula 16 atan(1/5) - 4 atan(1/239), using exact rational alternating sums with the first omitted term bounding the error.
- Sine and cosine use integer interval Taylor arithmetic scaled by 2^90. Sine retains terms through degree 65, cosine through degree 64. On |x|<4, the respective remainders are bounded by 4^67/67! and 4^66/66!, each strictly smaller than 2^-90; these rational inequalities are asserted in the program.
- A trigonometric time interval is enclosed using its midpoint and the 1-Lipschitz property of sine and cosine, with the radius rounded upward.
- Addition, subtraction and multiplication of binary64 interval endpoints are expanded outward with `nextafter`. Exact rational-to-binary64 conversions are also expanded outward. Nonfinite interval products are rejected.
- Time bisection weights are dyadic and the depth is limited to 30, so those interpolation parameters and their complements are exactly representable in binary64. Input rectangle integers are bounded so conversion to binary64 and scaling by 2^-30 are exact.

The trust assumptions are correct Python integer/rational arithmetic and IEEE-754 binary64 basic arithmetic and adjacent-float operations, without unsafe fast-math transformations. This is a conventional numerical enclosure argument, not a kernel-checked or platform-independent formal proof. Tests compare arithmetic enclosures to exact rational calculations and include deliberate collision/rejection cases.

## Reproduction

From this directory, with the documented dependencies installed:

```sh
python -m unittest -v test_pressure test_interval_verify

# Generate proposals from the committed, quantized controls; verify independently.
python replay_pressure.py --candidate 120-forward --skip-enclosure \
  --certificate results/certificates/120-forward.json \
  --rows 2048 --inset 0.0002 --verify \
  --output results/certificates/120-forward-report.json

# The checker alone requires only Python and NumPy, not the generator's packages.
python interval_verify.py results/certificates/120-forward.json --max-depth 8

# Compare the separate floating-point swept enclosure, with a denser-grid audit.
python replay_pressure.py --candidate 120-forward --samples 16385
```

The exact input controls and both successful and unsuccessful optimizer termination records are in `results/pressure-candidates.json`. Certificate recipes, SHA-256 hashes and exact rational areas are retained in the results manifest. Raw certificate payloads can be regenerated without repeating optimization. The generator uses floating geometry only to *propose* boxes; another version may propose different boxes, in which case its output needs a fresh verification rather than assuming the old area/hash.

## Negative and conservative outcomes

A much tighter right-angle proposal (4096 rows, inset 0.00006) did not complete verification within the local execution limit; no certificate is claimed for it. Wider insets completed. A few non-right-angle proposals contain a tiny disconnected piece: its area is discarded by exact component selection. This is why the connected-rectangle count can be smaller than the verified-rectangle count even when every proposed rectangle is safe.

The remaining gap to the numerical polygon area is mainly the rectangle approximation, the deliberate inset, and conservative interval tests. The checker cannot turn a locally optimized path into an optimality theorem.
