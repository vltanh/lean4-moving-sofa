# Projection-endpoint calculation: consolidated reference

The proof originally committed at this path duplicates the concurrently added [Note 64: positive corners are interior](64-positive-corners-are-interior.md). Use **Theorem 118 and Corollary 119 in that note** as the canonical numbered statements. The original version remains in Git history; this pointer preserves previously committed links without maintaining a second theorem with conflicting numbers.

The common result is the support estimate

\[
x_+-c_x\geq\frac{1-(1-c_y)\sin t}{\cos t},\qquad
c_x-x_-\geq\frac{1-(1-c_y)\cos t}{\sin t}
\]

for an interior-angle lower canonical corner in a hull contained in the incoming strip. A nonnegative-height corner is strictly inside the horizontal projection. A corner at or beyond an endpoint is strictly below the strip, so its sufficiently small local circular replacements remove no old strip points. The reflected upper-turn statement is analogous.

The consequence retains the outer-clearance and floating-normal qualifications of the singular-curvature improvements. It does not remove every outer/inner corner coincidence or establish the sharp density bound.

This is separate from the [width-gate supplement](64-width-gate-from-curvature-and-contact.md), whose WG1–WG3 labels avoid the concurrent numbered theorem sequence and whose main consequence is that curvature plus contact imply full turns. Its sharp area application is Corollary WG4 in [Note 31](31-closed-curvature-class-theorem.md).

No CI or Lean compilation was used. This consolidation changes references, not the mathematical result or its qualifications.
