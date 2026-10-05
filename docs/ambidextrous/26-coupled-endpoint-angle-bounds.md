# 26. The two endpoint angles are strongly coupled

The single-endpoint secant estimate misses the interaction between the two outgoing strips. This note gives an explicit upper bound from all three endpoint strips. It excludes a substantial partial-angle region, but does not force both endpoints to be quarter turns.

## 26.1 The two outgoing strips already improve the exclusion

Use the correctly signed endpoint magnitudes alpha,gamma from Theorem 30, and put

\[
a=\pi/2-\alpha,\qquad b=\pi/2-\gamma.
\tag{26.1}
\]

For a body of area above sqrt(2), the earlier single-strip estimate gives alpha,gamma>pi/4, hence 0<=a,b<pi/4. The hull lies in strips of width at most one with normals

\[
e_y,\qquad n_a=(\sin a,\cos a),\qquad n_b=(-\sin b,\cos b).
\]

If a+b>0, the two outgoing strips alone give

\[
|S|\leq|K|\leq\frac1{\sin(a+b)}.
\tag{26.2}
\]

Their determinant has absolute value sin(a+b); apply the same linear-coordinate argument as Proposition 23.

**Corollary 56 (combined endpoint restriction).** If |S|>=M, then

\[
\boxed{\alpha+\gamma\geq\pi-\arcsin(1/M).}
\tag{26.3}
\]

If |S|>M the inequality is strict. The statement includes a+b=0 trivially. Since M>8/5>sqrt(2), every such body satisfies alpha+gamma>3pi/4.

**Proof.** For a+b>0 use (26.2), and the strict increase of sine on [0,pi/2]. The case a+b=0 has alpha+gamma=pi. The last comparison follows from 1/M<1/sqrt(2). QED.

This is a joint constraint: the two missing angular intervals cannot independently approach their single-turn upper limits.

## 26.2 Centering is optimal for the endpoint-strip relaxation

Let P be any intersection of the three strips of width one with these fixed normals and arbitrary center offsets. Then -P is the intersection with the opposite offsets. Every point of (P+(-P))/2 belongs to the intersection P_0 of the three centered strips, since taking the average cancels each scalar offset and preserves its width bound.

The planar Brunn-Minkowski inequality, applied to P and -P, gives

\[
|(P+(-P))/2|^{1/2}\geq\tfrac12|P|^{1/2}+\tfrac12|-P|^{1/2}=|P|^{1/2}.
\]

Thus |P|<=|P_0|. If a strip originally has smaller width, enlarge it to one first. The bounded cases here are convex polygons, so this use of the classical Brunn-Minkowski theorem has no compactness or measurability qualification beyond the stated sets. A lower-dimensional intersection has zero area and causes no issue.

This symmetrization is only for the **convex endpoint-strip relaxation**. It is not a symmetrization of the moving sofa or of its two hallway motions.

## 26.3 Exact three-strip value

Assume a,b>0 and a+b<pi/2. The intersection of the two centered tilted strips is a parallelogram of area 1/sin(a+b). Its top vertex has height

\[
y_* =\frac{\sin a+\sin b}{2\sin(a+b)}>\frac12.
\]

The other pair of vertices has height magnitude
\(|\sin b-\sin a|/(2\sin(a+b))<1/2\).
The horizontal strip |y|<=1/2 therefore removes exactly the top and bottom triangles.

At a height near the top vertex the horizontal section length is

\[
(\cot a+\cot b)(y_*-y).
\]

Each removed triangle has area one half of (cot(a)+cot(b))(y_*-1/2)^2. Subtracting both gives

\[
\boxed{
T(a,b)=\frac1{\sin(a+b)}
-\frac{(\sin a+\sin b-\sin(a+b))^2}
{4\sin a\sin b\sin(a+b)}.
}
\tag{26.4}
\]

**Proposition 57 (three-strip endpoint bound).** For every competitive body with a,b>0,

\[
|S|\leq T(a,b).
\tag{26.5}
\]

The limiting values are T(0,b)=1/sin(b) and T(a,0)=1/sin(a) for positive remaining argument. At (0,0) all three strips coincide and this relaxation is unbounded.

The proof is the centering argument followed by the exact triangle subtraction. No approximation to a motion envelope is used. In particular, when both turns are partial the positive correction in (26.4) improves strictly on (26.2).

## 26.4 Equal endpoint deficits

For a=b=d>0, the value simplifies to

\[
T(d,d)=\frac{2-\cos d}{2\sin d}.
\tag{26.6}
\]

On 0<d<pi/4 this is strictly decreasing: its derivative is
\((1-2\cos d)/(2\sin^2d)<0\).
Thus an equal-endpoint candidate of area at least M must have d<=d_M, where the unique root satisfies

\[
\cos d_M+2M\sin d_M=2,
\]

or, explicitly,

\[
d_M=\arctan(2M)-\arccos\left(\frac2{\sqrt{1+4M^2}}\right).
\tag{26.7}
\]

The indicated branch is the small positive solution. This is an exact exclusion; no decimal evaluation is needed.

## 26.5 Why this is not a full-angle proof

As a,b tend jointly to zero, T(a,b) tends to infinity. Endpoint strips alone therefore give no useful upper bound in a neighborhood of full quarter turns. The small remaining angular sectors must be controlled by the interior hallway constraints or by a variational/free-endpoint argument.

The formula records exactly where the elementary strip route stops. In particular, a near-full endpoint cannot be declared equal to pi/2 merely because the combined deficit is small.
