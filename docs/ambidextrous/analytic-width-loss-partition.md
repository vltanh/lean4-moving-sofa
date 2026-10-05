# Analytic width proof, part I: a loss partition and a triangular overlap inequality

These lemmas replace the eight-dimensional covering viewpoint by an analytic one-turn loss estimate. They do not assume that the two motions are reflected copies. No computer-generated covering or polynomial template is used in their proofs.

Put

\[
 c=\sqrt{3/5},\qquad s=\sqrt{2/5},\qquad
 q=s/c=\sqrt{2/3},\qquad r=c/s=\sqrt{3/2},\qquad a=8/15.
\]

Use the two lower-turn orientations with frames (c,s),(-s,c) and (s,c),(-c,s). The upper-turn positions are expressed in the reflected coordinates (x,1-y), with their own independent translations.

## 1. Fixed, disjoint regions in the containing rectangle

Work in R=[0,2] times [0,1]. Partition the horizontal interval into

\[
X_o=[0,a]\cup[2-a,2],\qquad X_i=[a,2-a].
\]

For any pair of lower hallways, let O(x) be the minimum of their four outer roof lines, and let N(x) be the maximum of their two inner tent functions. A lower hallway requires y<=its outer roof and y>=its inner tent. Write

\[
[z]_{0}^{1/2}=\min\{1/2,\max\{0,z\}\},
\qquad
\Lambda=\int_{X_o}[1-O(x)]_0^{1/2}\,dx
       +\int_{X_i}[N(x)]_0^{1/2}\,dx.
\tag{LP.1}
\]

The first integral counts forbidden points only in the upper half of the two outside bands. The second counts forbidden points only in the lower half of the middle band. The corresponding upper-turn loss, computed in reflected coordinates, occupies the opposite vertical halves in each band.

**Lemma LP1 (independent-turn loss bound).** If a measurable S is contained in R and in these four hallway positions, then

\[
\boxed{|S|\leq 2-\Lambda_- -\Lambda_+.}
\tag{LP.2}
\]

**Proof.** Every point counted by either loss is forbidden by the corresponding hallway. The two counted sets are disjoint up to boundary lines: on X_o one is in y>=1/2 and the other in y<=1/2; on X_i the roles reverse. Their union therefore has area exactly Lambda_-+Lambda_+ and is disjoint from S up to null boundaries. Subtract from |R|=2. QED.

The half-height clipping is essential. Without it, opposite counted regions could overlap when a relaxed fiber is empty. Lemma LP1 does not require connectedness or nonempty fibers of the four-position envelope.

## 2. Coordinates for one of the lower hallways

Write its outer supports as A,B, so its inequalities are

\[
cx+sy\leq A,\quad-sx+cy\leq B,
\quad cx+sy\geq A-1\ \text{or}\ -sx+cy\geq B-1.
\]

Set

\[
d=1-B/c,\qquad e=1+2c/s-A/s,
\qquad k=1/c-1,\qquad l=1/s-1.
\tag{LP.3}
\]

The outer deficit is

\[
1-O_{d,e}(x)=\max\{d-qx,\ e-r(2-x)\},
\]

and the inner tent is

\[
T_{d,e}(x)=\min\{qx-d-k,\ r(2-x)-e-l\}.
\tag{LP.4}
\]

For canonical supports of a body in R, d,e>=0, since B<=c and A<=2c+s. No upper bound on d,e will be needed in the one-hallway localization lemma.

For the complementary orientation, the same formulas apply after replacing x by 2-x and interchanging its two deficit coordinates. This is a relabeling in an integral inequality, not a reflection performed during a body motion.

## 3. A uniform bound on the overlap of the two triangular niches

Consider the two reference triangles

\[
T_1=\operatorname{conv}\{(-r,0),(q,0),(0,1)\},\qquad
T_2=\operatorname{conv}\{(-q,0),(r,0),(0,1)\}.
\]

Let Delta_1,Delta_2 be arbitrary translates of positive dilates h_1 T_1,h_2 T_2. The positive portions of the two inner tents, before any clipping by R, are exactly such triangles.

**Lemma LP2 (triangular union bound).**

\[
\boxed{|\Delta_1\cup\Delta_2|\geq
\frac6{11}\bigl(|\Delta_1|+|\Delta_2|\bigr).}
\tag{LP.5}
\]

**Proof.** We use the classical planar mixed-area inequality

\[
V(C,P)^2\geq |C|\,|P|.
\]

For completeness, it follows by applying Brunn--Minkowski to C+tP and comparing with the polygon area expansion |C+tP|=|C|+2tV(C,P)+t^2|P|. Mixed area is additive in either argument and monotone under inclusion; for polygons these statements also follow directly from

\[
V(C,P)=\tfrac12\sum_{e\subset\partial P}|e|h_C(n_e).
\]

The triangles have |T_1|=|T_2|=(r+q)/2. The two nonhorizontal edge normals of T_1, before unit normalization, are (-1,r) and (1,q). The support of T_2 at both of these vectors is r. Its baseline contribution is zero. Consequently

\[
V(T_1,T_2)=r,\qquad
\frac{V(T_1,T_2)}{\sqrt{|T_1||T_2|}}
=\frac{2r}{r+q}=\frac65.
\]

Translations do not change mixed area, so the same ratio holds for Delta_1,Delta_2. Put A_i=|Delta_i| and P=Delta_1/sqrt(A_1)+Delta_2/sqrt(A_2), a Minkowski sum. Then

\[
|P|=2+2(6/5)=22/5.
\]

For C=Delta_1 intersect Delta_2, monotonicity gives

\[
V(C,P)\leq\sqrt{A_1}+\sqrt{A_2}.
\]

If C has zero area the desired bound is immediate. Otherwise the mixed-area inequality and (sqrt(A_1)+sqrt(A_2))^2<=2(A_1+A_2) give

\[
|C|\leq\frac5{22}(\sqrt{A_1}+\sqrt{A_2})^2
\leq\frac5{11}(A_1+A_2).
\]

Subtract this overlap from A_1+A_2. A degenerate triangle is handled directly or by a limit. QED.

This is a fixed analytic inequality for all translations and sizes of the two triangles. It replaces a case-by-case computation of their intersection and does not assume the contact pattern seen in the numerical search.

## 4. What still needs checking before using LP2

LP2 concerns whole triangles. To apply it to the middle-band loss in LP.1, their positive parts must fit inside that band and below height 1/2. Similarly, replacing the outside-band outer loss by its full triangular integral requires its support to fit in the outside bands and stay below the clipping height.

The next lemma proves these conditions whenever a one-hallway loss could be less than 9/50. Outside that parameter region the single hallway already supplies more than 9/50 of loss. This explicit localization, not an assumed optimizer contact pattern, is the remaining analytic reduction.

Only standard planar mixed-area/Brunn--Minkowski geometry and elementary set subtraction were used. These are pen-and-paper arguments with self-review, not independent refereeing. No CI or Lean/Lake compilation was used.
