# 46. An explicit unrestricted gap, certified by three small squares

This makes Note 45 quantitative. The proof is entirely rational/radical geometry: near equality in the diagonal estimate forces three fixed positive-area squares into the relaxed envelope. A sufficiently large body must meet all three, but any three such witness points fail one of two additional required hallway angles.

The resulting constant is not intended as an optimized finite-angle bound. It is a rigorously explicit upper bound for the unrestricted posed problem, independent of the curvature/contact hypotheses in Theorem 65.

Set

\[
T=\sqrt2,\qquad U_0=2T-1,\qquad\eta=1/20000.
\]

## 46.1 Stability of the rectangle calculation

**Lemma 88 (placement control near the diagonal maximum).** Let S be a compact connected subset of the diagonal relaxation D(W,H) intersect J_s from Note 44, and suppose

\[
|S|\geq U_0-\eta.
\]

Exchange the diagonal axes if necessary so W>=H, and define

\[
D=U_0-|S|,\qquad z_c=s+T/2.
\]

Then

\[
199/100\leq H\leq2,\quad |W-2|\leq1/100,
\qquad \left|z_c-\frac{W+H}{2}\right|\leq1/200.
\tag{46.1}
\]

**Proof.** The small-H and H>2 connected-component cases in Note 44 give area at most T or one, so neither is possible. Moreover H<=T gives area at most 4T-4. But

\[
U_0-\eta-(4T-4)=3-2T-\eta>0,
\]

using T<10/7 and eta<1/7. Hence T<H<=2, and (44.7) gives

\[
D\geq\tfrac12(2-H)^2.
\tag{46.2}
\]

Since D<=eta, H>=2-sqrt(2eta)=199/100.

Let delta_1,delta_2 be the nonnegative losses of the two arm rectangles relative to their individual strip maxima m(H-1). The middle rectangle contributes at most T(2-H), and S may omit further area. Thus

\[
D\geq\tfrac12(2-H)^2+\delta_1+\delta_2.
\tag{46.3}
\]

The u+v centers of the upper-left and lower-right arms are 1+H/2 and W+H/2-1. Their offsets from the strip center are

\[
z_1=z_c-1-H/2,\qquad z_2=z_c-W-H/2+1.
\]

Put d_H=(H-T)/2. Here d_H>1/4, using H>=199/100 and T<10/7. For an arm rectangle, shifting its centered strip by z with |z|<=d_H removes two corner triangles with legs d_H+z and d_H-z. Both legs remain in the triangular portions of the section density since T>1. Consequently its loss is exactly z^2 in this range. Outside this range the loss is at least d_H^2 by the symmetry and monotonicity proved in Lemma 84.

Since each delta_i<=eta<1/16<d_H^2, necessarily |z_i|<d_H and delta_i=z_i^2. It follows that

\[
z_1^2+z_2^2\leq D.
\]

But W-2=z_1-z_2, while z_c-(W+H)/2=(z_1+z_2)/2. Cauchy-Schwarz gives their bounds sqrt(2D) and sqrt(D/2), respectively. At D<=1/20000 these are 1/100 and 1/200. QED.

## 46.2 Three robust squares inside every such envelope

Center the rectangle coordinates by setting

\[
U=u-W/2,\qquad V=v-H/2,
\quad z=z_c-(W+H)/2.
\]

The incoming strip is |U+V-z|<=a, where a=T/2=1/T. Put d=1-a and r=1/64. Let Q_P,Q_A,Q_B be the closed axis-parallel squares of half-side r/4, with centers

\[
P_r=(r,-a+2r),\qquad
A_r=(1-r,-d-r),\qquad
B_r=(-d-r,1-r).
\tag{46.4}
\]

Each square has area

\[
(r/2)^2=1/16384>\eta.
\tag{46.5}
\]

**Claim.** Every square lies inside E=D(W,H) intersect J_s under (46.1).

For a direct check, Q_P and Q_A lie in the lower-right arm

\[
[W/2-1,W/2]\times[-H/2,H/2-1],
\]

and Q_B lies in the upper-left arm

\[
[-W/2,1-W/2]\times[1-H/2,H/2].
\]

The endpoints W/2,H/2 differ from one by at most 1/200. The smallest positive U-coordinate of Q_P is 3r/4=3/256>1/200; the largest U-coordinate of Q_A and V-coordinate of Q_B is 1-3r/4<1-1/200. All negative coordinates lie strictly between -1+1/200 and -1/200, using 7/10<a<5/7. These bounds verify the arm inclusions.

The sums U+V on Q_P range from -a+5r/2 to -a+7r/2. On each of Q_A,Q_B they range from a-5r/2 to a-3r/2. Since |z|<=1/200 and 3r/2>1/200, these intervals lie inside [z-a,z+a]. This verifies the incoming strip as well.

Note 44 bounds the total area of E by U_0 in this H<=2 regime, not just one of its components. Therefore

\[
|E\setminus S|=|E|-|S|\leq D\leq\eta.
\]

By (46.5), S must meet every one of Q_P,Q_A,Q_B. This argument does not assume that small area loss implies Hausdorff closeness of the body.

## 46.3 Any three selected points violate a unit hallway

Take arbitrary p in Q_P, A in Q_A, and B in Q_B, and use the normals

\[
n=(7,1)/(5T),\qquad m=(-1,7)/(5T).
\]

The coordinate error between a difference of two chosen points and the corresponding center difference is at most r/2 in each coordinate. Thus

\[
n\cdot(A-p)\geq\frac{6+T-21r}{5T}>1,
\]

\[
m\cdot(B-p)\geq\frac{8+3T-23r}{5T}>1.
\tag{46.6}
\]

The first strict inequality reduces to 363/64>4sqrt(2); squaring gives

\[
363^2=131769>131072=32\cdot64^2.
\]

The second reduces to 489/64>2sqrt(2), which follows already from 489/64>3>2sqrt(2). These are exact comparisons, not decimal estimates.

If all three points belong to a body S, any outer hallway bounds in directions n,m must be at least n dot A and m dot B. Its inner thresholds are one less. Equation (46.6) therefore puts p strictly in its forbidden quadrant. No translation of a unit hallway with this pair of normals can contain S.

With the original diagonal coordinate ordering these normals are the lower-turn frame at t_+=arctan(4/3). If the axes were exchanged to arrange W>=H, their unordered pair is the lower-turn frame at t_-=arctan(3/4). The hallway disjunction is symmetric in the pair, so this exchange is harmless. Both angles must be tested; no reflection of the physical body during its motion is being allowed.

## 46.4 The explicit global conclusion

**Theorem 89 (unrestricted upper bound with an explicit gap).** Every compact connected ambidextrous body in the posed problem satisfies

\[
\boxed{|S|<2\sqrt2-1-\frac1{20000}.}
\tag{46.7}
\]

In particular its supremum is at most the displayed constant; with the attainment from Theorem 55 it is strictly less.

**Proof.** Suppose |S|>=U_0-eta. This exceeds 5/3, since T>7/5 gives U_0>9/5 and eta<2/15. The correct-sign reduction of Theorem 30 applies. By the endpoint two-strip bound, both reduced endpoint magnitudes exceed t_+, whose secant is 5/3. Thus both diagonal positions, and both lower-turn angles t_- and t_+, are visited.

The diagonal positions put S in D(W,H) intersect J_s. Theorem 85 gives D=U_0-|S|>=0, so Lemma 88 applies. Section 46.2 forces S to meet all three squares. Section 46.3 shows this is incompatible with one of the required extra angles. This contradiction proves (46.7). QED.

This certificate uses the incoming strip, the two diagonal hallway positions, and the two possible additional lower-turn positions. It is not a numerical search and does not claim the finite-angle optimum has been computed. The deliberately conservative constant comes from the chosen robust squares.

The unrestricted value has not been identified with M. What is now available is a quantitative bound applying to every competitor, independent of the missing curvature and endpoint-equality reductions.
