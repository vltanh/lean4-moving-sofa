# Face-overhang accounting in the genuine minimum-width frame

**Scope.** This extends the reviewed MF signed identity to a general **regular-curvature, potentially asymmetric** full-turn class. It gives an exact decomposition into total horizontal face length, missing sub-slab niche area, and a nonnegative correction confined to face **overhangs**, with a purely hull-geometric upper bound on the latter. It proves sharp ordinary-area optimality on the infinite-dimensional aligned-face class with total face length at most the horizontal projection width, **without requiring unit vertical span or a specific reference support shape**. It does not prove the unrestricted full-turn result: general faces can be misaligned, their total length can exceed W, and the weighted deficits remain essential. Labels FO are local.

The inputs are the actual same-hull full-turn containment, MF2's exact identity, the elementary curvature-controlled niche confinement of CW/SR, and the existing SR/AF sharp regular-cap comparison. The signed full niche is never silently clipped. These are self-reviewed hand proofs.

## 1. Exact decomposition for two unequal horizontal faces

Let S be a compact connected full-turn ambidextrous body. In an incoming frame its actual convex hull has vertical span H=1-s, with s in [0,1), and lies between y=s and y=1. Its projection is I=[l,r], W=r-l>2, with upper and lower roofs A,B. Let the *actual upper horizontal face* of K be
\[
J_+=[a,b]=\{x:A(x)=1\},
\]
and the *actual bottom horizontal face* be
\[
J_-=[c,d]=\{x:B(x)=s\}.
\]
Their lengths are \(T_+=b-a\) and \(T_-=d-c\). Form downward height-one caps U,V with roofs A and 1+s-B, as in MF2. Let n_U,n_V be their full positive-height niche roofs, and \(\Psi(C)=|C|-|N(C)|-W/2\).

Assume the open-upper-quarter support-curvature measures of both U and V have densities between zero and one, with no interior atoms. Then the standard baseline-intercept argument (included in MS1) gives
\[
\boxed{\operatorname{supp}_x(n_U)\subset J_+,\qquad
\operatorname{supp}_x(n_V)\subset J_-.}\tag{FO.1}
\]
Here \(\operatorname{supp}_x\) may include the endpoints where the roof is zero; the assertion means the positive roof vanishes a.e. outside these face intervals. No bound on niche height or shared reference collars is needed for this inclusion.

Define the exactly nonnegative **unfilled slab areas**
\[
L_U(s)=\int_{J_+}(s-n_U(x))_+dx,\qquad
L_V(s)=\int_{J_-}(s-n_V(x))_+dx.
\tag{FO.2}
\]
By FO.1,
\[
\int_I\min(n_U,s)+\min(n_V,s)
=s(T_++T_-)-L_U(s)-L_V(s).
\]

MF2 gives the exact signed correction
\[
G_s=T_s+C_s-sW,
\quad
C_s=\int_I\left[
(\min(n_U,B)-s)_++(\min(n_V,1+s-A)-s)_+
\right]dx.
\]
Thus:

**Lemma FO1 (face-overhang identity).**
\[
\boxed{
G_s=s(T_++T_--W)-L_U(s)-L_V(s)+C_s.
}\tag{FO.3}
\]
This is an equality, not a discarded-sign estimate.

## 2. The positive correction lives only on mismatched horizontal faces

On \(J_+\cap J_-\) the hull floor is s and its roof is one, so the two terms in \(C_s\) vanish. Outside \(J_+\) the lower niche n_U vanishes; outside \(J_-\) the reflected upper niche n_V vanishes. Therefore the positive correction can be supported **only** on the symmetric difference of the two faces:
\[
C_s=\int_{J_+\setminus J_-}(\min(n_U,B)-s)_+dx
+\int_{J_-\setminus J_+}(\min(n_V,1+s-A)-s)_+dx.
\tag{FO.4}
\]
Since \(B\ge s\), \(A\le1\), it obeys the **purely convex-hull** bound
\[
\boxed{
0\le C_s\le H_{\rm flank}:=
\int_{J_+\setminus J_-}(B(x)-s)dx
+\int_{J_-\setminus J_+}(1-A(x))dx.
}\tag{FO.5}
\]
This bound counts material only over horizontal-face overhangs, **not** all tails of K or the whole cap's support-energy defect. It is exact when the active full niche roofs exceed the respective hull deficits there; no such activation is assumed generally.

Combining the preceding identities with the written weighted value \(\Psi(U),\Psi(V)\le M/2\) gives the unconditional-on-this-regular-domain **upper inequality**
\[
\boxed{|S|\le M-\Delta(U)-\Delta(V)
+s(T_++T_--W)-L_U(s)-L_V(s)+H_{\rm flank},}
\tag{FO.6}
\]
where \(\Delta(C)=M/2-\Psi(C)\ge0\). Alternatively SR1/AF3 supplies each regular-cap bound directly, without invoking the long WV selection/source-flux chain.

In particular a sufficient geometric-and-deficit comparison is
\[
s(T_++T_--W)+H_{\rm flank}
\le \Delta(U)+\Delta(V)+L_U(s)+L_V(s).
\tag{FO.7}
\]
This sufficient condition is **not** asserted universally; it is a transparent smaller set of terms that a global proof would have to pay.

## 3. A new sharp aligned-face subunit-span theorem

**Theorem FO2 (aligned short faces at arbitrary subunit span).** Under the regular-curvature and genuine full-turn hypotheses of Section 1, suppose the two horizontal faces **coincide**:
\[
J_+=J_-=[a,b],\qquad T=b-a\le W/2.
\]
Then
\[
\boxed{|S|\le M-s(W-2T)\le M.}\tag{FO.8}
\]
For \(s>0\) and \(T<W/2\), the bound is strictly below M.

**Proof.** Equal faces make the overhang correction \(C_s=0\) in FO.4, without needing an unknown contact or niche-height classification. FO.3 then yields
\[
G_s=s(2T-W)-L_U(s)-L_V(s)\le s(2T-W)\le0.
\]
Since both regular caps have \(\Psi\le M/2\) by the signed-roof SR1 and the sharp AF3 support-functional comparison, the exact MF2 identity gives
\[
|S|\le |E|=\Psi(U)+\Psi(V)+G_s
\le M-s(W-2T).
\]
No dilation, passage to a hypothetical unit-span competitor, or assumption that the two caps are identical was made. QED.

The theorem covers unequal *middle supports and upper/lower cap profiles* as long as the actual exposed horizontal **face interval** is shared and the quarter curvature bound holds. It is an infinite-dimensional extension beyond the exact scaled-reference SM1 family, although it does not supply SM's \(s^{3/2}\) margin when \(2T=W\).

## 4. Why this is not the general answer

The HC stadium has a common positive face with \(2T-W=11/10>0\). By MS2--MS3, uniformly scaled genuine stadium full-turn bodies in their **global minimum-width** frame have strictly positive \(G_s\). Therefore the term \(s(T_++T_--W)\) cannot be discarded, even in the aligned, smooth-open-quarter, symmetric class. The weighted deficits are needed to pay it. Likewise, different faces can make \(C_s>0\), as the original minimum-width package's offset-face diagnostic already suggested; that diagnostic was not a certified counterexample.

Most importantly, a competitive arbitrary full-turn body has not been proved to possess curvature densities bounded by one, matching faces, short total face length, or an inequality paying the flank overhangs. FO2 is a completed class theorem, not universal full-turn optimality. The partial-turn circular-corner estimate CC2 still needs its separate genuinely feasible completion or signed margin; the present proof assumes both rotations full.

No CI, Lean/Lake compilation, dependency installation, manuscript build, long optimization, or numerical proof input was used.
