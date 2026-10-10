# A coupled three-hallway hand bound: \(2\sqrt2-1-1/90\)

**Main theorem (JH1).** Every compact connected ambidextrous sofa admitting continuous motions around the unit-width right and left hallway corners from the **same incoming position**, with arbitrary partial turns, reversals or nonmonotone rotations, has area
\[
\boxed{|S|\le 2\sqrt2-1-\frac1{90}<1.817317.}
\tag{JH.1}
\]
This theorem is **computer-free**. It uses the hand-proved proper-angle reach lemma GH (equivalently the no-sideways-angle argument of O'Keefe/Gerver–Baek), the exact two-\(45^\circ\) envelope geometry MH, and a new **joint area-loss inequality**. It improves the earlier hand bound by more than \(0.011111\), rather than the negligible \(10^{-9}\) of the first TH attempt. It also improves the intermediate independent [QT](quantitative-three-hallway-hand-bound.md) \(1/175\) hand gap. It remains **weaker** than the external *computer-assisted* \(353/200=1.765\) theorem and does **not** prove the sharp Romik conjecture \(M\approx1.644955\). Labels JH are local.

The key idea is **not** to insist that each of three selected witness regions be larger than the *entire* possible area loss. Instead, use an *additive* budget for two necessarily missing tip triangles and a third hallway's forbidden wedge, then apply weighted Cauchy–Schwarz. All inequalities below are exact real hand arguments; a short rational checker can audit numerical constants but is not a proof premise.

## 1. Two opposing midpoint hallways

Let
\[
d=\sqrt2,\quad k=1-d/2,\quad H_1=1-k^2=d-\tfrac12,\quad
B=2H_1=2\sqrt2-1,\quad \epsilon=\frac1{90}.
\]
After an isometry, the two proper opposite-handed \(45^\circ\) hallways and the common incoming unit strip give an enclosure
\[
F(P,Q,c)=\left\{(u,v):
\begin{array}{l}
0\le u\le P,\quad 0\le v\le Q,\\
u\ge P-1\quad\text{or}\quad v\ge Q-1,\\
u\le 1\quad\text{or}\quad v\le1,\\
c-d/2\le u+v\le c+d/2
\end{array}\right\}.
\tag{JH.2}
\]
Here \(P,Q>0\) are arbitrary, and c is the sum-coordinate center of the diagonal band. An incoming strip of height below one only tightens the enclosure, so no area-changing rescaling is used. The earlier MH theorem establishes \(|F|\le B\) for every placement.

The two unit corner squares are
\[
A=[P-1,P]\times[0,1],\qquad D=[0,1]\times[Q-1,Q].
\tag{JH.3}
\]
Let \(J(h)\) be the area of one such unit square caught by the diagonal band when the band's sum midpoint is displaced by h from the square's sum midpoint. The sum of two unit uniform coordinates has a triangular density. Integrating it shows that \(J\) is even, nonincreasing in \(|h|\), and
\[
J(0)=H_1,\qquad J(h)=H_1-h^2\quad(|h|\le k).
\tag{JH.4}
\]
Put \(\mathcal D(h)=H_1-J(h)\). For \(k\le|h|\le1/2\) the rightmost band endpoint has passed the square's edge, giving
\[
\mathcal D(h)=\tfrac12(|h|+k)^2-k^2.
\]
Consequently
\[
\boxed{\mathcal D(h)\ge\tfrac9{10}h^2\quad(|h|\le1/2),\qquad
\mathcal D(1/2)>\tfrac9{40}.}
\tag{JH.5}
\]
**Verification.** Below k, \(\mathcal D(h)=h^2\). Above k,
\[
\mathcal D(h)-\tfrac9{10}h^2
=-\tfrac25h^2+k|h|-\tfrac12k^2.
\]
This is concave in \(|h|\in[k,1/2]\), so its minimum occurs at an endpoint. At k its value is \(k^2/10>0\). At \(1/2\) it is \(-1/10+k/2-k^2/2>0\), using \(29/100<k<3/10\). These same bounds give
\(\mathcal D(1/2)=1/8+k/2-k^2/2>1/8+29/200-9/200=9/40\). Every comparison is elementary.

Assume, seeking a contradiction, that
\[
\boxed{|S|>B-\epsilon,\qquad S\subset F.}\tag{JH.6}
\]
Thus \(|F|>B-\epsilon\) and
\[
\boxed{|F\setminus S|=|F|-|S|<\epsilon.}\tag{JH.7}
\]

## 2. Near equality gives an **exact positive-definite quadratic identity**

If \(\min(P,Q)\le1\), integrating the incoming diagonal band over the thinner coordinate gives \(|F|\le d<B-\epsilon\). If \(P,Q>2\), the only allowed positive-area pieces are the **strictly disjoint** two corner squares; connected S lies in one and has area at most \(H_1<B-\epsilon\). **When one width equals exactly 2**, a zero-area line can connect the two squares: this edge case must be retained and will be included in the area computation.

For the purpose of proving a **symmetric geometric stability estimate only**, interchange u and v if needed so
\[
1<Q=\min(P,Q)\le2,\quad t=2-Q,\quad q=Q-1=1-t.
\]
This interchange will **not** be made when analyzing the oriented third lower hallway in Section 4.

As in MH, dividing the surviving region into the layers \(0\le v\le q\), \(q\le v\le1\), \(1\le v\le Q\) yields
\[
|F|\le f_d(q)=d(1-q)+2q-\tfrac12(1+q-d)_+^2.
\]
If \(q\le d-1\), then \(B-f_d(q)\ge(2-d)^2/2>1/8>\epsilon\), impossible. Otherwise \(B-f_d(q)=t^2/2\). Thus
\[
\boxed{0\le t<\sqrt{2\epsilon}=\sqrt{1/45}<3/20.}
\tag{JH.8}
\]

The bottom and top layers lie within A and D; the intervening layer contributes at most \(dt\). Hence
\[
|F|\le J(c-P)+J(c-Q)+dt,
\tag{JH.9}
\]
which, together with \(|F|>2H_1-\epsilon\), implies
\[
\mathcal D(c-P),\ \mathcal D(c-Q)<\alpha:=\epsilon+dt.
\]
Since \(\sqrt\epsilon=\sqrt{1/90}<53/500\),
\[
\alpha<\epsilon+2\sqrt\epsilon
<\frac1{90}+\frac{53}{250}<\frac9{40}.
\]
Equation (JH.5) and monotonicity of \(\mathcal D\) give
\[
\boxed{|c-P|,\ |c-Q|<\tfrac12.}\tag{JH.10}
\]

We can bootstrap (JH.10) to the **quadratic zone**
\[
\boxed{|c-P|,\ |c-Q|<k.}\tag{JH.11}
\]
If \(P,Q\le2\), the allowed set is the union of the two corner squares and their positive overlap, and that overlap must be **subtracted**. Thus if either square-center displacement were at least k, \(|F|\le2H_1-k^2<B-\epsilon\), since \(k^2>3/35>\epsilon\).

If \(P>2,Q\le2\), the allowed set is A, D and the joining rectangle
\[
R=[1,P-1]\times[Q-1,1]
\]
of area \(ab\), where \(a=P-2\ge0,\ b=2-Q=t<3/20\). Write \(u=c-P,\ v=c-Q\). Then \(v-u=a+b\), so \(ab=b(v-u-b)\). Using (JH.5), any \(|u|\ge k\) or \(|v|\ge k\) would give
\[
\begin{aligned}
B-|F|
&\ge\mathcal D(u)+\mathcal D(v)-ab\\
&\ge\tfrac9{10}(u^2+v^2)+bu-bv+b^2\\
&\ge\tfrac9{10}k^2-bk-\tfrac5{18}b^2\\
&>\frac9{10}\left(\frac{29}{100}\right)^2
-\frac3{20}\frac3{10}-\frac5{18}\left(\frac3{20}\right)^2\\
&=\frac{611}{25000}>\epsilon,
\end{aligned}\tag{JH.12}
\]
a contradiction. The third line follows by minimizing each quadratic on its allowed interval: \(b/(9/5)<k\), so a constrained displaced variable is minimized at magnitude k with its adverse sign; the other quadratic completes a square. For \(b=0\), the degenerate connector has zero area and the inequality still holds.

Now the overlap of A,D, when \(P,Q\le2\), is wholly inside the diagonal band: its sum-coordinate endpoints are \(P+Q-2\) and 2, each at distance less than \(k+t<3/10+3/20<d/2\) from c. When \(P>2,Q\le2\), the bridge R has sum-coordinate endpoints Q and P, each within k of c. The connectors at equality widths have zero area. Thus we can compute the area **exactly**:
\[
|F|=J(c-P)+J(c-Q)-(P-2)(Q-2).
\tag{JH.13}
\]
With \(x=P-2,\ y=Q-2,\ h=c-2\), equations (JH.4) and (JH.13) give
\[
\boxed{
B-|F|
=(h-x)^2+(h-y)^2+xy
=\frac{x^2+y^2}{2}
+2\left(h-\frac{x+y}{2}\right)^2.
}\tag{JH.14}
\]
In particular
\[
x^2+y^2<2\epsilon,\quad
\boxed{|7y-x|<10\sqrt\epsilon<\frac{53}{50}.}
\tag{JH.15}
\]

We also need a **normal-direction** localization. Put \(u=c-P=h-x\) and \(v=c-Q=h-y\), and use \(xy=(h-u)(h-v)\). Completing squares again yields
\[
B-|F|=\frac23u^2+\frac34(v+u/3)^2+
\left(h-\frac{u+v}{2}\right)^2.
\tag{JH.16}
\]
The same holds with u,v exchanged. Consequently
\[
\boxed{
|c-P|,\ |c-Q|<
\sqrt{3\epsilon/2}=\sqrt{1/60}<\frac2{15}.
}\tag{JH.17}
\]
This square-root localization, rather than TH's fourth-root estimate, is the structural input that makes a meaningful hand gap possible.

## 3. The sofa must pay for **two missing tip triangles**

Return to the **original oriented** u,v axes of JH.2. Put \(\tau_0=2/5\). The two tip triangles
\[
\{(u,v)\in A:7(P-u)+v\le\tau_0\},\qquad
\{(u,v)\in D:u+7(Q-v)\le\tau_0\}
\tag{JH.18}
\]
lie wholly in F. Indeed their sum coordinates differ from P or Q by at most \(\tau_0\), and (JH.17) gives \(|c-P|,|c-Q|<2/15\), so the total difference is at most \(2/5+2/15=8/15<d/2\). Each triangle has area
\[
\frac{\tau_0^2}{14}=\frac{2}{175}>\frac1{90}=\epsilon.
\]
Thus (JH.7) forces S to contain at least one point in each triangle.

On the compact nonempty sets \(S\cap A,S\cap D\) define the attained nonnegative minima
\[
s_A=\min_{(u,v)\in S\cap A}[7(P-u)+v],\quad
s_D=\min_{(u,v)\in S\cap D}[u+7(Q-v)].
\tag{JH.19}
\]
We have \(0\le s_A,s_D\le\tau_0\). The **open** tip triangles with scores strictly below these respective minima are disjoint from S, remain wholly in F, and have areas exactly
\[
\boxed{T_{\rm missing}=\frac{s_A^2+s_D^2}{14}.}
\tag{JH.20}
\]
The triangles are mutually disjoint: the first has \(u\ge P-\tau_0/7>1.79\) while the second has \(u\le\tau_0=.4\), using \(P>2-3/20\). No positive-area piece has been charged twice.

## 4. A third hallway forces a central missing wedge

Use the **proper lower-turn** \(3\)-\(4\)-\(5\) normal pair
\[
\nu=(4/5,3/5),\qquad \nu^\perp=(-3/5,4/5).
\]
In the same oriented u,v coordinates (up to translation),
\[
\nu\cdot(x,y)=\frac{7u-v}{5\sqrt2},\qquad
\nu^\perp\cdot(x,y)=\frac{u+7v}{5\sqrt2}.
\tag{JH.21}
\]
The two actual sofa points attaining (JH.19) show that any candidate point \(p=(u,v)\) satisfies
\[
\begin{aligned}
5\sqrt2\,[h_S(\nu)-\nu\cdot p]
&\ge 7P-s_A-7u+v,\\
5\sqrt2\,[h_S(\nu^\perp)-\nu^\perp\cdot p]
&\ge7Q-s_D-u-7v.
\end{aligned}\tag{JH.22}
\]
At each point in a unit \(L\)-hallway, **at least one of these true support depths must be at most one**: the outer wall offsets cannot be below the actual support maxima. Thus any point where both right-hand sides exceed \(5\sqrt2\) must be absent from S.

Set \(u=P-1+r\), \(\eta=5\sqrt2-7>0\), and define
\[
L(r)=\eta+s_A+7r,\qquad
U(r)=\frac{7Q-P+1-s_D-5\sqrt2-r}{7}.
\]
Their difference is
\[
U(r)-L(r)=\frac{N-50r}{7},\qquad
\boxed{N=C+7y-x-7s_A-s_D,\quad C=62-40\sqrt2.}
\tag{JH.23}
\]
Consequently every point in the **open triangle**
\[
W=\{(r,v):0<r<N/50,\ L(r)<v<U(r)\}
\tag{JH.24}
\]
violates *both* required wall depths. We check that \(N>0\) and that the only part of W that may leave F is below the incoming diagonal band.

Indeed, using \(\sqrt2<99/70\), \(C>38/7\), equation (JH.15), and \(0\le s_A,s_D\le2/5\),
\[
N>\frac{38}{7}-\frac{53}{50}-\frac{16}{5}>0.
\]
Also \(\sqrt2>7/5\) gives \(C<6\), hence \(N<C+53/50<7.06\) and
\[
0<r<N/50<3/20<1.
\]
For the upper v-bound, \(U(r)\le U(0)\), and
\[
U(0)
<\frac{13+53/50-5\sqrt2}{7}<1,
\]
since \(\sqrt2>7071/5000\). The lower v-bound \(L(r)>0\) is automatic. Hence W lies inside the **corner square A** (\(P-1<u<P,\ 0<v<1\)), so all the two-midpoint outer and inner constraints are satisfied there except possibly the diagonal band.

The incoming band's **upper boundary cannot remove any of W**. Since \(r<3/20,\ v<1\), the sum coordinate is \(u+v<P+3/20\), whereas
\[
c+d/2>P-\frac2{15}+\frac7{10}>P+\frac12.
\]
For the lower boundary, the band requires
\[
v\ge c-P+k-r,\qquad k=1-\sqrt2/2.
\]
The difference between that line and the wedge lower side \(L(r)\) is
\[
\Delta-8r,\qquad
\Delta=k+(c-P)-\eta-s_A.
\]
Thus the total area of the part of W **below** the incoming band is at most
\[
\int_0^\infty(\Delta-8r)_+\,dr
=\frac{(\Delta_+)^2}{16},\qquad
\Delta_+=\max(\Delta,0).
\tag{JH.25}
\]
Using \(k<3/10\), \(c-P<2/15\), \(s_A\ge0\), and \(\eta>71/1000\), we have
\[
\boxed{\Delta_+<\frac3{10}+\frac2{15}-\frac{71}{1000}
=\frac{1087}{3000}<\frac{11}{30}.}
\tag{JH.26}
\]

The full wedge triangle has area \(N^2/700\). Therefore its part **inside F**, which must be missing from the sofa, has area at least
\[
\boxed{W_{\rm missing}\ge \frac{N^2}{700}-\frac{(\Delta_+)^2}{16}.}
\tag{JH.27}
\]
This missing wedge is disjoint from both missing tip triangles: its u-coordinate lies between \(P-1\) and \(P-1+3/20=P-17/20\), whereas the first tip triangle has \(u>P-\tau_0/7\), and the second has \(u<\tau_0=2/5<P-1\). No multiplicity or overlap has been hidden in the area accounting.

## 5. The coupled quadratic inequality pays **all** missing material

The exact base-envelope identity, the two absent tip triangles, and the third-hallway wedge now give
\[
\begin{aligned}
B-|S|
&=(B-|F|)+|F\setminus S|\\
&\ge
\frac{x^2+y^2}{2}
+\frac{s_A^2+s_D^2}{14}
+\frac{N^2}{700}
-\frac{(\Delta_+)^2}{16}.
\end{aligned}\tag{JH.28}
\]
We discarded the nonnegative extra quadratic term \(2(h-(x+y)/2)^2\) from JH.14.

The affine relationship
\[
\boxed{C=N+x-7y+7s_A+s_D,\qquad C=62-40\sqrt2}
\]
allows a single weighted Cauchy–Schwarz estimate:
\[
\begin{aligned}
C^2
&\le
\underbrace{(700+2+98+686+14)}_{1500}
\left(\frac{N^2}{700}
+\frac{x^2+y^2}{2}
+\frac{s_A^2+s_D^2}{14}\right).
\end{aligned}\tag{JH.29}
\]
The five positive coefficients in the parenthesis match the five dual weights: \(1/(1/700)=700\), \(1^2/(1/2)=2\), \(7^2/(1/2)=98\), \(7^2/(1/14)=686\), and \(1^2/(1/14)=14\).

Combining JH.26--JH.29 gives the **strict quantitative area deficit**
\[
\begin{aligned}
B-|S|
&\ge\frac{C^2}{1500}-\frac{(\Delta_+)^2}{16}\\
&>\frac{(38/7)^2}{1500}
-\frac{(11/30)^2}{16}\\
&=\boxed{\frac{39667}{3528000}}\\
&>\frac1{90}=\epsilon.
\end{aligned}\tag{JH.30}
\]
The final rational comparison has the positive gap
\[
\frac{39667}{3528000}-\frac1{90}
=\frac{467}{3528000}>0.
\]
This contradicts (JH.6), which asserted \(B-|S|<\epsilon\). Thus (JH.1) is proved.

## 6. Motion coverage, validation, and remaining sharp frontier

The argument in Sections 1--5 assumes the two **proper** opposing \(45^\circ\) hallway positions and one earlier proper \(36.87^\circ\) lower-turn hallway. For arbitrary ambidextrous motions, the no-sideways-angle and outgoing-strip argument already proved in GH (and in the external paper's "Turning the right way" reduction) forces both proper \(45^\circ\) positions whenever
\[
|S|>B-\epsilon>\sqrt2.
\]
The proper lower motion must pass through \(\alpha=\arcsin(3/5)<\pi/4\) by continuity, even if it reverses or ends at a smaller than \(90^\circ\) net turn. Both motions begin from the same incoming rigid position, so their hallway coordinates and the actual support witnesses belong to **one common shape**. The hand proof therefore applies to the unrestricted ambidextrous problem and, a fortiori, the full-quarter subclass.

**Scope and honest comparison.** This is an explicit **computer-free universal** inequality improving \(2\sqrt2-1\) by \(1/90\), more than eleven million times the first TH \(10^{-9}\) gap. It remains numerically weaker than the source-certified \(353/200=1.765\) and far from the desired Romik \(M\approx1.644955\). It proves neither optimality nor uniqueness. The novel technical steps are the exact positive-definite two-midpoint stability identity and the *joint* Cauchy–Schwarz payment of two missing actual-support tip triangles and a missing central wedge, with the diagonal-band clipping accounted for **once** by the explicit \((\Delta_+)^2/16\) error. All continuum claims are self-reviewed hand proofs, not independently refereed or kernel-checked.
