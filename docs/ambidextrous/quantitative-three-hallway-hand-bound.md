# A quantitative hand bound: \(2\sqrt2-1-1/175\) for every ambidextrous sofa

**Main theorem (QT1).** Every compact connected ambidextrous sofa that can negotiate the unit-width right and left corners from the same incoming position, by **arbitrary continuous, possibly partial/nonmonotone motions**, has area
\[
\boxed{|S|\le2\sqrt2-1-\frac1{175}<1.822714.}\tag{QT.1}
\]
The same applies to the complete-quarter full-turn subclass. **This is a completely computer-free proof**. The reduction to proper hallway angles uses the already written GH/Gerver--Baek no-sideways argument; the quantitative proof below is self-contained. It replaces the unnecessarily weak \(10^{-9}\) gain in [TH](strict-hand-three-hallway-bound.md) by a gain **over 5.7 million times larger**. It remains *weaker* than O'Keefe's independently computer-certified \(353/200=1.765\) global upper bound, and it does **not** establish the conjectured sharp \(M\approx1.644955\).

The key change is to calculate the near-equality area of the two \(45^\circ\) hallway envelope **exactly**, then use *triangular support reservoirs* instead of three tiny rectangles. Every real-geometry inequality is proved on paper; the optional rational checker only audits the finite constants. Labels QT are local.

## 1. Two \(45^\circ\) hallways and the unit-square concentration lemma

Put \(d=\sqrt2\), \(k=1-d/2\), \(H_1=1-k^2=d-1/2\), \(B=2H_1=2\sqrt2-1\), and
\[
\boxed{\epsilon=1/175.}
\]
Use the same isometric coordinates as MH, \(u=(x+y)/\sqrt2,\ v=(-x+y)/\sqrt2\), followed by a translation. Any body surviving a proper lower \(45^\circ\) hallway, a proper opposite-handed upper \(45^\circ\) hallway, and its incoming unit strip lies inside
\[
F=F(P,Q,c)=
\left\{\begin{array}{l}
0\le u\le P,\quad0\le v\le Q,\\
u\ge P-1\ \text{or}\ v\ge Q-1,\\
u\le1\ \text{or}\ v\le1,\\
c-d/2\le u+v\le c+d/2
\end{array}\right\},
\tag{QT.2}
\]
for suitable \(P,Q>0,c\in\mathbb R\). An incoming strip thinner than one is safely enlarged to the band of width \(d\). Its old exact universal bound is \(|F|\le B\).

Let \(J(h)\) be the area of a **unit square** intersected with a diagonal band of sum-coordinate width \(d\), when the band midpoint differs by \(h\) from the square's sum-coordinate center. Slicing the square by \(u+v\) gives a symmetric triangular density and proves:
\[
J(h)\le H_1,\quad J(0)=H_1,\qquad
\boxed{J(h)=H_1-h^2\ \ (|h|\le k).}\tag{QT.3}
\]
The deficit \(D(h)=H_1-J(h)\) is even and nondecreasing in \(|h|\). At \(r=17/40\), since \(k\in(29/100,3/10)\) and \(r>k\),
\[
D(r)=\frac{(k+r)^2}{2}-k^2
=\frac{r^2}{2}+kr-\frac{k^2}{2}
>\frac{289}{3200}+\frac{493}{4000}-\frac9{200}
>\boxed{\frac4{25}.}
\tag{QT.4}
\]
These formulas use only the elementary areas of triangles below the two band boundaries. We shall also use
\[
\frac{7071}{5000}<\sqrt2<\frac{99}{70},\qquad
\frac{29}{100}<k<\frac3{10},\qquad
k^2=\frac32-\sqrt2>\frac3{35}.
\tag{QT.5}
\]
All displayed square-root comparisons follow by squaring positive rational numbers.

Assume for contradiction
\[
|S|>B-\epsilon.
\tag{QT.6}
\]
Because \(S\subset F\) and \(|F|\le B\), we have \(|F|>B-\epsilon\) and \(|F\setminus S|<\epsilon\).

## 2. An exact **quadratic** stability identity at every near-maximal placement

We first derive the decisive strengthening of TH's prior fourth-root localization. If \(\min(P,Q)\le1\), the diagonal band has area at most \(d\) inside the thinner coordinate strip, whereas \(d<B-\epsilon\). If \(P,Q>2\), the two permitted unit corner squares
\[
A=[P-1,P]\times[0,1],\qquad D=[0,1]\times[Q-1,Q]
\tag{QT.7}
\]
are disconnected, with **no** zero-area connector line; connected \(S\) lies in one, of area at most \(H_1<B-\epsilon\). When just **one** of \(P,Q\) equals 2 a measure-zero connector may exist; it is retained below and never discarded.

The geometry of F is symmetric in u,v for the purpose of this *stability* calculation. Interchange the coordinate labels **only in this calculation**, if necessary, so that
\[
1<Q=\min(P,Q)\le2.
\]
We return to the original oriented u,v axes in Sections 3--4. Put \(t=2-Q\), \(q=Q-1=1-t\). Split F into the lower, middle and upper horizontal v-layers. The first is contained in the unit corner square A, the last in D, and the middle has height t and at most d horizontal band length. Thus
\[
|F|\le J(c-P)+J(c-Q)+dt.\tag{QT.8}
\]
The sharper middle-layer estimate already proved in MH gives
\[
|F|\le f_d(q):=d(1-q)+2q-\tfrac12(1+q-d)_+^2.
\]
The function is increasing in q. For \(q\le d-1\), \(B-f_d(q)\ge(2-d)^2/2>1/8>\epsilon\); hence \(q>d-1\). In this range
\[
B-f_d(q)=t^2/2.
\]
It follows that
\[
\boxed{0\le t<\sqrt{2\epsilon}<3/28.}\tag{QT.9}
\]

Set \(\alpha=\epsilon+dt\). Since \(\sqrt\epsilon<19/250\),
\[
\alpha<\epsilon+2\sqrt\epsilon
<\frac1{175}+\frac{19}{125}<\frac4{25}.
\tag{QT.10}
\]
The inequalities \(|F|>2H_1-\epsilon\) and (QT.8) force **both**
\[
J(c-P)>H_1-\alpha,\qquad J(c-Q)>H_1-\alpha.
\]
By (QT.4) and monotonicity of D,
\[
\boxed{|c-P|<17/40,\qquad |c-Q|<17/40.}\tag{QT.11}
\]

Next we bootstrap these bounds to the **exact quadratic zone** \(|c-P|,|c-Q|<k\).

If \(P,Q\le2\), the allowed region of (QT.2), before the diagonal band is applied, is precisely the union of the two corner squares A,D. Any positive overlap only **subtracts area**. If either midpoint offset had absolute value at least k, (QT.3) and monotonicity would imply
\[
B-|F|\ge k^2>\epsilon,
\]
a contradiction.

If \(P>2,Q\le2\), the allowed region is the two disjoint corner squares plus the bridging rectangle
\[
R=[1,P-1]\times[Q-1,1].
\]
Its area is \(ab\), with \(a=P-2>0\), \(b=2-Q=t\). From (QT.11),
\[
a+b=P-Q<17/20,\qquad 0\le b<3/28.
\]
The function \(b(17/20-b)\) is increasing on this b-range, so
\[
ab<b(17/20-b)
<\frac3{28}\left(\frac{17}{20}-\frac3{28}\right)
=\frac{39}{490}.
\tag{QT.12}
\]
If one square's band-center offset had absolute value at least k, then
\[
B-|F|\ge k^2-ab>\frac3{35}-\frac{39}{490}
=\frac3{490}>\frac1{175},
\]
again contradicting (QT.6). The bridge may have zero height when \(Q=2\), in which case the same argument applies with \(ab=0\).

We have proved
\[
\boxed{|c-P|<k,\qquad|c-Q|<k.}\tag{QT.13}
\]
Moreover the overlap/bridge rectangle is **entirely within the diagonal band**: in the case \(P,Q\le2\), the overlap sum-coordinate ranges from \(P+Q-2\) to 2, and both endpoints are within \(k+t<3/10+3/28<d/2\) of c; in the case \(P>2,Q\le2\), the bridge sum-coordinate ranges from Q to P, each within k of c.

Therefore we have the exact area identity, valid even when one width equals 2 and a zero-area line joins the corners:
\[
\begin{aligned}
|F|
&=J(c-P)+J(c-Q)-(P-2)(Q-2)\\
&=B-(c-P)^2-(c-Q)^2-(P-2)(Q-2).
\end{aligned}\tag{QT.14}
\]
Let \(x=P-2,\ y=Q-2,\ h=c-2\). Completing squares gives the **positive definite exact stability identity**
\[
\boxed{
B-|F|=(h-x)^2+(h-y)^2+xy
=\frac{x^2+y^2}{2}
+2\left(h-\frac{x+y}{2}\right)^2.
}\tag{QT.15}
\]
Hence
\[
\boxed{x^2+y^2<2\epsilon,\qquad
|7y-x|<10\sqrt\epsilon<19/25.}\tag{QT.16}
\]

We need one more consequence. Put \(a=c-P=h-x\), \(b=c-Q=h-y\). Since \(xy=(h-a)(h-b)\), another completion of squares yields
\[
B-|F|
=\frac23a^2+\frac34(b+a/3)^2
+\left(h-\frac{a+b}{2}\right)^2.
\tag{QT.17}
\]
Thus, **in either oriented coordinate order**,
\[
\boxed{
|c-P|,\ |c-Q|<
\sqrt{3\epsilon/2}=\sqrt{3/350}<93/1000.
}\tag{QT.18}
\]
The original midpoint rigidity was fourth-root in the area loss; QT.15--QT.18 are square-root bounds, with no regularity assumption on S.

## 3. Two triangular support reservoirs that the sofa cannot avoid

Return to the original **oriented** coordinates u,v from (QT.2), without exchanging their labels. Put
\[
\tau=\frac3{10}.
\]
Inside the lower-right unit corner square A, consider the triangle
\[
T_A=\{(u,v):7(P-u)+v\le\tau,\ u\le P,\ v\ge0\}.
\tag{QT.19}
\]
Inside the upper-left unit corner D, consider its reflected analogue
\[
T_D=\{(u,v):u+7(Q-v)\le\tau,\ u\ge0,\ v\le Q\}.
\tag{QT.20}
\]
Each is a right triangle of **exact area**
\[
\boxed{|T_A|=|T_D|=\frac{\tau^2}{14}
=\frac9{1400}>\frac1{175}=\epsilon.}\tag{QT.21}
\]
They lie entirely inside their respective unit squares since \(\tau<1\) and \(\tau/7<1\). They also lie entirely inside the incoming diagonal band: the sum coordinate on \(T_A\) lies between \(P-\tau/7\) and \(P+\tau\) (and similarly relative to Q on \(T_D\)), whereas QT.18 gives \(|c-P|,|c-Q|<93/1000\); thus the distance to c is at most \(93/1000+\tau<393/1000<d/2\). Hence \(T_A,T_D\subset F\).

Since \(|F\setminus S|<\epsilon\), both triangles contain actual points of the sofa. Choose \(p_A=(u_A,v_A)\in S\cap T_A\) and \(p_D=(u_D,v_D)\in S\cap T_D\). Their defining inequalities give
\[
\boxed{7(P-u_A)+v_A\le\tau,\qquad
u_D+7(Q-v_D)\le\tau.}\tag{QT.22}
\]
These are **actual retained support witnesses**, not merely points of the convex hull. Their presence follows from area alone.

## 4. The forced forbidden wedge has area greater than \(\epsilon\)

Consider the additional **proper lower-turn hallway at**
\[
\alpha=\arcsin(3/5),\qquad
\nu=(4/5,3/5),\quad\nu^\perp=(-3/5,4/5).
\]
Under the original u,v coordinates (up to harmless translation), these affine normal functionals have linear parts
\[
\nu\cdot(x,y)=\frac{7u-v}{5\sqrt2},\qquad
\nu^\perp\cdot(x,y)=\frac{u+7v}{5\sqrt2}.
\tag{QT.23}
\]
For a potential sofa point \(p=(u,v)\), the two retained witnesses QT.22 give
\[
\begin{aligned}
5\sqrt2\,[h_S(\nu)-\nu\cdot p]
&\ge 7u_A-v_A-(7u-v)
\ge7P-\tau-7u+v,\\
5\sqrt2\,[h_S(\nu^\perp)-\nu^\perp\cdot p]
&\ge u_D+7v_D-u-7v
\ge7Q-\tau-u-7v.
\end{aligned}\tag{QT.24}
\]
An ordinary unit hallway containing the whole sofa requires **at least one** of these actual support depths to be at most one, at every p. So every p for which both RHS's in QT.24 exceed \(5\sqrt2\) must be *absent* from S.

Write \(u=P-1+r\) and \(\eta=5\sqrt2-7\). Define two affine bounds
\[
L(r)=\eta+\tau+7r,\qquad
U(r)=\frac{7Q-P+1-\tau-5\sqrt2-r}{7}.
\]
The forbidden region contains the triangle
\[
\mathcal W=\{(r,v):0<r<N/50,\quad L(r)<v<U(r)\},
\tag{QT.25}
\]
where
\[
\boxed{N=7Q-P+50-40\sqrt2-8\tau.}
\tag{QT.26}
\]
Indeed \(U(r)-L(r)=(N-50r)/7\); both support depths from QT.24 are then strictly greater than one. The drift estimate QT.16 and (QT.5) yield
\[
\boxed{
\frac{397}{175}<N<\frac{19}{5}<4.
}\tag{QT.27}
\]
For the lower inequality use \(7Q-P=12+7y-x\), \(62-40\sqrt2>38/7\), and \(10\sqrt\epsilon<19/25\), so \(N>38/7-12/5-19/25=397/175\). For the upper use \(\sqrt2>707/500\) and the opposite drift sign.

We will retain the **strictly interior** subtriangle
\[
\mathcal W'=\mathcal W\cap\{r\ge1/500\}.
\tag{QT.28}
\]
This small cutoff makes the entire forbidden region lie inside the **incoming diagonal band**, not merely inside the four hallway outer walls. Verify that geometrically:

1. From QT.27, \(0<r<N/50<19/250<1/10\). The bounds \(0<L(r)<U(r)<1\) hold whenever the wedge is nonempty: \(L(r)>0\), while \(U(r)\le U(0)\), and using \(5\sqrt2>7\) with the drift \(7y-x<19/25\) gives \(U(0)<(13-3/10-7+19/25)/7<1\). Therefore each wedge point is inside the **lower-right corner square** \(A=[P-1,P]\times[0,1]\).
2. Since \(\sqrt2>7071/5000\), we have \(\eta>71/1000\). For \(r\ge1/500\), \(v>L(r)\) implies
\[
u+v>P-1+\eta+\tau+8r
>P-\frac{613}{1000}.
\]
But the lower boundary of the incoming band satisfies
\[
c-\frac{\sqrt2}{2}
<P+\frac{93}{1000}-\frac{707}{1000}
=P-\frac{614}{1000}
\]
by QT.18 and \(\sqrt2/2>707/1000\). So every wedge point lies **above** the incoming band bottom.
3. For its upper boundary, \(u+v<P+1/10\) since \(r<1/10,v<1\), while
\[
c+\frac{\sqrt2}{2}
>P-\frac{93}{1000}+\frac{707}{1000}
=P+\frac{614}{1000}.
\]
Thus every wedge point is **below** the band top.

It follows rigorously that
\[
\boxed{\mathcal W'\subset F\setminus S.}\tag{QT.29}
\]
Its area is computed by a single triangle integral:
\[
\begin{aligned}
|\mathcal W'|
&=\int_{1/500}^{N/50}\frac{N-50r}{7}\,dr\\
&=\frac{N^2}{700}-\int_0^{1/500}\frac{N-50r}{7}\,dr\\
&>\frac{(397/175)^2}{700}-\frac{19}{17500}\\
&=\frac{134334}{21437500}
>\frac1{175}=\epsilon.
\end{aligned}\tag{QT.30}
\]
The last inequality is **entirely rational**:
\(134334>122500=21437500/175\).

This contradicts \(|F\setminus S|<\epsilon\). Thus (QT.6) is impossible, proving the new bound (QT.1).

## 5. Arbitrary partial turns really visit these three frames

If \(|S|>B-\epsilon\), then \(|S|>\sqrt2\) (since \(B-\sqrt2=\sqrt2-1>1/175\)). The no-sideways-angle and outgoing-strip argument of GH, or O'Keefe's Section 4 *Turning the right way* lemma, forces each continuous handed motion to pass through its proper \(45^\circ\) frame. In particular the lower motion also passes through \(\arcsin(3/5)<45^\circ\). **No hypothesis of monotone rotation or an already completed full quarter is introduced.** The coordinates from the two \(45^\circ\) placements and the one earlier lower placement give the three hallways used above, in one common incoming frame. Thus QT1 applies to the unrestricted common-starting-position ambidextrous problem, not merely to its full-turn subclass.

The external O'Keefe proof already gives the stronger **computer-assisted** bound \(353/200=1.765\), so QT1 does **not** supersede it numerically. Our contribution is a much more meaningful completely **hand-derived** strict gain from \(2\sqrt2-1\) than TH's \(10^{-9}\), together with an explicit positive-definite stability identity QT.15 and a constructive forbidden-area comparison. The continuing sharp \(M\) inequality remains open.

No numerical fit, long computation, CI, Lean/Lake compilation, dependency installation, or manuscript build is a premise of this theorem. A separate exact rational checker may test the finite constants, but it does not verify the continuum argument; independent mathematical review is still warranted.
