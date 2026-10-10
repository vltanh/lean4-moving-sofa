# A \(1/51\) computer-free global ambidextrous bound via a two-sided clipping dual

**Main theorem (JD1).** Every compact connected sofa that can turn around the right-angle unit hallway corner **in both directions from one common incoming position**, through arbitrary continuous, partial or nonmonotone motions, has area
\[
\boxed{|S|\le 2\sqrt2-1-\frac1{51}<1.808821.}
\tag{JD.1}
\]
The same holds for the complete-full-turn subclass. The proof is entirely **pen and paper**; the only externally needed motion fact is the already hand-proved GH no-sideways-angle/endpoint-strip reduction guaranteeing passage through both proper \(45^\circ\) orientations and the earlier proper \(36.87^\circ\) lower orientation when \(|S|>\sqrt2\). It supersedes the initial \(10^{-9}\), the intermediate \(1/175\), and the [JH \(1/90\)](coupled-three-hallway-hand-bound.md) computer-free bounds. It remains numerically weaker than O'Keefe's computer-certified \(353/200=1.765\), and **does not prove** Romik's sharp \(M\approx1.644955\). Labels JD are local.

**Key new step.** The JH proof subtracted a worst-case geometric clipping allowance from a weighted Cauchy--Schwarz lower bound. Here both clipping terms are retained **as positive-part squares of linear functionals**. The weighted quadratic is minimized under the exact support relationship. Its variance from that minimizer automatically pays the lower clipping, while a separate variation bound pays upper clipping whenever that wall actually becomes active. Empty forbidden wedges and the zero-area midpoint connectors are handled explicitly. The hand improvement is \(1/51\approx0.019608\), about **19.6 million times** the original tiny gain.

## 1. Two-midpoint enclosure and preliminary near-equality rigidity

Put
\[
d=\sqrt2,\quad k=1-d/2,\quad H_1=d-\tfrac12,\quad
B=2H_1=2\sqrt2-1,\quad
\epsilon=\frac1{51}.
\]
Our two proper opposite-handed \(45^\circ\) hallways enclose the sofa after an isometry in
\[
F(P,Q,c)=\left\{(u,v):
\begin{array}{l}
0\le u\le P,\ 0\le v\le Q,\\
(u\ge P-1\ \text{or}\ v\ge Q-1),\\
(u\le1\ \text{or}\ v\le1),\\
c-d/2\le u+v\le c+d/2
\end{array}\right\}
\tag{JD.2}
\]
for some \(P,Q>0,c\in\mathbb R\). The incoming strip height may be below one; taking its full unit-width band only enlarges F. The MH hand theorem gives \(|F|\le B\).

For a unit square, let \(J(h)\) be its area in a sum-coordinate band of width \(d\) whose center differs by h from the square's sum-coordinate center. Its triangular one-dimensional convolution density shows that \(J\) is even and nonincreasing in \(|h|\), and with \(D(h)=H_1-J(h)\),
\[
D(h)=h^2\quad(|h|\le k),\qquad
D(h)=\tfrac12(|h|+k)^2-k^2
\quad(k\le|h|\le7/10).
\tag{JD.3}
\]
The latter identity holds on this range since \(7/10<d/2\).

**Lemma JD2 (sufficient preliminary localization).** If
\[
\boxed{S\subset F,\ S\text{ connected},\quad |S|>B-\epsilon,}
\tag{JD.4}
\]
then both \(|c-P|\) and \(|c-Q|\) are less than k, and in fact
\[
\boxed{
B-|F|=\frac{(P-2)^2+(Q-2)^2}{2}
+2\left(c-\frac{P+Q}{2}\right)^2.
}\tag{JD.5}
\]
Consequently
\[
\boxed{
(P-2)^2+(Q-2)^2<2\epsilon,\qquad
|7(Q-2)-(P-2)|<10\sqrt\epsilon<\frac{141}{100},
}
\tag{JD.6}
\]
and
\[
\boxed{|c-P|,\ |c-Q|<\sqrt{3\epsilon/2}
=\sqrt{1/34}<\frac{43}{250}.}
\tag{JD.7}
\]

**Proof of the lemma.** The \(\min(P,Q)\le1\) case gives \(|F|\le d<B-\epsilon\). If both \(P,Q>2\), the two unit corner squares are strictly separated and connected S occupies only one, of area at most \(H_1\), also impossible. **When one dimension equals 2**, possible *zero-area connector lines* are retained in the subsequent area calculation.

For this **symmetric area-localization argument only**, swap the u,v labels if needed so \(1<Q=\min(P,Q)\le2\). Set \(t=2-Q\), \(q=Q-1=1-t\). MH's lower/middle/upper v-layer analysis gives
\[
|F|\le f_d(q)=d(1-q)+2q-\tfrac12(1+q-d)_+^2.
\]
For \(q\le d-1\), the deficit is at least \((2-d)^2/2>1/8>\epsilon\). For \(q>d-1\), it is exactly \(t^2/2\). Thus
\[
0\le t<\sqrt{2\epsilon}=\sqrt{2/51}<1/5.
\tag{JD.8}
\]

Let \(A=[P-1,P]\times[0,1]\), \(D_0=[0,1]\times[Q-1,Q]\) be the two unit corner squares. The first and last layers lie in these squares; the middle is at most \(dt\). Therefore
\[
|F|\le J(c-P)+J(c-Q)+dt.
\]
If \(|F|>B-\epsilon\), both square area deficits are below
\[
\alpha=\epsilon+dt<\epsilon+2\sqrt\epsilon
<\frac1{51}+\frac{282}{1000}<\frac{403}{1000}.
\]
(The rational square-root comparison is \(\sqrt{1/51}<141/1000\).) Since
\[
D(7/10)=\frac{49}{200}+\frac7{10}k-\frac{k^2}{2}
>\frac{49}{200}+\frac7{10}\frac{29}{100}-\frac9{200}
=\frac{403}{1000},
\]
monotonicity of D implies \(|c-P|,|c-Q|<7/10\).

Throughout this range a stronger pointwise bound holds:
\[
\boxed{D(h)\ge\frac45h^2\quad(|h|\le7/10).}\tag{JD.9}
\]
For \(|h|\le k\) it is immediate. For \(k\le|h|\le7/10\), the difference is
\(-\frac3{10}h^2+k|h|-\frac12k^2\), concave in \(|h|\). At \(h=k\) it is \(k^2/5>0\); at \(7/10\) it exceeds \(-147/1000+203/1000-45/1000=11/1000>0\), using \(29/100<k<3/10\).

Now if \(P,Q\le2\), the allowed region is exactly the union of A and \(D_0\), with any overlap subtracted. If either offset \(|c-P|\) or \(|c-Q|\) were at least k, the deficit would be at least \(k^2>\epsilon\), impossible.

If \(P>2,Q\le2\), the allowed region consists of A, \(D_0\), and a central bridging rectangle of area \(ab\), where \(a=P-2\ge0\) and \(b=2-Q=t<1/5\). Write \(u=c-P,\ v=c-Q\), so \(v-u=a+b\). Consequently
\[
B-|F|\ge D(u)+D(v)-ab
\ge\frac45(u^2+v^2)+bu-bv+b^2.
\]
Suppose one of \(|u|,|v|\) were at least k. Minimizing the two quadratics in u,v, subject to that one lower-magnitude constraint, yields
\[
B-|F|\ge\frac45k^2-bk+\frac{11}{16}b^2
>\frac45\left(\frac{29}{100}\right)^2
-\frac3{10}b+\frac{11}{16}b^2
\ge\frac{1739}{50000}>\epsilon.
\tag{JD.10}
\]
For the last inequality the displayed convex quadratic is decreasing on \(0\le b\le1/5\), and the lower value is its value at \(b=1/5\). We used \(b/(2\cdot4/5)<k\), so the adverse constrained variable is minimized at magnitude k; the other completes a square. This also covers the \(b=0\) zero-area connector case.

Hence \(|c-P|,|c-Q|<k\). The overlap of A and \(D_0\) for \(P,Q\le2\), and the bridge for \(P>2,Q\le2\), are **entirely within the diagonal band**: their sum-coordinate endpoints are within \(k+t<3/10+1/5<d/2\) of c. Counting the overlap with a minus sign and the bridge with a plus sign gives
\[
|F|=J(c-P)+J(c-Q)-(P-2)(Q-2).
\]
Using \(D(h)=h^2\) in this range gives (JD.5). Complete squares to deduce (JD.6). For the final bound, put \(x=P-2,y=Q-2,h=c-2\), then \(a_0=c-P=h-x,b_0=c-Q=h-y\); the identity
\[
B-|F|=\frac23a_0^2+\frac34(b_0+a_0/3)^2+
\left(h-\frac{a_0+b_0}{2}\right)^2
\]
(and its swapped counterpart) gives \(|c-P|,|c-Q|<\sqrt{3\epsilon/2}<43/250\). QED.

The u,v swap was used only inside this symmetric lemma. We henceforth use **the original oriented coordinates**, required for the third lower-turn hallway.

## 2. Two absent support triangles and a potentially clipped forbidden wedge

Assume (JD.4) throughout, so \(|F\setminus S|<\epsilon\).

Put \(\tau=21/40\). At each of the two corner squares A,\(D_0\), the score triangles
\[
T_A(\tau)=\{(u,v)\in A:7(P-u)+v\le\tau\},\quad
T_D(\tau)=\{(u,v)\in D_0:u+7(Q-v)\le\tau\}
\tag{JD.11}
\]
are inside F: the sum coordinate differs from P or Q by at most \(\tau\), and \(\tau+43/250=697/1000<d/2\). Their exact areas are
\[
\boxed{\frac{\tau^2}{14}=\frac{63}{3200}>\frac1{51}=\epsilon.}
\]
Thus both meet S. On the compact intersections \(S\cap A,S\cap D_0\), define the minimum scores
\[
s_A=\min(7(P-u)+v),\qquad s_D=\min(u+7(Q-v)).
\]
They lie in \([0,\tau]\). The corresponding *open* triangles of score strictly below these minima belong to \(F\setminus S\) and together contribute the disjoint area
\[
\boxed{\frac{s_A^2+s_D^2}{14}.}
\tag{JD.12}
\]
These are actual **missing** regions forced by retained sofa support points, not assumed tangent geometry.

The proper third **lower** hallway has unit normal pair
\(\nu=(4/5,3/5),\ \nu^\perp=(-3/5,4/5)\). In the current u,v frame its two normal forms, up to translation, are
\[
f(u,v)=\frac{7u-v}{5\sqrt2},\qquad
g(u,v)=\frac{u+7v}{5\sqrt2}.
\tag{JD.13}
\]
The minimum-score sofa points force the actual support depths at a point \(p=(u,v)\) to obey
\[
5\sqrt2[h_S(\nu)-\nu\cdot p]\ge 7P-s_A-7u+v,\qquad
5\sqrt2[h_S(\nu^\perp)-\nu^\perp\cdot p]\ge 7Q-s_D-u-7v.
\tag{JD.14}
\]
Any point satisfying both lower bounds *strictly above \(5\sqrt2\)* cannot belong to a sofa fitting **any** placement of that third unit hallway: every feasible point must be protected by at least one actual-support inner wall.

Write \(u=P-1+r\), \(\eta=5\sqrt2-7>0\), and
\[
L(r)=\eta+s_A+7r,\quad
U(r)=\frac{7Q-P+1-s_D-5\sqrt2-r}{7}.
\]
Let
\[
x=P-2,\quad y=Q-2,\quad h=c-2,\quad
C=62-40\sqrt2,\qquad
\boxed{N=C+7y-x-7s_A-s_D.}
\tag{JD.15}
\]
Then \(U(r)-L(r)=(N-50r)/7\).

**Case \(N\le0\).** The support data already force enough missing tip/base area to contradict (JD.4). Indeed \(C=N+x-7y+7s_A+s_D\), so \(x-7y+7s_A+s_D=C-N\ge C>0\). Weighted Cauchy--Schwarz gives
\[
\frac{x^2+y^2}{2}+\frac{s_A^2+s_D^2}{14}
\ge\frac{(x-7y+7s_A+s_D)^2}{2+98+686+14}
\ge\frac{C^2}{800}
>\frac{(38/7)^2}{800}>\epsilon.
\]
These terms already occur in \(B-|S|\), a contradiction. Therefore we may assume **\(N>0\)**.

In that case every point in the open triangular wedge
\[
W=\{(r,v):0<r<N/50,\quad L(r)<v<U(r)\}
\tag{JD.16}
\]
violates both actual third-hallway support depths. Its **full** area is \(N^2/700\). However, unlike the JH proof, we do **not** assume W entirely below \(v=1\). We charge all needed clipping explicitly.

First, \(N<C+|7y-x|<6+141/100=741/100\) by (JD.6), hence \(0<r<N/50<3/20\) and \(P-1<u<P\). Also \(v>L(r)>0\). Above the horizontal level \(v=1\), since \(U(r)=U(0)-r/7\), the missing wedge portion is bounded by
\[
\int_0^\infty(U(0)-1-r/7)_+\,dr
=\frac{(\Theta_+)^2}{14},\qquad
\boxed{\Theta=7y-x-(5\sqrt2-6)-s_D.}
\tag{JD.17}
\]
Here \(\Theta_+=\max(\Theta,0)\) and \(U(0)-1=\Theta/7\).

After enforcing \(v\le1\), the wedge lies in the lower-right corner square A. Its sum coordinate satisfies \(u+v<P+3/20\), whereas the incoming band's **upper** boundary is
\(c+d/2>P-43/250+707/1000>P+1/2\). So upper-band clipping is impossible. The lower boundary requires
\[
v\ge(c-P)+k-r,\qquad k=1-\sqrt2/2.
\]
The difference between this lower band line and the wedge's lower line \(L(r)\) is \(\Delta-8r\), where
\[
\boxed{\Delta=k+(c-P)-\eta-s_A.}\tag{JD.18}
\]
Thus the wedge's part below the band has area at most
\[
\int_0^\infty(\Delta-8r)_+\,dr
=\frac{(\Delta_+)^2}{16}.
\]
We have therefore identified an **actual missing region** in F of area at least
\[
\boxed{\frac{N^2}{700}
-\frac{(\Delta_+)^2}{16}
-\frac{(\Theta_+)^2}{14}.}
\tag{JD.19}
\]

The central region and the two absent tip triangles from JD.12 are mutually disjoint. Indeed the central wedge has \(P-1<u<P-17/20\); the lower-right tip triangle has \(u>P-\tau/7>P-1/10\), and the upper-left tip triangle has \(u\le\tau=21/40<P-1\), since \(P>2-1/5\). The bounds remain valid even if the central region is reduced to a line or empty after clipping. Consequently
\[
\begin{aligned}
B-|S|
&=(B-|F|)+|F\setminus S|\\
&\ge
\underbrace{\left[\frac{x^2+y^2}{2}
+2\left(h-\frac{x+y}{2}\right)^2
+\frac{s_A^2+s_D^2}{14}+\frac{N^2}{700}\right]}_{=:Q_0}\\
&\hspace{20mm}
-\frac{(\Delta_+)^2}{16}
-\frac{(\Theta_+)^2}{14}.
\end{aligned}\tag{JD.20}
\]

## 3. The quadratic **variance identity** pays the lower clipping

Put \(\omega=h-(x+y)/2\), and regard
\[
z=(N,x,y,s_A,s_D,\omega)
\]
as a vector with the diagonal positive weighted squared norm
\[
Q_0=\frac{N^2}{700}+\frac{x^2+y^2}{2}
+\frac{s_A^2+s_D^2}{14}+2\omega^2.
\tag{JD.21}
\]
The affine support identity from JD.15 is
\[
\boxed{C=N+x-7y+7s_A+s_D.}\tag{JD.22}
\]
Weighted Cauchy--Schwarz shows \(Q_0\ge C^2/1500\), with the exact sum of inverse-weight coefficients
\[
700+2+98+686+14=1500.
\]
More importantly, the **exact minimizer** on JD.22 is
\[
\boxed{
z_*=\left(\frac{7C}{15},\,\frac C{750},\,
-\frac{7C}{750},\,\frac{49C}{750},\,
\frac{7C}{750},\,0\right).
}
\tag{JD.23}
\]
Because \(z_*\) is the weighted orthogonal projection of the origin onto the affine plane JD.22, there is the **exact Pythagorean identity**
\[
\boxed{Q_0=\frac{C^2}{1500}
+\|z-z_*\|_{\mathrm{weighted}}^2.}
\tag{JD.24}
\]
This can alternatively be checked by direct expansion; it does not assume the area maximizer itself has Romik's support or any particular contact pattern.

Express the lower-band clipping parameter JD.18 using these same variables:
\[
\Delta=A_0+\omega-\frac x2+\frac y2-s_A,\qquad
A_0=k-\eta=8-\tfrac{11}{2}\sqrt2.
\]
Its value at the quadratic minimizer is
\[
\boxed{\Delta_*=A_0-\frac{53C}{750}<0.}\tag{JD.25}
\]
Indeed \(A_0<k<3/10\), whereas \(53C/750>53(38/7)/750>3/10\), since \(C>38/7\).

The squared dual norm of the linear functional
\(z\mapsto\Delta-\Delta_*\) against the weighted norm JD.21 is **exactly**
\[
\frac{(1/2)^2}{1/2}
+\frac{(1/2)^2}{1/2}
+\frac{1^2}{1/14}
+\frac{1^2}{2}
=\frac{31}{2}<16.
\]
Therefore
\[
(\Delta-\Delta_*)^2
\le\frac{31}{2}\,\|z-z_*\|_{\mathrm{weighted}}^2.
\]
If \(\Delta>0\), then \(\Delta-\Delta_*>\Delta\), so this bound and JD.24 show that the positive variance pays **more** than \(\Delta^2/16\). If \(\Delta\le0\), that clipping cost is zero. In both cases,
\[
\boxed{Q_0-\frac{(\Delta_+)^2}{16}
\ge\frac{C^2}{1500}.}
\tag{JD.26}
\]
This is stronger than JH's crude worst-case subtraction, and is the decisive hand step.

## 4. The remaining **upper** clipping is either absent or forces extra variance

Recall \(\Theta=7y-x-(5\sqrt2-6)-s_D\).

**Case \(\Theta\le0\).** The upper penalty vanishes. Using JD.20 and JD.26,
\[
B-|S|\ge \frac{C^2}{1500}
>\frac{(38/7)^2}{1500}
=\frac{1444}{73500}
>\boxed{\frac1{51}=\epsilon}.
\tag{JD.27}
\]
The last rational comparison is \(1444\cdot51=73644>73500\). This contradicts (JD.4).

**Case \(\Theta>0\).** The value of \(\Theta\) at the quadratic minimizer JD.23 is
\[
\boxed{\Theta_*=
-\frac{19C}{250}-(5\sqrt2-6)<-\frac{29}{20}.}
\tag{JD.28}
\]
The inequality follows from \(C>38/7\) and \(\sqrt2>7071/5000\), yielding \(19C/250+(5\sqrt2-6)>722/1750+1071/1000>29/20\).

The squared dual norm of \(z\mapsto\Theta-\Theta_*\) equals
\[
\frac{(-1)^2}{1/2}+\frac{7^2}{1/2}
+\frac{(-1)^2}{1/14}=2+98+14=114.
\]
Hence JD.24 gives
\[
Q_0-\frac{C^2}{1500}
\ge\frac{(\Theta-\Theta_*)^2}{114}
>\frac{(29/20)^2}{114}
=\frac{841}{45600}.
\tag{JD.29}
\]

The two positive clipping terms have explicit small bounds, using JD.6--JD.7:
\[
\begin{aligned}
\Delta_+&\le k+|c-P|-\eta
<\frac{293}{1000}+\frac{43}{250}-\frac{71}{1000}
=\frac{394}{1000}<\frac25,\\
\Theta_+&\le |7y-x|-(5\sqrt2-6)
<\frac{141}{100}-\frac{1071}{1000}
=\frac{339}{1000}<\frac{17}{50}.
\end{aligned}\tag{JD.30}
\]
(The first strict estimate \(k<293/1000\) follows from \(\sqrt2>7071/5000\).)

Combining JD.20, JD.29 and JD.30, without incorrectly using JD.26 and the **same** variance twice, yields
\[
\begin{aligned}
B-|S|
&>
\frac{(38/7)^2}{1500}
+\frac{841}{45600}
-\frac{(2/5)^2}{16}
-\frac{(17/50)^2}{14}\\
&=\boxed{\frac{1107821}{55860000}}
>\boxed{\frac1{51}=\epsilon}.
\end{aligned}\tag{JD.31}
\]
The exact positive difference is
\[
\frac{1107821}{55860000}-\frac1{51}
=\frac{212957}{949620000}>0.
\]
This again contradicts (JD.4).

All possibilities \(N\le0\), or \(N>0\) with either sign of \(\Theta\), have been handled. Thus the area bound (JD.1) follows.

## 5. Motion coverage, mathematical status, and verification boundary

As in GH/O'Keefe's no-sideways-angle lemma, any sofa of area greater than \(B-1/51>\sqrt2\) making both handed continuous motions from the same incoming position must visit **both** proper \(45^\circ\) hallway frames. The proper lower-turn motion must also pass through the earlier \(\arcsin(3/5)\approx36.87^\circ\) frame by the intermediate-value theorem. This does not assume a monotone rotation or a completed quarter turn. Therefore the three-hallway argument above is an upper bound for **unrestricted partial and full turns**, not only a special fixed-support family.

**What has been accomplished:** a global computer-free bound below \(1.808821\), based on exact positive-definite midpoint stability, two necessary support-reservoir triangle losses, an actual third-hallway forbidden wedge, two separately controlled clipping errors, and a *weighted quadratic variance argument* that prevents counting favorable and unfavorable terms inconsistently. It makes no assumption that a maximizer is smooth, symmetric, equal to Romik's candidate, or has curvature at most one.

**What remains open:** the much stronger sharp bound \(M\approx1.644955\) and uniqueness. The external already certified \(353/200=1.765\) is still the best global upper benchmark in this project. The hand theorem is **self-reviewed**, not independently refereed or Lean-checked. A separate short exact-rational checker can test the displayed arithmetic and quadratic identities; no computation is a mathematical premise. No massive certificate, CI, Lean/Lake compilation, dependency installation or manuscript build is required.
