# Exact angle-by-angle inner-corner and niche-area cost of rectangle filling

**Theorem FAP1 (fully general filled-core angular identity).**
Let V be any compact convex downward core of vertical
height at most \(1-h\), and let \(T,h\ge0\).
Form the expanded one-turn cap
\[
U=V+([0,T]\times[0,h]),
\]
which is assumed to lie in an incoming strip of
height at most one. The core V may be curved,
polygonal, asymmetric and nonsmooth; no
Gerver/Romik contact phase is assumed.

At any conventional turning angle
\(0<t<\pi/2\), set \(c=\cos t,s=\sin t\),
\(u=(c,s)\), \(v=(-s,c)\). Let the two
outer support values be \(f_X=h_X(u)\),
\(g_X=h_X(v)\) for \(X=V,U\).
Then
\[
\boxed{
f_U=f_V+Tc+hs,\qquad
g_U=g_V+hc.
}
\tag{FAP.1}
\]

Define the two *inner forbidden wall roofs*
\[
R_X(t,x)=\frac{f_X-1-xc}{s},\qquad
L_X(t,x)=\frac{g_X-1+xs}{c}
\]
and the inner corner
\[
C_X(t)=(f_X-1)u+(g_X-1)v.
\]
The exact geometric effect of the rectangular filler is

\[
\boxed{
\begin{aligned}
R_U(t,x)&=R_V(t,x-T)+h,\\
L_U(t,x)&=L_V(t,x)+h,\\
C_U(t)&=C_V(t)+(Tc^2,Tsc+h).
\end{aligned}}
\tag{FAP.2}
\]

In particular the **turn-forbidden corner rises by
exactly \(h+T\sin t\cos t\)**, regardless of
the shape or support regularity of V.

## 1. Exact positive forbidden triangle at each angle

Put
\[
x_R^X(t)=\frac{f_X(t)-1}{c},\qquad
x_L^X(t)=\frac{1-g_X(t)}s
\]
for the abscissae where the first and
second inner forbidden walls respectively
meet the horizontal baseline \(y=0\).
Let \(B_X(t)=x_R^X-x_L^X\) be their
signed separation. The two wall slopes
are \(-\cot t\) and \(+\tan t\).

For B_X>0, the positive-height forbidden
quadrant is *exactly* the open right-angled
triangle with horizontal baseline length
B_X and apex height
\[
H_X(t)=B_X(t)\,s c.
\]
For B_X≤0 there is no positive-height
forbidden region. Thus the true ordinary
area of this single-angle forbidden triangle is
\[
\boxed{
\mathcal N_{X,t}=
\frac12\,sc\,\bigl(B_X(t)_+\bigr)^2.
}
\tag{FAP.3}
\]
This counts the actual positive plane region
at **one** angular placement. It does not
sum overlapping forbidden triangles from
different angles.

Using FAP.1 gives the exact baseline and
corner increases
\[
\boxed{
\begin{aligned}
x_R^U&=x_R^V+T+h\tan t,\\
x_L^U&=x_L^V-h\cot t,\\
B_U(t)&=B_V(t)+T+\frac{h}{sc},\\
H_U(t)&=H_V(t)+Tsc+h.
\end{aligned}}
\tag{FAP.4}
\]

Therefore the **entire single-angle area
contribution** of the filled cap is
\[
\boxed{
\mathcal N_{U,t}
=\frac12 sc\left(
B_V(t)+T+\frac{h}{sc}
\right)_+^2.
}
\tag{FAP.5}
\]

If U is a genuine normalized one-turn
cap of height at most one, its complete
niche N(U) contains this single-angle
triangle, so for each chosen real angle t,
\[
\boxed{|N(U)|\ge \mathcal N_{U,t}.}
\tag{FAP.6}
\]
No finite-angle sampling claim is made;
this is one exact admissible forbidden
subset. Using multiple angles requires
a rigorously computed *union*, not the sum
of their areas.

## 2. Proof of the wall and area identities

The support function of a Minkowski sum
is the sum of the support functions.
The rectangle [0,T]×[0,h] has support
\(Tc+hs\) in direction u, and \(hc\)
in direction v, because v has a negative
horizontal and positive vertical component.
This gives FAP.1.

Insert FAP.1 into the two roof formulas:
\[
R_U(t,x)
=\frac{f_V-1-(x-T)c}{s}+h,
\qquad
L_U(t,x)
=\frac{g_V-1+xs}{c}+h.
\]
The inner corner is expressed in the
orthonormal basis (u,v). Its difference
is \(Tc\,u+hs\,u+hc\,v\).
The h contribution simplifies because
\(s u+c v=(0,1)\), giving
\((Tc^2,Tsc+h)\). This proves FAP.2.

The two baseline roots differ by B_X.
Their wall functions are the two sides
of a triangle above the baseline if B_X>0,
with intersection height B_X sc.
Ordinary triangle area is half the
base times height, proving FAP.3.
The new right root increases by
\(T+h\tan t\) and the new left root
decreases by \(h\cot t\).
Since \(\tan t+\cot t=1/(sc)\),
FAP.4 follows; substitute into FAP.3
to get FAP.5.

## 3. What this contributes to the user's idea

Earlier [UHCD1](universal-horizontal-core-decomposition.md)
established that the horizontal face-length
segment is already a genuine Minkowski
summand of **every** downward convex cap.
FAP1 now gives the **exact angle-by-angle
collision penalty** incurred by that
segment and by any vertical middle filling.

At angle pi/4 it specializes to
\[
\mathcal N_{U,\pi/4}
=\frac14\bigl(B_V(\pi/4)+T+2h\bigr)_+^2.
\]
This is the geometric mechanism behind
the two independent positive forbidden
triangles in the triangular-core sharp
theorem TCG1.

For genuinely curved Gerver-like cores,
the union over **all** angles is crucial;
one cannot simply integrate FAP.5 with
respect to t, as that would count
overlapping forbidden regions repeatedly.
The sharp two-cap area bound still
requires a global, overlap-aware lower
bound on the **effective** forbidden area
inside the other one-turn cap, not just
the full forbidden triangle N(U).
The exact core-pair area identity in
[UHCD.6](universal-horizontal-core-decomposition.md)
makes the latter distinction explicit.

This is an entirely pen-and-paper identity.
No numerical optimizer, Lean formalization,
CI, or unrestricted optimality claim is involved.
