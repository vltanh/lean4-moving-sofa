# Joint terminal strips: a general full-turn-to-partial-turn value transfer

**Main results.** Let \(A_F\) be the supremum for compact connected sofas with both complete conventional quarter turns, and \(\mu_A\) the unrestricted common-starting-position ambidextrous supremum. The two actual outgoing strips give a joint bound on the **sum** of the missing turning angles. Combining this with the circular completion allowance and the existing gap-compression theorem gives
\[
A\le A_F+\lambda\!\left(\arcsin\frac1A\right),\qquad
\lambda(e)=\tan(e/2)-e/2,
\tag{JT.1}
\]
for every ambidextrous sofa of area \(A>\sqrt2\). In particular
\[
\boxed{0\le\mu_A-A_F\le1/80.}\tag{JT.2}
\]
There is also a precise sufficient route to the user's requested \(1/6\) improvement:
\[
\boxed{A_F\le33/20\quad\Longrightarrow\quad
\mu_A\le41543/25000=1.66172
<2\sqrt2-7/6.}\tag{JT.3}
\]
**The premise \(A_F\le33/20\) is NOT proved here or elsewhere in the current written chain.** Consequently this is a reduction of the target, not a proof of a new absolute upper bound of 1.66172. The current three-hallway hand theorem and the external computer-assisted 1.765 theorem remain numerically weaker than that missing premise.

The circle allowance and connectedification are not new: see CC/D4 and GC. The new step is to use the **two outgoing strips together**, instead of bounding each terminal angle independently, then use superadditivity of the circle allowance. The proof below includes the geometry of the reduction. It depends on the earlier self-reviewed GC connectedification theorem; no claim of independent or kernel verification is made.

## 1. Effective partial turns and the outgoing-strip pair

Let \(S\) have area \(A>\sqrt2\), with common incoming height \(H\le1\). By the no-sideways-angle and final-strip argument already proved in GH, each handed motion reaches its proper angles up to its terminal orientation. If it reaches the full quarter, use that quarter instead: canonical support tightening and the original incoming width give a valid full motion with an outgoing strip of width H. Otherwise use its original partial terminal position. In this way choose effective turning amounts
\[
\alpha_-,\alpha_+\in(0,\pi/2],\qquad
\varepsilon_-=\pi/2-\alpha_-,\quad
\varepsilon_+=\pi/2-\alpha_+.
\]
Each proper angle in \([0,\alpha_\pm]\) is available by continuity, without assuming that the original motion is monotone. Let \(q_-,q_+\le1\) be the actual widths of S in the two effective outgoing strip normals. For a replaced full quarter use \(q_\pm=H\).

The individual incoming/outgoing strip intersections give
\[
A\sin\varepsilon_\pm\le Hq_\pm\le1.
\]
Thus, since \(A>\sqrt2\), each \(\varepsilon_\pm<\pi/4\), and their sum \(e=\varepsilon_-+\varepsilon_+\) lies in \([0,\pi/2)\).

In the original body coordinates, choose the unoriented outgoing normals as
\[
n_{\pi/2-\varepsilon_-},\qquad
n_{\pi/2+\varepsilon_+}.
\]
Their angle is **the sum** e. The intersection of two strips of widths \(q_-,q_+\) at angle e has area \(q_-q_+/\sin e\), regardless of their translations. Because the same S lies in both strips,
\[
A\sin e\le q_-q_+.
\]
For \(e=0\) this inequality is automatic; otherwise it is the parallelogram area formula. Since e is in the interval where sine is increasing,
\[
\boxed{\varepsilon_-+\varepsilon_+
\le\arcsin(q_-q_+/A)\le\arcsin(1/A).}\tag{JT.4}
\]
This is stronger than applying the individual angle estimate twice. It concerns two endpoints of two separate motions of one rigid body; it does not require the translations or times of those motions to agree.

## 2. Completing by deletion, with the ordinary-area loss explicit

For clarity, recall the circle allowance geometrically. Suppose S lies in two strips with unit normals \(n_0,n_e\) and widths at most one, with \(0<e<\pi/2\). Let D be the intersection of their upper supporting lines. For \(0\le t\le e\), positive sine interpolation gives
\[
h_S(n_t)\le D\cdot n_t.
\]
A point p whose actual support depth \(h_S(n_t)-p\cdot n_t\) exceeds one for some intermediate normal therefore belongs to the larger region in which \(x=D-p\) satisfies
\[
x\cdot n_0\le1,\quad x\cdot n_e\le1,
\quad x\cdot n_t>1\text{ for some }t\in(0,e).
\]
The maximum of the scalar product cannot occur at the two endpoint normals. An interior maximum occurs when x points along \(n_t\), so in polar coordinates x has direction t in \((0,e)\) and radius
\[
1<r\le\min(\sec t,\sec(e-t)).
\]
Consequently this larger region has exact area
\[
\frac12\int_0^e\left[\min(\sec^2t,\sec^2(e-t))-1\right]dt
=\tan(e/2)-e/2=\lambda(e).
\tag{JT.5}
\]
Keeping the actual endpoint widths gives D4's smaller allowance, but is unnecessary here.

Apply this construction to the missing first-normal arc of each effective turn, between its outgoing normal and its incoming normal. Delete from S any point whose first support depth exceeds one on either missing arc. The remaining closed set C satisfies all original hallway constraints and all the added ones: on each added frame the selected first wall protects every retained point. Canonical support functions provide continuous full motions. The set may be disconnected, but
\[
|C|\ge A-\lambda(\varepsilon_-)-\lambda(\varepsilon_+).
\]
It is nonempty: the loss is at most \(\lambda(\pi/2)=1-\pi/4<1\), whereas \(A>\sqrt2\).

GC1--GC3 convert this compact set into a connected full-turn body of **at least** its area. Specifically, the map
\[
(x,y)\longmapsto (T(x),y),\qquad
T(x)=\int_l^x1_{\operatorname{proj}_x C}(r)\,dr
\]
collapses the empty horizontal gaps, preserves each safe support depth at most one, and preserves area. Filling its vertical fibers preserves the conventional hallway constraints, does not decrease area, and makes the result connected. The common incoming height stays at most one. The operation need not preserve the original hull or width; neither is constrained in the definition of \(A_F\).

Thus the correct **ordinary-area** inequality, including disconnected completions, is
\[
\boxed{A\le A_F+\lambda(\varepsilon_-)+\lambda(\varepsilon_+).}\tag{JT.6}
\]
No signed integral is identified with area across empty fibers, and no assumption that C was already connected is used.

## 3. Combine the angles before paying the completion cost

For \(r,s\ge0\), \(r+s<\pi/2\), the tangent addition identity gives
\[
\lambda(r+s)-\lambda(r)-\lambda(s)
=\frac{ab(a+b)}{1-ab}\ge0,
\quad a=\tan(r/2),\ b=\tan(s/2).
\]
Also \(\lambda\) is increasing, since \(\lambda'(e)=\tfrac12\tan^2(e/2)\ge0\). Combining this with JT.4 and JT.6 yields
\[
\boxed{A\le A_F+\lambda\!\left(\arcsin\frac{q_-q_+}{A}\right)
\le A_F+\lambda\!\left(\arcsin\frac1A\right).}\tag{JT.7}
\]
This proves JT.1. It gives a comparison between the two *general optimization problems*, not only between scaled reference families.

For \(a>1\), define
\[
F(a)=a-\lambda(\arcsin(1/a)).
\]
It is strictly increasing: a increases and the subtracted term decreases. Thus any full-turn upper bound \(A_F\le U\) implies an unrestricted upper bound at the unique root of \(F(a)=U\) above U, provided the small-area case \(A\le\sqrt2\) is already below the proposed threshold. Computability or attainment of either optimum is not needed for this pointwise implication.

## 4. An unconditional gap of at most 1/80

The known feasible Romik sofa gives \(A_F\ge M\), with
\[
M=1+4Y^2+\arctan Y,\quad4Y^3+3Y-1=0,\quad Y>0.
\]
The root lies between \(59/200\) and \(3/10\). Since \(\arctan y\ge y-y^3/3\) for \(y\ge0\), and the resulting polynomial is increasing on this interval,
\[
M>\frac{39229021}{24000000}>49/30>\sqrt2.
\]
For any sofa with \(A\le A_F\), the claimed value comparison is immediate. Otherwise \(A>A_F>49/30\). Put
\[
u=\tan\!\left(\tfrac12\arcsin(1/A)\right)
=\frac1{A+\sqrt{A^2-1}}.
\]
On \(0<u<1\), the inverse relation is \(A=(u+u^{-1})/2\), a decreasing function of u. The exact rational inequality
\[
49/30-\tfrac12(171/500+500/171)=59/171000>0
\]
therefore gives \(u<171/500\).

The alternating arctangent bound implies
\[
u-\arctan u\le u^3/3-u^5/5+u^7/7.
\]
The polynomial on the right is increasing on \([0,1]\), since its derivative is \(u^2(1-u^2+u^4)>0\). At \(u=171/500\) its value is
\[
\frac{682298888869763091}{54687500000000000000}<1/80,
\]
with positive rational difference \(1294861130236909/54687500000000000000\). Inserting this in JT.7 proves \(A\le A_F+1/80\) for every sofa. Taking suprema and using the obvious \(A_F\le\mu_A\) gives JT.2. The explicit rational polynomial value is in fact a slightly stronger uniform additive bound, but improving this constant is not the current objective.

This is **not** an absolute upper bound of 1/80 for any sofa area. It bounds the possible difference between the unrestricted and full-turn suprema.

## 5. Exact sufficient condition for the requested 1/6 improvement

Suppose the genuinely missing theorem \(A_F\le33/20=1.65\) were proved. Set
\[
a_0=41543/25000=1.66172,\qquad u_0=1673/5000.
\]
We verify by rational arithmetic that
\[
a_0-\tfrac12(u_0+u_0^{-1})=8233/83650000>0.
\]
Thus, for every \(A>a_0\), its half-angle parameter satisfies \(u<u_0\). The same alternating arctangent bound gives
\[
\lambda(\arcsin(1/A))
< P(u_0):=u_0^3/3-u_0^5/5+u_0^7/7.
\]
The exact margin is
\[
a_0-33/20-P(u_0)
=\frac{1117653653116181013187}{234375000000000000000000000}>0.
\]
JT.7 would consequently give
\[
A\le33/20+P(u_0)<a_0,
\]
contradicting \(A>a_0\). So \(\mu_A\le a_0\).

Finally
\[
8-(a_0+7/6)^2=\frac{1287359}{5625000000}>0,
\]
and both sides of the square-root comparison are positive. Hence
\[
\boxed{\mu_A\le1.66172<2\sqrt2-7/6.}
\]
This proves the implication JT.3 **without asserting its premise**. It means a proof of the full-turn bound 1.65 would already suffice for the requested unrestricted 1/6 gain; one would not also need to prove that every partial turn completes without loss, or to prove exact Romik optimality.

For orientation only, substituting the conjectural \(A_F=M\) in the implicit transfer would give a bound about 1.656789. This decimal is explanatory and conditional, not a proved unrestricted upper bound.

## 6. What remains unproved and what the bounded tests mean

No current result proves \(A_F\le33/20\). The existing three-hallway argument cannot establish it: the companion SX note constructs a connected area-5/3 polygon satisfying even six of those fixed positions. A short, fixed-iteration local search with denser rational-angle meshes was used only to assess the next finite formulation; its values are lower witnesses or approximate local values, never global upper certificates. In particular a local value below 1.65 does not establish that all placements are below 1.65.

The new mathematical gain is JT.4 and its consequences JT.2--JT.3. These are hand arguments, with prior dependencies on the documented canonical motion setup, the feasible reference lower bound, and GC connectedification. They have not been independently refereed or Lean-verified. No CI, Lean/Lake compilation, dependency installation, manuscript build, or long search was used. The requested absolute upper bound and Romik optimality remain unproved.
