# No compulsory pre-turn traverse: exact corner startup slopes and the Gerver–Romik boundary difference

**Date:** October 8, 2026. **Purpose:** Address the user's observation that the ambidextrous sofa appears to waste corridor space by first moving to "the other wall" before turning. There is **no mandatory sideways pre-turn traverse** in the mathematical problem: the two handed turns are *separate motions* from the same incoming orientation/pose; straight-arm translations do not impose further area constraints. Romik's and Gerver's **assumed initial outer-wall contacts are genuinely different**, however, and the complete two-handed motion imposes **two separate start/end corner-activation constraints** on the actual common convex hull.

The result below records four **exact first-order physical inner-corner height derivatives for arbitrary nonsmooth convex hulls**, and identifies a meaningful difference between the already-controlled *aligned-face* full-turn domain and the unresolved *opposite-end-face* domain. It does **not** prove Romik's area bound, force vertical reflection symmetry, or assert area loss from a corner that falls **outside the proposed hull**.

**Source:** [Romik, Sections 4–5, equations (23), (45)–(46)](https://arxiv.org/html/1606.08111v3): Gerver is derived using the initial outer-wall contact \(A(0)=(1,0)\), whereas the ambidextrous construction assumes \(A(0)=(1,1/2)\). Both reference paths already rotate through *positive* angles from zero, with the same initial set of contacts \(\{A,C,D\}\). These **contact-height ansätze**, not a physical requirement to translate to a wall before rotation, distinguish the constructions.

## 1. Normalize the incoming strip and its two genuinely independent turns

Let \(S\) be compact and connected with \(K=\operatorname{conv}S\subseteq\mathbb R\times[0,1]\), with vertical span exactly one and horizontal projection \([l,r]\), \(W=r-l\). Suppose both conventional handed turns are available over some angle intervals, which may be partial.

Denote the **actual upper horizontal exposed face**
\[
F_{\rm top}(K)=[a,b]\times\{1\}
\]
and the **actual lower exposed face**
\[
F_{\rm bottom}(K)=[c,d]\times\{0\}.
\]
Each interval may collapse to one point.

For the canonical lower-handed frame
\[
u_t=(\cos t,\sin t),\quad v_t=(-\sin t,\cos t),
\]
its physical inner sharp corner in fixed-sofa coordinates is
\[
C_-(t)=\bigl(h_K(u_t)-1\bigr)u_t+
       \bigl(h_K(v_t)-1\bigr)v_t
      =(\xi_-(t),\eta_-(t)).
\tag{IW.1}
\]
For the upper-handed frame, reflect \(K\) vertically across the strip midline: \(\rho(x,y)=(x,1-y)\). The reflected upper-handed sharp-corner function \(C_+(t)=(\xi_+(t),\eta_+(t))\) is constructed from \(h_{\rho K}\) by the same formula. Its actual physical height is \(1-\eta_+(t)\).

At **zero angle**, the first support pair is \((r,1)\). Hence, with no smoothness,
\[
\boxed{C_-(0)=(r-1,0),\qquad
\rho C_+(0)=(r-1,1).}\tag{IW.2}
\]
The two physical corners lie on **opposite boundaries of the incoming corridor**, but these are the **two different hypothetical handed hallways**, not two physical positions a single sofa must visit in sequence. Both inward 0-angle disjunctions are already satisfied throughout the incoming unit strip. Neither imposes a positive-area initial niche or a compulsory lateral movement.

## 2. Universal one-sided derivatives of all four endpoint corner heights

**Theorem IW1 (four exact endpoint activation slopes).** For arbitrary compact convex \(K\), including nonsmooth edges or point faces, write \(L=\pi/2\). The four one-sided sharp-corner height expansions are
\[
\boxed{
\begin{aligned}
\eta_-(t)&=(r-a-1)t+o(t),
&\eta_+(t)&=(r-c-1)t+o(t)
&& (t\downarrow0),\\[2pt]
\eta_-(L-t)&=(b-l-1)t+o(t),
&\eta_+(L-t)&=(d-l-1)t+o(t)
&& (t\downarrow0).
\end{aligned}}\tag{IW.3}
\]
All heights use the corresponding **lower-handed reflected coordinate** so that positive height means the physical sharp corner enters the relevant side of the incoming corridor.

**Proof.** Put
\(f(t)=h_K(u_t)\), \(g(t)=h_K(v_t)\). Then
\[
\eta_-(t)=(f(t)-1)\sin t+(g(t)-1)\cos t.
\tag{IW.4}
\]
The support function is directionally differentiable from either side. Its directional derivative at an exposed supporting face is the maximum of the tangent-direction dot products over that face. Consequently, at the start
\[
f(t)=r+O(t),\quad
g(t)=1-a\,t+o(t),
\]
because \(v_t=(-t,1)+O(t^2)\) selects the **left endpoint** \(a\) of the upper face. Insert into IW.4 to obtain
\(\eta_-(t)=(r-a-1)t+o(t)\).

At the quarter-turn endpoint write \(\tau=L-t\); then
\[
u_\tau=(t,1)+O(t^2),\quad
v_\tau=(-1,t)+O(t^2),
\]
so
\(f(\tau)=1+b\,t+o(t)\), because the slight positive x-tilt selects the **right endpoint** \(b\) of the top face, and \(g(\tau)=-l+O(t)\).
Insert into IW.4:
\(\eta_-(L-t)=(b-l-1)t+o(t)\).
The vertically reflected hull \(\rho K\) has the same horizontal projection but top exposed face \([c,d]\times\{1\}\). Repeating gives the other two expansions. \(\square\)

**Interpretation:** A strictly positive coefficient means this one physical corner acquires positive height and creates an ambient inner-wall tent immediately. A strictly negative coefficient means its early/late tent stays below the baseline and imposes no positive-height forbidden region near that endpoint. A **zero** coefficient is inconclusive without higher-order support information. In particular an *ambient* tent can fall outside the physical hull, so **positive corner height does not by itself imply a positive ordinary material loss from an actual sofa**.

### The exact start-up baseline interval

At the lower-turn initial angle \(t>0\), a baseline point \((x,0)\) lies inside the physical inner forbidden quadrant exactly when
\[
\frac{1-g(t)}{\sin t}<x<
\frac{f(t)-1}{\cos t}.
\]
The two endpoints converge as \(t\downarrow0\) to
\[
\boxed{a,\quad r-1,}
\tag{IW.5}
\]
respectively. Thus whenever \(r-a-1>0\), a **vanishingly shallow** forbidden wedge enters over a horizontal interval of limiting length \(r-a-1\). This is the precise geometric content of the intuitive "empty/wasted initial space"; it is not a compulsory travel distance.

If \(K\) contains the entire rectangle \([a,b]\times[0,1]\) and \(a<r-1\le b\), then the true one-angle **ordinary area carved from K** at the start has the asymptotic
\[
\boxed{
\left|K\cap Q^-_{K,t}\cap\{y\ge0\}\right|
=\frac12(r-a-1)^2\,t+o(t).
}\tag{IW.6}
\]
Indeed the full below-corner triangle has height
\(\eta_-(t)=(r-a-1)t+o(t)\), and exact area
\(\eta_-(t)^2/(2\sin t\cos t)\).
Its horizontal projection converges to \([a,r-1]\), which is contained in the bottom rectangle face; the portion outside \([a,b]\times[0,1]\) is \(o(t)\), since the triangle's height is \(O(t)\) and its projection overshoot is \(o(1)\). This yields IW.6. **Without the common rectangle premise it would be false** to count the entire ambient triangle as actual removed hull material.

For Romik's exact normalized reference \(l=-m,r=m\) and top/bottom faces \([a,b]=[c,d]=[-m/2,m/2]\),
\[
r-a-1=b-l-1=\frac{3m}{2}-1>0,\qquad
m=\frac{1}{3\sin\beta}\approx1.16705.
\]
Thus both upper- and lower-handed *separate* single-angle bottom/top wedges begin with equal leading carving coefficient \(\tfrac12(3m/2-1)^2\). This is the **two-handed initial niche cost**, not time spent moving the sofa sideways before turning.

## 3. The face dichotomy makes the true remaining "waste" issue explicit

For compact connected **complete-two-turn** sofas of vertical span one and competitive horizontal width \(W>2\), the existing full-turn face classification [FD1](full-turn-face-dichotomy.md) gives the following alternatives when both faces have positive lengths.

**Case A: aligned top and bottom faces.** They coincide, \(F_{\rm top}=F_{\rm bottom}=[a,b]\), and
\[
a\le l+1<r-1\le b.
\]
Then **all four** endpoint coefficients in IW.3 are at least \(W-2>0\). Thus the sharp corners of **both separate turns** penetrate the incoming strip immediately at **both** small-angle ends; because the common face rectangle really lies in the hull, their one-angle wedges remove positive ordinary area. This is the class for which the sharp face-alignment value theorem FAS1 already supplies \(|S|\le M\) (subject to its analytic dependency chain).

**Case B: top face at the left end, bottom face at the right end.** Suppose
\[
[a,b]\subseteq[l,l+1],\qquad[c,d]\subseteq[r-1,r].
\]
The four slopes obey
\[
\boxed{
\begin{array}{c|cc}
&\text{start }t=0&\text{end }t=L\\\hline
\text{lower turn}&r-a-1\ge W-2>0&b-l-1\le0\\
\text{upper turn}&r-c-1\le0&d-l-1\ge W-2>0
\end{array}}\tag{IW.7}
\]
The lower corner need not enter the strip at the end, and the upper corner need not enter it at the start; the two turns **exchange which side incurs the ambient corner intrusion**. The orientations reverse for top-right/bottom-left faces. When one of these coefficients is zero, higher-order terms decide whether the corresponding niche is initially empty.

**Crucial caveat:** This case can have positive *ambient* early corner height but no corresponding material at the baseline because the *opposite* hull face is displaced. The single-angle area asymptotic IW.6 must therefore not be transplanted into Case B. This **actual overlap/clipping** is the very structural difficulty left by the existing full-turn sharp aligned-face theorem, and it is precisely where an asymmetric sofa might economize on what looks like wasted initial inner-corner carving.

The [PD3 value reduction](full-turn-positive-face-density.md) proves that the remaining Case B **carries the entire unresolved full-turn supremum in area limits**. Thus it is **not** a uniformly low-area curiosity or a case that can be dismissed by its off-center faces. Moreover none of these *full-turn end* arguments automatically covers genuinely partial original turn histories. A viable sharp proof must jointly account for the saved ambient corner wedge, the altered outer cap material, the non-overlap of the two handed turn motions, and both outgoing strips.

## 4. Concrete next proof target, not another local deformation

The user's observation isolates a clear high-priority global subproblem:

> Prove a sharp **ordinary-area comparison for arbitrary full-turn, unit-span hulls with positive top and bottom faces at *opposite ends***, exploiting IW.7's complementary onset/exit activation and the exact physical clipping of the two full inner-wall ray sweeps.

This is the central still-open full-turn value class; bounding it by \(M\), with a valid passage from full to partial terminal angles, would directly advance unrestricted optimality. The endpoint slope identities alone are **necessary boundary geometry**, not an area certificate.

The takeaway is **not** that ambidexterity forces an inefficient sideways pre-turn translation; it forces the **same nonconvex shape** to survive two different rotating corner families. Romik's midpoint outer contact balances those costs symmetrically. A possibly better shape can redistribute the costs asymmetrically, and the nontrivial task is proving that any apparent saving is paid for by loss of allowable outer material.

No CI, Lean/Lake build, area optimization, or unproved global shape classification is claimed. This is a self-reviewed elementary support asymptotic and its exact place in the existing value reduction.
