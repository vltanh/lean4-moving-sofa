# Outer-wall support **and the physical inner-corner trajectory**, before carving the niche

**Date: October 8, 2026. Status:** Corrects an earlier misinterpretation of the user's idea. The proposal is to use **both the outer-wall contacts and the moving sharp inner corner**, *then* carve the niche made by the two inner-wall rays. The previous [OH](outer-hull-first-carving-audit.md) primarily analyzed the outer supporting walls and missed the distinct role of the **corner trajectory**.

This direction is exactly related to Romik's **rotation-path formulation** (his 2016 paper, Section 2, especially equations (7)–(8)): the path of the hallway's inner corner in sofa coordinates parametrizes candidate shapes. This note is not a proof of sharp optimality or an original claim to have invented that parametrization. It gives two exact geometric diagnostics: the sharp corner lies **inside Romik's actual convex hull** at a known angle; and relaxing inner-wall rays to just their moving corner **points** is far too weak if the supporting hull is not enforced as the body's true hull.

## 1. The corner is determined by the outer contacts, not independently chosen

Use one conventional lower turn with
\[
u_t=(\cos t,\sin t),\qquad v_t=(-\sin t,\cos t),
\quad 0<t<\pi/2.
\]
For a proposed compact convex outer hull \(K\) let
\[
f(t)=h_K(u_t),\qquad g(t)=h_K(v_t).
\]
Tightening the two **outer** hallway walls to support \(K\) gives
\[
p\cdot u_t\le f(t),\qquad p\cdot v_t\le g(t).
\]
Because the corridor is exactly one unit wide, its **physical sharp inner corner** has sofa-frame position
\[
\boxed{c_K(t)=(f(t)-1)u_t+(g(t)-1)v_t.}\tag{OC.1}
\]
Thus once the outer supports and angle are given, **the corner position is forced**. Conversely, prescribing a continuous corner rotation path \(c(t)\) gives the pair of outer-wall offsets
\[
\boxed{f(t)=1+c(t)\cdot u_t,\qquad
g(t)=1+c(t)\cdot v_t.}\tag{OC.2}
\]
For an arbitrary prescribed path these offsets need not be tight to the eventual actual convex hull; retightening is a separate admissibility step.

The two *inner-wall rays* meet at \(c_K(t)\). Their southwest forbidden quadrant is
\[
Q_{K,t}=\{p:p\cdot u_t<f(t)-1,\ 
                   p\cdot v_t<g(t)-1\}
       =c_K(t)-\{a u_t+b v_t:a,b>0\}.\tag{OC.3}
\]
Writing \(c_K(t)=(\xi_t,\eta_t)\), the exact vertical roof of this quadrant is the **two-sided tent**
\[
\boxed{
w_t(x)=\eta_t-
\begin{cases}
(\xi_t-x)\tan t,&x\le\xi_t,\\
(x-\xi_t)\cot t,&x\ge\xi_t.
\end{cases}}\tag{OC.4}
\]
Indeed the two inner-wall inequalities give respectively
\(y<\eta_t-(x-\xi_t)\cot t\) and
\(y<\eta_t+(x-\xi_t)\tan t\); taking their minimum produces OC.4.

Let \(a_K(x),b_K(x)\) be the actual upper/lower hull roofs. The area removed at **that single corner position** by its attached inner-wall rays is exactly
\[
\boxed{
|K\cap Q_{K,t}|
=\int_{\operatorname{proj}_xK}
\left[\min(a_K(x),w_t(x))-b_K(x)\right]_+dx.}\tag{OC.5}
\]
This is an **ordinary-area** statement, not a signed support integral. Its full-turn counterpart takes the **union** over all \(t\), and the opposite-handed turn contributes its own reflected corner and rays. Pointwise maxima of the roofs handle the entire continuum of angles. Positive parts are required whenever a tent misses or completely cuts a fiber.

If \(f,g\) are differentiable, the actual corner velocity is
\[
\boxed{c_K'(t)=p(t)u_t+q(t)v_t,\quad
p=f'-g+1,\quad q=g'+f-1.}\tag{OC.6}
\]
The signs and zero crossings of \(p,q\) determine when the niche boundary is traced by the moving **corner** itself, versus by the *envelopes of the two attached inner-wall rays*. This is the substantive contact-switching problem in Romik's and the branch's ODE frameworks; removing the rays cannot be justified by a slogan.

## 2. The corner lies *strictly inside* Romik's proposed convex hull

Let \(K_*=\operatorname{conv}\Sigma_*\) be the horizontally centered actual hull of Romik's ambidextrous construction. Its entire central rectangle
\[
[-m/2,m/2]\times[0,1]\subset K_*,\qquad m>1
\]
is present in the outer hull, even though the eventual sofa loses some of that rectangle to the inner niche.

The exact middle-phase upper support values in the [Romik reference support](romik-horizontal-misalignment-sharp-bound.md), at \(t=\pi/4\), coincide:
\[
f_*(\pi/4)=g_*(\pi/4)
=\frac{R_0+1/2}{\sqrt2},\qquad
\frac{128}{100}<R_0<\frac{131}{100}.
\]
Consequently OC.1 gives
\[
\boxed{
c_{K_*}(\pi/4)=(0,H_*),\qquad
H_*=R_0+\tfrac12-\sqrt2.
}\tag{OC.7}
\]
The elementary rational inequalities \(7/5<\sqrt2<3/2\) yield
\[
\boxed{\frac7{25}<H_*<\frac{41}{100}<\frac12.}\tag{OC.8}
\]
Moreover \(m/2>1/2>H_*\). Thus **the moving physical inner corner lies strictly in the interior of the convex hull \(K_*\)** at this turning orientation. Requiring \(c_K(t)\notin K\), or insisting the **convex hull itself** clear the point corner, would exclude the Romik candidate and is **not** a necessary condition on actual sofa hulls.

At this precise midpoint angle, OC.4 simplifies to
\[
w_{\pi/4}(x)=H_*-|x|.
\]
The single-angle forbidden triangle
\[
T^-=\{(x,y):|x|<H_*,\ 0\le y<H_*-|x|\}
\]
lies entirely inside the central rectangle of \(K_*\). Its area is *exactly* \(H_*^2\). The upper-handed midpoint corner gives the vertically reflected triangle of the same area. As \(H_*<1/2\), the triangles are disjoint, and the actual two-turn sofa must omit their interiors:
\[
\boxed{|T^-\cup\rho T^-|=2H_*^2.}\tag{OC.9}
\]
This is a rigorous **corner-driven compulsory area loss from one angle of each turn**. Further moving corner positions and their wall rays carve additional material; OC.9 is **not** the complete niche area or a sharp global area bound.

## 3. Why replacing the two inner-wall rays by only their corner points is unsafe

There is also an exact negative control on a *relaxed* first stage that retains the outer supporting walls but only asks that a body avoid the physical point-corner trajectories, without their rays or an **actual-hull equality**.

Take the auxiliary outer hull
\[
K_W=[-W/2,W/2]\times[0,1],\qquad W>4.
\]
For \(c=\cos t\), \(s=\sin t\), OC.1 becomes
\[
\boxed{c_{K_W,x}(t)=\frac W2\cos2t+s-c,\qquad
c_{K_W,y}(t)=Wsc+1-s-c.}\tag{OC.10}
\]
Let the **connected** central rectangle
\[
S_W=[-W/2+2,W/2-2]\times[0,1]\subset K_W,
\qquad |S_W|=W-4.
\]
Suppose \(c_{K_W,y}(t)\in[0,1]\). By OC.10,
\[
Wsc\le s+c\le\sqrt2.
\]
Since \(\max(s,c)\ge1/\sqrt2\), it follows that
\(\min(s,c)\le2/W\).
If \(s\le2/W\), then
\[
c_{K_W,x}(t)
\ge\frac W2(1-2s^2)-1
\ge W/2-1-4/W>W/2-2.
\]
If \(c\le2/W\), the symmetric calculation gives
\[
c_{K_W,x}(t)
\le-W/2+1+4/W<-W/2+2.
\]
Thus **no point of the entire physical corner trajectory with height in the incoming strip can belong to \(S_W\)**. The opposite-handed trajectory is its reflection through \(y=1/2\) and also misses \(S_W\). Yet \(S_W\) fits *all* outer supporting halfplanes of **the auxiliary** \(K_W\) and has unbounded area \(W-4\).

**Important qualification:** Here \(\operatorname{conv}S_W=S_W\ne K_W\). This is **not a counterexample** to a relaxation that additionally enforces the hull equality \(K=\operatorname{conv}S\), nor a feasible actual sofa in the original hallway. It proves only that **outer walls of an auxiliary hull plus avoidance of its two moving corner points** cannot by themselves bound area, even for connected bodies. The rays, actual-hull self-consistency, or both must do essential work.

## 4. The corrected hull/corner-first strategy

The rigorous sequence suggested by the user's clarification is:

1. Choose an **outer-wall contact path** (equivalently, continuous rotating inner-corner trajectories) for both handed passages; the unit corridor width fixes the relationship OC.1–OC.2.
2. Form the outer convex envelope \(K\) from all corresponding outer supporting halfplanes and the common incoming strip. Allow the moving inner corner to lie **inside** \(K\); this is necessary even for Romik's reference.
3. Using the same corner trajectories, carve the **complete swept quadrants made by the attached inner-wall rays**. Their boundaries comprise active corner-path arcs and ray-envelope arcs; OC.4–OC.6 identify both.
4. Optimize the **ordinary surviving connected area**, with actual hull support retightening where needed. For partial turns impose both full-body outgoing strips, as in [OS1](original-motion-signed-convex-domain.md).

**Possible sharp theorem sought:** Find a global geometric inequality that charges outward convex-hull area against the **full corner/ray sweep** for arbitrary paths, not just Romik's contact pattern. This avoids treating the upper and lower cap deficits separately; the joint ordinary union is carved once. No such universal sharp comparison has been proved.

This is essentially the rotation-path/contact construction in **Romik Section 2**, now interpreted for two independent handed motions and the branch's actual-hull connectedification. It is a valid new focus, not a solved optimization.
