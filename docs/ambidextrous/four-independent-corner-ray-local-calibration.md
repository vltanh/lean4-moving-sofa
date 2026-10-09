# Four independent middle-source arcs: a sharp **asymmetric** ordinary-area exclusion around Romik

**Status (2026-10-08):** A genuinely *two-handed, vertically asymmetric* strict local area comparison for the **complete moving inner-wall ray sweeps**, with **no upper curvature cap or nonsmooth-edge exclusion** for the perturbed hull. This strengthens [VC3–VC5](vertical-corner-frozen-ray-calibration.md), whose final area comparison assumed **vertical-reflection symmetry of the entire hull** and therefore coupled the two handed turns. Here all **four** middle support arcs of the actual outer convex hull may vary independently, and the resulting actual sofa need not have **any reflection symmetry**.

The result excludes **area ≥ Romik's \(M\)** for an open Hausdorff neighborhood of the reference **inside a fixed-support-outside-the-middle-arcs class**. It is a *two-sided above-\(M\) exclusion*, not just an example of perturbations approaching \(M\) from below. It is **not global optimality**: arbitrary altered axis supports, exposed face endpoints, support switches, separated opposite faces, large deformations and partial-turn motion intervals remain outside its hypothesis.

No use is made of the unproved global two-cap clipping inequality \(G\le\Delta_U+\Delta_V\). All niche charges are **actual ordinary** one-hand swept-ray areas inside a protected central rectangle; the two opposite-handed niches stay disjoint by a proved strict height margin.

## 1. Four independent middle support variations on one actual convex hull

Let \(K_*=\operatorname{conv}\Sigma_*\subseteq\mathbb R\times[0,1]\) be the Romik reference hull with horizontal projection \(I=[-m,m]\), central top/bottom face interval \(J_*=[-m/2,m/2]\), and fixed \(M=|\Sigma_*|\). Let \(\rho(x,y)=(x,1-y)\).

For **any convex hull** \(K\subset\mathbb R\times[0,1]\) with the same four axis supports as \(K_*\), let
\[
U_K=\{(x,y):x\in I,\quad0\le y\le a_K(x)\},
\qquad
V_K=\{(x,y):x\in I,\quad0\le y\le1-b_K(x)\},
\tag{FA.1}
\]
where \(a_K,b_K\) are its upper/lower vertical outer roofs. Both \(U_K,V_K\) are downward-closed convex caps with the same projection \(I\), and \(K=U_K\cap\rho V_K\).

Let \(T=(\beta,\pi/2-\beta)\) be the open reference middle support interval. Fix two compact intervals
\[
J_0\Subset J_1\Subset T
\]
sufficiently close to \(t=\pi/4\) that the explicit reference first-wall, second-wall and moving-corner exposed graphs have all the strict margins established in [VC3](vertical-corner-frozen-ray-calibration.md). In the following, **all four source perturbations are independent**:
\[
\begin{aligned}
h_{U_K}(u_t)&=f_*(t)+\phi_U(t),&
h_{U_K}(v_t)&=g_*(t)+\psi_U(t),\\
h_{V_K}(u_t)&=f_*(t)+\phi_V(t),&
h_{V_K}(v_t)&=g_*(t)+\psi_V(t),
\end{aligned}\tag{FA.2}
\]
and all these supports agree with the reference **outside \(J_0\)**, including every axis and corner-contact switch. Each \(\phi_U,\psi_U,\phi_V,\psi_V\) is Lipschitz with compact support in \(J_0\). The reference hull's upper and lower cap support semicircles may therefore deform entirely **independently**: \(K\) is not assumed symmetric under \(x\mapsto-x\) or \(y\mapsto1-y\).

The four support descriptions must arise from **one actual compact convex hull** \(K\) (not from arbitrarily incompatible cap pairs). This is automatic if one starts with such a \(K\); in the converse constructive statement below the requirement is the usual nonnegative distributional support-curvature and unchanged axis jumps.

## 2. Small *Hausdorff* distance suffices, without a new curvature bound

**Lemma FA1 (simultaneous fixed-support local admission).** There exists \(\varepsilon_*>0\), depending only on the fixed intervals and exact reference support data, such that if \(K\) satisfies FA.2 and
\[
\boxed{\|h_K-h_{K_*}\|_{L^\infty(\mathbb S^1)}<\varepsilon_* ,}\tag{FA.3}
\]
then:

1. All original outer midline extremes \((\pm m,1/2)\) and the four original core-face endpoints \((\pm m/2,0),(\pm m/2,1)\) remain in \(K\); hence \(J_*\times[0,1]\subset K\) and the full horizontal midline \(I\times\{1/2\}\subset K\).
2. For both complete conventional quarter turns the actual positive forbidden sweeps remain confined to \(\operatorname{int}(J_*)\times[0,1/2)\) (lower turn) and \(\operatorname{int}(J_*)\times(1/2,1]\) (upper turn), with a uniform clearance.
3. The **complete canonical envelope** \(S_K=E_{\pi/2,\pi/2}(K)\) is a compact connected actual full-two-turn sofa, has all fibers nonempty, and satisfies \(\operatorname{conv}S_K=K\).

**Proof.** On each upper source quarter, convexity of the actual support gives \(h+h''\ge0\) as a measure. The reference support is smooth on \(J_1\) and has bounded positive curvature there. Thus the elementary **semiconvex chord estimate** [VC4](vertical-corner-frozen-ray-calibration.md) converts FA.3 to uniform smallness of **both one-sided first derivatives** of the four independent differences \(\phi_U,\psi_U,\phi_V,\psi_V\), of order \(O(\sqrt{\varepsilon_*})\). This works for exposed-edge curvature atoms as well; smoothness of \(K\) is not required.

At each of the six reference retained points all affected reference outer supporting lines have a **strict positive support slack** on a sufficiently small interval around \(\pi/4\) (verified explicitly in [VC.4](vertical-corner-frozen-ray-calibration.md) and by the vertical and horizontal reference symmetries). Outside \(J_0\) the supports are literally unchanged. Therefore each point still lies in the intersection of *all* perturbed supporting halfplanes when \(\varepsilon_*\) is small; the six points are in \(K\). Convexity supplies their entire rectangle and midline convex hull.

The moving corner positions depend continuously on the two support values, so the strict **whole-angle height ceilings** of the reference, and the margins of the baseline intercepts inside \(J_*\), persist under FA.3. At all unaffected angular directions the reference geometry is identical; at affected directions the two corner heights and baseline intercepts change by only \(O(\varepsilon_*)\). Thus all positive niche points remain in the stated open central half-rectangles, with uniform midline clearance. As in [VC1](vertical-corner-frozen-ray-calibration.md), the full envelope has nonempty interval fibers containing the midline, and is connected. Both continuous canonical quarter-turn motions and incoming/outgoing whole-body strip endpoints follow from actual support tightening and the fixed axis widths.

Every extreme point of \(K\) on its curved flanks lies outside \(\operatorname{int}J_*\), by the small first-derivative changes and the strict original flank-contact margins; all four core face endpoints are among the retained points. Thus no extreme point is carved away, so the actual hull of the saturated body remains \(K\). \(\square\)

**Substantive scope:** The admissibility conclusion does not assume *vertical symmetry*. It follows from **separate strict clearances** for both handed sweeps around the same common core. No global symmetrization of a nonconvex sofa is performed.

## 3. The exact ordinary-area identity splits, but the perturbations do not

Because \(K\) and both sweeps contain/avoid the required rectangle as in Lemma FA1, the original lower niche \(\mathcal N(U_K)\) lies wholly inside \(K\), and the original upper niche \(\rho\mathcal N(V_K)\) also lies wholly inside \(K\). They are separated by the horizontal midline. Put their true ordinary areas \(N(U_K),N(V_K)\).

The **outer** actual convex hull fibers satisfy
\[
a_K(x)\ge\frac12,\qquad b_K(x)\le\frac12,
\]
so
\[
\boxed{|K|=|U_K|+|V_K|-|I|.}\tag{FA.4}
\]
Carving the **entire ordinary swept rays** gives
\[
\boxed{
|S_K|=(|U_K|-N(U_K))+
       (|V_K|-N(V_K))-|I|.
}\tag{FA.5}
\]
The reference equality is \(|\Sigma_*|=2(|U_*|-N(U_*))-|I|=M\).

This separation of the two **actual** niche areas is an equality because all relevant removal lies in disjoint central half-rectangles, not an inequality obtained by discarding the old clipping correction. It applies to arbitrary asymmetry of the four perturbed support arcs **within FA.3**.

## 4. Each handed sweep has a frozen-reference ray minorant, with **arbitrary new contact switches**

Let \((\phi,\psi)\) denote either independent pair \((\phi_U,\psi_U)\) or \((\phi_V,\psi_V)\), and let \(U\) denote that actual downward convex cap. Denote its full positive continuous-angle niche area by \(N(U)\).

The frozen-reference comparison [VC.25–VC.27](vertical-corner-frozen-ray-calibration.md) relies only on the reference's three globally exposed source pieces on \(J_0\). For each **old** first/second stationary wall abscissa, the old maximizing angular parameter still provides a valid new inner-ray constraint. At each **new** moving-corner abscissa, the new corner itself provides a valid two-wall niche constraint, even if it is not the new global maximizer. The new corner x-coordinate remains strictly monotone over \(J_0\) because its derivative depends only on the **first derivatives of the source supports**, controlled by FA1. The three comparison x-images are pairwise disjoint by the old contact margins and the \(C^1\)-smallness, so their lower bounds can be **integrated without multiplicity**.

The resulting exact inequality is
\[
\boxed{
N(U)-N(U_*)\ge
\int_{J_0}(\rho_{f,*}\phi+\rho_{g,*}\psi)\,dt+
\frac12\int_{J_0}(\phi^2+\psi^2)\,dt+
\int_{J_0}\phi\psi'\,dt.
}\tag{FA.6}
\]
The last integral is a genuine **oriented cross term**, not an independently positive quantity. All derivatives are interpreted a.e. for Lipschitz perturbations; the proof by integration by parts survives curvature atoms. No upper bound \(f''+f\le1\), \(g''+g\le1\), or stable new niche contact chart is assumed.

The **exact outer cap area polarization** is
\[
\boxed{
|U|-|U_*|
=\int_{J_0}(\rho_{f,*}\phi+\rho_{g,*}\psi)dt
+\frac12\int_{J_0}
(\phi^2+\psi^2-\phi'^2-\psi'^2)dt.
}\tag{FA.7}
\]
Subtract FA.6 from FA.7:
\[
\boxed{
(|U|-N(U))-(|U_*|-N(U_*))
\le-\frac12\int_{J_0}
(\phi'^2+\psi'^2+2\phi\psi')\,dt.
}\tag{FA.8}
\]

The **Poincaré inequality** on \(J_0\) of length \(\ell<\pi/2\) gives
\[
\left|2\int_{J_0}\phi\psi' dt\right|
\le\frac\ell\pi\int_{J_0}(\phi'^2+\psi'^2)dt.
\]
Therefore, for each independently perturbed handed cap,
\[
\boxed{
(|U|-N(U))-(|U_*|-N(U_*))
\le-\frac12\left(1-\frac\ell\pi\right)
\int_{J_0}(\phi'^2+\psi'^2)\,dt.
}\tag{FA.9}
\]

## 5. The **asymmetric four-arc local sharp theorem**

**Theorem FA2 (full-two-turn, four independent upper/lower middle arcs).** Under FA.2–FA.3, with the reference support outside \(J_0\) fixed and \(K\) an arbitrary convex hull otherwise, one has
\[
\boxed{
\begin{aligned}
|E_{\pi/2,\pi/2}(K)|
&\le M-\frac12\left(1-\frac{|J_0|}{\pi}\right)\mathcal E_4(K),\\
\mathcal E_4(K)
&=\int_{J_0}\bigl[
|\phi_U'|^2+|\psi_U'|^2+
|\phi_V'|^2+|\psi_V'|^2\bigr]dt .
\end{aligned}}\tag{FA.10}
\]
The coefficient is **strictly greater than \(1/4\)**. Equality implies **all four** support perturbations vanish identically, and hence \(K=K_*\) and the saturated sofa equals Romik's reference sofa.

This result is **not merely a sequence of below-\(M\) examples**. It excludes *every* \(|S|\ge M\) compact connected full-turn sofa whose actual hull lies in the stated Hausdorff-neighborhood/angle-support class, except Romik itself. It allows:

- changes to **both handed** outer-wall paths, independently, with **no vertical-reflection symmetry**;
- horizontal and vertical motion of both inner-corner trajectories;
- arbitrarily large positive curvature spikes, exposed-edge atoms and nonsmooth actual supports;
- completely different **new** niche active-ray contact charts, provided the original **reference chart** supplies the fixed witnesses.

**Proof.** Apply FA.9 to the two independent cap pairs in FA.2. Sum and invoke the **exact actual ordinary two-turn area identity** FA.5. The equality conditions follow because the integral of four nonnegative squared derivatives vanishes only if all compactly supported functions are constant, and each vanishes outside \(J_0\). \(\square\)

**Limitations:** This does not prove all arbitrary close-to-Romik hulls have smaller area: support changes touching the axis normals, reference switching angles or central face endpoints are excluded by FA.2. Nor are partial terminal angles covered. A hypothetical better sofa can still lie outside this explicitly described stable subspace; the theorem makes no claim that every above-\(M\) competitor admits a reduction into the subspace without loss.

No CI, Lean/Lake formalization, numerical optimizer, certified global above-\(M\) counterexample, or solved unrestricted sharp bound is claimed. All statements are self-reviewed written arguments awaiting independent verification.
