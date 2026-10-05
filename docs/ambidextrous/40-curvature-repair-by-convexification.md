# 40. Convexifying a wall family repairs excessive support curvature

This note constructs a geometric repair instead of inferring a curvature bound from high area. It identifies the exact support modification and its area gain in a protected contact configuration. Note 41 verifies that configuration for the previously committed high-frequency examples and resolves the sign of their area difference from M.

The elementary one-dimensional convex-envelope facts used below carry no novelty claim. The repair is local in the angle/support variables; it is not asserted for every arbitrary maximizing hull.

## 40.1 The correct variable for the right-wall envelope

On an angle interval J compactly contained in (0,pi/2), set

\[
s=-\cot t,\qquad
\phi(s)=\frac{1-f(t)}{\sin t}.
\tag{40.1}
\]

Then the R wall-height function is

\[
R_t(x)=s x-\phi(s).
\]

The change of variables has ds/dt=1/sin^2(t). Direct differentiation gives

\[
\phi'(s)=B_x(t),\qquad
\phi''(s)=(1-\rho_f(t))\sin^3t.
\tag{40.2}
\]

Thus the desired cap rho_f<=1 is precisely convexity of phi, not convexity of f itself. Convexity of the original hull gives the other bound phi''<=sin^3(t).

Let phi_c be the greatest convex minorant of phi on the closed s-interval I corresponding to J. Define

\[
f_c(t)=1-\sin t\,\phi_c(-\cot t),\qquad
u(t)=f_c(t)-f(t)\geq0.
\tag{40.3}
\]

The operation raises the hull support; it does not shave off excessive curvature by an unproved body deformation.

## 40.2 Convex-envelope facts with the needed endpoint control

**Lemma 79 (local support repair).** Suppose phi is C^2 on I. Suppose it equals a C^2 function phi_* near the endpoints of I, that phi_*'' is bounded below by a positive constant on I, and that the support of phi-phi_* lies in a fixed smaller interior interval. For phi sufficiently close to phi_* in C^1:

1. phi_c agrees with phi near both endpoints;
2. phi_c is C^{1,1}, is affine on each component of {phi_c<phi}, and equals phi with the same first derivative at its interior contact points;
3. phi_c tends to phi_* in C^1 as phi tends to phi_* in C^1;
4. if the original rho_f is nonnegative, then the repaired support satisfies 0<=f_c''+f_c<=1 almost everywhere, and can be joined to the unchanged support outside J without new curvature atoms;
5. the supremum of the R wall-height family is unchanged by the repair, for every x.

**Proof.** A tangent line to phi_* at a point near an endpoint lies a uniformly positive distance below phi_* on the interior perturbation interval, by strict convexity and their positive separation. For a sufficiently small uniform perturbation, that line remains below phi everywhere and touches it at the chosen endpoint-near point. Therefore the convex minorant agrees with phi there.

Each noncontact component of a greatest convex minorant is an affine chord between two contact points; otherwise the minorant could be raised on that component while staying convex and below phi. At a contact with a differentiable obstacle, the left and right slopes of the minorant are both forced to equal phi'. Thus phi_c is C^1. Its derivative agrees with phi' on the contact set and is constant on every complementary interval. Since phi' is Lipschitz, the same is true of phi_c'; this can be checked by inserting the intervening chord endpoints between any two points.

For completeness, let delta_1=||phi'-phi_*'||_infinity and let mu<=phi_*''<=C. A noncontact chord with endpoints a,b has phi'(a)=phi'(b), so b-a<=2delta_1/mu. Its constant slope differs from phi_*' at any point of the chord by at most delta_1(1+2C/mu). On the contact set the difference is at most delta_1. Uniform closeness of the functions follows by sandwiching phi_c between phi_*-||phi-phi_*||_infinity and phi. This proves C^1 convergence.

On a noncontact interval phi_c''=0, so (40.2) gives repaired curvature one. On the contact set, phi_c''=phi'' almost everywhere. Indeed the Lipschitz functions phi_c' and phi' agree there, and the derivative of their difference vanishes almost everywhere on its zero set. Convexity of phi_c and the input inequality phi''<=sin^3(t) give the two curvature bounds. Endpoint agreement supplies the claimed gluing without atoms.

Finally, at a point on an affine chord, s x-phi_c(s) is a convex combination of the two endpoint values s_i x-phi(s_i), so it cannot exceed their maximum. At a contact it is already an original wall-height function. Since phi_c<=phi, the opposite inequality for suprema is immediate. Thus

\[
\sup_{s\in I}(sx-\phi_c(s))=\sup_{s\in I}(sx-\phi(s))
\quad\text{for every }x.
\tag{40.4}
\]

This finishes all assertions. QED.

The curvature can be arbitrarily large before repair; only the C^1 displacement and the nonnegative original hull curvature are controlled here. The C^{1,1} bound for a particular repaired function need not be uniform over such inputs.

## 40.3 The protected geometry required for an area comparison

For the remainder suppose a symmetric common hull and its two full-turn envelopes have the following properties, both before repair and along f_z=f+z nu, 0<=z<=1, with g fixed on the upper half and the modification reflected on the lower half:

- all niches lie inside a common retained central rectangle and are strictly separated;
- the lower roof's left part is the unchanged D envelope;
- its right part is the supremum of the R family, hence is unchanged by (40.4);
- its middle part is the standard corner graph, with c_x strictly decreasing and with unchanged endpoints;
- the support modification is confined to an interior subinterval of this middle angular range.

These are geometric hypotheses, not formal consequences of replacing phi by phi_c. In particular preserving the supremum of R alone does not prove preservation of the supremum of min(R,L). Note 41 proves the stated hybrid roof description in the intended application.

## 40.4 Exact area gain of the repair

**Lemma 80 (repair gain identity).** Under Section 40.3, let S and S_c be the full surviving envelopes. Then

\[
\boxed{
|S_c|-|S|
=2\int_J(1-q-\nu)\nu\,dt
+\int_J\nu'^2\,dt.
}
\tag{40.5}
\]

Consequently the repair strictly increases area whenever nu is not identically zero and 1-q-nu has a positive lower bound on J.

**Proof.** The only niche boundary that changes is the standard corner part. Along f_z=f+z nu its q component is q+z nu. Equation (35.6), or direct integration by parts of the corner determinant integral, gives the lower niche-area increase

\[
\int_J q\nu\,dt+\tfrac12\int_J\nu^2\,dt.
\]

The D envelope is fixed, since D=c-q mu and both terms change by z nu mu. The R envelope is fixed by (40.4): the intermediate obstacle (1-z)phi+z phi_c has the same convex minorant and the same supremum of affine wall heights. The upper niche contributes the same change by reflection.

The convex hull area difference is

\[
2\int_J\rho_f\nu\,dt+\int_J(\nu^2-\nu'^2)\,dt,
\]

by expansion of its support-area integral. Subtracting the two niche changes yields

\[
|S_c|-|S|=2\int_J(\rho_f-q)\nu\,dt-\int_J\nu'^2\,dt.
\tag{40.6}
\]

On {nu>0} the repaired curvature is one, so nu''+nu=1-rho_f there. Both sides may be multiplied by nu, since it vanishes elsewhere. Integration by parts, with endpoint values zero, gives

\[
\int_J\rho_f\nu
=\int_J\nu+\int_J\nu'^2-\int_J\nu^2.
\]

Insert this in (40.6) to obtain (40.5). The formulas remain valid for the C^{1,1} repaired support by absolute continuity and the H^1 support-area identity. QED.

A simpler assertion that the repair leaves the **entire** niche unchanged would be false: it moves the corner graph. The term involving q is exactly that missing area cost. Its inclusion is essential to the positive gain test.

## 40.5 Scope

This provides an explicit curvature-improving operation with an exact area accounting in a verified contact neighborhood. It is not an inference from small Hausdorff distance, and it is not yet an operation valid for arbitrary partial-turn, clipped, or coincident-contact configurations. Those distinctions are retained in the application that follows.
