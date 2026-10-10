# 47. The protected repair works for curvature measures, not only C² inputs

This removes the input smoothness restriction from the local operation in Notes 40–42. The input may have exposed-edge atoms or singular-continuous curvature. Proximity is measured by uniform support distance, not by an assumed C¹ norm.

The angular perturbations still remain in fixed windows away from the axis normals and the candidate's switching neighborhoods. This is a measure-level local repair, not yet a repair for every global maximizer.

## 47.1 Uniform support closeness controls both derivative traces

**Lemma 90 (semiconvex trace estimate).** Let f be a convex-body support restriction on an interval, and let f_* be a C² reference restriction there. Suppose |f-f_*|<=epsilon and |f|<=M_0. Put C=M_0+||f_*''||_infinity+1. At a point t whose distance from the endpoints is at least ell, both one-sided derivative traces satisfy

\[
|f'_\pm(t)-f_*'(t)|\leq\frac{2\varepsilon}{\ell}+\frac{C\ell}{2}.
\tag{47.1}
\]

In particular, on a fixed smaller interval these traces converge uniformly to f_*' when epsilon tends to zero. If ell=2sqrt(epsilon/C) is available, the bound is 2sqrt(C epsilon).

**Proof.** Convexity of the body means sigma_f=f+f'' is a nonnegative measure, so f''>=-M_0 dt distributionally. Thus w=f-f_* satisfies w''>=-C dt, and w(t)+Ct²/2 is convex. Its supporting-line inequality yields, for either derivative trace v of w at t,

\[
w(t+s)\geq w(t)+vs-Cs^2/2.
\]

Use s=ell and s=-ell and |w|<=epsilon to bound v from above and below. The optimized choice gives the stated square-root estimate. Existence and ordering of the one-sided traces follow from convexity after adding Ct²/2. QED.

Consequently a uniformly small perturbation of a smooth support function cannot have large derivative jumps on a compact interior window, even though its curvature density may be arbitrarily large and its curvature may be singular.

## 47.2 The wall transformation in the sense of measures

Use the first-quarter variable

\[
s=-\cot t,\qquad\phi(s)=\frac{1-f(t)}{\sin t}
\]

on a compact angle interval J inside (0,pi/2). With B_x=(f-1)cos(t)-f' sin(t), the derivative traces obey phi'=B_x. Distributionally,

\[
dB_x=\sin t\,(dt-d\sigma_f).
\tag{47.2}
\]

Thus, after pushing this measure forward by s=-cot(t),

\[
\phi''\leq k(s)\,ds,\qquad k(s)=\sin^3(t(s)).
\tag{47.3}
\]

For a density this is the earlier identity phi''=(1-rho_f)sin³(t). A positive atom of sigma_f produces a **negative** derivative jump in phi. The measure formula follows directly by differentiating B_x as a product of smooth functions and a function of bounded variation; ds/dt=1/sin²(t) gives (47.3).

In particular phi is semiconcave with a bounded constant on this compact interval. It need not be convex or differentiable everywhere.

## 47.3 Convex minorants of these obstacles are regular

**Lemma 91 (measure-valued local repair).** Suppose f=f_* outside a fixed smaller interval inside J, where the reference wall obstacle phi_* has strictly positive second derivative on J. If f is sufficiently uniformly close to f_*, let phi_c be its greatest convex minorant on the corresponding closed s-interval. Then:

- phi_c agrees with phi near both endpoints;
- phi_c is C¹,¹, and 0<=phi_c''<=k(s) almost everywhere;
- the repaired f_c=1-sin(t)phi_c(-cot(t)) satisfies 0<=sigma_{f_c}<=dt, with no singular part in J;
- f_c>=f and its support difference u=f_c-f vanishes near the endpoints;
- f_c tends uniformly to f_* and its derivative tends uniformly to f_*' as the original support error tends to zero;
- the supremum of the R wall family is unchanged for every horizontal coordinate.

**Proof.** Strict convexity of phi_* supplies supporting tangent lines in neighborhoods of the outer endpoints with a positive gap over the smaller perturbation interval. A sufficiently small uniform perturbation leaves those lines below phi, so phi_c=phi near the endpoints. This uses only uniform closeness and exact agreement off the smaller interval.

Every noncontact component of {phi_c<phi} is an affine chord between contact points. At an interior contact x, semiconcavity supplies derivative traces phi'_-(x)>=phi'_+(x). The touching inequalities and convexity give

\[
\phi'_-(x)\leq\phi'_{c,-}(x)
\leq\phi'_{c,+}(x)\leq\phi'_+(x).
\]

All quantities are therefore equal. In particular a downward jump in the obstacle derivative cannot be a contact point of the convex minorant.

For any subinterval I_0, semiconcavity of phi bounds the increase of its derivative between contact points by (sup_{I_0} k) times their distance. On a noncontact chord the derivative of phi_c is constant. Between any two points, insert the first and last intervening contact points; if there are none the derivative is constant. This proves

\[
0\leq\phi_c'(y)-\phi_c'(x)
\leq(\sup_{[x,y]} k)(y-x).
\]

Hence phi_c is C¹,¹; shrinking [x,y] and using continuity of k gives 0<=phi_c''<=k almost everywhere. Transforming (47.2) back yields exactly 0<=sigma_{f_c}<=dt. Endpoint agreement gives gluing without new atoms.

If delta=||phi-phi_*||_infinity, then phi_*-delta is a convex minorant, so phi_*-delta<=phi_c<=phi<=phi_*+delta. This proves uniform convergence. The transformed f_c is a convex support restriction with bounded curvature; Lemma 90, or convex secant bounds directly, gives derivative convergence on the window. The original and repaired functions agree with the reference near its endpoints.

Finally, on a noncontact chord the quantity sx-phi_c(s) is the convex combination of its endpoint values with the original obstacle. It cannot exceed their maximum. At contact points it is already an original wall value. Since phi_c<=phi, this proves equality of the two wall suprema exactly as in (40.4). QED.

For the g wall use s=tan(t), psi=(1-g)/cos(t), and replace sin by cos throughout. Its curvature statement is the same.

## 47.4 The energy identity includes all singular curvature

Let u=f_c-f. The functions f and u are Lipschitz, their first derivatives have bounded variation, and their second derivatives are finite measures. On the open set {u>0}, phi_c is affine, so sigma_{f_c}=dt there. Therefore

\[
\boxed{
\int_J u\,d\sigma_f
=\int_J u\,dt+\int_J u'^2\,dt-\int_J u^2\,dt.
}
\tag{47.4}
\]

**Proof.** Distributionally u''+u dt=sigma_{f_c}-sigma_f. Multiply by the continuous compactly supported u. Since u vanishes on the contact set, integral u d sigma_{f_c}=integral u dt. Integration by parts for a Lipschitz function whose derivative is BV gives integral u d u''=-integral u'^2; it follows, for example, by smooth approximation in the integration-by-parts identity for finite measures. Rearrangement gives (47.4). QED.

The left side includes original curvature atoms and singular-continuous mass. They are not discarded by replacing sigma_f with its density.

Moreover u=0 if and only if phi was convex, equivalently 0<=sigma_f<=dt on the window. Thus any violation of measure domination, not merely a density exceeding one, produces a nonzero repair.

## 47.5 Zero-curvature reference windows

If sigma_{f_*}=0 on a window and delta=f-f_* is supported strictly inside it with sigma_f>=0, the perturbation is identically zero. Indeed pair the nonnegative measure delta''+delta with the strictly positive function cos(t-m), where m is the midpoint and the window has length less than pi. Distributional integration by parts gives zero, hence the measure is zero. The equation delta''+delta=0 and the unchanged endpoint neighborhoods then give delta=0.

This is the measure version of Lemma 82. It shows which candidate windows can actually support singular convex perturbations.

The analytic repair is now available for arbitrary convex support measures in the protected neighborhood. The next note checks the two-wall geometry and actual area gains in that setting; preserving one wall supremum alone is still not claimed to preserve the whole niche.
