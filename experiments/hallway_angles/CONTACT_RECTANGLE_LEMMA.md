# Contact rectangles: alignment without full Hausdorff stability

**Analytic proof draft.** This lemma replaces the use of the actual-set Hausdorff theorem in the final near-reversal alignment argument. It still uses the reverse-class majorant and quadratic path deficit. No optimality or feasibility assertion is inferred from numerical samples.

Write e=pi-beta, T_e=A_e S_e, A_e(x,y)=(e x,y), and let ell_e>0 be the candidate's top/bottom flat-contact length. Thus `[0,ell_e] x [-1/2,1/2]` is contained in the convex candidate T_e.

## 1. A guaranteed core from coordinatewise path errors

Let R be an aligned reverse sofa, centered in its actual vertical strip, with normalized area deficit d=e(V(e)-area(R)). Fix the usual horizontal canonical gauge. Suppose its rescaled canonical corner differs from the full-width stationary corner coordinatewise by at most eta_x, eta_y on the whole parameter interval.

The reverse-class majorant constructs the containing region

    Omega = {(X,Y): -w/2<=Y<=w/2, g_R(Y)<=X<=F_R(Y)}

and proves

    A_e R subset Omega,    area(Omega minus A_e R)<=d.

This is the crossing/excursion argument, not the later Hausdorff/inball estimate. Its endpoint-height inclusion is as explained in `REVERSE_SET_STABILITY.md`, Section 1.A.

If 2 eta_x<ell_e and 2 eta_y<1, then the rectangle

    Q=[eta_x,ell_e-eta_x] x [-1/2+eta_y,1/2-eta_y]       (1)

is contained in Omega. To prove this:

- The full-width candidate corner has X<=0 throughout. At each crossing height the competing corner therefore has g_R(Y)<=eta_x.
- Rescaled outer normals have nonnegative horizontal component. The candidate rectangle gives its outer supports the lower bound `N_x ell_e+|N_y|/2`. Canonical support offsets change by at most `N_x eta_x+|N_y| eta_y`. Every point of (1) consequently satisfies all competing outer support inequalities.
- The endpoint corner-height difference is exactly (1-w)/2, so eta_y>=(1-w)/2. Hence (1) lies in the actual strip.

In particular, `area(Q minus A_e R)<=d`. No convexity of R, lower bound for the competing corner speed, or Hausdorff control is required.

## 2. Directional width from a rectangle with little missing area

Let a compact measurable set E miss area at most d from a rectangle of width W>0 and height H>0. For a direction whose component magnitudes are a,b>0, assume

    d < min{a W^2/(2b), b H^2/(2a)}.                  (2)

Then

    width(E,(a,b)) >= a W+b H-2 sqrt(a b d).           (3)

Translations and sign changes of the direction do not affect the assertion.

Proof. Translate the rectangle so its projection interval is [0,L], L=aW+bH. Write [s,t] for the projection interval of E. Put x=max(s,0), y=max(L-t,0). The missing lower and upper corner caps have projection depths x and y. If either depth reached m=min(aW,bH), the missing triangular cap would have area at least m^2/(2ab)>d by (2). Thus both caps lie in the triangular regime. They are disjoint (s<=t), and their total missing area is (x^2+y^2)/(2ab). It follows that x+y<=2 sqrt(abd). Also L-(t-s)<=x+y, proving (3). Compactness ensures the extrema exist; the same statement follows by limiting extrema for bounded measurable sets.

## 3. Consequence for a misaligned high-area competitor

Let S be unrestricted, area(S)>=V(e), and let nu be its entry/exit normal mismatch. Set lambda=cos(nu/2), R=lambda S. Once its aligned class is reverse,

    0<=d=e[V(e)-lambda^2 area(S)]<=eV(e) nu^2/4.

The original exit strip gives `width(A_e R,(sin(nu)/e,cos(nu)))<=lambda`. Apply (1)-(3) with

    a=|sin(nu)|/e, b=cos(nu),
    W=ell_e-2eta_x, H=1-2eta_y.

Provided (2) holds, every nonzero nu must satisfy

    ell_e a <= lambda-b+2a eta_x+2b eta_y+2 sqrt(a b d). (4)

The candidate flat penalty is linear in |nu|/e. Explicit quadratic coercivity makes eta_x,eta_y=O(|nu|), whereas d=O(nu^2). Thus (4) permits a direct numerical cutoff once the path constants are bounded.

Unlike the earlier global proof, this route does not depend on uniform Hausdorff stability, the universal limiting body, a geometric inball, or any existential set-stability constant. Those remain separate results. The current lemma makes no particular numerical cutoff claim; that requires the constants and inequalities to be checked next.
