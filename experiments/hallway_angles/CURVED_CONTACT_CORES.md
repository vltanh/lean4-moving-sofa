# Curved-contact cores: using more than the flat top segment

**Sixth-round analytic checkpoint.** This lemma strengthens the geometry used by `CONTACT_RECTANGLE_LEMMA.md`. It does not yet claim a new numerical global cutoff. The cap/crossing/excursion majorant and the explicit reverse candidate remain dependencies. No CI or Lean verification is used.

Write T_e=A_e S_e, A_e(x,y)=(e x,y), and write its horizontal slices as g_e(Y)<=X<=F_e(Y). The candidate is symmetric in Y, with g_e convex, F_e concave, and g_e(+-1/2)=0. Let an aligned reverse competitor R have canonical path errors bounded coordinatewise by eta_x,eta_y after the usual normalization. Its majorant region Omega contains A_e R and satisfies

    area(Omega minus A_e R)<=d,
    d=e[V(e)-area(R)].

## 1. A family of guaranteed rectangles

For any 0<B<=1/2 the candidate contains

    [g_e(B), F_e(B)] x [-B,B].

If B>eta_y and F_e(B)-g_e(B)>2eta_x, then Omega contains

    [g_e(B)+eta_x, F_e(B)-eta_x]
       x [-B+eta_y, B-eta_y].                         (1)

For the left boundary: at a competing crossing height |Y|<=B-eta_y the candidate path height differs by at most eta_y, hence lies in [-B,B]. Its horizontal coordinate is at most g_e(B), so the competing crossing coordinate is at most g_e(B)+eta_x.

For the outer constraints: a candidate rectangle with right endpoint F_e(B) gives the lower support bound N_x F_e(B)+|N_y|B, where N_x>=0 for the reverse outer normals. Canonical support errors are at most N_x eta_x+|N_y|eta_y. Every point of (1) satisfies all the competing outer inequalities. Finally eta_y>=(1-w)/2 from the endpoint heights, so the rectangle lies in the actual strip.

Therefore the competitor misses area at most d from (1). This argument does not require Hausdorff stability or a lower bound on the competitor's corner speed.

## 2. Simple uniform rectangles from curvature bounds

Let h_e(phi) be the upper support function, rho_e=h_e+h_e'', and ell_e=e h_e'(0) the rescaled flat-contact length. Suppose that for all 0<=u<=u_* one has

    0<r_-<=e^2 rho_e(eu)<=r_+,
    cos(eu)>=c_*>0.

The upper support point has rescaled coordinates X(u),Y(u). Differentiating its parametrization gives

    X(u)-ell_e=integral_0^u e^2 rho_e(ev) cos(ev) dv
                 >=r_- c_* u,
    1/2-Y(u)=integral_0^u e^2 rho_e(ev) sin(ev)/e dv
                 <=r_+ u^2/2.

By convexity, symmetry, and g_e<=0, the candidate consequently contains

    [0,ell_e+r_- c_*u]
       x [-1/2+r_+u^2/2, 1/2-r_+u^2/2].              (2)

Shrinking (2) horizontally by eta_x at each side and vertically by eta_y at each side gives another guaranteed core of Omega.

For a testing direction (a,b), a,b>0, its unshrunk projected width is at least

    a ell_e+b+a r_-c_*u-b r_+u^2.

The last two terms expose the improvement over using only the flat-contact rectangle u=0. They are a concave quadratic in u, maximized at u=a r_-c_*/(2b r_+) unless the allowed u interval intervenes.

## 3. Use and remaining checks

The missing-area directional-width lemma applies to every such rectangle once its positive dimensions and triangular-cap regime are verified. A different rectangle may be chosen for each mismatch direction. Uniform curvature bounds over (e,u), path/width constants, and all small-mismatch cases must be established before converting this observation into a new global cutoff.

Exploratory floating-point tests favor these larger interior rectangles, but are not a proof. Their advantage is geometric: the curved cap widens quickly just below the flat top, so the proof need not discard almost all of the useful candidate shape.
