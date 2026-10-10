# All-angle surviving wings do not give the desired core-area comparison

**Purpose.** MW2 constructs actual full-height convex surviving wings from a weighted maximizer. It is tempting to insert those smaller wings into the already calibrated two-wing functional and infer an ordinary-area upper bound. This note rules out that substitution on the reference candidate itself, by an exact triangle calculation. It is a negative result about this comparison, not a counterexample to Romik optimality. Labels AO are local.

The original truncated-wing calibration and the valid MW height/support statements are not retracted. The missing premise remains the ordinary-area comparison. Dependencies are the explicit reference wing geometry in TW.6 and the definition CS.3 of the actual-inward-intersection functional. No numerical premise is used.

## 1. The reference inward vertex and its two edges

Let beta be the reference angle, c=cos(beta), s=sin(beta), and let A=(r,1/2) be the candidate's right horizontal extreme. On -beta<=theta<=beta its hull support is A dot n_theta. The reference right wing R_* has inward vertex

$$Q=(r-1/c,1/2)$$

and two straight inward edges from Q to

$$Z_-=(r-c,1/2-s),\qquad Z_+=(r-c,1/2+s).\tag{AO.1}$$

Equivalently Z_- - Q = -tan(beta) n'_beta and Z_+ - Q = tan(beta) n'_{-beta}. These are precisely the cut-edge endpoint formulas used in WC/CS. The left wing is the horizontal reflection.

The support definition in TW.6 also identifies R_* with the candidate's truncated canonical right wing: on the outward semicircle its bounds are the candidate hull's, on the inward constrained arcs they are the corresponding inner-wall bounds, and on the inward normal gap they are the positive combinations of its endpoint supporting inequalities. Thus adding more inner-wall constraints gives a subset of R_*.

## 2. A single extra wall removes a positive triangle

The all-angle right wing includes the theta=0 inner-wall condition

$$x\ge r-1.$$

Set

$$d=1/c-1=(1-c)/c>0.$$

The horizontal distance from Q to either Z is s^2/c. Since

$$d/(s^2/c)=1/(1+c)<1,$$

the new vertical cut meets the interiors of the two displayed straight edges. In coordinates X=x-Q_x, Y=y-1/2, those edges are Y=plus or minus (c/s)X. Convexity and the triangle with vertices Q,Z_-,Z_+ show that the wing section is exactly this wedge for 0<=X<=d. The removed area is therefore

$$
\boxed{D=\int_0^d2(c/s)X\,dX=(c/s)d^2=\frac{(1-c)^2}{sc}>0.}
\tag{AO.2}
$$

The cut leaves portions of both inward supporting edges. Hence their support values at pi-beta and pi+beta are unchanged, and their supporting-line intersection in CS.3 remains Q. The outward supports used by the core are unchanged as well. One way to see this is that the actual right flank is retained; it attains every outward-semicircle support, as in MW1. The cut lies strictly left of that flank for the explicit reference geometry.

Thus the pair obtained by applying this single horizontal cut to each reference wing has exactly the same core curves and inward connector vertices as the reference pair, but loses area D in each positively counted wing. It follows directly from CS.3 that

$$
\boxed{\widehat{\mathcal W}(R_*\cap\{x\ge r-1\},D_*^{\rm cut})=M-2D<M.}
\tag{AO.3}
$$

These cut wings are still valid full-height convex data for SQ1. Validity for an auxiliary calibration is not the same as enclosing the reference body with its chosen core.

## 3. The complete all-angle wings retain the same cut vertices

For |theta|<beta, the extra first-wall depth of Z_+ or Z_- is

$$
h_K(\theta)-Z_\pm\cdot n_\theta
=c\cos\theta\mp s\sin\theta
=\cos(\theta\pm\beta)\le1.
\tag{AO.4}
$$

Outside that short gap, Z_+,Z_- already belong to the reference truncated wing. They therefore survive every extra all-angle right-wall constraint. Consequently the all-angle wing still attains both inward cut supports, since the endpoints Z_+,Z_- lie on the original supporting lines. Its actual inward intersection is still Q.

MW2 gives the retained outward supports. Thus the core curves and connector terms in CS.3 remain exactly the reference terms, while each all-angle wing is contained in the singly cut wing from Section 2. Therefore:

**Theorem AO1 (reference obstruction).** On Romik's reference hull, the all-angle surviving wings satisfy

$$
\boxed{
\widehat{\mathcal W}(\overline R_*,\overline D_*)
\le M-\frac{2(1-\cos\beta)^2}{\sin\beta\cos\beta}<M=|\Sigma|.
}
\tag{AO.5}
$$

In particular the proposed comparison |Sigma|<=widehat W of those all-angle wings is false. This proof uses only the explicit candidate geometry; it does not suppose that candidate optimality is known or that the candidate cap has already been proved to maximize Psi.

## 4. Consequence for continuation

The all-angle wings from MW2 are actual surviving material, are full height, and retain all outward supports. Those properties alone still do not prove the core enclosure. Some surviving material can legitimately switch hallway arms during the omitted early angles. Forcing the same arm at every angle removes material that the old fixed-cut core does not restore.

Use the truncated MW1 wings only with an explicitly justified core comparison. Use the all-angle wings only with a separately corrected core functional. Do not try to repair AO.5 by finer sampling or by invoking SQ1's equality kernel: the inequality fails exactly on the reference, before any numerical error or limiting argument.

A short exploratory polygon calculation suggested this failure; AO.1--AO.5 replace that observation with a hand proof. The original bounded diagnostic is kept in the session record and is not a certificate. No CI, Lean/Lake compilation, long search, dependency installation, or manuscript build was used.
