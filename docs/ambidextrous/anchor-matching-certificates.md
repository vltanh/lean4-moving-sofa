# Ordinary-area certificates using extreme points and disjoint pairs

This strengthens the direct-area search without using a hull-energy enclosure. The verifier needs no LP optimality assertion: it proves some cells empty and checks a disjoint list of pairs that cannot both be occupied. Labels AM are local. This note defines the certificate theorem; concrete complete coverings and their execution records are separate data.

## 1. Domain and actually visited frames

Let S be compact, connected, ambidextrous, and contained in 0<=y<=1, with horizontal projection [0,W]. Let P=(0,a), Q=(W,b) be actual points of S. A parameter box specifies W in [w0,w1], a in [a0,a1], and b in [b0,b1], with w0>1. The existing conventional-motion reduction applies when |S|>8/5.

For r in (0,1) rational, define c=(1-r^2)/(1+r^2), s=2r/(1+r^2). Lemma AA1 in [anchor-angle-coverage.md](anchor-angle-coverage.md) guarantees a lower frame at angle 2 arctan(r) when c>=5/8 or w0*c+(b0-a1)*s>1. For the upper frame, replace the last expression by w0*c+(a0-b1)*s. Use only frames passing one of these exact tests.

The ordered normals are (c,s),(-s,c) for the lower turn, and (c,-s),(-s,-c) for the upper turn. Their placements and angles remain independent.

## 2. Keep the same width in coordinate differences

Partition the actual rectangle into nx*ny closed cells

$$C_{ij}(W)=[Wi/n_x,W(i+1)/n_x]\times[j/n_y,(j+1)/n_y].$$

A site is stored as a box for (xi,y), with physical coordinate x=W*xi. The two anchors have sites (0,[a0,a1]) and (1,[b0,b1]). Every site uses the **same** W. Replacing it by independently chosen widths in two different cells is safe but unnecessarily weak.

For sites B_p=[xi_p^-,xi_p^+] times [y_p^-,y_p^+] and B_q, put

$$D_x=[\xi_q^- -\xi_p^+,\xi_q^+ -\xi_p^-],\qquad
D_y=[y_q^- -y_p^+,y_q^+ -y_p^-].$$

For any normal n=(u,v), an exact lower bound for n dot (q-p) is

$$\ell_n(p,q)=\min_{w\in\{w0,w1\},\ d\in\partial D_x}u w d
+\min_{d\in\partial D_y}v d.\tag{AM.1}$$

Bilinearity on a rectangle puts each minimum at endpoints. The two separate minima may occur at different parameters; this only weakens the bound. In particular AM.1 is valid simultaneously for every W,a,b in the parameter box.

## 3. Exclusions derived from known occupied sites

The forbidden-triple equivalence CF1 says that a set fitting in a placed unit hallway with normals u,v cannot contain p,q,r with

$$(q-p)\cdot u>1,\qquad(r-p)\cdot v>1.$$

Repeated witnesses q=r are allowed. Thus a finite list of sites cannot all be met if some ordered triple from that list satisfies ell_u(p,q)>1 and ell_v(p,r)>1 for a guaranteed frame. This conclusion is uniform throughout the parameter box. No relation between unknown points in different sites is presumed beyond their common width coordinate.

The two anchors are known to be occupied. Test each cell together with these anchors; a contradictory triple proves that cell empty. Let E be any resulting collection of distinct empty cells.

For a pair of remaining cells, test the two cells and both anchors. A contradictory triple proves that the two cells cannot both be met. Choose a collection M of such pairs, with every cell appearing in at most one pair and none belonging to E.

**Theorem AM1 (disjoint-pair area bound).** For |S|>8/5 throughout the parameter box,

$$\boxed{|S|\le\frac{w1}{n_xn_y}\bigl(n_xn_y-|E|-|M|\bigr).}\tag{AM.2}$$

**Proof.** Assign z_i=1 when S meets the closed cell and zero otherwise. Each empty cell has z_i=0; each matched pair has z_i+z_j<=1; every unmatched cell has z_i<=1. Disjointness makes these inequalities add without double counting. Since the cells cover S and each has area W/(nx*ny), their occupied area bounds |S|. Replacing W by w1 gives AM.2. Boundaries have planar measure zero and can only increase the meet count. QED.

A maximum matching is not needed for validity. Any checked disjoint matching supplies the theorem. Searching for one is untrusted discovery; the replay checks only its geometric witnesses and disjointness.

Without the hypothesis |S|>8/5, the unconditional bound is the maximum of 8/5 and AM.2. This qualification must be retained when a bin's computed expression falls below 8/5.

## 4. A complete width covering

A certificate declares one constant pair of anchor-height intervals, a width interval, rational angle parameters, and consecutive width bins. Each bin gives its grid and matching. The verifier re-derives empty cells itself and rejects a gap, overlap, invalid index, repeated matched cell, matched empty cell, or geometrically unjustified pair.

If every bin's AM.2 expression is below a target C>8/5, all bodies in the declared region have area below C. This is a continuum conclusion because each geometric separation is an interval bound, not a test at the center of a box.

To obtain an exclusion independent of width, the certificate still needs every remaining width. AW-W gives |S|<41/25 for W<=2. The hand proof AL1 in [anchor-width-localization.md](anchor-width-localization.md) gives W<=2999/1020 for |S|>8/5. Thus a certificate covering [2,2999/1020] with C>41/25 suffices for its declared anchor-height region. This does not exclude other extreme-height configurations.

## 5. Exact comparison with the candidate

The planned replay target is C=411/250. It is strictly below Romik's candidate M without relying on a floating-point value. Let z=149/500. Then

$$4z^3+3z-1=-4551/31250000<0,$$

so the positive root Y of 4Y^3+3Y-1=0 exceeds z. Also arctan(z)>z-z^3/3, obtained by integrating 1/(1+t^2)>1-t^2 for t>0. Consequently

$$M=1+4Y^2+\arctan Y>
1+4z^2+z-z^3/3=616648051/375000000,$$

and the last number exceeds 411/250 by 148051/375000000. No decimal rounding is part of the target comparison.

## 6. Trust boundary and remaining task

The replay uses unbounded integers and rational arithmetic. Integer-scaled AM.1 is exact; it must not replace strict separation >1 by >=1. The generator may use guarded machine integers and a graph algorithm, but the verifier reconstructs all accepted contradictions independently. A reported maximum matching size or LP status alone is never accepted.

The earlier unrestricted LP has a fractional floor; conditioning on actual anchors and exhibiting a disjoint matching avoids relying on fractional rounding. It does not mean that two anchors suffice for a sharp certificate near the candidate. More graph edges, denser cells, or more angles are not claimed to close every remaining region.

Small endpoint-height difference still does not imply height near 1/2 or a candidate neighborhood. The weighted one-turn arm theorem still needs weighted one-turn maximality. Neither statement is silently inserted into AM1 or a proposed local finishing theorem.

This is a written proof with self-review. No CI or Lean/Lake compilation was used. The unrestricted optimal value remains unproved until all other regions and the sharp residual comparison are addressed.
