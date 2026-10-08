# Exact ordinary-area identity: central rectangle + two arbitrary convex cores − effective niche cost

**Theorem RCE1 (the correct filled-core area formula).**
Let \(T>0\). Let \(V_1,V_2\subseteq
[0,T]\times[0,1/2]\) be **arbitrary
independent convex cores** whose horizontal
projection is [0,T], vertical height 1/2,
and bottom face is the entire segment
[0,T]×{0}. Add the explicit rectangular
filler
\[
R_T=[0,T]\times[0,1/2],
\qquad
U_i=V_i+R_T.
\]
Each U_i is a downward convex one-turn
cap of projection [0,2T] and height 1,
containing \([0,2T]\times[0,1/2]\).
Let \(A_i(x)\) be its upper roof and
\(n_i(x)\) its full positive one-turn
forbidden niche roof. Assume
\[
\boxed{0\le n_i(x)\le1/2\quad
\text{for both caps, almost everywhere.}}
\tag{RCE.1}
\]

Put \(\rho(x,y)=(x,1-y)\) and let
\(E=(U_1\setminus N_1)\cap
\rho(U_2\setminus N_2)\).
Then E is compact, connected, follows
both complete conventional unit-width
quarter turns, and its **ordinary**
area has the **exact geometric identity**
\[
\boxed{
|E|=T+|V_1|+|V_2|
-\int_0^{2T}
\left[(n_1+A_2-1)_+
+(n_2+A_1-1)_+\right]dx,
}
\tag{RCE.2}
\]
where \(z_+=\max(z,0)\).
The two integral terms are the
**effective niche area actually removed**
from the common outer core-plus-rectangle
intersection, not the untruncated
whole-niche areas. They have the
correct sign for arbitrary asymmetric
core profiles, curvature atoms and
distinct contact patterns.

This is a **fully proved exact area
formula**, not yet the Romik upper
bound: for arbitrary cores, the
sharp inequality that would finish
this subclass is
\[
\boxed{
\int_0^{2T}\!\!
\left[(n_1+A_2-1)_+
+(n_2+A_1-1)_+\right]dx
\ge T+|V_1|+|V_2|-M.
}
\tag{RCE.3}
\]
RCE.3 is true for the special core
families proved in
[TCG](triangular-core-expanded-gerver-sharp-hand-bound.md)
and [SCR](sheared-romik-core-sharp-local-theorem.md),
but remains **unproved for unrestricted
independent convex cores**.

## 1. Exact Minkowski mixed-area contribution of the filler

For a compact convex body V with
horizontal projection [0,T] and
vertical span 1/2, Minkowski
addition of [0,T] e_x increases
ordinary area by \(T/2\).
The resulting convex body's width
is 2T. Adding [0,1/2] e_y
increases area by \(T\).
Thus *for any shape of the core*,
\[
\boxed{|U_i|=|V_i|+3T/2.}
\tag{RCE.4}
\]

The added half-height rectangle
also supplies the **whole**
lower half of the incoming strip.
The bottom-face condition and
convexity give downward closure,
because every point is joined
vertically to the bottom segment
in the cap. These are true
Minkowski sums, not heuristic
“fill the center” drawings.

## 2. Outer two-cap overlap is exactly the cores plus T

The downward cap U_i has vertical
fiber \([0,A_i(x)]\), with
\(1/2\le A_i(x)\le1\).
Its vertically reflected mate
\(\rho U_2\) has fiber
\([1-A_2(x),1]\).
The common convex outer intersection
C=U_1∩ρU_2 consequently has
nonempty fiber
\([1-A_2(x),A_1(x)]\) at every
\(x\in[0,2T]\). Thus
\[
\begin{aligned}
|C|&=\int_0^{2T}
(A_1+A_2-1)\,dx\\
&=|U_1|+|U_2|-2T\\
&=\boxed{T+|V_1|+|V_2|}.
\end{aligned}
\tag{RCE.5}
\]
The term T is **exactly the
central rectangular filling area
remaining after the two separate
Minkowski additions are combined**.

## 3. Two disjoint, *effective* niche losses

For an ordinary cap U_i,
the positive full niche is
downward closed in y and its
vertical section is \([0,n_i(x))\)
up to null boundaries.
By RCE.1, \(n_i\le1/2\le A_i\),
so \(N_i\subset U_i\) up to
null boundaries. The lower niche
N_1 cuts away from C exactly
the interval
\([1-A_2(x),n_1(x))\) if
\(n_1+A_2>1\), and nothing
otherwise; its length is
\((n_1+A_2-1)_+\).

The upper reflected niche
\(\rho N_2\) removes precisely
\((n_2+A_1-1)_+\) from C.
The lower removal occurs at
heights ≤1/2 and the upper one
at heights ≥1/2. They are disjoint
up to their common horizontal
midline, a planar null set.
Fubini and RCE.5 therefore prove
the exact identity RCE.2.
Nothing depends on the niches'
horizontal sections being
intervals, or on any signed
curve-area interpretation.

## 4. Feasibility and the irreducible interaction term

Each one-turn survivor has
vertical interval sections
\([n_i(x),A_i(x)]\) containing
height 1/2. Their reflected
intersection E therefore has
nonempty interval vertical
sections sharing the entire
horizontal midline. It is
compact and connected.
Every point of E satisfies
both complete canonical
support-tightened hallway
families of the parent caps,
which depend continuously
on angle. The incoming/terminal
straight arms can be appended
as usual, making E a **genuine
ambidextrous sofa**.

If \(n_i\) is confined to
the flat top-face interval of
its own cap, but that interval
is displaced relative to the
other's, some niche lies outside
the other cap's full-height part.
Only its **effective** loss in
RCE.2 can then be charged.
Replacing either positive part by
n_i without proving an inclusion
would overcount forbidden area
and yield a false upper bound.
This is exactly the earlier
nonnegative OT1 clipping correction
in core-plus-rectangle coordinates.

The **Romik reference core**
satisfies all hypotheses with
\(V_1=V_2=V_*\); its effective
niche terms equal its two full
niche areas, and equality in
RCE.3 occurs at area M.
The new TCG1 hand proof shows
RCE.3 strictly for a two-parameter
family of independent triangular
cores. SCR1 proves it with a
quantitative quadratic margin for
small independent shears of the
actual smooth reference core.

Thus the user's geometric
construction has an exact and
nontrivial mathematical meaning.
The unresolved global task is
**the effective niche lower bound
RCE.3 for arbitrary core profiles
or an area-nondecreasing operation
reducing arbitrary sofas to this
core class**. Neither follows from
plain width-two Gerver optimality.

This note contains only
pen-and-paper set-area identities
and explicit scope limitations.
No Lean formalization, optimization,
CI or independent refereeing
is claimed.
