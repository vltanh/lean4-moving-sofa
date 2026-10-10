# 2. A common convex outer set and the overlap term

This note continues the [two-motion formulation](01-two-motion-envelopes.md). Statements about sets and area are unconditional for its witness data. The final height estimate is explicitly restricted to quarter-turn quadrant representations.

## 2.1 Exact outer-set-minus-niches representation

Use the hallways of Note 1. Set

\[
O_- =\{x\leq1,\ y\leq1\},\quad Q_- =\{x<0,\ y<0\},
\qquad O_+=\rho O_-,\quad Q_+=\rho Q_-.
\]

Directly from the definitions, \(H_d=O_d\setminus Q_d\). For fixed witnesses define the **common outer set**

\[
K=B\cap\bigcap_{d\in\{-,+\}}
\left(g_d(0)^{-1}H_0\cap g_d(1)^{-1}V_d
\cap\bigcap_{t\in[0,1]}g_d(t)^{-1}O_d\right).
\]

Also define the open swept quadrants and their portions inside K:

\[
W_d=\bigcup_{t\in[0,1]}g_d(t)^{-1}Q_d,
\qquad U=K\cap W_-,\quad V=K\cap W_+.
\]

**Proposition 5 (common convex outer set).** K is compact and convex, and the exact two-motion envelope is

\[
E=K\setminus(U\cup V).
\tag{2.1}
\]

**Proof.** Every endpoint arm and every O_d is convex and closed; rigid inverse images preserve these properties. The intersection with compact convex B is compact and convex. For a point already in K, membership in every hallway inverse image is equivalent to exclusion from every swept open quadrant. Exclusion from all such quadrants is precisely exclusion from \(W_-\cup W_+\). Intersecting those quadrants with K does not change which points of K are removed. QED.

This representation allows arbitrary continuous motions and independent witnesses. However, K is **not asserted to be a canonical one-turn cap** with its motion determined by its support function. Both motion paths remain part of the data. Passing from this broad class to a smaller support-function class requires an additional argument.

## 2.2 The sign of overlap

**Proposition 6 (exact inclusion-exclusion).** For measurable U,V contained in finite-area K,

\[
|E|=|K|-|U|-|V|+|U\cap V|.
\tag{2.2}
\]

**Proof.** Integrate the pointwise identity
\(1_{U\cup V}=1_U+1_V-1_{U\cap V}\) on K. QED.

Consequently,

\[
|K|-|U|-|V|\ \leq\ |E|,
\]

not the other way around. Dropping a nonnegative overlap term from (2.2) produces a lower bound. For example, U=V=K with |K|=1 gives a true surviving area of 0 and a double-subtracted expression of -1. This example tests the algebra; it is not claimed to be an extremal sofa configuration.

**Corollary 7 (an overlap budget).** If \(a\leq|U|\), \(b\leq|V|\), and \(|U\cap V|\leq r\), then

\[
|E|\leq|K|-a-b+r.
\tag{2.3}
\]

The total gap in (2.3) is exactly

\[
(|U|-a)+(|V|-b)+(r-|U\cap V|).
\tag{2.4}
\]

Thus equality forces all three losses to vanish. A signed swept-area expression must first be proved to be the appropriate lower bound; it cannot simply be identified with niche area when a sweep is not injective.

## 2.3 A conditional geometric overlap budget

Here is a useful elementary estimate for a **restricted representation**. Suppose the lower niche is swept by quadrants

\[
Q_t(c)=\{c(t)-a\mu_t-b\nu_t:a,b>0\},\quad
\mu_t=(\cos t,\sin t),\quad \nu_t=(-\sin t,\cos t),
\quad0\leq t\leq\pi/2.
\]

Suppose the upper niche is the reflection, across y=1/2, of such a sweep for an independent path d(t). Let

\[
m_c=\sup_t c_y(t),\qquad m_d=\sup_t d_y(t).
\]

**Lemma 8 (ceiling, floor, and overlap slab).** In this representation,

\[
U\subseteq\{y\leq m_c\},\qquad
V\subseteq\{y\geq1-m_d\},\qquad
U\cap V\subseteq K\cap\{1-m_d\leq y\leq m_c\}.
\tag{2.5}
\]

In particular, \(m_c+m_d\leq1\) implies \(|U\cap V|=0\). If the horizontal projection of K has length at most D, then

\[
|U\cap V|\leq D\,(m_c+m_d-1)_+.
\tag{2.6}
\]

**Proof.** A point in Q_t(c) has vertical coordinate
\(c_y(t)-a\sin t-b\cos t\leq c_y(t)\), since sine and cosine are nonnegative on the specified interval. Take the union over t; reflection gives the upper-niche inequality. Their intersection lies in the indicated slab. A slab of nonpositive thickness is empty or a line and has zero area. Otherwise enclose K in its horizontal projection times that slab; this rectangle has area at most its width D times the slab thickness. QED.

The sharper version replaces the rectangle by

\[
|U\cap V|\leq\int_{1-m_d}^{m_c}\ell_K(y)\,dy
\quad\text{when }1-m_d<m_c,
\]

where \(\ell_K(y)\) is the length of the horizontal slice; this is Fubini's theorem. Neither a global height bound nor this restricted representation has been established for arbitrary ambidextrous competitors.

## 2.4 Why a different certificate may be better

Proving a uniform separation theorem is one possible route, but is stronger than needed for an upper bound sharp at one separated candidate. A fixed spatial partition can charge each niche on a disjoint part of the plane, producing a valid upper bound even for overlapping competitors. The next note develops that alternative without changing the sign in (2.2).
