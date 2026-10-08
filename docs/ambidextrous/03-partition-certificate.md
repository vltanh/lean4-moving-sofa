# 3. A spatial partition certificate that permits overlap

This is an elementary but potentially useful alternative to a universal separation theorem. It is a valid upper bound for all the witness data of Notes 1–2. The still-missing step is to bound an analytically tractable version of this majorant by Romik's area.

Fix measurable \(U,V\subseteq K\), where K has finite area, and let \(E=K\setminus(U\cup V)\).

## 3.1 Weighted charging without double subtraction

Let \(w:\mathbb R^2\to[0,1]\) be measurable and define

\[
P_w(K,U,V)=|K|-\int_U w\,dp-\int_V(1-w)\,dp.
\tag{3.1}
\]

**Theorem 9 (partition majorant and exact slack).**

\[
|E|\leq P_w(K,U,V),
\]

and in fact

\[
P_w-|E|=
\int_{U\setminus V}(1-w)\,dp+
\int_{V\setminus U}w\,dp.
\tag{3.2}
\]

In particular, equality holds exactly when

\[
w=1\text{ a.e. on }U\setminus V,
\qquad w=0\text{ a.e. on }V\setminus U.
\tag{3.3}
\]

**Proof.** Pointwise on K,

\[
1_{U\cup V}-w1_U-(1-w)1_V
=(1-w)1_{U\setminus V}+w1_{V\setminus U}.
\]

The identity follows by considering points in neither set, either exclusive part, and the overlap. In the overlap the amount charged is \(w+(1-w)=1\), not 2. Integrate and use nonnegativity. A nonnegative measurable function has zero integral exactly when it vanishes almost everywhere, giving the equality conditions. QED.

There is **no hypothesis that U and V are disjoint**. In contrast to dropping the overlap term from inclusion-exclusion, the direction of the bound is always correct.

## 3.2 A fixed horizontal separator

For a fixed height h take \(w=1_{\{y\leq h\}}\). Writing \(D_h=\{y\leq h\}\), \(D_h^c=\{y>h\}\), the certificate is

\[
P_h=|K|-|U\cap D_h|-|V\cap D_h^c|,
\tag{3.4}
\]

with exact gap

\[
P_h-|E|=
|(U\setminus V)\cap D_h^c|+
|(V\setminus U)\cap D_h|.
\tag{3.5}
\]

A candidate with its lower niche entirely below h and upper niche entirely above h is therefore tight for this **globally valid** bound. Competitors may have overlapping niches or cross the separator; the resulting nonnegative slack is retained.

This changes the geometric task: instead of proving separation for every optimizer, seek lower bounds on the two *clipped* niche areas in (3.4), sharp at the candidate. Merely knowing a lower bound on the full area |U| does not give the same lower bound on \(|U\cap D_h|\).

**Corollary 10 (a tractable certificate with a recorded deficit).** Suppose for witness data z=(K,U,V,...) there are functions a(z), b(z) with

\[
a(z)\leq|U\cap D_h|,\qquad b(z)\leq|V\cap D_h^c|.
\]

Set \(Q(z)=|K|-a(z)-b(z)\). For every measurable \(S\subseteq E\),

\[
Q(z)-|S|=D_-(z)+D_+(z)+D_{\rm mask}(z)+D_{\rm fill}(z),
\tag{3.6}
\]

where

\[
D_- =|U\cap D_h|-a,\quad
D_+ =|V\cap D_h^c|-b,
\]

\[
D_{\rm mask}=|(U\setminus V)\cap D_h^c|+|(V\setminus U)\cap D_h|,
\quad D_{\rm fill}=|E\setminus S|.
\]

All four terms are nonnegative. This is an exact algebraic identity, proved by inserting (3.5) and \(|E|-|S|=|E\setminus S|\).

The potential optimality theorem would additionally prove \(Q(z)\leq M\) uniformly, with M the candidate area. That assertion is **not proved** here. Equation (3.6) identifies the equality obligations without assuming the conclusion.

## 3.3 Two useful stress tests

**Averaging is generally not sharp.** For the constant weight w=1/2,

\[
P_{1/2}-|E|=\tfrac12|U\mathbin{\triangle}V|.
\]

Thus averaging the two niche charges loses half their symmetric difference. In particular, separated nonzero candidate niches cannot make that average sharp. Spatial allocation, rather than a scalar average, matters.

**Optimizing over every measurable weight is tautological.** By taking w=1 on \(U\setminus V\), w=0 on \(V\setminus U\), and arbitrary values elsewhere, one gets

\[
\inf_{0\leq w\leq1} P_w=|E|.
\]

This identity is not a solution: its minimizing weight depends on the unknown exclusive niches. The research target is a fixed geometrically simple weight, or a controlled family of weights, for which a uniform analytic bound can actually be established.

## 3.4 Reflection and local tightness

Reflection \(\rho(x,y)=(x,1-y)\) exchanges the niche labels:
\((K,U,V)\mapsto(\rho K,\rho V,\rho U)\).
If \(w(\rho p)=1-w(p)\) almost everywhere, change of variables gives

\[
P_w(\rho K,\rho V,\rho U)=P_w(K,U,V).
\tag{3.7}
\]

The midline separator h=1/2 has this property; its value on the midline is immaterial to area. Equation (3.7) is invariance of the certificate, **not** a proof that an optimizer is symmetric.

**Lemma 11 (robust tightness in a restricted path class).** In the quarter-turn representation of Note 2, suppose a pair of paths has \(m_c<h-\delta\) and \(1-m_d>h+\delta\) for some \(\delta>0\). Perturb both paths in their vertical coordinates by less than \(\delta\) in uniform norm, keeping the same angular representation. For every common outer set associated with the perturbed paths, \(P_h=|E|\).

**Proof.** The perturbed lower sweep remains below h and the reflected upper sweep remains above h by Lemma 8. Both terms in (3.5) vanish. QED.

This says a strict candidate separation margin removes the mask loss in a neighborhood of the candidate, even under independent perturbations of the two paths. It does not establish that the candidate is stationary, or control configurations outside that neighborhood.

## 3.5 Immediate next inequality

For h=1/2, the concrete target is

\[
|K|-a(z)-b(z)\leq M,
\qquad a(z)\leq|U\cap\{y\leq1/2\}|,
\quad b(z)\leq|V\cap\{y>1/2\}|.
\tag{3.8}
\]

Candidate tightness requires equality in the two clipped-area estimates as well as in the mask. A Mamikon-type or support-function construction of a and b must control clipping, sweep multiplicity, endpoint terms, independent motions, and any reduction of the witness class. None of these requirements is supplied just by Theorem 9.
