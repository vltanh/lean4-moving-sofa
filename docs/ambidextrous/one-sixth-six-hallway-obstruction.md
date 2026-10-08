# An exact obstruction to reaching a 1/6 gain with the current hallway angles

**Scope.** The requested improvement is the global target
\[
T_*=2\sqrt2-1-\frac16=2\sqrt2-\frac76\approx1.6617604581.
\]
This note proves that the three-hallway method TH/QT/JH/JD cannot reach this target by better constants alone. In fact, even **six** positions, at angles \(\arcsin(3/5),\pi/4,\arcsin(4/5)\) in each handed family, admit a compact connected polygon of area **exactly \(5/3>T_*\)**. The polygon need not move between the specified positions; this is an obstruction to the finite relaxation, not a counterexample to the desired sofa bound. Labels SX are local.

The proof is elementary and rational apart from the isometry between coordinates. It does not use the external four-angle witness, which does not impose the exact 45-degree positions and therefore would not by itself refute this particular approach.

## 1. An explicitly defined rational polygon

Use isometric coordinates \((u,v)\), and put
\[
P=19/10,\qquad a=127/10,\qquad b=68/5.
\]
Let \(S\) be the intersection of the following closed sets:

1. The diagonal band \(|u+v-P|\le7/10\).
2. The two opposing unit midpoint hallways
\[
0\le u,v\le P,\quad
(u\ge P-1\ \text{or}\ v\ge P-1),\quad
(u\le1\ \text{or}\ v\le1).
\]
3. A narrower rational hallway
\[
X=\{7u-v\le a,\ u+7v\le b,\quad
7u-v\ge a-7\ \text{or}\ u+7v\ge b-7\},
\]
and its images under the two commuting reflections
\[
J(u,v)=(v,u),\qquad R(u,v)=(P-v,P-u).
\]
Thus impose \(X,JX,RX,JRX\), in addition to the two midpoint hallways.

To interpret these in the physical plane, use
\[
x=(u-v)/\sqrt2,\qquad y=(u+v-P+7/10)/\sqrt2.
\]
This is an isometry followed by translation, so it preserves area. The band becomes a horizontal incoming strip of height \(7/(5\sqrt2)<1\).

The gradients of the two affine coordinates of \(X\), divided by \(5\sqrt2\), become the physical unit normals \((4/5,3/5)\) and \((-3/5,4/5)\). Its arm width is \(7/(5\sqrt2)<1\). Increasing that width to one while leaving the outer walls fixed only enlarges the hallway, so membership in \(X\) proves membership in a translated ordinary unit hallway of proper angle \(\arcsin(3/5)\). The reflection \(J\) supplies the complementary lower angle \(\arcsin(4/5)\); \(R\) supplies the upper-handed counterparts. Reflection about the actual strip midline rather than the unit-strip midline differs only by a permitted hallway translation. The original midpoint constraints are the exact unit hallways at 45 degrees. Thus the construction really satisfies all six stated positions.

## 2. A seven-piece profile proves connectedness and computes the area

Put
\[
z=u-v,\qquad t=u+v-P.
\]
The defining set is invariant under independent changes of sign of \(z\) and \(t\). For \(z\ge0,t\ge0\), the six hallway constraints reduce exactly to
\[
0\le t\le H(z),
\]
where
\[
\begin{split}
H(z)=\min\{&7/10,\ P-z,\ 2-P+z,\
7/3-4z/3,\ 3/2-3z/4,\
&\max(4z/3,\ 1/4-3z/4),\ 1/4+3z/4\}.
\end{split}
\]
Here the last entry is the other maximum from the reflected inner-wall alternative: for \(z\ge0\), \(\max(-4z/3,1/4+3z/4)=1/4+3z/4\). The two midpoint inner alternatives supply \(t\le2-P+z\); their outer walls supply \(t\le P-z\).

Ordering these affine functions gives the exact table

| Interval for z | H(z) |
|---|---|
| \([0,3/35]\) | \(1/10+z\) |
| \([3/35,3/25]\) | \(1/4-3z/4\) |
| \([3/25,3/10]\) | \(4z/3\) |
| \([3/10,3/5]\) | \(1/10+z\) |
| \([3/5,16/15]\) | \(7/10\) |
| \([16/15,10/7]\) | \(3/2-3z/4\) |
| \([10/7,7/4]\) | \(7/3-4z/3\) |

Beyond \(z=7/4\), no positive-height fiber occurs. The adjacent expressions agree at every breakpoint, and each expression in the table is positive on the interior of \([0,7/4]\). Consequently
\[
S=\{|z|\le7/4,\quad |t|\le H(|z|)\}
\]
in these coordinates is compact and connected: every vertical t-fiber is an interval meeting the entire horizontal midline \(t=0\). No zero-area component was discarded.

Since \(du\,dv=\tfrac12\,dz\,dt\), fourfold symmetry gives
\[
|S|=2\int_0^{7/4} H(z)\,dz=\boxed{5/3}.
\]
The last equality is integration of the seven displayed affine expressions and can be checked by rational arithmetic alone. Thus connectedness, all six hallway memberships, and the exact area are established without relying on a numerical feasibility sample.

## 3. Consequence for the requested target

The target is strictly below \(5/3\):
\[
2\sqrt2-7/6<5/3
\quad\Longleftrightarrow\quad
2\sqrt2<17/6,
\]
which follows by squaring, since \(8<289/36\).

**Theorem SX1.** No area theorem assuming only the incoming unit strip and these six freely translated hallway positions can prove the proposed \(1/6\) gain. This also rules out obtaining that gain solely by sharpening the constants of JD1, which uses only three of these positions. Additional hallway angles or a property of the continuous motions that is absent from this finite relaxation is necessary.

This is not an assertion that the full ambidextrous bound \(|S|\le T_*\) is false. The polygon is a finite-position witness; neither continuous motion between those positions nor full-turn feasibility is asserted. In particular it does not contradict Romik optimality.

## 4. Bounded discovery, not an upper-bound calculation

A short, prescribed rational polygon screen suggested the construction. Another nearby rational choice \(P=37/20,a=25/2,b=67/5\), with the same band and narrower hallway width, gave finite-envelope area \(1415927/840000\approx1.685627\). The simpler \(5/3\) witness above was selected for its seven-piece hand computation, not because it is the finite relaxation's maximizer.

This result is a reason to stop optimizing the old three-hallway constants toward \(1/6\), not a reason to abandon the target. It changes the proof requirements. The companion joint-terminal-strip reduction gives a different sufficient route: a full-turn bound of \(33/20\) would imply an unrestricted bound below \(T_*\). That full-turn premise is still unproved.

No CI, Lean/Lake compilation, dependency installation, manuscript build or long search was used. This hand proof is self-reviewed and has not been independently refereed or kernel-checked.
