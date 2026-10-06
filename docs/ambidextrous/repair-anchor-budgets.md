# Genuine hull repairs have shared endpoint-anchor budgets

The failed energy enclosure in SAT1/SAC2 rules out charging an arbitrary positive multiple of the whole repair derivative energy to ordinary missing area. This note records a different restriction that the earlier freely varying auxiliary increments discarded: the two reflected repairs share the same horizontal exposed points of the original body. Their total room is at most the height of the incoming strip.

The inequalities below are proved for any pair of nested convex hulls with the same axis supports. They do not use maximality, curvature, or a claim that the repaired envelope is feasible. A possible ordinary-area comparison at the end is explicitly **not proved**. Labels AB are local to this note.

## 1. Two witnesses are shared by both halves

Let K and Kbar be nonempty compact convex bodies such that

$$
K\subseteq\overline K\subseteq[-a,a]\times[0,1],
$$

and suppose both have horizontal extrema -a,a and vertical extrema 0,1. Centering the horizontal interval is a translation, not a symmetry assumption. Choose actual points

$$
P_R=(a,y_R)\in K,\qquad P_L=(-a,y_L)\in K,
\qquad 0\leq y_R,y_L\leq1.
$$

For 0<=t<=L=pi/2 write c=cos(t),s=sin(t),

$$
f=h_K(t),\quad g=h_K(t+L),\qquad
\bar f=h_{\bar K}(t),\quad\bar g=h_{\bar K}(t+L).
$$

Use a superscript rho for reflection in y=1/2, so h^rho(t)=h(-t)+sin(t). Define nonnegative support increments

$$
u=\bar f-f,\quad v=\bar g-g,
\qquad u^\rho=\bar f^\rho-f^\rho,\quad
v^\rho=\bar g^\rho-g^\rho.
$$

**Lemma AB1 (paired anchor bounds).** For every t in [0,L],

$$
\begin{aligned}
0\leq u(t)&\leq(1-y_R)\sin t,&
0\leq u^\rho(t)&\leq y_R\sin t,\\
0\leq v(t)&\leq(1-y_L)\cos t,&
0\leq v^\rho(t)&\leq y_L\cos t.
\end{aligned}
\tag{AB.1}
$$

Consequently

$$
\boxed{u+u^\rho\leq\sin t,\qquad v+v^\rho\leq\cos t.}
\tag{AB.2}
$$

**Proof.** The right exposed point supplies f>=a c+y_R s. Rectangle containment gives bar f<=a c+s. Their difference proves the first bound. The reflected right point is (a,1-y_R), giving f^rho>=a c+(1-y_R)s and the reflected inequality. For the other quarter, scalar product with (-s,c) at P_L gives g>=a s+y_L c, while bar g<=a s+c. Reflect that same point to obtain the last inequality. Nonnegativity is inclusion. QED.

The heights y_R,y_L are fixed across all angles in this argument. They need not equal 1/2, need not equal each other, and no reflected-pair motion is assumed. If an extremal face has several points, any one chosen point gives valid bounds.

The least curvature majorant GM2 has the required nesting and the same axis supports, so its actual increments obey AB.1. The estimate also applies to any other nested same-axis comparison, whether or not it is curvature dominated. All increments vanish at the appropriate endpoints because the axis supports agree.

## 2. A reduced pointwise maximization

For a real coefficient A, a nonnegative number s, and nonnegative u,w with u+w<=s,

$$
A(u+w)+\frac12(u^2+w^2)
\leq\left(As+\frac12s^2\right)_+.
\tag{AB.3}
$$

Here x_+=max(x,0). To prove it, put z=u+w. Since u^2+w^2<=z^2, the left side is at most Az+z^2/2. This convex quadratic on [0,s] attains its maximum at an endpoint, where its values are zero and As+s^2/2. No assumption on the sign of A is needed.

This inequality explains why assigning an independent full-height allowance to each reflected increment overestimates adverse work. It is one shared budget, not two.

## 3. A candidate comparison without the rejected derivative charge

For a normalized profile h and four nonnegative increments define the expression

$$
\mathcal J_0(h;\mathbf u)
=\widetilde{\mathcal Q}(h)
-\sum_{\text{two halves}}\int_0^L
[(1-q_+)u+(1+p_-)v]dt,
\tag{AB.4}
$$

where p=f'-g+1, q=g'+f-1, p_-=min(p,0), q_+=max(q,0). Unlike AS.1, this expression does not subtract the whole derivative energy of a face-moving repair. It should not be calibrated on arbitrary unbounded increments; the geometric budget AB.2 is relevant.

For actual wide common hulls, one possible sufficient route would be the two separate statements

$$
|S|\leq\mathcal J_0(h_{R(K)};h_{R(K)}-h_K),
\qquad
\mathcal J_0(h;\mathbf u)\leq M
\text{ on a domain containing those actual repairs}.
\tag{AB.5}
$$

**Neither inequality in AB.5 is asserted or proved in this note.** In particular, omitting a term that caused a counterexample does not establish the first inequality. Actual niche clipping, partial motion endpoints, and the ordinary area of the old body must still be accounted for. The anchor lemma supplies a concrete constraint for testing this route; it is not a new maximizer theorem.

## 4. How this differs from previous corrections

AC1 and AS1 allowed arbitrary nonnegative H^1_0 increments and used their derivative energy to control adverse contact work. SAT1/SAC2 show that a universal geometric inequality using that charge is too strong. AB.1 is information supplied by the original hull that those enlarged function spaces discarded. It may permit a different analytic budget, but only after a genuine ordinary-area comparison is established or its failure is exhibited.

All results in Sections 1–2 are elementary written proofs. This note has no numerical premise and uses no CI or Lean/Lake compilation. The proposed comparison is retained as an explicit test, not relabelled as proof progress toward unrestricted closure.
