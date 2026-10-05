# The terminal strip pays for a missing final rotation interval

**Status:** written analytic proof, not Lean-checked or independently reviewed. This is the local angle estimate needed to pass from arbitrary sofas to the right-angle cap theorem. No maximizing-cap or injectivity assumption is imposed.

Use K0,G,a,b,x_-,H from 06-local-upper-bound.md, and put v=pi/2. All caps below are normalized by h_K(v)=1 and floor y=0, and sufficiently close to K0. Let R be a fixed radius containing this whole cap neighborhood; set Cw=2R+1.

## Proposition

There are c>0 and sufficiently small neighborhoods of K0 and v such that the following holds. Let omega=v-alpha, 0<=alpha sufficiently small, and let S be a measurable subset of K satisfying

    S subset L_K(t)                         for 0<=t<=omega,
    p.u_omega >= h_K(omega)-1               for every p in S. (1)

The second condition is the lower wall of the terminal unit strip; its upper wall is automatic from S subset K. Then

    |S| <= A(K)-c alpha.                                      (2)

Let U=K minus N(K), epsilon=M-|S|. The local cap theorem consequently implies

    alpha <= epsilon/c,
    M-A(K) <= epsilon,
    |S minus U| <= epsilon,
    |U minus S| <= 2 epsilon.                                (3)

S need not be a right-angle sofa, U need not be asserted connected, and no extension of the motion of S is assumed.

## 1. A fixed floor region lost to the terminal strip

Choose once and for all a nontrivial closed interval I=[l,r] strictly inside the left wing floor interval (x_-,a). Put d=a-r>0, length(I)=ell_I, and c0=ell_I*d/4.

For every small eta>0, Section 2 of 06-local-upper-bound.md supplies a cap neighborhood in which all top-face points of K have abscissa at least a-eta, every niche is confined to [a-eta,b+eta], and I x [0,h_I] is contained in U for some fixed h_I>0, provided eta<d/4.

Take a top-face point q=(q_x,1) of K. For alpha>0,

    W=(h_K(omega)-1)/cos(omega)
      >= q_x+(sin(omega)-1)/cos(omega)
       = q_x-tan(alpha/2).

For alpha small enough that tan(alpha/2)<=eta, this gives W>=a-2eta. Therefore, for x in I and eta<=d/4, the terminal condition (1) requires

    y >= tan(alpha)(W-x) >= alpha*d/2.

The rectangle

    F_alpha=I x [0,alpha*d/4]

lies in U when alpha*d/4<=h_I, but is disjoint from S. Its area is exactly c0*alpha. No estimate of d_H(S,G) in terms of epsilon has been used.

## 2. The omitted wedges have only a small linear area cost

Define

    N_omega={y>=0} intersect union_{0<t<omega} Q_K^-(t),
    V=K minus N_omega,
    E=V minus U=K intersect (N(K) minus N_omega).

Then S subset V and F_alpha subset U subset V.

For omega<=t<v write z=v-t, so 0<z<=alpha. The support is R-Lipschitz, h_K(v)=1, and |h_K|<=R. Thus

    (x_K(t))_y
      =(h_K(t)-1)sin(t)+(h_K(t+v)-1)cos(t)
      <= R*z+(R+1)*z = Cw*z <= Cw*alpha.                    (4)

A forbidden wedge above the floor lies below its inner corner. Consequently every point of E has height at most Cw*alpha. By the niche localization lemma it also has x-coordinate in [a-eta,b+eta].

For the same fixed eta, the finite-cover property (3) of 06-local-upper-bound.md supplies h_eta>0 and t_eta<v such that

    [a+eta,b-eta] x [0,h_eta] subset N_omega

for all nearby K once omega>t_eta. Choose alpha also with Cw*alpha<=h_eta. Any point of E must therefore lie in the two horizontal endpoint windows

    [a-eta,a+eta] union [b-eta,b+eta].

Their combined width is 4eta, so

    |E| <= 4eta*Cw*alpha.                                  (5)

The order of choices matters: R,I,d,c0 are fixed first, then eta is chosen small, then the cap neighborhood and angular threshold. We do not ask eta to shrink with epsilon and do not assume a rate for the qualitative neighborhood theorem.

## 3. Compare the two costs

Choose eta so small that 4eta*Cw<=c0/2, in addition to the preceding geometric restrictions, and put c=c0/2. Since V is the disjoint union of U and E, while F_alpha lies in U and is disjoint from S,

    |S| <= |V|-|F_alpha|
         = A(K)+|E|-c0*alpha
         <= A(K)-c*alpha.

Here |U|=A(K) was proved locally in 06-local-upper-bound.md; it is not assumed for arbitrary caps. This proves (2). For alpha=0, the omitted set E is empty and (2) is simply S subset U.

Since A(K)<=M, (2) gives c*alpha<=epsilon and M-A(K)<=epsilon. Also (5) gives |S minus U|<=|E|<=c*alpha<=epsilon, whence

    |U minus S|=A(K)-|S|+|S minus U|<=2epsilon.

This proves (3). Notice in particular that the loss of final angle is O(epsilon), stronger than the square-root shape rate.

## 4. An approximate full-angle constraint for the original S

This elementary estimate is needed because S is not claimed to be contained in U. For p in S set

    m_K(t,p)=max(p.u_t-h_K(t)+1,
                 p.v_t-h_K(t+v)+1).

For |p|<=R, each entry and hence their maximum is 2R-Lipschitz in t. The known motion gives m_K(t,p)>=0 for t<=omega, including omega. Therefore

    m_K(t,p)>=-2R*alpha                  for every 0<=t<=v. (6)

If delta=d_H(K,K0), uniform support control gives

    m_K0(t,p)>=-(delta+2R*alpha).                            (7)

This is an approximate hallway inequality, not a claim of full-angle feasibility. Together with the reference roof geometry, it controls the directed distance from S to G; the other directed distance follows from the missing-area bound in (3).

## Rejected shortcut

It would be incorrect to infer that S can complete the final rotation merely because it fits the strips at omega and v. Width can exceed 1 between two unit-width directions. The proof above does not extend S's motion. It compares the area of the omitted wedges with a definite region excluded by the existing terminal strip, and uses (6) only as an inequality.
