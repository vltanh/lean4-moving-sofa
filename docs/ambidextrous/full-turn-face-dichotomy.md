# Remaining full-turn face configurations and a failed approximation shortcut

**Scope.** Combined with FAS1, the elementary floor tests leave only two kinds of full-turn counterexample: a point face, or two nondegenerate faces in opposite unit end intervals. This is a case reduction, not a proof that the remaining cases have area at most M. It also rules out a tempting limiting shortcut for aligned point faces. Labels FD are local.

The geometry uses only the retained-point floor exclusions already proved in OT3/LF. The value consequence invokes the new FAS1 theorem and thus its stated weighted and analytic-width dependencies. No numerical calculation is used.

## 1. Exact interval classification

Let K be the unit-span common hull of a compact connected body S with both full conventional turns. Suppose W=r-l>2. Write the top and bottom exposed face intervals as [a,b] and [c,d], and put

$$u=l+1,\qquad v=r-1,\qquad u<v.$$

Retained face endpoints and the initial/final hallway positions give

$$c,d\notin(a,v)\cup(u,b),\qquad
 a,b\notin(c,v)\cup(u,d).\tag{FD.1}$$

An interval with reversed or equal endpoints in these forbidden expressions is empty. These tests do not require any curvature bound or positive-face assumption.

**Lemma FD1.** If both faces are nondegenerate, exactly one of the following holds:

1. They are identical and contain [u,v].
2. The top face is contained in [l,u], and the bottom face is contained in [v,r].
3. The bottom face is contained in [l,u], and the top face is contained in [v,r].

**Proof.** First suppose a=c. If a>=v, then a=c belongs to (u,d), since d>c>=v>u, contradicting FD.1. Hence a<v. Since b>a and d>a, the initial exclusions force b,d>=v. The final exclusions applied to a then imply a<=u. If b<d, b lies in (u,d), and if d<b, d lies in (u,b). Both contradict FD.1. Thus b=d, and the common face contains [u,v].

Suppose a<c. The initial exclusion of c from (a,v) gives c>=v, so d>c>u. Since a<d and a is excluded from (u,d), one has a<=u. The same exclusion for b says either b<=u or b>=d. In the latter case, the exclusion of d from (u,b) forces b=d, but then c lies in (u,b), a contradiction. Thus b<=u. This is case 2. Interchanging the faces proves case 3 when c<a. The cases are disjoint since u<v and both face lengths are positive. QED.

This proof supplies the exact alternatives; it does not infer that both faces are crowded at the same end from a one-sided initial test.

## 2. The ordinary-area consequence after FAS1

For a putative body with |S|>M, the analytic width bound already gives W>2. If both conventional turns are full and both faces are nondegenerate, Lemma FD1 applies. Case 1 is now entirely covered by FAS1, including common face lengths below one.

**Corollary FD2.** Any full-turn body with area greater than M must have either

- at least one horizontal hull face consisting of a single point; or
- two nondegenerate horizontal faces contained in opposite unit end intervals [l,l+1] and [r-1,r].

In the second alternative both face lengths are at most one. In particular no shifted but overlapping positive-face configuration remains, and the whole aligned positive-face class is excluded. Partial-turn bodies are not classified by the final-angle half of FD.1 and remain a separate coverage obligation.

## 3. Why an aligned point face cannot be handled by the obvious limit

It is tempting to add a small horizontal segment to an aligned point-face hull, use the positive-face theorem, and pass to the limit. The necessary floor tests prevent the required approximation within the same full-turn, unit-span class.

**Proposition FD3.** Suppose K_j are actual common hulls of full-turn bodies in the strip 0<=y<=1, each of vertical span one, with identical nondegenerate top and bottom faces. Suppose K_j converge in Hausdorff distance to K and their widths converge to W>2. Then both horizontal faces of K contain a common interval of length at least W-2. In particular they cannot be single points.

**Proof.** By FD1 their common face intervals [a_j,b_j] satisfy b_j-a_j>=W_j-2. Boundedness and a subsequence give a_j->a, b_j->b with b-a>=W-2>0. The points (a_j,0),(b_j,0),(a_j,1),(b_j,1) belong to K_j. Their limits belong to K and lie on its two horizontal supporting lines. Convexity supplies the full common interval at both heights. QED.

For a point-face K with W>2, adding a horizontal segment of length epsilon at fixed height creates aligned face length epsilon and width W+epsilon. FD1 would demand epsilon>=W+epsilon-2, or W<=2. Thus such an addition cannot give an actual full-turn feasible hull in the desired class, however small epsilon is.

Uniformly shrinking first and adding a horizontal segment does not repair the inference automatically. The shrink reduces the vertical span below one, whereas FAS1 is a theorem in the unit-span normalization. Restoring the span requires a separately proved feasible operation. No anisotropic rescaling or motion-preserving Minkowski enlargement is silently used here.

This is a failure of a proposed approximation premise, not a counterexample to the reference optimality claim. It explains why the positive-face result does not already close the point-face case.

## 4. Remaining proof boundary

The exact remaining full-turn classes in FD2 still require a sharp ordinary-area bound or an area-improving operation at a maximizer. The known near-reference point-face examples cannot be discarded by a fixed positive area gap. General partial-turn coverage is also still open.

FAS1, the central-face criteria and the scaled width margin are pen-and-paper reductions, not a complete global covering. No computer-assisted search, CI, Lean/Lake compilation, dependency installation or manuscript build is used.
