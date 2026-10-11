# Prior work

[Back to the README](../README.md)

From a search on 10 October 2026 of arXiv, journal and publisher pages, GitHub repositories and issue trackers,
and press coverage. The ambidextrous variant, in which a shape must turn both left and right, has its own page in
[lean4-ambidextrous-sofa](https://github.com/vltanh/lean4-ambidextrous-sofa/blob/main/docs/prior-work.md).

## The moving sofa problem

- Leo Moser posed the problem in 1966 (*SIAM Review* 8, Problem 66-11,
  [doi:10.1137/1008074](https://doi.org/10.1137/1008074)): the largest area of a connected planar shape that can be
  moved around the right-angled corner of a hallway of unit width.
- Hammersley set it as an exercise in 1968 (*Bulletin of the Institute of Mathematics and its Applications* 4,
  66–85, Appendix IV, Problem 8, [scan](https://archive.org/details/hammersley1968)): show that the area is less than
  $2\sqrt2 \approx 2.83$, and that a shape of area $\pi/2 + 2/\pi \approx 2.2074$ (two quarter-discs separated by a
  $4/\pi \times 1$ block, with a half-disc of radius $2/\pi$ removed) can be moved. It ends with the question "Is
  this the largest possible value for A?".
  - *SIAM Review* printed follow-ups by Goldberg (1969, [doi:10.1137/1011013](https://doi.org/10.1137/1011013))
    and Sebastian (1970, [doi:10.1137/1012114](https://doi.org/10.1137/1012114)); Howden searched by computer for
    the largest rectangle of a given width that turns the corner (*The Computer Journal* 11, 1968,
    [doi:10.1093/comjnl/11.3.299](https://doi.org/10.1093/comjnl/11.3.299)).
  - Shapes of slightly larger area than Hammersley's are recorded by Guy (*American Mathematical Monthly* 84,
    1977, [doi:10.1080/00029890.1977.11994487](https://doi.org/10.1080/00029890.1977.11994487)).
- Gerver (*Geometriae Dedicata* 42, 1992) found a sofa of area $2.21953\ldots$, bounded by 18 curves and segments,
  and conjectured that it is optimal. Gerver's Theorem 1 states a balance condition that a maximum sofa satisfies,
  and Gerver's Theorem 2 that this sofa satisfies it.
  - Gerver also proved that the motion of a maximum sofa can be taken to rotate it monotonically, through an
    angle between $\pi/3$ and $\pi/2$ (as cited by Kallus and Romik, §1).
  - Baek notes that Gerver's argument does not address the connectedness of the sofa, and proves the balance
    condition again (§1.1 of his paper).
  - Romik recounts, after Stewart, that B. F. Logan found the same shape in 1976 without publishing it.
- The problem appears in Croft, Falconer and Guy, *Unsolved Problems in Geometry* (Springer, 1991, pp. 171–172),
  in Finch, *Mathematical Constants* (Cambridge, 2003, §8.12), and in Stewart, *Another Fine Math You've Got Me
  Into…* (Freeman, 1992; Dover, 2004).
- Romik (*Experimental Mathematics* 27, 2018) derived Gerver's sofa from a system of differential
  equations that balance the sides of the sofa, and solved it explicitly; the Challenge's definition
  of Gerver's sofa follows this description.
- Kallus and Romik (*Advances in Mathematics* 340, 2018) proved, with a computer-assisted method,
  that the maximum is at most $2.37$, and that a maximum sofa rotates by at least $\arcsin(84/85) \approx 81.2°$.
  - The method maximizes, over the positions of the hallway at finitely many angles, the area of a connected
    piece of the intersection of the rotated hallways, by a geometric branch and bound. Their program,
    [SofaBounds](https://github.com/ykallus/SofaBounds) (C++, CGAL's Nef polygons, exact rational arithmetic,
    angles entered as Pythagorean triples), took 480 hours on one core for the bound $2.37$.
  - The certificate is the run itself: the paper names the program and four parameter files. In 2019 a user
    reported that the a priori box of positions was too small in the case of final angle $\pi/2$, the case of
    the bound $2.37$ ([issue #1](https://github.com/ykallus/SofaBounds/issues/1)); the code was corrected
    ([pull request #2](https://github.com/ykallus/SofaBounds/pull/2)), and the thread records no later run of
    that computation. The rotation bound does not use that case, and Baek's theorem implies the bound $2.37$.
- Baek's preprint *Optimality of Gerver's Sofa* (arXiv:2411.19826, 2024, 119 pages) proves that
  Gerver's sofa is optimal. This repository formalizes version 1 of it, still the only one.
  - On 10 October 2026 it is a preprint with no journal reference; the forthcoming papers of the *Annals of
    Mathematics* do not include it, and press reports of January 2026 said that it was under review there
    ([Korea Herald](https://www.koreaherald.com/article/10648326)).
  - Its proof needs no computer "except for numerical computations that can be done on a scientific
    calculator"; an earlier, computer-assisted version used Baek's program
    [sofa-designer](https://github.com/jcpaik/sofa-designer), and a talk abstract of February 2024 announced a
    computer-assisted bound of $2.32$ ([abstract](https://www.mathematics.pitt.edu/content/moving-sofa-problem)),
    with no paper found.
- Concurrent work, in 2024: Baek's [conditional upper bound](https://arxiv.org/abs/2406.10725)
  1 + π²/8 = 2.2337… for sofas with the injectivity condition, which the paper supersedes; Leng, Bi,
  Cha, Pinilla and Thiyagalingam's [numerical evidence](https://arxiv.org/abs/2407.11106) (*Symmetry* 16, 1388,
  [doi:10.3390/sym16101388](https://doi.org/10.3390/sym16101388)), by neural networks, that Gerver's sofa is the
  global maximum, with an improvement of the five-angle bound of Kallus and Romik from 2.37 to 2.3337, computed in
  double precision and with no certificate; and Deng's
  [calculus of variations approach](https://arxiv.org/abs/2407.02587), which recovers Gerver's sofa
  as a solution of the Euler–Lagrange equations under convexity assumptions.
- Other numerical work:
  - Batsch reproduced Gerver's sofa numerically (*Symmetry* 14, 2022, 1409,
    [doi:10.3390/sym14071409](https://doi.org/10.3390/sym14071409)).
  - AlphaEvolve (Georgiev, Gómez-Serrano, Tao and Wagner, [arXiv:2511.02864](https://arxiv.org/abs/2511.02864),
    Problems 6.62 to 6.64) found Gerver's sofa within 0.02%, by evaluation code whose values its
    [notebook](https://github.com/google-deepmind/alphaevolve_repository_of_problems/blob/main/experiments/the_2d_moving_sofa/the_2d_moving_sofa.ipynb)
    says are not rigorous lower bounds, and gave the rigorous lower bound 1.81 for the volume of a sofa in a
    three-dimensional corridor that turns in two perpendicular planes.
- Variants: He computed locally optimal areas for corners of angle 15° to 150°
  ([arXiv:2608.11206](https://arxiv.org/abs/2608.11206), 2026), and Mushkarov and Nikolov treat rectangles and
  boxes in hallways of unequal widths ([arXiv:2604.01174](https://arxiv.org/abs/2604.01174), 2026).
- Later work is in the report's [What's next](../baek/REPORT.md#10-whats-next).
- That Gerver's sofa is the only optimal sofa, up to rigid motions, is not proved in Baek's paper.
  Google DeepMind's [formal-conjectures](https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/Wikipedia/MovingSofa.lean)
  states it as `volume_eq_sofaConstant_iff_congruent_gerversSofa`, in its category `research open`;
  this repository proves that statement. We know of no earlier proof, but have not searched the
  literature systematically.

## Formalizations of the same proof

Two Lean 4 formalizations of Baek's proof appeared shortly before this one:
[deancureton/MovingSofa](https://github.com/deancureton/MovingSofa), written by AI agents directed by Dean Cureton, and
[RuifengCao/sofa-formal](https://github.com/RuifengCao/sofa-formal), written with Claude under the direction of Ruifeng Cao. Both prove the statement of
Google DeepMind's
[formal-conjectures](https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/Wikipedia/MovingSofa.lean),
`sofaConstant = volume gerversSofa`, and neither proves the uniqueness of the optimal sofa.
[Formalizations of Baek's proof](../baek/formalizations.md) compares the three: what each proves, their
definitions, how closely each follows the paper, how each treats Gerver's sofa, the errors each found
in the paper, how each is checked, and how each was made.

Like the earlier two, this repository proves the facts about Gerver's sofa that the paper states
without proof or takes from Gerver and Romik (Theorems 6.1.2, 8.4.1 and 8.4.2). For the niche,
Theorem 8.4.1(2), the proof reduces a two-parameter family of inequalities to one-variable
inequalities verified by interval arithmetic.

- Trela's [GerverSofaLean](https://github.com/dawidmtrela-dotcom/GerverSofaLean) (September 2026) proves that
  Gerver's four constants exist and are unique, with 8,713 interval obligations checked by the kernel through
  the LeanCert library, and that Gerver's sofa is a moving sofa; Cureton's formalization builds on it.
- Cureton's has about 66,000 lines, written in about four days by OpenAI Codex and Claude Code; its README
  reports that it found 11 small errors or gaps and 33 misprints in the paper, none of which breaks the main
  theorem, and that it proves the area of Gerver's sofa to be at least 11/5 only. Lean Pool, an archive of
  formalized mathematics, imported it on 29 September 2026.
- Cao's also proves Hammersley's bounds $\pi/2 + 2/\pi \le$ `sofaConstant` $\le 2\sqrt2$, and replaces the
  paper's uses of Green's theorem and of the Jordan curve theorem by explicit area computations.
- formal-conjectures added its statement in March 2026 and corrected it twice: the uniqueness was restated up to
  a rigid motion ([pull request #4852](https://github.com/google-deepmind/formal-conjectures/pull/4852)) and the
  order of translation and rotation in a motion was fixed
  ([pull request #5827](https://github.com/google-deepmind/formal-conjectures/pull/5827)). On 10 October 2026 it
  marks `sofaConstant = volume gerversSofa` as solved, linking Cureton's and Cao's proofs
  ([#6440](https://github.com/google-deepmind/formal-conjectures/pull/6440),
  [#6526](https://github.com/google-deepmind/formal-conjectures/pull/6526)), and the uniqueness as open; a pull
  request that links this repository and marks the uniqueness solved is open
  ([#6808](https://github.com/google-deepmind/formal-conjectures/pull/6808)).
- Smaller repositories state the problem or prove that simple shapes are moving sofas
  ([abobreshov/moving-sofa-lean](https://github.com/abobreshov/moving-sofa-lean)). The search found no
  formalization of the problem in Isabelle, Coq/Rocq or HOL.

## Computer-assisted bounds for related problems

- Lebesgue's universal covering problem: Baez, Bagdasaryan and Gibbs lowered the upper bound to 0.8441153 by a
  double-precision computation that Egan rechecked in 2000-digit arithmetic (*Journal of Computational
  Geometry* 6, 2015, [arXiv:1502.01251](https://arxiv.org/abs/1502.01251)); Xie proved the lower bound 0.833 for
  convex covers in outward-rounded interval arithmetic ([arXiv:2606.04458](https://arxiv.org/abs/2606.04458),
  2026).
- Moser's worm problem: Keller proved $0.239 \le \alpha \le 0.24633\ldots$ for convex covers of unit arcs
  ([arXiv:2609.21968](https://arxiv.org/abs/2609.21968), 2026), with rational certificates exported as Lean
  declarations and checked by the kernel ([repository](https://github.com/ethan-keller/moser-worm-improved-bounds)).
- Packings of 31 to 33 equal circles in a square were proved optimal by interval branch and bound (Markót,
  *Journal of Global Optimization* 81, 2021).

## References

- L. Moser, Problem 66-11, Moving furniture through a hallway, *SIAM Review* 8 (1966), 381.
- J. M. Hammersley, On the enfeeblement of mathematical skills by "Modern Mathematics" and by similar soft
  intellectual trash in schools and universities, *Bulletin of the Institute of Mathematics and its Applications*
  4 (1968), 66–85.
- J. L. Gerver, [On moving a sofa around a corner](https://doi.org/10.1007/BF02414066), *Geometriae Dedicata* 42 (1992), 267–283.
- D. Romik, [Differential equations and exact solutions in the moving sofa problem](https://doi.org/10.1080/10586458.2016.1270858), *Experimental Mathematics* 27 (2018), 316–330.
- Y. Kallus, D. Romik, [Improved upper bounds in the moving sofa problem](https://doi.org/10.1016/j.aim.2018.10.022), *Advances in Mathematics* 340 (2018), 960–982.
- J. Baek, [Optimality of Gerver's sofa](https://arxiv.org/abs/2411.19826), arXiv:2411.19826v1 (2024).
- K. Leng, J. Bi, J. Cha, S. Pinilla, J. Thiyagalingam, [Deep learning evidence for global optimality of
  Gerver's sofa](https://doi.org/10.3390/sym16101388), *Symmetry* 16 (2024), 1388.
- B. Georgiev, J. Gómez-Serrano, T. Tao, A. Z. Wagner, [Mathematical exploration and discovery at
  scale](https://arxiv.org/abs/2511.02864), arXiv:2511.02864 (2025).
- R. Schneider, *Convex Bodies: The Brunn–Minkowski Theory*, 2nd edition, Cambridge University Press, 2013.
