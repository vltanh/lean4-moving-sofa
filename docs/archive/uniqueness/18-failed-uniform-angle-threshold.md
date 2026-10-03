# 18. Negative result: the smaller extent threshold cannot be used at every angle

Date: 2026-10-02. Exact pen-and-paper counterexample to a proposed simplification of the proof, not a counterexample to sofa uniqueness.

In the smaller-angle reduction, put T=tan(omega), d equal to the excess of the rightmost cap extent over c=sec(omega)-tan(omega), and

    r_y=1-d/T,   g=sqrt(1-r_y^2).

The two geometric inequalities required by the triangle-cut argument are

    d sin(omega)>1,   g>2 cos(omega).

It is tempting to use the smaller threshold d_0=11/10 for the entire range omega>=arcsec(11/5), instead of the two thresholds in note 14. That simplification is false.

Take omega=arcsec(11/5) and d=11/10. Then T=4 sqrt(6)/5 and 0<d<T, so r_y is in (0,1) and g is well defined. First,

    (d sin(omega))^2 = (121/100)(96/121)=24/25<1.

Thus the first required strict inequality already fails.

The second fails as well. Since all denominators are positive, g^2>4 cos(omega)^2 would be equivalent to

    q(T)=220T^3-521T^2+220T-121>0.

At the stated value,

    q(T)=(21296 sqrt(6)-53041)/25<0,

because

    53041^2-6*21296^2=92229985>0.

Hence g<2 cos(omega). Neither failure is a rounding issue.

This shows that the area truncation estimate alone, even if it supplies d>11/10, cannot justify the angular width step at the lower end of the interval. A larger threshold there, or a different geometric argument, is genuinely needed. Note 19 proves the two-threshold estimates using positive-coefficient polynomials, without the original trigonometric convexity/numerical checks.

No body of maximal sofa area is constructed here. The point is to exclude a logically invalid simplification before assembling the final proof.
