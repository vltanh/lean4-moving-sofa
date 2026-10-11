"""Exact-integer scalar bounds for an explicit unrestricted optimality cutoff.

This checks continuous parameter intervals, not sampled values. It relies on
parameter_certificate.Interval and width_certificate.sinc. Mathematical use
of its bounds is in EXPLICIT_GLOBAL_CUTOFF.md; this is not a Lean proof.
"""
from __future__ import annotations

from fractions import Fraction
import argparse
import json

from parameter_certificate import BITS, SCALE, Interval, sin_cos
from width_certificate import sinc


def quantities(e: Interval) -> dict[str, Interval]:
    """Removable-endpoint formulas, valid including epsilon=0."""
    if e.lo < 0 or e.hi > Interval.rational(1, 10).hi:
        raise ValueError("epsilon interval must be contained in [0,1/10]")
    e2 = e.square()
    sc = sinc(e)
    _, d = sin_cos(e)
    se = sinc(e/2)/2  # sin(e/2)/e
    _, c = sin_cos(e/2)
    m = 2-d
    eta = (m/(2+d)).sqrt()
    kappa = (e2+3/sc.square()).sqrt()  # epsilon times the frequency
    sk, ck = sin_cos(kappa/2)
    D = ck+eta*sk
    re = se*eta/c  # r/epsilon
    for positive in (sc, se, c, d, m, sk, ck, D):
        if positive.lo <= 0:
            raise ArithmeticError("unresolved positive denominator or trigonometric sign")
    T = eta*sk/ck
    eV = e2/m+(1+2*d)/(4*sc)+3*d.square()*eta*sk/(2*sc*m.square()*D)
    endpoint = -(sc/d)*((2*d-1)*sk-eta*(2*d+1)*ck)/((1+d)*sk+eta*(1-d)*ck)
    c1 = -2*(T*d+T+d-2)/((T+1)*m)
    c2 = (2*T*d+3*T+2*d-3)/(4*(T+1))
    eB = -d/(2*m*se*D)
    eA = (c/2+re*eB*sk)/se
    ell = eA+d*kappa*(-sk+eta*ck)/(2*m*D)
    dj = c*sk+e2*re*se*ck
    jy = (se*(sk-eta*ck)+re)/dj
    wx = -c/(2*se)+(1+eta*sk/c)/(2*se*D)
    jx_monotone = (kappa+e2*re)*ck*c-(1+re*kappa)*sk*e2*se
    wy_monotone = (1+re*kappa)*ck*c-(kappa+e2*re)*sk*se
    return dict(eV=eV, ell=ell, endpoint=endpoint,
                width_slope=(c1+2*c2)/sc,
                width_half_slope=(c1+Interval.rational(3, 2)*c2)/sc,
                narrow_gap=eV-1/sinc(e/2),
                jacobi_y=jy, width_x=wx,
                jacobi_x_monotone=jx_monotone, width_y_monotone=wy_monotone)


# Strict rational bounds used in the proof, not approximate display values.
BOUNDS = {
    "eV": (Fraction(27, 20), Fraction(34, 25)),
    "ell": (Fraction(143, 500), Fraction(1, 3)),
    "endpoint": (Fraction(59, 250), Fraction(1, 4)),
    "width_slope": (Fraction(1, 10), Fraction(1)),
    "width_half_slope": (Fraction(1, 10), Fraction(1)),
    "narrow_gap": (Fraction(1, 3), Fraction(1, 2)),
    "jacobi_y": (Fraction(0), Fraction(16, 25)),
    "width_x": (Fraction(0), Fraction(7, 20)),
    "jacobi_x_monotone": (Fraction(0), Fraction(2)),
    "width_y_monotone": (Fraction(0), Fraction(1)),
}


def prove_scalars(cells: int = 256) -> dict:
    if isinstance(cells, bool) or not isinstance(cells, int) or cells < 1:
        raise ValueError("cells must be a positive integer")
    minima = {k: None for k in BOUNDS}
    maxima = {k: None for k in BOUNDS}
    margins = []
    for j in range(cells):
        left = Interval.rational(j, 10*cells)
        right = Interval.rational(j+1, 10*cells)
        values = quantities(Interval(left.lo, right.hi))
        row = {}
        for name, (lower, upper) in BOUNDS.items():
            value = values[name]
            lo = value.lo*lower.denominator-lower.numerator*SCALE
            hi = upper.numerator*SCALE-value.hi*upper.denominator
            if min(lo, hi) <= 0:
                raise ArithmeticError(f"inconclusive cell {j} for {name}: margins {lo}, {hi}")
            row[name] = [lo, hi]
            minima[name] = value.lo if minima[name] is None else min(minima[name], value.lo)
            maxima[name] = value.hi if maxima[name] is None else max(maxima[name], value.hi)
        margins.append(row)
    return dict(format="explicit-cutoff-scalars-v1", status="all interval bounds proved",
                epsilon_interval=["0", "1/10"], cells=cells, bits=BITS, denominator=SCALE,
                rational_bounds={k: [str(a), str(b)] for k, (a, b) in BOUNDS.items()},
                enclosure_numerators={k: [minima[k], maxima[k]] for k in BOUNDS},
                cell_margins=margins,
                trust="Exact Python integer arithmetic; inherited Taylor remainders; no floating point")


def prove_propagation(emax: Fraction = Fraction(1, 19)) -> dict:
    """All remaining sufficient inequalities use exact rational arithmetic."""
    emax = Fraction(emax)
    if not 0 < emax <= Fraction(1, 10):
        raise ValueError("cutoff must lie in (0,1/10]")
    F = Fraction
    aa, bb, rr = F(35, 96), F(43, 24), F(1, 3)
    det = aa*bb-rr*rr
    zx = (bb+2*rr*F(1, 200)+aa*F(1, 200)**2)/(2*det)
    zy = (bb/4+rr+aa)/(2*det)
    bx, by = F(5, 2), F(17, 10)
    trace_x = bx*bx-zx-F(250, 59)
    trace_y = by*by-zy-F(16, 25)**2*F(250, 59)
    nmax = 3*emax/4
    ex = F(35, 24)*nmax+F(119, 100)*nmax*nmax
    ey = F(119, 120)*nmax+F(17, 10)*nmax*nmax
    W, H = F(143, 500)-2*ex, 1-2*ey
    dmax = F(17, 50)*nmax*nmax
    am, bm = F(3, 4), F(99, 100)
    checks = {
        "matrix_determinant": det,
        "trace_x_slack": trace_x,
        "trace_y_slack": trace_y,
        "sqrt_deficit_slack": F(7, 12)**2-F(17, 50),
        "sqrt_triangle_slack": F(101, 200)**2-am*F(17, 50),
        "normal_mismatch_slack": F(3, 4)*(1-F(3, 40)**2/6)-F(20, 27),
        "sinc_mismatch_slack": 1-F(3, 40)**2/6-F(999, 1000),
        "cos_mismatch_slack": 1-F(3, 40)**2/2-bm,
        "reverse_class_area_slack": F(27, 40)/emax-3,
        "small_deficit_slack": F(1, 3)-dmax,
        "core_width": W,
        "core_height": H,
        "triangle_horizontal_slack": F(999, 1000)*W*W/2-F(17, 50)*nmax*emax,
        "triangle_vertical_slack": bm*H*H/(2*am)-dmax,
        "alignment_contradiction_slack": F(143, 500)*F(999, 1000)/emax-F(6217, 1200)-F(1137, 200)*nmax,
    }
    if any(value <= 0 for value in checks.values()):
        failed = {k: str(v) for k, v in checks.items() if v <= 0}
        raise ArithmeticError(f"sufficient estimates do not certify this cutoff: {failed}")
    return dict(format="explicit-cutoff-propagation-v1", status="all rational inequalities positive",
                epsilon_cutoff=str(emax), trace_coefficients_squared=[str(zx), str(zy)],
                path_constants=[str(bx), str(by)], minimum_core_size=[str(W), str(H)],
                rational_slacks={k: str(v) for k, v in checks.items()})


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--cells", type=int, default=256)
    parser.add_argument("--cutoff", default="1/19", help="epsilon cutoff as an exact rational")
    parser.add_argument("--output")
    args = parser.parse_args()
    result = dict(scalars=prove_scalars(args.cells), propagation=prove_propagation(Fraction(args.cutoff)))
    text = json.dumps(result, indent=2)+"\n"
    if args.output:
        from pathlib import Path
        Path(args.output).write_text(text)
    else:
        print(text, end="")
