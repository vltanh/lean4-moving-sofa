"""Short exact arithmetic checks for MW/AO/CG/SE/VE/WV, not an optimality proof.

Uses Python integers and Fraction only. The continuum cap reductions, area
admission, and external Gerver theorem are not verified by these checks.
Run under an external short wall-clock cap, e.g. timeout 5s python this_file.py.
"""
from __future__ import annotations
import argparse
from fractions import Fraction as Q
from hashlib import sha256
import json
from pathlib import Path
import platform
from time import perf_counter


def run() -> dict:
    start = perf_counter()
    names = []
    controls = []
    def check(name: str, condition: bool) -> None:
        if not condition:
            raise AssertionError(name)
        names.append(name)

    # The upper endpoints in the pinned source, respecting the sign of each
    # term in A+C+segment-x+B+D.
    gerver = sum(map(Q, ('0.7202', '1.334', '0.8069', '-0.6013', '-0.003', '-0.0369')))
    check('Gerver six-enclosure upper sum', gerver == Q(22199, 10000))
    t = Q(48, 35)
    check('positive square-root comparison side', gerver > t)
    chord_margin = t*t + 1 - 4*(gerver-t)**2
    check('strict top-length contradiction', chord_margin == Q(1471551, 1225000000) > 0)
    arm_margin = Q(17, 4) - (3*t/2)**2
    check('at least one arm below improved threshold', arm_margin == Q(89, 4900) > 0)
    check('improved threshold exceeds two', Q(17, 4) > 4)
    check('improved threshold below known 9/4 bound', Q(17, 4) < Q(9, 4)**2)
    check('guard energy threshold identity', Q(17, 4)-Q(1, 4) == 4)

    sin_lower = Q(1, 2)-Q(1, 2)**3/6
    one_minus_cos_lower = Q(1, 2)**2/2-Q(1, 2)**4/24
    check('sine Taylor lower polynomial', sin_lower == Q(23, 48))
    check('cosine Taylor lower polynomial', one_minus_cos_lower == Q(47, 384))
    height_margin = sin_lower + Q(3, 16)*one_minus_cos_lower-Q(1, 2)
    check('strict corner-height contradiction', height_margin == Q(13, 6144) > 0)
    check('endpoint p lower bound at one half', Q(1, 2)-Q(9, 4)/2 == -Q(5, 8))
    check('companion curvature bound', (1+Q(5, 8))/2 == Q(13, 16))
    check('excess-integral coarse bound', 2*Q(1, 4)*(Q(1, 2)-Q(2, 9)) == Q(5, 36))

    # Exact local identity, not an assertion that these samples are cap
    # trajectories or satisfy an entire boundary-value problem.
    energy_cases = 0
    for p in (Q(0), Q(1, 8), Q(1, 4), Q(1, 2)):
        for q in (Q(0), Q(1, 4), Q(3, 4), Q(5, 4)):
            for v in (Q(0), Q(1, 4), Q(1, 2)):
                pd, qd = -1-q, v-1+p
                derivative = 2*(p-Q(1, 2))*pd+2*(q+1)*qd
                expected = 2*(q+1)*(v-Q(1, 2))
                if derivative != expected or derivative > 0:
                    raise AssertionError('Energy identity sample')
                energy_cases += 1
    check('energy identity rational regressions', energy_cases == 48)

    # Exact unit-circle examples of the cut triangle; no trigonometric
    # floating-point values or numerical candidate data enter.
    triangle_cases = 0
    for half_tangent in (Q(1, 20), Q(1, 10), Q(3, 20), Q(1, 5), Q(1, 4), Q(1, 3)):
        r = half_tangent
        c, s = (1-r*r)/(1+r*r), 2*r/(1+r*r)
        d = 1/c-1
        x_tip = s*s/c
        if c*c+s*s != 1 or not 0 < d < x_tip:
            raise AssertionError('Triangle lies on cut edges')
        if d/x_tip != 1/(1+c):
            raise AssertionError('Relative cut position')
        area = c*d*d/s
        if area != (1-c)**2/(s*c) or area <= 0:
            raise AssertionError('Positive exact lost triangle')
        triangle_cases += 1
    check('reference-triangle rational regressions', triangle_cases == 6)

    # The physical flux is not ordinary arc length at a corner: both source
    # directions are retained, even when the finite boundary alternates.
    flux_cases = 0
    for r in (Q(1, 10), Q(1, 5), Q(1, 3), Q(1, 2)):
        c, sn = (1-r*r)/(1+r*r), 2*r/(1+r*r)
        for p0 in (-Q(1, 4), -Q(1, 2), -Q(3, 4)):
            for q0 in (Q(1, 4), Q(1, 2), Q(3, 4)):
                dx, dy = -p0*c+q0*sn, -p0*sn-q0*c
                if c*dx+sn*dy != -p0 or sn*dx-c*dy != q0:
                    raise AssertionError('Two-source corner flux')
                flux_cases += 1
        for density in (Q(0), Q(1, 4), Q(1, 2), Q(1)):
            dx, dy = (1-density)*c, (1-density)*sn
            if c*dx+sn*dy != 1-density or sn*dx-c*dy != 0:
                raise AssertionError('Single-wall tangency flux')
    check('corner flux decompositions', flux_cases == 36)
    check('tangent flux decompositions', True)
    energy2_cases = 0
    for x in (Q(1), Q(5,4), Q(3,2), Q(2)):
        for yy in (Q(1), Q(3,2), Q(2)):
            for fraction in (Q(0), Q(1,2), Q(1)):
                u0 = fraction*yy/2
                xd, yd = yy-u0, -x/2
                derivative = 2*x*xd+2*yy*yd
                if derivative != x*(yy-2*u0) or derivative < 0:
                    raise AssertionError('Good-future energy inequality')
                energy2_cases += 1
    check('good-future energy rational regressions', energy2_cases == 36)
    check('energy endpoint obstruction', (1+Q(1,100))**2+4 > 5 and 2**2+1 == 5)

    # Intentional incorrect sign/threshold formulas must not survive.
    wrong_energy = 2*(Q(1, 4)-Q(1, 2))*(-1-Q(3, 4))+2*(Q(3, 4)+1)*(Q(0)-1+Q(1, 4))
    if wrong_energy == -2*(Q(3, 4)+1)*(Q(0)-Q(1, 2)):
        raise AssertionError('Failed to reject wrong energy sign')
    controls.append('reversed energy sign rejected')
    if chord_margin == t*t+1-4*(Q(2221,1000)-t)**2:
        raise AssertionError('Failed to reject altered Gerver upper endpoint')
    controls.append('altered numerical enclosure detected')
    if Q(17, 4)-Q(9, 4)**2 >= 0:
        raise AssertionError('Known arm bound falsely treated as sufficient')
    controls.append('9/4 is not the sufficient sqrt(17)/2 threshold')

    return dict(status='exact_checks_passed', named_checks=len(names), checks=names,
                energy_identity_cases=energy_cases, triangle_identity_cases=triangle_cases,
                corner_flux_cases=flux_cases, good_future_energy_cases=energy2_cases,
                negative_controls=controls, gerver_upper=str(gerver),
                top_length_margin=str(chord_margin), good_arm_margin=str(arm_margin),
                corner_height_margin=str(height_margin),
                arithmetic='Python unbounded integers and Fraction',
                python_version=platform.python_version(),
                internal_seconds=perf_counter()-start,
                source_sha256=sha256(Path(__file__).read_bytes()).hexdigest(),
                geometric_admission_verified=False, external_gerver_theorem_verified=False,
                unrestricted_optimality_proved=False, ci_or_lean_used=False)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    output = json.dumps(run(), indent=2)+'\n'
    if args.output:
        args.output.write_text(output, encoding='utf-8')
    print(output, end='')
