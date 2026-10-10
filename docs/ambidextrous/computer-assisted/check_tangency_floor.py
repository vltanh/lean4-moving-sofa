"""Short exact checks for TF and HF; not an optimality certificate.

Standard-library fractions only. The differential-inequality comparison,
projection convergence, and maximizing-cap hypotheses are proved in the notes,
not certified by this finite regression script. No search or Lean invocation.
Run under a short external wall-clock limit (for example timeout 5s).
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
    def check(name: str, ok: bool) -> None:
        if not ok:
            raise AssertionError(name)
        names.append(name)

    z = Q(21, 100)
    sl = z-z**3/6
    cu = 1-z*z/2+z**4/24
    margin = Q(46588123, 128000000000)
    check('beta comparison numerator',
          Q(9,40)-Q(9,40)**3/6-Q(2,9) == Q(1013,1152000))
    check('beta strict comparison', Q(1013,1152000) > 0)
    check('sqrt2 upper bound', Q(99,70)**2 > 2)
    check('reciprocal sqrt2 lower bound', Q(7,10)**2*2 < 1)
    check('reference Q0 upper bound', Q(351,160)**2-Q(77,16) == Q(1,25600))
    check('reference Q0 lower bound', Q(77,16) > 4)
    check('sqrt2 Q0 lower bound', 2*Q(77,16) > Q(14,5)**2)
    check('test time rational upper bound', Q(9,40)+Q(99,70)*z == Q(261,500))
    t = Q(261,500)
    sin_upper = t-t**3/6+t**5/120
    check('test time below pi/6 via sine bound', sin_upper < Q(1,2))
    check('reference q exact margin', Q(351,160)*cu-Q(7,10)*sl == 2-margin)
    check('reference q margin positive', margin > 0)
    rp = z*z/2-Q(14,5)*sl
    check('reference p upper value', rp == -Q(2808141,5000000))
    check('reference p below minus one half', rp < -Q(1,2))
    check('test remains above p=-1', -Q(3,2)*Q(9,4)*z == -Q(567,800) > -1)

    # The area identity is checked separately before imposing T=W/2.
    cases = 0
    for width in (Q(5,2),Q(8,3),Q(14,5)):
        for top in (Q(1),Q(5,4),Q(4,3)):
            for mass in (Q(3,2),Q(5,3),Q(7,4)):
                for support_moment in (Q(2),Q(3)):
                    cap = (support_moment+width/2+top)/2
                    niche = (support_moment-mass)/2
                    psi = cap-niche-width/2
                    if psi != mass/2+top/2-width/4:
                        raise AssertionError('Stationary area identity')
                    cases += 1
    check('stationary area identity on rational cases', cases == 54)
    for width in (Q(5,2),Q(8,3),Q(14,5)):
        mass = Q(5,3); top=width/2
        check('half-width perimeter cancellation '+str(width),
              mass/2+top/2-width/4 == mass/2)

    # Reject two overstrong replacements by direct rational countervalues.
    ell, actual, local = Q(1,2), Q(1,2), Q(1)
    if actual == ell and local-actual != 0:
        controls.append('balance does not imply local-bound saturation')
    else:
        raise AssertionError('Logical gap control')
    width, top, mass = Q(5,2), Q(1), Q(5,3)
    if mass/2+top/2-width/4 != mass/2:
        controls.append('perimeter simplification needs half-width top')
    else:
        raise AssertionError('Missing face-ratio control')

    return {
        'status':'exact_checks_passed',
        'named_checks':names,
        'named_check_count':len(names),
        'rational_area_identity_cases':cases,
        'negative_controls':controls,
        'q_reference_margin':str(margin),
        'sine_comparison_margin':str(Q(1,2)-sin_upper),
        'arithmetic':'Python unbounded integers and fractions.Fraction',
        'elapsed_seconds':perf_counter()-start,
        'python_version':platform.python_version(),
        'source_sha256':sha256(Path(__file__).read_bytes()).hexdigest(),
        'script_wall_clock_cap_seconds':5,
        'unrestricted_optimality_proved':False,
        'geometric_dependencies_independently_verified':False,
        'scope':'Finite TF rational constants and HF algebra; not the continuum comparison proof',
        'ci_or_lean_used':False,
    }


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path)
    args=parser.parse_args()
    text=json.dumps(run(),indent=2)+'\n'
    if args.output:
        args.output.write_text(text,encoding='utf-8')
    print(text,end='')
