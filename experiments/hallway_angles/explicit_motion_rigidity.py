"""Exact-rational propagation of explicit near-optimal motion rigidity.

See EXPLICIT_MOTION_RIGIDITY.md. This uses the scalar bounds proved in
explicit_cutoff_certificate.py, not a sampled motion or numerical optimizer.
"""
from fractions import Fraction as F
import argparse
import json

from explicit_cutoff_certificate import prove_scalars


def prove_motion_rigidity() -> dict:
    e, D = F(1, 100), F(1, 10000)
    n = 3*e/4
    deficit = D+F(17, 50)*n*n
    root_bound = F(9, 800)
    ex = F(5, 2)*root_bound+F(7, 2)*deficit
    ey = F(17, 10)*root_bound+5*deficit
    W, H = F(143, 500)-2*ex, 1-2*ey
    Wmin, Hmin = F(9, 40), F(19, 20)
    amax, bmin, sincmin = F(3, 4), F(99, 100), F(999, 1000)
    K = F(40)
    rdef = 1+F(17, 50)*K*K*e*e
    checks = {
        'global_cutoff_inclusion': F(1, 19)-e,
        'normal_mismatch': F(3, 4)*(1-F(3, 40)**2/6)-1/(F(27, 20)-D),
        'reverse_class': (F(27, 20)-D)/(2*e)-3,
        'deficit_is_small': F(1, 3)-deficit,
        'deficit_root_bound': root_bound**2-deficit,
        'core_width': W-Wmin,
        'core_height': H-Hmin,
        'triangle_vertical': bmin*Hmin*Hmin/(2*amax)-deficit,
        'horizontal_failure_coefficient': 40*sincmin*Wmin*Wmin/2-1,
        'horizontal_failure_absorption': 41*(1-F(68, 5)*e*n)-40,
        'horizontal_failure_conclusion': 40-F(41, 100),
        'square_root_direction_bound': F(7, 8)**2-amax,
        'triangle_error_coefficient': 9-(2*amax*F(5, 2)+2*F(17, 10)+F(7, 4)),
        'triangle_absorption': K*(F(143, 500)*sincmin-F(21, 4)*e-F(1137, 200)*e*n)
                               -(9+F(61, 400)),
        'actual_width': 11-10*rdef,
        'aligned_deficit_root': F(103, 100)**2-rdef,
        'aligned_path_x': 3-F(5, 2)*F(103, 100)-F(7, 2)*rdef/F(100),
        'aligned_path_y': 2-F(17, 10)*F(103, 100)-5*rdef/F(100),
    }
    if any(v <= 0 for v in checks.values()):
        raise ArithmeticError({k: str(v) for k, v in checks.items() if v <= 0})
    return dict(format='explicit-motion-rigidity-v1', status='all rational inequalities positive',
                epsilon_max=str(e), normalized_deficit_max=str(D), mismatch_constant=str(K),
                actual_width_constant='11', aligned_path_constants=['3', '2'],
                deficit_ratio=str(rdef),
                rational_slacks={k: str(v) for k, v in checks.items()})


if __name__ == '__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--cells', type=int, default=256)
    parser.add_argument('--output')
    args=parser.parse_args()
    result=dict(scalars=prove_scalars(args.cells), motion=prove_motion_rigidity())
    text=json.dumps(result,indent=2)+'\n'
    if args.output:
        from pathlib import Path
        Path(args.output).write_text(text)
    else:
        print(text,end='')
