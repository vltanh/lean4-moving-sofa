"""Reproduce fifth-round scalar proofs, rejection checks, values, and local tests.

This is a local command, not a GitHub Actions/CI workflow. Exact scalar checks
and supplementary floating-point geometry tests have distinct trust roles.
"""
from fractions import Fraction
from pathlib import Path
import argparse
import hashlib
from importlib.metadata import version
import json
import platform
import unittest

from explicit_cutoff_certificate import prove_propagation, prove_scalars, quantities
from explicit_motion_rigidity import prove_motion_rigidity
from parameter_certificate import Interval, SCALE, ceil_div, pi_interval

BASELINE_BLOBS = {
    'parameter_certificate.py': 'd823a8937a550c72a1f596785d9de4c1b8d9de8e',
    'width_certificate.py': '6fbfc4643eb0e00769e5eb010d626a36ab698bb1',
    'reverse_exact.py': 'be73f2032da918913f7d8ed34edc99909fff701e',
}
TESTS = ['test_explicit_cutoff', 'test_explicit_motion_rigidity']


def git_blob(path: Path) -> str:
    data=path.read_bytes()
    return hashlib.sha1(f'blob {len(data)}\0'.encode()+data).hexdigest()


def decimal_enclosure(value: Interval, digits: int = 9) -> dict[str,str]:
    factor=10**digits
    lo=value.lo*factor//SCALE
    hi=ceil_div(value.hi*factor,SCALE)
    def format_number(n):
        sign='-' if n<0 else ''
        n=abs(n)
        return f'{sign}{n//factor}.{n%factor:0{digits}d}'
    return dict(lower=format_number(lo),upper=format_number(hi))


def run() -> dict:
    root=Path(__file__).resolve().parent
    for name,expected in BASELINE_BLOBS.items():
        actual=git_blob(root/name)
        if actual!=expected:
            raise RuntimeError(f'baseline source changed: {name}: {actual}; review before rechecking')
    scalars=prove_scalars(256)
    proof_hash=hashlib.sha256(json.dumps(scalars,sort_keys=True,separators=(',',':')).encode()).hexdigest()
    propagation=prove_propagation()
    motion=prove_motion_rigidity()
    negatives={}
    for name,check in [('coarse_single_cell',lambda:prove_scalars(1)),
                       ('cutoff_53_over_1000',lambda:prove_propagation(Fraction(53,1000)))]:
        try:
            check()
        except ArithmeticError as error:
            negatives[name]=dict(rejected=True,message=str(error))
        else:
            raise RuntimeError(f'expected rejection did not occur: {name}')
    pi=pi_interval()
    values=[]
    for beta in [177,178,179]:
        e=pi*Interval.rational(180-beta,180)
        if e.hi>Interval.rational(1,19).lo:
            raise ArithmeticError('illustrative angle is outside the proved cutoff')
        V=quantities(e)['eV']/e
        values.append(dict(bend_degrees=beta,optimum=decimal_enclosure(V),
                           interval_numerators=[V.lo,V.hi],denominator=SCALE))
    suite=unittest.defaultTestLoader.loadTestsFromNames(TESTS)
    outcome=unittest.TextTestRunner(verbosity=2).run(suite)
    if not outcome.wasSuccessful() or outcome.skipped:
        raise RuntimeError('local tests failed or were skipped')
    source_files=list(BASELINE_BLOBS)+['explicit_cutoff_certificate.py','explicit_motion_rigidity.py',
                                      'test_explicit_cutoff.py','test_explicit_motion_rigidity.py',
                                      'round5_check.py']
    scalars.pop('cell_margins')
    return dict(format='hallway-round5-checks-v1',
                status='Proof draft; not independently reviewed or Lean checked',
                starting_commit='ce09bb5910d86cd2f233ce52d2c3f3279a610836',
                source_blobs={name:git_blob(root/name) for name in source_files},
                environment=dict(python=platform.python_version(),numpy=version('numpy'),shapely=version('shapely')),
                tests=dict(command='python -m unittest -v '+' '.join(TESTS),run=outcome.testsRun,
                           passed=outcome.testsRun,skipped=0,ci=False,lean=False),
                scalar_certificate=scalars,full_scalar_record_sha256=proof_hash,
                propagation=propagation,motion_rigidity=motion,
                global_cutoff_degrees=decimal_enclosure(180-180/(19*pi)),
                exact_optimum_values=values,negative_checks=negatives,
                reproduction='python round5_check.py --output results/round5-checks.json')


if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output')
    args=parser.parse_args()
    text=json.dumps(run(),indent=2)+'\n'
    if args.output:
        Path(args.output).write_text(text)
    else:
        print(text,end='')
