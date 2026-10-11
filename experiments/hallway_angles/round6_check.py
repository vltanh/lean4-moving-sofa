"""Reproduce round-six scalar certificates and local tests without CI.

The global cutoff depends on the prior analytic geometry proof. The analytic
forward crossing is a CONTACT-MODEL result, not a global phase transition.
"""
from __future__ import annotations
from fractions import Fraction as F
from pathlib import Path
from importlib.metadata import version
import argparse
import hashlib
import json
import platform
import unittest

BASELINE_BLOBS={
    'parameter_certificate.py':'d823a8937a550c72a1f596785d9de4c1b8d9de8e',
    'width_certificate.py':'6fbfc4643eb0e00769e5eb010d626a36ab698bb1',
    'reverse_exact.py':'be73f2032da918913f7d8ed34edc99909fff701e',
}


def blob(path):
    data=path.read_bytes()
    return hashlib.sha1(f'blob {len(data)}\0'.encode()+data).hexdigest()


def canonical_hash(value):
    return hashlib.sha256(json.dumps(value,sort_keys=True,separators=(',',':')).encode()).hexdigest()


def run():
    root=Path(__file__).resolve().parent
    for name,sha in BASELINE_BLOBS.items():
        if blob(root/name)!=sha:raise RuntimeError(f'baseline changed; review before proceeding: {name}')
    from test_interior_core import InteriorCoreChecks
    from test_contact_model import ScalarCertificateChecks
    from interior_core_certificate import path_constants,constants,scalars,EMAX
    from contact_crossing_certificate import I,SCALE,pi_interval,interval,isolate_t,at
    modules=['test_interior_core','test_contact_model']
    suite=unittest.defaultTestLoader.loadTestsFromNames(modules)
    outcome=unittest.TextTestRunner(verbosity=2).run(suite)
    if not outcome.wasSuccessful() or outcome.skipped:
        raise RuntimeError('some new tests failed or were skipped')
    foundation=InteriorCoreChecks.foundation
    directions=InteriorCoreChecks.directions
    crossing=ScalarCertificateChecks.proof
    core=dict(foundation=foundation,path=path_constants(),directions=directions)
    pi=pi_interval()
    def decimal(x,digits=9):
        k=10**digits
        lo=x.lo*k//SCALE;hi=-((-x.hi*k)//SCALE)
        def fmt(n):
            sign='-' if n<0 else '';n=abs(n)
            return f'{sign}{n//k}.{n%k:0{digits}d}'
        return dict(lower=fmt(lo),upper=fmt(hi))
    values=[]
    for b in [173,175,177,179]:
        e=pi*I.rational(180-b,180)
        if e.hi>I.rational(EMAX).lo:raise ArithmeticError('angle not covered by the cutoff')
        v=scalars(constants(e))['eV']/e
        values.append(dict(bend_degrees=b,global_optimum_formula=decimal(v),interval=[v.lo,v.hi]))
    blo,bhi=map(F,crossing['root_bend_degrees_interval'])
    beta=pi*interval(blo/180,bhi/180);t=isolate_t(beta,pi)
    _,_,w,alpha=at(beta,t,pi)
    sources=list(BASELINE_BLOBS)+['interior_core_certificate.py','forward_contact_equations.py',
        'contact_crossing_certificate.py','test_interior_core.py','test_contact_model.py',
        'forward_contact_diagnostics.py','round6_check.py']
    return dict(
        format='hallway-round6-checks-v1',
        status='Analytic proof drafts and exact scalar certificates; not independently reviewed or Lean checked',
        starting_commit='9d08bce1b5c45cabea6c990e8965cfc238af699f',
        source_blobs={name:blob(root/name) for name in sources},
        environment=dict(python=platform.python_version(),**{n:version(n) for n in ['numpy','scipy','shapely','mpmath']}),
        tests=dict(command='python -m unittest -v '+' '.join(modules),run=outcome.testsRun,
                   passed=outcome.testsRun,skipped=0,ci=False,lean=False),
        core_certificate=dict(epsilon_cutoff='1/8',cutoff_degrees=decimal(180-180/(8*pi)),
            parameter_cells=foundation['cells'],boundary_parameters=foundation['points'],
            common_rectangles=len(foundation['rectangles']),
            used_rectangles=len(set(r['rectangle'] for r in directions['cell_records'])),
            direction_cells=directions['cells'],minimum_normalized_margin=directions['minimum_normalized_margin'],
            scalar_bounds=foundation['scalar_bounds'],scalar_enclosures=foundation['scalar_enclosures'],
            path=core['path'],full_certificate_sha256=canonical_hash(core)),
        global_value_enclosures=values,
        contact_model_certificate={**{k:v for k,v in crossing.items() if k!='tube_records'},
            'root_T_enclosure':decimal(t,12),'root_alpha_degrees_enclosure':decimal(alpha.v*180/pi,9),
            'root_signed_area_enclosure':decimal(w.v,9),'full_certificate_sha256':canonical_hash(crossing)},
        exclusions=['No forward-class upper bound matching the contact model is proved.',
                    'Continuous feasibility and the boundary topology of the contact model are not certified.',
                    'The scalar model root is not identified with the unrestricted beta_c.',
                    'The sufficient cutoff is not the true onset of global reverse optimality.'],
        reproduction=['python interior_core_certificate.py --parameter-cells 128 --points 128 --direction-cells 1024 --output interior-core-proof.json',
                      'python contact_crossing_certificate.py --cells 256 --output contact-model-proof.json',
                      'python round6_check.py --output results/round6-checks.json'])


if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--output')
    args=p.parse_args();text=json.dumps(run(),indent=2)+'\n'
    if args.output:Path(args.output).write_text(text)
    else:print(text,end='')
