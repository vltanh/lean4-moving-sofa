"""Generate all witnesses, then independently replay the tilted-height theorem.

This is a compact reproducibility recipe, not a substitute for executing the
verifier. No matching size or optimizer assertion is trusted. The generated
JSON contains all concrete pairs and can be replayed without NumPy/NetworkX.
"""
from __future__ import annotations
import argparse
from fractions import Fraction as Q
from hashlib import sha256
import json
from pathlib import Path
import platform
import numpy as np
import networkx as nx
from discover_anchor_matching import discover, DEFAULT_PARAMETERS
from verify_anchor_matching import verify

BREAKS = ['2', '41/20', '21/10', '43/20', '11/5', '9/4', '91/40',
          '23/10', '47/20', '12/5', '49/20', '5/2', '51/20', '13/5',
          '53/20', '27/10', '11/4', '14/5', '57/20', '29/10', '2999/1020']
CLAIMED_BOUND = Q(84151, 51200)


def reproduce(output: Path) -> dict:
    output.mkdir(parents=True, exist_ok=True)
    bins = []
    attempts = []
    for lo, hi in zip(BREAKS, BREAKS[1:]):
        spec = dict(width=[lo, hi], left_height=['19/20', '1'],
                    right_height=['0', '1/20'], grid=[80, 32])
        pairs, report = discover(spec, DEFAULT_PARAMETERS,
                                 exact_matching=True, replay=True)
        attempts.append(report)
        (output/'discovery.json').write_text(json.dumps(attempts, indent=2)+'\n')
        if report['exact_replay'] is None:
            raise RuntimeError('Unresolved bin: '+repr(spec['width']))
        bins.append(dict(width=[lo, hi], grid=[80, 32], pairs=pairs))
        print('Replayed width bin', lo, hi, flush=True)
    data = dict(format='ambi-anchor-matching-v1',
                region=dict(width=[BREAKS[0], BREAKS[-1]],
                            left_height=['19/20', '1'], right_height=['0', '1/20']),
                parameters=DEFAULT_PARAMETERS, bins=bins)
    raw = (json.dumps(data, separators=(',', ':'))+'\n').encode()
    (output/'tilted_full_width.json').write_bytes(raw)
    # A complete second replay also verifies that there is no coverage gap.
    result = verify(data)
    if Q(result['unconditional_area_upper']) > CLAIMED_BOUND:
        raise RuntimeError('Certificate fails the claimed stronger bound')
    root = Path(__file__).resolve().parent
    result.update(certificate_sha256=sha256(raw).hexdigest(),
                  source_sha256={name: sha256((root/name).read_bytes()).hexdigest()
                                 for name in ('verify_anchor_matching.py',
                                              'discover_anchor_matching.py',
                                              'reproduce_tilted_matching.py')},
                  python_version=platform.python_version(),
                  numpy_version=np.__version__, networkx_version=nx.__version__,
                  scope='All widths in the specified extreme-height region only',
                  independent_mathematical_review=False)
    (output/'tilted_full_width.result.json').write_text(json.dumps(result, indent=2)+'\n')
    return result


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output-dir', type=Path, required=True)
    args = parser.parse_args()
    print(json.dumps(reproduce(args.output_dir), indent=2))
