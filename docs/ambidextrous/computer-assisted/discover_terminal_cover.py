"""Untrusted LP discovery followed by the existing exact CF verifier.

This generates an endpoint exclusion, not a proof of unrestricted optimality.
Only verify_configurations.py decides certificate acceptance. In particular,
floating-point separation, LP convergence, and rounded dual weights are not
trusted: every selected geometric witness and the final bound are replayed.
"""
from __future__ import annotations
import argparse
from fractions import Fraction as Q
from hashlib import sha256
import json
from pathlib import Path
import platform
from time import perf_counter
import numpy as np
import scipy
from scipy.optimize import linprog
from scipy.sparse import coo_matrix
from verify_configurations import direction, frame_data, verify_bin, verify

BREAKS = ['12/25', '49/100', '1/2', '51/100', '13/25', '53/100',
          '27/50', '11/20', '14/25', '57/100', '23/40', '29/50']


def propose_bin(lo_text: str, hi_text: str, n: int = 24,
                iterations: int = 45) -> tuple[dict, dict]:
    lo, hi = Q(lo_text), Q(hi_text)
    if not Q(12, 25) <= lo < hi <= Q(29, 50) or not 1 <= n <= 64:
        raise ValueError('Outside the stated search domain')
    count = n*n
    ca, sa = direction(hi)
    frames = []
    for r in sorted({Q(k, 40) for k in range(4, 40)} | {lo}):
        c, s = direction(r)
        if r <= lo:
            frames.append(dict(turn='lower', r=str(r)))
        if c >= Q(5, 8) or (ca*c-sa*s <= 0 and sa*c+ca*s > Q(5, 8)):
            frames.append(dict(turn='upper', r=str(r)))
    exact_frames = [frame_data(f, lo, hi) for f in frames]
    ii, jj = np.arange(count)//n, np.arange(count)%n
    dx0 = (ii[None, :]-ii[:, None]-1)/n
    dx1 = dx0+2/n
    dy0 = (jj[None, :]-jj[:, None]-1)/n
    dy1 = dy0+2/n
    relations = []
    for pair in exact_frames:
        rr = []
        for aa, bb in pair:
            a, b = list(map(float, aa)), list(map(float, bb))
            lower = (np.minimum.reduce([v*d for v in a for d in (dx0, dx1)])
                     + np.minimum.reduce([v*d for v in b for d in (dy0, dy1)]))
            rr.append(lower > 1+1e-10)
        relations.append(rr)
    # Each key is an unordered triple; the value is its concrete frame and
    # ordered witness. Only a small lazily separated subset is needed.
    edges = {}
    progress = []
    start = perf_counter()
    for iteration in range(iterations):
        kept = list(edges)
        rows, cols = [], []
        for row, edge in enumerate(kept):
            rows.extend([row]*3)
            cols.extend(edge)
        matrix = coo_matrix((np.ones(len(rows)), (rows, cols)),
                            shape=(len(kept), count)).tocsr()
        # Fractional cover in x=1-z. Its dual is a fractional matching whose
        # vertex loads are at most one, before exact renormalization below.
        answer = linprog(np.ones(count), A_ub=-matrix if kept else None,
                         b_ub=-np.ones(len(kept)) if kept else None,
                         bounds=(0, None), method='highs')
        if not answer.success:
            raise RuntimeError(answer.message)
        z = 1-np.minimum(answer.x, 1)
        added = 0
        for fi, (u, v) in enumerate(relations):
            us, vs = np.where(u, z[None, :], -10), np.where(v, z[None, :], -10)
            q, r = us.argmax(axis=1), vs.argmax(axis=1)
            scores = z+us[np.arange(count), q]+vs[np.arange(count), r]-2
            for p in np.flatnonzero(scores > 1e-7):
                edge = tuple(sorted({int(k) for k in (p, q[p], r[p])}))
                if len(edge) != 3:
                    raise RuntimeError('Unexpected repeated-cell discovery witness')
                if edge not in edges:
                    edges[edge] = [fi, int(p), int(q[p]), int(r[p])]
                    added += 1
        upper = (count-answer.fun)/(count*float(ca))
        progress.append(dict(iteration=iteration, proposed_upper=upper,
                             constraints=len(kept), added=added,
                             seconds=perf_counter()-start))
        if (upper < 1.639 and kept) or not added:
            break
    triples = []
    for edge, marginal in zip(kept, answer.ineqlin.marginals):
        weight = int(round(max(0.0, -float(marginal))*1_000_000))
        if weight:
            triples.append(edges[edge]+[weight])
    data = dict(lo=lo_text, hi=hi_text, n=n, frames=frames, triples=triples)
    # Rejecting here means no theorem has been obtained for this interval.
    checked = verify_bin(data)
    return data, dict(progress=progress, exact_replay=checked)


def reproduce(output: Path) -> dict:
    output.mkdir(parents=True, exist_ok=True)
    bins, attempts = [], []
    for lo, hi in zip(BREAKS, BREAKS[1:]):
        data, details = propose_bin(lo, hi)
        bins.append(data)
        attempts.append(details)
        (output/'discovery.json').write_text(json.dumps(attempts, indent=2)+'\n')
        print('Exactly replayed endpoint bin', lo, hi, flush=True)
    certificate = dict(format='ambi-forbidden-triples-v1', bins=bins)
    raw = (json.dumps(certificate, separators=(',', ':'))+'\n').encode()
    (output/'terminal_to_29_50.json').write_bytes(raw)
    result = verify(certificate)
    root = Path(__file__).resolve().parent
    result.update(certificate_sha256=sha256(raw).hexdigest(),
                  source_sha256={name: sha256((root/name).read_bytes()).hexdigest()
                                 for name in ('verify_configurations.py',
                                              'discover_terminal_cover.py')},
                  python_version=platform.python_version(),
                  numpy_version=np.__version__, scipy_version=scipy.__version__,
                  ci_or_lean_used=False, independent_mathematical_review=False)
    (output/'terminal_to_29_50.result.json').write_text(json.dumps(result, indent=2)+'\n')
    return result


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output-dir', type=Path, required=True)
    args = parser.parse_args()
    print(json.dumps(reproduce(args.output_dir), indent=2))
