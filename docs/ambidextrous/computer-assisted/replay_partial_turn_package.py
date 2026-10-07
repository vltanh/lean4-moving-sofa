"""Replay the supplied PC package with provenance and a ten-second subprocess cap.

The original and missing-only modes are diagnostics, not geometric certificates.
The original archive is an explicit input and is never changed.
"""
from pathlib import Path
from zipfile import ZipFile
from hashlib import sha256
import argparse
import json
import subprocess
import sys

ARCHIVE_SHA = '03dffee9b89a6cecb359b8b5c49d6284952f466bc34f7a3a21ceaa28636b1a81'
SCRIPT_PATH = 'docs/ambidextrous/computer-assisted/partial-turn-completion/check_partial_turn_completion.py'
SCRIPT_SHA = '2f80073b434dafc42418556ac96f2408e00feb61a19d9dd8cfd0a37fd8ffa0d1'


def replace_once(source, old, new):
    if source.count(old) != 1:
        raise ValueError('Expected exactly one source edit anchor: ' + old)
    return source.replace(old, new)


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--package', type=Path, required=True)
    ap.add_argument('--output', type=Path, required=True)
    ap.add_argument('--mode', choices=['original', 'missing-only'], default='original')
    args = ap.parse_args()
    data = args.package.read_bytes()
    if sha256(data).hexdigest() != ARCHIVE_SHA:
        raise ValueError('Archive differs from the audited upload')
    with ZipFile(args.package) as archive:
        raw = archive.read(SCRIPT_PATH)
    if sha256(raw).hexdigest() != SCRIPT_SHA:
        raise ValueError('Original checker differs from the audited source')
    source = raw.decode('utf-8')
    if args.mode == 'missing-only':
        source = replace_once(source,
            'nUv, nUf = niche(K, x, tl), niche(K, x, tf)',
            'tf = np.unique(np.concatenate([tl, np.linspace(alpha, L, 1001)[:-1]]))\n'
            '        nUv, nUf = niche(K, x, tl), niche(K, x, tf)\n'
            '        assert np.all(nUf >= nUv - 1e-14)')
        source = replace_once(source, 'tau = 0.5*kap**2*np.sin(eps)',
            '''tau = 0.5*kap**2*np.sin(eps)
        a_cross, b_cross = nUf - Br, nV - (1-Ar)
        R_true = np.trapezoid(np.maximum(a_cross,0)+np.maximum(b_cross,0)-np.maximum(a_cross+b_cross,0),x)
        Z_empty = np.trapezoid(np.maximum(-(top-np.maximum(nUf,Br)),0),x)
        Xi = np.trapezoid(np.maximum(Br,nUf)-np.maximum(Br,nUv),x)
        assert abs((Cas-Ef) - (R_true-Z_empty)) < 1e-12
        assert abs((Ev-Ef) - (Xi-Z_empty)) < 1e-12
        assert Ev >= Ef - 1e-12''')
        source = replace_once(source, 'AS_remainder=float(Cas-Ef), min_fiber=',
            'AS_remainder=float(Cas-Ef), true_R=float(R_true), empty_fiber_Z=float(Z_empty), '
            'signed_increment_Xi=float(Xi), circular_bound=float(kap-eps/2), min_fiber=')
        source = replace_once(source, '"labels": "PC"', '"labels": "PC missing-only-angle review"')
    args.output.mkdir(parents=True, exist_ok=True)
    script = (args.output / ('checker-' + args.mode + '.py')).resolve()
    record = (args.output / ('result-' + args.mode + '.json')).resolve()
    script.write_text(source, encoding='utf-8')
    result = subprocess.run([sys.executable, '-I', str(script), str(record)],
                            capture_output=True, text=True, timeout=10, check=False)
    (args.output / (args.mode + '.stdout')).write_text(result.stdout, encoding='utf-8')
    (args.output / (args.mode + '.stderr')).write_text(result.stderr, encoding='utf-8')
    manifest = {'archive_sha256': ARCHIVE_SHA, 'original_script_sha256': SCRIPT_SHA,
        'mode': args.mode, 'executed_script_sha256': sha256(script.read_bytes()).hexdigest(),
        'subprocess_timeout_seconds': 10, 'returncode': result.returncode,
        'wrapper_sha256': sha256(Path(__file__).read_bytes()).hexdigest(),
        'certificate': False, 'ci_or_lean_used': False}
    (args.output / ('manifest-' + args.mode + '.json')).write_text(json.dumps(manifest, indent=2)+'\n')
    if result.returncode:
        raise RuntimeError(result.stderr or 'Checker failed')
    print(record.read_text())


if __name__ == '__main__':
    main()
