"""Compare explicit lower certificates against midpoint upper bounds.

Only excludes the full-rotation, aligned-endpoint class described in
CLASS_BOUNDS.md. No unrestricted moving-sofa upper bound is asserted.
"""
from fractions import Fraction
import json
from pathlib import Path
from interval_verify import Q, trig_point


def class_upper(degrees: str, mode: str) -> Fraction:
    half = Fraction(str(degrees))/360
    if not 0 < half < Fraction(1, 2) or mode not in ('forward', 'reverse'):
        raise ValueError('invalid bend or class')
    sine, cosine = trig_point(half)
    lo = sine[0] if mode == 'forward' else cosine[0]
    if lo <= 0:
        raise ArithmeticError('positive trigonometric denominator not resolved')
    return Fraction((2 if mode == 'forward' else 1)*Q, lo)


def compare(manifest: dict) -> list[dict]:
    rows=[]
    for r in manifest['results']:
        degrees,mode=r['candidate'].split('-')
        other='reverse' if mode=='forward' else 'forward'
        interval=r['interval']
        lower=Fraction(interval['area_numerator'],interval['area_denominator'])
        upper=class_upper(degrees,other)
        scaled=upper*10**6
        ceiling=-((-scaled.numerator)//scaled.denominator)
        rows.append({'candidate':r['candidate'],'compared_class':other,
            'class_upper_numerator':upper.numerator,'class_upper_denominator':upper.denominator,
            'class_upper_decimal_ceiling_6':f'{ceiling//10**6}.{ceiling%10**6:06d}',
            'excluded_by_certificate':lower>upper})
    return rows

if __name__=='__main__':
    folder=Path(__file__).parent/'results'
    result={'status':'conditional on the checked lower certificates; exclusion only of the specified aligned-endpoint class',
        'results':compare(json.loads((folder/'interval-manifest.json').read_text()))}
    text=json.dumps(result,indent=2)+'\n'
    (folder/'class-exclusions.json').write_text(text)
    print(text,end='')
