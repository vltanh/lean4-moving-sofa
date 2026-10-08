"""Exact replay and deliberate-corruption tests for two restricted certificates.

The complete matching and terminal witness JSON files are positional inputs.
No search package, CI, Lean/Lake, or network access is needed. These checks do
not certify unrestricted optimality or independently review the geometry.
"""
from __future__ import annotations
from copy import deepcopy
from fractions import Fraction as Q
from pathlib import Path
from hashlib import sha256
import sys,json,platform,argparse
HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE/'occupancy'))
import verify_anchor_matching as am
sys.path.insert(0,str(HERE))
import verify_configurations as cf

parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('matching',type=Path)
parser.add_argument('terminal',type=Path)
parser.add_argument('--output',type=Path)
args=parser.parse_args()
matching_path,terminal_path=args.matching,args.terminal
matching=json.loads(matching_path.read_text())
terminal=json.loads(terminal_path.read_text())
rejected=[]
def rejects(name,fun):
 try:fun()
 except (ValueError,TypeError,ZeroDivisionError,IndexError):rejected.append(name);return
 raise AssertionError('Mutation accepted: '+name)

def match_spec(d):
 b=d['bins'][0]
 return dict(width=b['width'],grid=b['grid'],left_height=d['region']['left_height'],right_height=d['region']['right_height'])

def match_mutate(name,fn):
 d=deepcopy(matching);fn(d)
 rejects(name,lambda:am.verify_bin(match_spec(d),d['bins'][0]['pairs'],d['parameters']))

match_mutate('matching duplicated pair',lambda d:d['bins'][0]['pairs'].append(d['bins'][0]['pairs'][0]))
match_mutate('matching repeated endpoint',lambda d:d['bins'][0]['pairs'][0].__setitem__(1,d['bins'][0]['pairs'][0][0]))
match_mutate('matching negative cell',lambda d:d['bins'][0]['pairs'][0].__setitem__(0,-1))
match_mutate('matching out-of-range cell',lambda d:d['bins'][0]['pairs'][0].__setitem__(0,2560))
match_mutate('matching malformed triple',lambda d:d['bins'][0]['pairs'][0].append(7))
match_mutate('matching grid out of range',lambda d:d['bins'][0]['grid'].__setitem__(0,257))
match_mutate('matching broadened heights not justified',lambda d:d['region'].__setitem__('left_height',['0','1']))
d=deepcopy(matching);d['bins']=d['bins'][:1]
rejects('matching incomplete width cover',lambda:am.verify(d))
d=deepcopy(matching);d['bins'][0]['width'][0]='201/100'
rejects('matching initial coverage gap',lambda:am.verify(d))

for name,fn in [
 ('terminal repeated cell',lambda b:b['triples'][0].__setitem__(2,b['triples'][0][1])),
 ('terminal negative weight',lambda b:b['triples'][0].__setitem__(4,-1)),
 ('terminal zero weight',lambda b:b['triples'][0].__setitem__(4,0)),
 ('terminal false angle guarantee',lambda b:b['frames'][0].__setitem__('r','1')),
 ('terminal empty certificate',lambda b:b.__setitem__('triples',[])),
 ('terminal unsupported grid',lambda b:b.__setitem__('n',65)),
 ('terminal out-of-range frame',lambda b:b['triples'][0].__setitem__(0,999)),
 ('terminal unsupported endpoint',lambda b:b.__setitem__('hi','3/5'))]:
 b=deepcopy(terminal['bins'][0]);fn(b);rejects(name,lambda b=b:cf.verify_bin(b))
d=deepcopy(terminal);d['bins']=d['bins'][:1]
rejects('terminal incomplete interval cover',lambda:cf.verify(d))
d=deepcopy(terminal);d['bins'][0]['lo']='49/100'
rejects('terminal initial coverage gap',lambda:cf.verify(d))

# Equality at a wall is allowed: the exclusion test must remain strictly >1.
assert not am.separated((0,0,0,0),(2,2,0,0),(1,0),(2,2,2),4)
assert am.separated((0,0,0,0),(3,3,0,0),(1,0),(2,2,2),4)
# Exact comparison with M using the positive cubic root and arctan lower bound.
y=Q(149,500)
assert 4*y**3+3*y-1<0
lower_M=1+4*y*y+y-y**3/3
assert Q(84151,51200)<Q(411,250)<lower_M
assert 3*29**2>50**2  # 2 arctan(29/50) > pi/3.

mr=am.verify(matching);tr=cf.verify(terminal)
result=dict(status='all_replays_and_controls_passed',rejected_controls=rejected,
            strict_wall_tests_passed=True,candidate_lower_bound=str(lower_M),
            matching_bound=mr['unconditional_area_upper'],matching_bins=len(mr['bins']),
            matching_pairs=sum(x['disjoint_pairs'] for x in mr['bins']),
            terminal_bins=len(tr['bins']),terminal_triples=sum(x['verified_triples'] for x in tr['bins']),
            terminal_worst_bound=str(max(Q(x['area_upper']) for x in tr['bins'])),
            certificate_sha256={'matching':sha256(matching_path.read_bytes()).hexdigest(),
                                'terminal':sha256(terminal_path.read_bytes()).hexdigest()},
            source_sha256=sha256(Path(__file__).read_bytes()).hexdigest(),
            python_version=platform.python_version(),unrestricted_optimality_proved=False,
            ci_or_lean_used=False)
if args.output:
 args.output.write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
