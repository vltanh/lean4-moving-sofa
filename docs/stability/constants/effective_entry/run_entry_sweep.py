"""Resumable exact angle-slab cover, with source hashes in every receipt.

Run selected slabs with --first/--last, then --verify-only to require all20.
Partial execution or a surviving frontier never counts as full separation.
"""
from entry_terminal_pinned import TerminalPinnedSearch
from entry_box_search import Q
from pathlib import Path
import argparse,hashlib,json,platform

SOURCES=('entry_box_search.py','entry_terminal_pinned.py','run_entry_sweep.py')
def hashes():return {p:hashlib.sha256(Path(__file__).with_name(p).read_bytes()).hexdigest() for p in SOURCES}
def collect(directory):
 rows=[];h=hashes()
 for i in range(60,80):
  p=directory/f'slab-{i:02d}.json'
  if not p.exists():raise RuntimeError(f'missing slab {i}')
  r=json.loads(p.read_text())
  if r['source_hashes']!=h:raise RuntimeError(f'source mismatch slab {i}')
  if r['status']!='separated' or r['frontier_boxes']!=0:raise RuntimeError(f'slab {i} is inconclusive')
  if r['terminal_half_angle_tangent_interval']!=[str(Q(i,100)),str(Q(i+1,100))]:raise RuntimeError('cover gap')
  if Q(r['upper_area_bound'])>Q(2219,1000):raise RuntimeError('invalid area bound')
  rows.append(r)
 assert Q(2774,1250)-Q(2219,1000)==Q(1,5000)
 assert Q(5,11)<Q(8,17) # arccos(5/11) > 2 atan(3/5)
 return {'status':'separated','terminal_half_angle_tangent_interval':['3/5','4/5'],
   'upper_area_bound':'2219/1000','reference_area_lower':'2774/1250','area_gap':'1/5000',
   'omega_lower_after_gap':'2*atan(4/5)','slab_count':len(rows),
   'visited':sum(r['visited'] for r in rows),'pruned':sum(r['pruned'] for r in rows),
   'reports':rows,'scope':'coarse terminal-angle entry, NOT the local Gerver shape neighborhood',
   'python':platform.python_version(),'source_hashes':h}
def main():
 p=argparse.ArgumentParser();p.add_argument('--first',type=int,default=60);p.add_argument('--last',type=int,default=80)
 p.add_argument('--nodes',type=int,default=2000);p.add_argument('--directory',default='entry-receipts')
 p.add_argument('--verify-only',action='store_true');args=p.parse_args()
 if not 60<=args.first<=args.last<=80:raise ValueError('slab range outside the stated cover')
 d=Path(args.directory);d.mkdir(parents=True,exist_ok=True)
 if not args.verify_only:
  for i in range(args.first,args.last):
   print('SLAB',i,flush=True)
   r=TerminalPinnedSearch(Q(i,100),Q(i+1,100)).run(args.nodes)
   r['source_hashes']=hashes();r['target']='2219/1000'
   (d/f'slab-{i:02d}.json').write_text(json.dumps(r,indent=2)+'\n')
 if args.verify_only or (args.first==60 and args.last==80):
  r=collect(d);Path('entry-sweep.json').write_text(json.dumps(r,indent=2)+'\n')
  print(json.dumps({k:v for k,v in r.items() if k!='reports'},indent=2))
if __name__=='__main__':main()
