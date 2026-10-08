"""Exact depth-first covering search; an unfinished tree is NOT a theorem."""
import argparse,hashlib,json,pickle,time
from pathlib import Path
import numpy as np
from exact_width import template_certificate,MAX_DEPTH_PER_COORDINATE
from fast_exact import area_bound_int,template_box_int,axis_int,below_target


def run(directory: Path,budget: int,resume: bool=False):
 directory.mkdir(parents=True,exist_ok=True)
 rows,maximum,pivots,opt=template_certificate(); rows=np.array(rows,dtype=np.int64)
 assert int(np.max(abs(rows))) < 2**31
 statefile=directory/'state.pkl';treefile=directory/'tree.bin'
 if resume:
  with statefile.open('rb') as f:stack,stats=pickle.load(f)
  if treefile.stat().st_size != stats['visited']:raise ValueError('tree/checkpoint mismatch')
 else:
  if statefile.exists() or treefile.exists():raise ValueError('refusing to overwrite a run')
  stack=[(np.zeros(8,np.int64),np.zeros(8,np.int64))]
  stats={'visited':0,'splits':0,'area_leaves':0,'template_leaves':0,'unresolved_depth':0,'seconds':0.}
 start=time.time();limit=stats['visited']+budget
 with treefile.open('ab') as f:
  while stack and stats['visited']<limit:
   ids,dep=stack.pop();stats['visited']+=1
   if template_box_int(ids,dep,rows):f.write(b'\x02');stats['template_leaves']+=1
   else:
    num,den=area_bound_int(ids,dep)
    if below_target(num,den):f.write(b'\x01');stats['area_leaves']+=1
    else:
     axis=axis_int(dep)
     if dep[axis]>=MAX_DEPTH_PER_COORDINATE:
      f.write(b'\x03');stats['unresolved_depth']+=1
     else:
      f.write(b'\x00');stats['splits']+=1
      d=dep.copy();d[axis]+=1;l=ids.copy();r=ids.copy();l[axis]*=2;r[axis]=l[axis]+1
      stack.append((r,d.copy()));stack.append((l,d))
   if stats['visited']%200000==0:print('visited',stats['visited'],'stack',len(stack),'elapsed',time.time()-start,flush=True)
 stats['seconds']+=time.time()-start
 stats['open_stack']=len(stack);stats['complete']=not stack and stats['unresolved_depth']==0
 stats['target']='411/250';stats['template_maximum']=str(maximum)
 with statefile.open('wb') as f:pickle.dump((stack,stats),f)
 (directory/'search_summary.json').write_text(json.dumps(stats,indent=2)+'\n')
 print(json.dumps(stats,indent=2),flush=True)
 if stats['complete']:
  print('TREE SHA256',hashlib.sha256(treefile.read_bytes()).hexdigest(),flush=True)
 return stats
if __name__=='__main__':
 ap=argparse.ArgumentParser();ap.add_argument('directory',type=Path);ap.add_argument('--budget',type=int,default=1000000);ap.add_argument('--resume',action='store_true');a=ap.parse_args()
 run(a.directory,a.budget,a.resume)
