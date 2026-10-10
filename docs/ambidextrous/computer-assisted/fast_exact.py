"""Checked-int64 accelerator for the exact rational spatial upper bound."""
import numpy as np
from numba import njit
from exact_width import D,GRID

@njit(cache=True)
def area_bound_int(indices,depths):
 q=1 << np.max(depths)
 if q > 8192: raise ValueError('int64 guard: coordinate depth exceeds 13')
 a=np.empty(18,np.int64);b=np.empty(18,np.int64)
 a[0]=a[1]=0;b[0]=0;b[1]=D*q
 for j in range(2):
  if j==0:cn,sn,dn=4,3,5
  else:cn,sn,dn=481,600,769
  vals=np.empty((4,2),np.int64)
  for m in range(4):
   i=(2*j+m) if m<2 else (4+2*j+m-2)
   factor=q//(1 << depths[i]);lo=indices[i]*factor;hi=lo+factor
   if i%2==0:vals[m,0]=sn*q+2*cn*lo;vals[m,1]=sn*q+2*cn*hi
   else:vals[m,0]=cn*lo;vals[m,1]=cn*hi
  al,ah=vals[0,0],vals[0,1];bl,bh=vals[1,0],vals[1,1]
  cl,ch=vals[2,0],vals[2,1];el,eh=vals[3,0],vals[3,1]
  ac=D*cn//sn;as_=D*sn//cn;i=2+8*j
  a[i]=-ac;a[i+1]=as_;a[i+2]=-ac;a[i+3]=as_
  a[i+4]=ac;a[i+5]=-as_;a[i+6]=ac;a[i+7]=-as_
  b[i]=D//sn*ah;b[i+1]=D//cn*bh;b[i+2]=D//sn*(al-dn*q);b[i+3]=D//cn*(bl-dn*q)
  b[i+4]=D*q-D//sn*ch;b[i+5]=D*q-D//cn*eh
  b[i+6]=D*q-D//sn*(cl-dn*q);b[i+7]=D*q-D//cn*(el-dn*q)
 knots=np.empty(308,np.int64);knots[0]=0;knots[1]=2*GRID;n=2
 for i in range(18):
  for j in range(i+1,18):
   num=b[j]-b[i];den=q*(a[i]-a[j])
   if den<0:num=-num;den=-den
   if den!=0 and 0<num<2*den:
    val=num*GRID;fl=val//den;rem=val%den
    knots[n]=fl;knots[n+1]=fl+int(rem!=0);n+=2
 knots=np.sort(knots[:n]);prev=knots[0];hp=height_int(prev,a,b,q);total=0;small=0
 for i in range(1,n):
  x=knots[i]
  if x==prev:continue
  hx=height_int(x,a,b,q);width=x-prev
  total+=(hp+hx)*width;small+=int(width==1);prev=x;hp=hx
 return total+(4*D*q//3)*small,2*D*q*GRID*GRID

@njit(cache=True)
def height_int(x,a,b,q):
 low=0;up=D*q*GRID
 for j in range(2):
  i=2+8*j
  y0=a[i]*q*x+b[i]*GRID;y1=a[i+1]*q*x+b[i+1]*GRID
  y2=a[i+2]*q*x+b[i+2]*GRID;y3=a[i+3]*q*x+b[i+3]*GRID
  y4=a[i+4]*q*x+b[i+4]*GRID;y5=a[i+5]*q*x+b[i+5]*GRID
  y6=a[i+6]*q*x+b[i+6]*GRID;y7=a[i+7]*q*x+b[i+7]*GRID
  up=min(up,y0,y1);low=max(low,min(y2,y3));low=max(low,y4,y5);up=min(up,max(y6,y7))
 return max(0,up-low)

@njit(cache=True)
def template_box_int(indices,depths,rows):
 q=1 << np.max(depths)
 if q>8192:raise ValueError('int64 guard')
 for row in rows:
  total=row[0]*q
  for i in range(8):total+=row[i+1]*(indices[i]+int(row[i+1]<0))*(q//(1 << depths[i]))
  if total<0:return False
 return True

@njit(cache=True)
def axis_int(depths):
 ns=(8,1,481,1,8,1,481,1);ds=(3,1,300,1,3,1,300,1);best=0
 for i in range(1,8):
  if ns[i]*ds[best]*(1 << depths[best]) > ns[best]*ds[i]*(1 << depths[i]):best=i
 return best

@njit(cache=True)
def below_target(num,den):
 # floor(411*den/250), evaluated without the overflowing multiplication.
 threshold=den+(den//250)*161+((den%250)*161)//250
 return num<=threshold
