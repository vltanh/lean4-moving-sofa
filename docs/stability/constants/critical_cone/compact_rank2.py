"""The same two penalties with coincident piece contributions combined first.

This is an algebraic enclosure improvement, not a different relaxation.
"""
from certify_critical_rank2 import Model,iv,Z,ONE
class CompactModel(Model):
 def __post_init__(self):
  super().__post_init__()
  p,v,b,c,T,A=self.phi,self.v,self.b,self.c,self.T,self.A
  C=ONE/iv.cos(c)
  a0=A*(A-iv.sin(p))-C*(A-iv.sin(c))
  a1=A*A-C*(A-iv.sin(c))
  self.VB=[(1,p,c,A,Z),(1,c,b,A-C,Z),(2,b,v,A-C,Z),
   (3,v,v+p,a0,Z),(3,v+p,v+c,a1,A),(3,v+c,T,A*(A-C),A-C)]
  d0=self.DD*iv.sin(p)-iv.sin(self.d)/iv.sin(T-self.d)
  self.VD=[(3,v,self.d,d0,Z),(3,self.d,T,self.DD*iv.sin(p),Z)]
  self.G11=self.inner(self.VB,self.VB);self.G12=self.inner(self.VB,self.VD);self.G22=self.inner(self.VD,self.VD)
  self.S11=self.DB+self.G11;self.S22=self.DD+self.G22;self.S12=self.G12
  self.det=self.S11*self.S22-self.S12**2
  assert self.det.a>0
  self.w01=self.inner(self.P0,self.VB);self.w02=self.inner(self.P0,self.VD)
