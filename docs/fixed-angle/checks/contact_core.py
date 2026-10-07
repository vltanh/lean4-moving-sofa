"""Piecewise elementary shooting formulas; no ODE solver or compilation."""
from math import sin as fsin, cos as fcos

def sn(x):
    return x.sin() if hasattr(x, 'sin') else fsin(x)
def cs(x):
    return x.cos() if hasattr(x, 'cos') else fcos(x)

def arm_step(f, g, h, flags):
    C,B,D=flags
    if not C:
        ff=D/2+(f-D/2)*cs(h)+(g-B/2)*sn(h)
        gg=B/2-(f-D/2)*sn(h)+(g-B/2)*cs(h)
    elif B==D==0:
        ff,gg=f+h,g-h
    elif B==1 and D==0:
        ff,gg=f+g*h/2-h*h/4,g-h
    elif B==0 and D==1:
        ff,gg=f+h,g-f*h/2-h*h/4
    else:
        ff,gg=f*cs(h/2)+g*sn(h/2),g*cs(h/2)-f*sn(h/2)
    return ff,gg

def step(state,h,flags):
    f,g,p,d=state
    C,B,D=flags
    co,si=cs(h),sn(h)
    pp=p*co+d*si
    dd=-p*si+d*co
    if not C:
        pp+=B*(1-co)/2
        dd+=B*si/2
    elif B==D==0:
        pp+=(g-1)*(1-co)-(h-si)
        dd+=(g-1)*si-(1-co)
    elif B==1 and D==0:
        pp+=g*(1-co)/2-(h-si)/2
        dd+=g*si/2-(1-co)/2
    elif B==0 and D==1:
        pp+=(g-1)*(1-co)-f*(h-si)/2-(h*h-2+2*co)/4
        dd+=(g-1)*si-f*(1-co)/2-(h-si)/2
    else:
        pp+=2*g*(cs(h/2)-co)/3-2*f*(sn(h/2)-si/2)/3
        dd+=2*g*(-sn(h/2)/2+si)/3-2*f*(cs(h/2)/2-co/2)/3
    ff,gg=arm_step(f,g,h,flags)
    return ff,gg,pp,dd

def events(w,phi,b,c):
    return {'0':w*0,'a':phi,'b':b,'c':c,'dc':w-c,'db':w-b,
            'za':w-phi,'m':w/2,'w':w}

def flags_between(order,index):
    left=set(order[:index+1])
    return (int('a' in left and 'za' not in left),
            int('b' in left and 'c' not in left),
            int('dc' in left and 'db' not in left))

def shooting(w,phi,b,c,order,event_map=None):
    ev=events(w,phi,b,c) if event_map is None else event_map
    zero=w*0
    f0,g0=zero+1,zero
    f1,g1=zero+1,zero+1
    for j,(lo,hi) in enumerate(zip(order,order[1:])):
        if lo=='m': break
        h=ev[hi]-ev[lo]; flags=flags_between(order,j)
        f0,g0=arm_step(f0,g0,h,flags)
        f1,g1=arm_step(f1,g1,h,flags)
    init_g=-(f0-g0)/((f1-g1)-(f0-g0))
    state=(zero+1,init_g,zero,zero)
    states={'0':state}
    for j,(lo,hi) in enumerate(zip(order,order[1:])):
        state=step(state,ev[hi]-ev[lo],flags_between(order,j))
        states[hi]=state
    fm,gm,pm,dm=states['m']
    p0=(fm+dm-pm)/(cs(w/2)+sn(w/2))
    fa,ga,pa,da=states['a']
    fb,gb,pb,db=states['b']
    fc,gc,pc,dc=states['c']
    q=fa-1
    # pa=da=0: the first p-curvature vanishes before the core cut.
    rx=pb*cs(b)-db*sn(b)+2*sn((b+phi)/2)*sn((b-phi)/2)+q*sn(phi)
    ry=pb*sn(b)+db*cs(b)-sn(b)+sn(phi)-q*cs(phi)
    rz=(pc-1)*sn(c)+dc*cs(c)
    return [rx,ry,rz],p0,init_g,states

def float_order(w,phi,b,c):
    ev=events(w,phi,b,c)
    return sorted(ev,key=ev.get)

def residual(x,w):
    return shooting(w,*x,float_order(w,*x))[0]
