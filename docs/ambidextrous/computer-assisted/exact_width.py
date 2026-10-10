"""Exact certificate kernel for a four-position, width-two relaxation.

Only integer/Fraction arithmetic is used in proof decisions. See THEORY.md.
The optional Numba wrapper executes these same bounded int64 instructions.
"""
from fractions import Fraction as F
from math import lcm

D = 288600  # lcm(3, 4, 600, 481)
GRID = 1 << 14
MAX_DEPTH_PER_COORDINATE = 13
DIRECTIONS = ((4, 3, 5), (481, 600, 769))
TOP = (11, 3, 1, 9, 17, 16, 9, 8, 16, 1, 10, 2)
BOTTOM = (15, 7, 0, 5, 13, 12, 5, 4, 12, 0, 14, 6)


def rational_lines():
    """y=a*x+b(t), with normalized placement coordinates t in [0,1]^8."""
    zero = [F(0)] * 9
    one = zero.copy(); one[0] = F(1)
    lines = [(F(0), zero), (F(0), one)]
    for j, (cn, sn, dn) in enumerate(DIRECTIONS):
        c, s = F(cn, dn), F(sn, dn)
        A = zero.copy(); A[0] = s; A[1+2*j] = 2*c
        B = zero.copy(); B[2+2*j] = c
        C = zero.copy(); C[0] = s; C[5+2*j] = 2*c
        E = zero.copy(); E[6+2*j] = c
        def aff(row, multiplier, constant):
            ans = [multiplier*x for x in row]; ans[0] += constant
            return ans
        lines += [(-c/s, aff(A, 1/s, 0)), (s/c, aff(B, 1/c, 0)),
                  (-c/s, aff(A, 1/s, -1/s)), (s/c, aff(B, 1/c, -1/c)),
                  (c/s, aff(C, -1/s, 1)), (-s/c, aff(E, -1/c, 1)),
                  (c/s, aff(C, -1/s, 1+1/s)), (-s/c, aff(E, -1/c, 1+1/c))]
    return lines


def solve(matrix, vector):
    """Exact Gaussian elimination; singular input is rejected."""
    n = len(vector)
    a = [[F(x) for x in row]+[F(v)] for row, v in zip(matrix, vector)]
    for j in range(n):
        pivot = next((i for i in range(j, n) if a[i][j]), None)
        if pivot is None: raise ValueError('singular certificate matrix')
        a[j], a[pivot] = a[pivot], a[j]
        p = a[j][j]; a[j] = [x/p for x in a[j]]
        for i in range(n):
            if i != j:
                p = a[i][j]; a[i] = [x-p*y for x, y in zip(a[i], a[j])]
    return [row[-1] for row in a]


def positive_ldl(matrix):
    """Check positive definiteness by an exact LDL decomposition."""
    n = len(matrix); L = [[F(0)]*n for _ in range(n)]; pivots = []
    for i in range(n):
        if any(matrix[i][j] != matrix[j][i] for j in range(n)):
            raise ValueError('not symmetric')
        d = matrix[i][i]-sum(L[i][k]**2*pivots[k] for k in range(i))
        if d <= 0: raise ValueError('nonpositive LDL pivot')
        pivots.append(d); L[i][i] = F(1)
        for j in range(i+1, n):
            L[j][i] = (matrix[j][i]-sum(L[j][k]*L[i][k]*pivots[k] for k in range(i)))/d
    return pivots


def template_certificate():
    """Derive, rather than trust, the fixed polynomial and all validity rows."""
    lines = rational_lines(); zero = [F(0)]*9
    end = zero.copy(); end[0] = 2
    matrix = [[F(0)]*9 for _ in range(9)]; conditions = []
    companions = {8:9,9:8,16:17,17:16,4:5,5:4,12:13,13:12}
    def sub(a,b): return [x-y for x,y in zip(a,b)]
    for sequence, sign in ((TOP, 1), (BOTTOM, -1)):
        endpoints = [zero]
        for i,j in zip(sequence,sequence[1:]):
            ai,bi=lines[i]; aj,bj=lines[j]
            if ai == aj: raise ValueError('parallel chart switch')
            endpoints.append([x/(ai-aj) for x in sub(bj,bi)])
        endpoints.append(end)
        for t,left,right in zip(sequence,endpoints,endpoints[1:]):
            a,b=lines[t]; length=sub(right,left); conditions.append(length)
            for endpoint in (left,right):
                value=[a*x+y for x,y in zip(endpoint,b)];value[0]-=F(1,2)
                conditions.append([sign*x for x in value])
                if t in companions:
                    ao,bo=lines[companions[t]]
                    conditions.append([sign*((a-ao)*x+y-z) for x,y,z in zip(endpoint,b,bo)])
            for i in range(9):
                for j in range(9):
                    matrix[i][j] += sign*(a*(right[i]*right[j]-left[i]*left[j])+b[i]*length[j]+length[i]*b[j])/2
    negative_hessian=[[-2*matrix[i+1][j+1] for j in range(8)] for i in range(8)]
    pivots=positive_ldl(negative_hessian)
    optimum=solve(negative_hessian,[2*matrix[0][j+1] for j in range(8)])
    v=[F(1)]+optimum
    maximum=sum(v[i]*matrix[i][j]*v[j] for i in range(9) for j in range(9))
    if maximum >= F(411,250): raise ValueError('template is not below target')
    integer_rows=[]
    for row in conditions:
        den=lcm(*(x.denominator for x in row))
        integer_rows.append([int(x*den) for x in row])
    return integer_rows, maximum, pivots, optimum


def exact_area_bound(indices, depths):
    """Rational upper bound represented by integer numerator and denominator.

    Each coordinate ranges from indices[i]/2**depths[i] to its successor.
    Crossings are fenced on a fixed dyadic spatial grid. Large grid intervals
    have exactly affine fiber heights; unit grid intervals receive a proven
    Lipschitz error. No floating-point sorting or rounding enters this bound.
    """
    q=1 << max(depths)
    a=[0,0];b=[0,D*q]
    for j,(cn,sn,dn) in enumerate(DIRECTIONS):
        vals=[]
        for i in (2*j,2*j+1,4+2*j,5+2*j):
            factor=q//(1 << depths[i]);lo=indices[i]*factor;hi=lo+factor
            if i%2 == 0: vals.append((sn*q+2*cn*lo,sn*q+2*cn*hi))
            else: vals.append((cn*lo,cn*hi))
        (al,ah),(bl,bh),(cl,ch),(el,eh)=vals
        ac=D*cn//sn;as_=D*sn//cn
        a += [-ac,as_,-ac,as_,ac,-as_,ac,-as_]
        b += [D//sn*ah,D//cn*bh,D//sn*(al-dn*q),D//cn*(bl-dn*q),
              D*q-D//sn*ch,D*q-D//cn*eh,
              D*q-D//sn*(cl-dn*q),D*q-D//cn*(el-dn*q)]
    knots={0,2*GRID}
    for i in range(18):
        for j in range(i+1,18):
            num=b[j]-b[i];den=q*(a[i]-a[j])
            if den < 0: num=-num;den=-den
            if den and 0 < num < 2*den:
                fl,rem=divmod(num*GRID,den)
                knots.add(fl);knots.add(fl+int(rem != 0))
    knots=sorted(knots)
    unit=D*q*GRID
    def height(x):
        y=[a[i]*q*x+b[i]*GRID for i in range(18)]
        low=0;up=unit
        for j in range(2):
            i=2+8*j
            up=min(up,y[i],y[i+1]);low=max(low,min(y[i+2],y[i+3]))
            low=max(low,y[i+4],y[i+5]);up=min(up,max(y[i+6],y[i+7]))
        return max(0,up-low)
    previous=knots[0];hp=height(previous);total=0;small=0
    for x in knots[1:]:
        hx=height(x);width=x-previous
        total += (hp+hx)*width
        small += int(width == 1)
        previous=x;hp=hx
    numerator=total+(4*D*q//3)*small
    denominator=2*D*q*GRID*GRID
    return numerator,denominator


def verify_template_box(indices,depths,rows):
    q=1 << max(depths)
    for row in rows:
        total=row[0]*q
        for i in range(8):
            coordinate=indices[i]+int(row[i+1]<0)
            total += row[i+1]*coordinate*(q//(1 << depths[i]))
        if total < 0: return False
    return True


def next_axis(depths):
    # Initial weighted lengths: 8/3,1,481/300,1, repeated.
    ns=(8,1,481,1,8,1,481,1);ds=(3,1,300,1,3,1,300,1)
    best=0
    for i in range(1,8):
        if ns[i]*ds[best]*(1 << depths[best]) > ns[best]*ds[i]*(1 << depths[i]):best=i
    return best

if __name__=='__main__':
    rows,maximum,pivots,point=template_certificate()
    print('template maximum:',maximum, float(maximum))
    print('maximum row coefficient bits:',max(abs(x).bit_length() for r in rows for x in r))
    print('LDL pivots positive:',all(p>0 for p in pivots))
    print('root area bound:',exact_area_bound([0]*8,[0]*8))
