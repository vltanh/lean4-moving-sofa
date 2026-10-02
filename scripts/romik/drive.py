from gen import *

def taylor_cos(x, n):  # sum_{i<n} (-1)^i x^(2i)/(2i)!
    return sum(Fr((-1) ** i) * x ** (2 * i) / math.factorial(2 * i) for i in range(n))
def taylor_sin(x, n):
    return sum(Fr((-1) ** i) * x ** (2 * i + 1) / math.factorial(2 * i + 1) for i in range(n))

def cos_lo(x, k, dig): return rnd_down(taylor_cos(x, 2 * k), dig)
def cos_hi(x, k, dig): return rnd_up(taylor_cos(x, 2 * k + 1), dig)
def sin_lo(x, k, dig): return rnd_down(taylor_sin(x, 2 * k), dig)
def sin_hi(x, k, dig): return rnd_up(taylor_sin(x, 2 * k + 1), dig)

PI_LO6, PI_HI6 = Fr('3.141592'), Fr('3.141593')
PI_LO20, PI_HI20 = Fr('3.14159265358979323846'), Fr('3.14159265358979323847')

BOXD = 10
box_atoms = {
    'φ': (Fr('0.039'), Fr('0.04')),
    'θ': (Fr('0.68'), Fr('0.69')),
    'c': (cos_lo(Fr('0.04'), 3, BOXD), Fr(1)),
    's': (sin_lo(Fr('0.039'), 3, BOXD), sin_hi(Fr('0.04'), 3, BOXD)),
    'C': (cos_lo(Fr('0.69'), 3, BOXD), cos_hi(Fr('0.68'), 3, BOXD)),
    'S': (sin_lo(Fr('0.68'), 3, BOXD), sin_hi(Fr('0.69'), 3, BOXD)),
    'p': (PI_LO6, PI_HI6),
}

PHI0, THETA0 = Fr('0.0391773648'), Fr('0.6813015094')
Z0D = 22
z0_atoms = {
    'φ': (PHI0, PHI0),
    'θ': (THETA0, THETA0),
    'c': (cos_lo(PHI0, 2, Z0D), cos_hi(PHI0, 2, Z0D)),
    's': (sin_lo(PHI0, 2, Z0D), sin_hi(PHI0, 2, Z0D)),
    'C': (cos_lo(THETA0, 4, Z0D), cos_hi(THETA0, 4, Z0D)),
    'S': (sin_lo(THETA0, 4, Z0D), sin_hi(THETA0, 4, Z0D)),
    'p': (PI_LO20, PI_HI20),
}

R = Fr(1, 10 ** 10)
TD = 16
tiny_atoms = {
    'φ': (PHI0 - R, PHI0 + R),
    'θ': (THETA0 - R, THETA0 + R),
    'c': (z0_atoms['c'][0] - R, z0_atoms['c'][1] + R),
    's': (z0_atoms['s'][0] - R, z0_atoms['s'][1] + R),
    'C': (z0_atoms['C'][0] - R, z0_atoms['C'][1] + R),
    'S': (z0_atoms['S'][0] - R, z0_atoms['S'][1] + R),
    'p': (PI_LO20, PI_HI20),
}

if __name__ == '__main__':
    for k, v in box_atoms.items(): print('box', k, fmt(v[0]), fmt(v[1]))
    box_names = ['rom_K', 'rom_Kθ', 'rom_D', 'rom_Nb', 'rom_U1', 'rom_V1', 'rom_U2', 'rom_V2',
                 'rom_Dφ', 'rom_Dθ', 'rom_Nbφ', 'rom_Nbθ', 'rom_U1φ', 'rom_U1θ', 'rom_V1φ', 'rom_V1θ',
                 'rom_U2φ', 'rom_U2θ', 'rom_V2φ', 'rom_V2θ', 'rom_H1φ', 'rom_H1θ', 'rom_H2φ', 'rom_H2θ',
                 'rom_G1φ', 'rom_G1θ', 'rom_G2φ', 'rom_G2θ']
    res, txt = gen_regime('box', box_names, box_atoms, BOXD)
    for n in box_names: print(n, [float(x) for x in res[n]])
    z0_names = ['rom_K', 'rom_D', 'rom_Nb', 'rom_U1', 'rom_V1', 'rom_U2', 'rom_V2', 'rom_H1', 'rom_H2', 'rom_MH1', 'rom_MH2']
    res0, txt0 = gen_regime('z0', z0_names, z0_atoms, Z0D)
    for n in z0_names: print(n, [float(x) for x in res0[n]])
    tiny_names = ['rom_K', 'rom_D', 'rom_β₀', 'rom_N', 'rom_a₁', 'rom_b₁', 'rom_b₂', 'rom_c₁', 'rom_Δ₁', 'rom_Δ₂',
                  'rom_κ₂₁', 'rom_κ₂₂', 'rom_κ₃₁', 'rom_κ₃₂', 'rom_κ₄₁', 'rom_κ₅₁']
    rest, txtt = gen_regime('tiny', tiny_names, tiny_atoms, TD)
    for n in tiny_names: print(n, [mp.nstr(mp.mpf(x.numerator) / x.denominator, 15) for x in rest[n]], float(rest[n][1] - rest[n][0]))
