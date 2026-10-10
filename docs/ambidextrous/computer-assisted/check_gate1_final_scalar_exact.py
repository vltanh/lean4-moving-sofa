#!/usr/bin/env python3
"""Exact arithmetic certificates for the final Gate 1 scalar exclusions.

Python standard library only. All computations use Fraction; there are no
floating-point evaluations, sampled angles, searches, or optimizations.
This verifies the stated arithmetic, not the geometric prerequisites.
"""

from fractions import Fraction as F


count = 0


def require(label, condition):
    global count
    if not condition:
        raise AssertionError(label)
    count += 1


def equal(label, actual, expected):
    require(f"{label}: {actual} != {expected}", actual == expected)


# Radical enclosures used in FR and its inherited FT clipping check.
r_lo, r_hi = F(140, 99), F(99, 70)
c_lo, c_hi = F(923, 1000), F(231, 250)
require("sqrt(2) enclosure", r_lo**2 < 2 < r_hi**2)
# cos(pi/8)^2=(2+sqrt(2))/4, with all quantities positive.
require("cos(pi/8) lower", c_lo**2 < (2 + r_lo) / 4)
require("cos(pi/8) upper", (2 + r_hi) / 4 < c_hi**2)
equal("k lower endpoint", r_lo - 1, F(41, 99))
equal("k upper endpoint", r_hi - 1, F(29, 70))
require("k>2/5, A<3/5, gamma<3/10", r_lo > F(7, 5))
require("b*A=8-5sqrt(2)>3/4", 8 - 5 * r_hi > F(3, 4))
clip = -F(41, 198) + F(8, 5) * F(71, 100) / 9 + F(11, 48) * F(17, 50)
equal("inherited FT21 clipping bound", clip, -F(129, 44000))
require("critical point is unclipped", clip < 0)

# FR4--FR5: the first-good strip C<=73/100, 1/20<=h<=21/100.
require("H(73/100)<8/25", 1 - F(73, 100)**2 > F(17, 25)**2)
require("H(37/50)<1/3", 1 - F(37, 50)**2 > F(2, 3)**2)
d = F(219, 100)
radius = d**2 + F(7, 16)**2
equal("FR4 radius", radius, F(798001, 160000))
equal("FR4 gap", 5 - radius, F(1999, 160000))
require("FR4 strict radius condition", radius < 5)
for height, root_lower, expected in (
    (F(1, 20), F(31, 100), F(634973, 160000)),
    (F(21, 100), F(61, 100), F(553949, 160000)),
):
    require(f"FR5 root lower at h={height}", root_lower**2 < height * (2 - height))
    B = -F(13, 50) + F(5, 4) * height
    value = d**2 + B**2 + B * (1 - height) - d * root_lower
    equal(f"FR5 endpoint at h={height}", value, expected)
    require(f"FR5 strict energy condition at h={height}", value < 4)

# FR11--FR13, including critical-point and monotonicity enclosures.
s0_lo = F(219, 100) * r_lo + F(127, 100) - 4 * c_hi
s0_hi = F(219, 100) * r_hi + F(127, 100) - 4 * c_lo
require("s0 enclosure", F(2, 3) < s0_lo < s0_hi < F(7, 10))
D_lo = F(1, 2) - 2 * c_hi + r_lo
D_hi = F(1, 2) - 2 * c_lo + r_hi
equal("D upper enclosure", D_hi, F(239, 3500))
require("both floor positive parts positive", D_lo > F(21, 400))
require("positive support bracket", s0_lo - F(3, 5) * F(21, 400) > 0)
ell_upper = -F(1, 5) + F(3, 5) * F(7, 10) / 9 + F(3, 10) * (D_hi + F(1, 8))
require("linear coefficient<-9/100", ell_upper < -F(9, 100))
equal("quadratic coefficient upper endpoint", -F(1, 8) + F(5, 8) * F(3, 10), F(1, 16))
require("strict decrease on full tilt interval", -F(9, 100) + F(21, 100) / 8 < 0)
bracket_lower = s0_lo - F(3, 400)
equal("FR11 lower bracket", bracket_lower, F(43789, 66000))
equal("FR11 bracket gap", bracket_lower - F(53, 80), F(4, 4125))
require("FR11 positive gap", bracket_lower > F(53, 80))
require("FR12 first floor bound", D_hi - F(1, 80) < F(7, 125))
require("FR12 second floor bound", D_hi + F(1, 12) + F(3, 80) < F(19, 100))
floor_upper = F(3, 10) * (F(7, 125)**2 + F(19, 100)**2)
equal("FR12 floor fraction", floor_upper, F(29427, 2500000))
require("FR12 floor<3/250", floor_upper < F(3, 250))
fr13 = (F(123, 50) * F(29, 70) - F(529, 5000) - F(41, 3960)
        - F(1, 3200) - F(2, 9) * F(53, 80)**2 + F(3, 250))
equal("FR13 final bound", fr13, F(7550393, 9240000))
equal("FR13 final gap", F(41, 50) - fr13, F(26407, 9240000))
require("FR13 strict exclusion", fr13 < F(41, 50))

# SH4--SH6 and SH12--SH14: endpoint constants and norm tangents.
require("K<10/9", 81 * 1369 < 100 * 1131)
require("H(37/50)<33/100", 1 - F(37, 50)**2 > F(67, 100)**2)
require("excess height bound", F(19, 100) < F(7, 36))
equal("excess parabola terminal value", F(7, 36) - F(1, 3) / 2 - F(1, 3)**2 / 4, 0)
equal("excess parabola integral", F(7, 36) / 3 - F(1, 3)**2 / 4 - F(1, 3)**3 / 12, F(11, 324))
equal("SH6 moment bound", F(11, 15) * F(11, 324), F(121, 4860))
equal("SH6 moment gap", F(1, 40) - F(121, 4860), F(1, 9720))
lam_lo, lam_hi = F(8086, 10000), F(8087, 10000)
m_hi, a_lo = F(1471, 10000), F(956, 10000)
require("SH12 lambda enclosure", lam_lo**2 < F(17, 26) < lam_hi**2)
require("SH12 m enclosure", F(9, 416) < m_hi**2)
require("SH12 a enclosure", (1 - lam_hi) / 2 > a_lo)
z_coefficient = m_hi + F(1, 80) - a_lo * F(9, 10)
equal("SH13 z coefficient", z_coefficient, F(1839, 25000))
equal("SH13 h coefficient", F(37, 50) + m_hi, F(8871, 10000))
require("SH14 sqrt(17) lower", F(4123, 1000)**2 < 17)
require("SH14 sqrt(26) lower", F(5099, 1000)**2 < 26)
S0_lower = (2 * F(4123, 1000) + F(5099, 1000)) / 6
equal("SH14 S0 lower", S0_lower, F(2669, 1200))
G0 = F(22199, 10000)
equal("SH14 gap", S0_lower - G0, F(16, 3750))
require("SH14 strict ordinary-area contradiction", S0_lower > G0)

# SH18: exact positivity of the decreasing normalized cubic.
A, D, Q0 = F(11591, 30000), F(8871, 10000), F(84261, 640000)
equal("SH17 linear coefficient", (2 + lam_lo) / 6 - z_coefficient * F(10, 9), A)
equal("SH17 square coefficient", (2 + lam_hi) * F(3, 64), Q0)
hmax, kap, smax = F(509, 10000), F(10000, 19491), F(63, 200)
equal("SH18 inverse height coefficient", 1 / (2 - hmax), kap)
equal("SH18 smax square gap", smax**2 - hmax * (2 - hmax), F(1581, 100000000))
require("SH18 positive coefficients, hence decreasing bracket", D > 0 and Q0 > 0 and kap > 0)
cubic = A - (D * kap + F(5, 9)) * smax - Q0 * smax * (F(10, 9) + kap * smax)**2
equal("SH18 exact cubic endpoint", cubic, F(11102231813, 13507522880000))
require("SH18 strict positivity", cubic > 0)

# SH20--SH24: the complementary radius-failure certificate.
require("SH20 sqrt(19)/6>29/40", F(19, 36) > F(29, 40)**2)
require("SH20 C0<11/16", F(17, 36) < F(11, 16)**2)
require("SH20 2+lambda>14/5", 2 + lam_lo > F(14, 5))
equal("SH21 radius residual", 5 - 9 * F(37, 50)**2, F(179, 2500))
equal("SH21 radius gap", F(179, 2500) - F(16, 225), F(11, 22500))
require("SH22 small-h root", F(1, 40) * F(79, 40) < F(9, 40)**2)
equal("SH22 small-h z bound", F(10, 9) * F(9, 40), F(1, 4))
equal("SH22 other z bound", (F(7, 30) - F(1, 32)) * F(4, 3), F(97, 360))
require("SH22 z<27/100", F(97, 360) < F(27, 100))
anchor = S0_lower + F(14, 5) * (F(29, 40) - F(11, 16))
equal("SH23 tangent anchor", anchor, F(559, 240))
sh23 = anchor - D * hmax - (z_coefficient + smax / 2) * F(27, 100)
equal("SH23 final lower bound", sh23, F(666488123, 300000000))
equal("SH24 final gap", sh23 - G0, F(518123, 300000000))
require("SH24 strict ordinary-area contradiction", sh23 > G0)

print(f"PASS: {count} exact Fraction checks (FR4/FR5/FR11-FR13; SH12/SH14/SH18/SH23-SH24 and required enclosures).")
