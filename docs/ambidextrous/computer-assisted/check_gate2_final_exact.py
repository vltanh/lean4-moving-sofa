#!/usr/bin/env python3
"""Fixed exact arithmetic checks for the Gate 2 written proof.

Run with Python 3; only the standard-library Fraction class is used.
These checks certify rational margins and squared radical comparisons.
They do not verify the continuum source, geometry, or motion arguments.
There is no angular sampling, numerical optimization, or search.
"""

from fractions import Fraction as F


CHECKS = []


def check(name, condition):
    assert condition, name
    CHECKS.append(name)


def eq(name, left, right):
    check(name, left == right)


def lt(name, left, right):
    check(name, left < right)


def cos_lower(x):
    # cos(x) >= this polynomial on [0,1], by the stated Taylor proof.
    return 1 - x * x / 2 + x**4 / 25


# Reference separation and the all-width terminal cutoff.
a = F(149, 500)
lt("reference cubic below its root", 4 * a**3 + 3 * a, 1)
reference_half_lower = (1 + 4 * a * a + a - a**3 / 3) / 2
eq("reference rational lower value", reference_half_lower,
   F(616648051, 750000000))
lt("AT bound below 0.822", F(5259, 6400), F(411, 500))
lt("0.822 below reference lower value", F(411, 500), reference_half_lower)
lt("sqrt2 below the reference comparison", 2, F(41, 25)**2)

# WC's joint floor payment and final scalar certificate.
lt("WC support-floor constant", F(2, 3) - F(1846, 1000) + F(99, 70),
   F(47, 200))
eq("WC derivative constant", -F(1, 5) + F(71, 1500) + F(47, 500),
   -F(22, 375))
eq("WC derivative upper endpoint", -F(22, 375) + F(17, 50) / 60,
   -F(53, 1000))
lt("WC floor allowance", F(3, 10) * F(47, 200)**2, F(17, 1000))
wc_value = F(62, 25) * F(29, 70) - F(72, 625) \
    - F(2, 9) * F(703, 1000)**2 + F(17, 1000)
eq("WC final value", wc_value, F(25811237, 31500000))
eq("WC final strict gap", F(41, 50) - wc_value, F(18763, 31500000))

# MP's geometric localization and both scalar-average ranges.
lt("MP companion cutoff lies before terminal angle", 37**2 * 73, 325**2)
lt("MP sqrt2 upper", 2, F(99, 70)**2)
lt("MP coarse sqrt2 upper", 2, F(10, 7)**2)
lt("MP sqrt5 lower", F(11, 5)**2, 5)
lt("MP sqrt59 upper", 59, F(77, 10)**2)
lt("MP sqrt1001 lower", F(158, 5)**2, 1001)
eq("MP first-range low-width margin", F(70, 99) - F(2, 3), F(4, 99))
eq("MP first-range high-width margin", F(602, 495) - F(6, 5), F(8, 495))
lt("MP first-range margin pays common allowance", F(39, 4400), F(8, 495))
lt("MP rational angle majorant", F(9, 73), F(44, 125)**2)
lt("MP second-range first left endpoint", F(5, 16), F(8623, 27000))
lt("MP second-range first left radical", 1 - F(19, 20)**2, F(5, 16)**2)
lt("MP second-range first right endpoint", F(18127, 27000), F(84, 125))
lt("MP second-range first right radical", F(84, 125)**2 + F(37, 50)**2, 1)
eq("MP low-width second-range margin", F(189, 275) - F(2, 3), F(17, 825))
lt("MP second-range high-width left radical",
   1 - F(829, 1000)**2, F(15103, 27000)**2)
lt("MP second-range high-width right radical",
   F(24607, 27000)**2, 1 - F(411, 1000)**2)
eq("MP high-width average majorant",
   (F(829, 1000) - F(411, 1000)) / F(44, 125), F(19, 16))
eq("MP uniform strict margin", F(329, 275) - F(19, 16), F(39, 4400))
lt("MP low-width margin exceeds uniform one", F(39, 4400), F(17, 825))

# RX: cot(alpha) <= 1/8, with exact terminal impulse included.
lt("RX half-angle bound", 65, F(129, 16)**2)
lt("RX negative height bound", F(124, 125)**2, F(64, 65))
lt("RX initial Q positivity", 1, F(3, 2) * F(124, 125) - F(1, 8))
lt("RX impulse allowance", F(53, 100) / 256, F(1, 480))
lt("RX excess-domain lower d", F(1999, 1000)**2, 4 - F(1, 480))
lt("RX low-e crossing", F(3, 5),
   2 * F(1999, 1000) * F(4, 25) - F(4, 25)**2)
lt("RX low-e energy", F(1801, 800)**2 + F(1, 480), F(451, 200)**2)
lt("RX low-e duration", F(101, 50), F(57, 40)**2)
lt("RX low-e end", F(4, 25) + F(17, 40), F(18, 25))
rx_d, rx_e = F(1801, 800), F(3, 4)
rx_z = rx_d**2 - rx_e * (1 - rx_e) + F(1, 480)
lt("RX positive crossing", 2 * rx_e,
   2 * rx_d * F(109, 300) - F(109, 300)**2)
lt("RX positive energy", rx_z, F(221, 100)**2)
lt("RX positive duration", 4 * F(221, 100) - 7, F(407, 300)**2)
eq("RX positive end", F(109, 300) + F(107, 300), F(18, 25))
rx_d, rx_e = F(111, 50), F(19, 25)
rx_z = rx_d**2 - rx_e * (1 - rx_e) + F(1, 480)
lt("RX negative crossing", 2 * rx_e,
   2 * rx_d * F(3, 8) - F(3, 8)**2)
lt("RX negative energy", rx_z, F(109, 50)**2)
lt("RX negative duration", 4 * F(109, 50) - 7, F(21, 16)**2)
lt("RX negative end", F(3, 8) + F(5, 16), F(18, 25))
lt("RX cosine separation", F(37, 50), cos_lower(F(18, 25)))

# AC: the entire complementary angle interval, all middle signs.
lt("AC sine lower bound", F(14, 15)**2, F(64, 73))
lt("AC half-angle bound", 73, F(94, 11)**2)
x = F(3, 8)
lt("AC terminal gap bound", x - x**3 / 3 + x**5 / 5, F(9, 25))
lt("AC sqrt73 lower", F(17, 2)**2, 73)
lt("AC ordinary endpoint box", F(37, 50)**2, F(5, 9))
eq("AC outgoing endpoint upper", F(111, 200) - F(1, 32), F(419, 800))
lt("AC positive pressure", F(1, 2) + F(3, 4) * F(419, 800), F(179, 200))
lt("AC positive width parameter", F(111, 50) + F(1, 11), F(2311, 1000))
eq("AC negative pressure upper", F(1, 2) + F(1, 12) + F(333, 800),
   F(2399, 2400))
lt("AC negative pressure below one", F(2399, 2400), 1)
eq("AC unused-gap Q lower", F(3, 2) * F(14, 15) - F(3, 8), F(41, 40))
lt("AC impulse allowance", F(4, 121), F(1, 30))
lt("AC universal excess energy", F(2311, 1000)**2 + F(1, 30), F(58, 25)**2)
lt("AC universal excess duration", 4 * F(58, 25) - 7, F(38, 25)**2)
eq("AC linear envelope factor", (1 + F(13, 25)) / 2, F(19, 25))
lt("AC pre-impulse endpoint", F(9, 25) + F(13, 25), F(91, 100))
lt("AC W_d radical comparison", F(119, 59), F(9, 4))
lt("AC W_d positive bound", 0, -F(1, 2) + F(180, 217))
lt("AC clipped-crossing time bound", F(59, 30)**2, F(119, 30))
ac_d, ac_e = F(2311, 1000), F(179, 200)
ac_z = ac_d**2 - ac_e * (1 - ac_e) + F(1, 30)
eq("AC positive time squared margin",
   2 * ac_d * F(107, 250) - F(107, 250)**2 - 2 * ac_e, F(629, 125000))
eq("AC positive energy squared margin", F(2299, 1000)**2 - ac_z, F(3193, 600000))
eq("AC positive duration squared margin",
   F(741, 500)**2 - (4 * F(2299, 1000) - 7), F(81, 250000))
eq("AC positive episode endpoint", F(107, 250) + F(241, 500), F(91, 100))
ac_d = F(111, 50)
eq("AC negative time squared margin",
   2 * ac_d * F(51, 100) - F(51, 100)**2 - 2, F(43, 10000))
eq("AC negative energy squared margin", F(223, 100)**2 - ac_d**2 - F(1, 30),
   F(67, 6000))
eq("AC negative duration squared margin", F(139, 100)**2 - (4 * F(223, 100) - 7),
   F(121, 10000))
lt("AC negative episode endpoint", F(51, 100) + F(39, 100), F(91, 100))

# The final cubic error and the exact overlap between angle cases.
eq("AC cosine margin", cos_lower(F(147, 200)) - F(37, 50),
   F(62448881, 40000000000))
eq("AC relevant interval length", F(91, 100) - F(147, 200), F(7, 40))
cubic = F(19, 25) / (6 * F(2, 3)) * F(7, 40)**3
eq("AC cubic error", cubic, F(6517, 6400000))
lt("AC lower cosine at kappa=1/8", F(3, 25)**2, F(1, 65))
eq("AC terminal allowance", F(39, 4400) * F(3, 25), F(117, 110000))
eq("AC final payment gap", F(117, 110000) - cubic, F(3193, 70400000))
lt("AC final payment is strict", cubic, F(117, 110000))


if __name__ == "__main__":
    print(f"PASS: {len(CHECKS)} exact rational checks for the Gate 2 written proof.")
    print("Arithmetic only; no continuum geometry or Lean verification is claimed.")
