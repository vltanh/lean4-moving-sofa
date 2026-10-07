# Historical constants proof-source prototypes

These eleven files are preserved byte-for-byte from PR #10 at
`077e5d3e21f6fcae5b2bd0bc799d2e8b1a3c6525`.
They were uncompiled source written against the pre-integration stability modules.
The paper branch has since consolidated those modules and kernel-checked its
own stability/coercive development. Keeping these old imports in that library's
glob would break the integration, so the prototypes are archived, not counted
as verified results. Their mathematics and research history remain available.

The active baseline for the quantitative formalization is paper commit
`859ba93f8bb73ccc4378118a7b47415827710c2f`. New work must use the integrated
`Basic`, `Deficit`, `CapEstimate`, `Global`, and `Sharpness` interfaces.
The analytic notes and certificate generators stay in
`docs/stability/constants/`. No original Baek, uniqueness, bridge, or Challenge
proof is replaced by these prototypes.
