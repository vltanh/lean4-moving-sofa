# Contact-discovery failures and preliminary successes

This log records the first attempt before changing the detector. No CI was run.
Inputs were the previously saved PR #6 solutions, not a new optimization.

## Positive: corner exposure can be detected without the input cut

For a point p and a hallway angle s, define the inner-wall slack

    max(1 + <p,u_s> - h_K(s), 1 + <p,v_s> - h_K(s+pi/2)).

A negative minimum over s means p is removed by another hallway's forbidden
wedge. For a polygon cap the two slacks are sinusoids on each common-normal
cell. Checking cell endpoints, stationary points, and switches between the two
walls minimizes their maximum over the whole interval in exact arithmetic.
The implementation uses floating point, so this is not an interval certificate.

Apply this to the inner corner x_K(t), omitting |s-t|<g to exclude its own
contact. The first change from negative to positive identifies entry into the
exposed core. Searching over the entire half-turn, rather than a Gerver-based
bracket, found:

| Input intervals | Input cut | First exposure | Last exposure |
| --- | --- | --- | --- |
| 32 | 0.04 | 0.0394410075257 | 1.5313550360922 |
| 64 | 0.04 | 0.0391962572596 | 1.5316002389263 |

Changing the exclusion radius g among 0.1, 0.2, and 0.3 changed each root by
less than 1.1e-14. Both roots lie inside the cap. The first finest-grid root is
about 1.9e-5 from Gerver's known phi, which is used only as a post-solve check.
The inferred cut is not simply the supplied value 0.04.

## Negative: first departure from a wall-slack plateau is not reliable

The initial tail detector took the first cell whose wall slack exceeded a
multiple of the between-node feasibility defect, then fitted an offset plus
a one-sided quadratic or cubic. This failed, despite successful least-squares
termination. Representative quadratic fits were:

| Input intervals | Spurious fitted left transition | Fit RMS |
| --- | --- | --- |
| 32 | 0.220593888374 | 1.20028e-4 |
| 64 | 0.156984288110 | 2.41431e-5 |

These are not credible estimates of a phase transition. The fitted amplitudes
collapsed almost to zero (about 5.1e-11 and 7.6e-12), so the cutoff was not
identified by the data at all. A least-squares success flag must not be treated
as evidence that a contact angle has been identified.

At grid 64, tiny unequal cells around the inserted cut have positive slacks
4.90e-5 and 4.57e-5, whereas the long active-wall plateau has minimum slack
about -8.37e-6. The detector mistook these local discretization artifacts for
the end of the long plateau. On this mesh the long plateau actually continues
to an angular cell minimum at 0.67495155; the next cell minimum, 0.69504450,
has positive slack 3.63e-5.

The next implementation will locate the longest resolved active plateau,
retain threshold and model sensitivity, and distinguish numerical fit success
from actual event identification. This is a diagnostic revision, not evidence
for a continuum contact theorem or an automatically derived ODE system.
