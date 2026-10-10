# Analytic width reduction: the two diagonal positions alone are insufficient

This begins an attempt to replace the computer-assisted width-at-most-two certificate by a short, fully analytic argument. The target is the same ordinary-area exclusion, not the unrestricted sharp sofa theorem. The old certificate is retained rather than deleted before a replacement is established.

## An exact obstruction to the simplest relaxation

Put

\[
a=1-1/\sqrt2,\qquad X=x-1,\qquad
T(x)=\min\{1,\ a+\sqrt2-|X|,\ 1-a+|X|\}
\quad(0\leq x\leq2).
\]

Define

\[
E=\{(x,y):0\leq x\leq2,\ 1-T(x)\leq y\leq T(x)\}.
\]

**Lemma AW-D1.** E is compact and connected, has horizontal span two and vertical span one, fits a lower-turn diagonal hallway and an independently allowed upper-turn diagonal hallway, and has area

\[
|E|=4\sqrt2-4>411/250.
\]

**Proof.** A lower hallway with dual angle pi/4 and inner corner (1,a) has outer condition

\[
y\leq a+\sqrt2-|x-1|
\]

and inner condition y>=a-|x-1|. Its reflection in y=1/2 gives the upper-turn conditions y>=1-a-sqrt(2)+|x-1| and y<=1-a+|x-1|. Intersecting these with [0,2] times [0,1] gives exactly E.

The function T is continuous. On 0<=z=|X|<=1 it equals 1-a+z for 0<=z<=a, equals 1 for a<=z<=1-a, and equals a+sqrt(2)-z for 1-a<=z<=1. Its minimum is 1-a>1/2, so every fiber contains (x,1/2) and has positive length. This proves compactness, connectedness, and both spans.

The area lost from the rectangle is two central niche triangles and four outer corner triangles. Equivalently, integrate the preceding three pieces. The two central losses total 2a^2 and the four corner losses total 2a^2. Thus

\[
|E|=2-4a^2=4\sqrt2-4.
\]

For the strict comparison it suffices that sqrt(2)>1411/1000, whose square is less than two. This gives 4sqrt(2)-4>411/250. QED.

This is an example in the **finite-position relaxation**, not a claimed continuously movable ambidextrous sofa. It proves that deleting the additional sampled orientations from the existing certificate cannot give the desired bound merely by optimizing the diagonal placements more accurately.

## Direction of the analytic attempt

The existing four-position certificate already suggests a piecewise-quadratic bound, but its validity was established over millions of parameter boxes. A pen-and-paper replacement must prove its geometric domain globally, or use a different inequality. Reprinting the rational stationary value or its positive Hessian does not replace that domain proof.

The intended next step is an ordinary-area decomposition that separates the two motions without assuming they are reflections of each other, and then controls the relevant wall/niche losses analytically. Every inequality must remain valid for disconnected relaxed envelopes, or use the connected body's actual horizontal projection explicitly.

Exploratory local calculations may help select an inequality; they are not proof dependencies. The committed lemma above is verified directly by the displayed geometry and elementary integration. No CI or Lean/Lake compilation was used.
