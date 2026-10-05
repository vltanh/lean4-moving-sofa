# Width-two exclusion: a completed exact covering

**Theorem CA-W:** a compact connected ambidextrous sofa in a common incoming unit-span normalization with horizontal width at most two has area at most

$$
411/250=1.644<M,
$$

where M is Romik's candidate area. This excludes the narrow-width regime without assuming curvature bounds, symmetry, contact order, or full-quarter endpoint angles. It does **not** close the unrestricted moving problem.

Read [THEORY.md](THEORY.md) for the geometric reduction and correctness argument, [RESULT.json](RESULT.json) for the executed complete covering/replay record, and [DISCOVERY.md](DISCOVERY.md) for unsuccessful searches and numerical suggestions that are not proof inputs.

## Reproduce the complete proof

With Python, NumPy and Numba available, run from this directory:

```sh
python exact_width.py
python check_width.py
python search_width.py run_width --budget 12000000
python verify_width_complete.py run_width/tree.bin --output replay.json
```

The tested environment was Python 3.13.5, NumPy 2.3.5 and Numba 0.65.1. No Lean, Lake, CI, or manuscript build is invoked. Numba compiles the local bounded-integer accelerator; that compilation is not a formal verification.

The complete deterministic search has 11,697,975 nodes, so the displayed budget covers the recorded run. The generator refuses to overwrite an existing run. For an intentionally interrupted **trusted local** run, continue with `--resume`; its pickle checkpoint must never be loaded from an untrusted source. The verifier does not load or trust any checkpoint.

A completed replay must report `complete: true`, target `411/250`, 5,848,987 splits, 5,448,929 spatial leaves, 400,059 polynomial leaves, and maximum coordinate depth eight. The raw tree SHA-256 is

```text
e41b83a31344e04b591b6d3f23473d3a8411a392b6647d7661aca8bac4d9e119
```

A successful numerical search, an unfinished tree, or a search log without complete replay is not an acceptable substitute.

## Arbitrary-precision verifier

The same complete tree can be replayed without NumPy, Numba, or fixed-width arithmetic:

```sh
python verify_width_complete.py run_width/tree.bin --pure
```

This path uses only the Python standard library and unbounded integers/Fraction. **The whole recorded tree was replayed in guarded-int64 mode, not in pure mode.** The pure evaluator was compared with the accelerated evaluator on 1,200 boxes. An independently implemented rational polygon-clipping evaluator checked 500 spatial bounds, and both replay paths rejected all seven selected malformed/false trees. These are checks in addition to the full replay and the written correctness argument, not proof by sampling.

THEORY.md gives an explicit int64 overflow bound. The accelerated path rejects depths above 13 and large generated template coefficients; the actual certificate uses depth at most eight. Exact rational matrix calculations are performed with Fraction before acceleration. No floating-point quantity participates in a pruning or acceptance decision.

## Certificate storage

The complete raw tree is 11,697,975 bytes, or 1,494,626 bytes as deterministic gzip. The generated binary is distributed with the conversation's certificate bundle; it is **not checked into this branch**. Its full deterministic generator, verifier, expected hashes and executed record are committed here. Regenerating it with the command above produces the same raw hash. The verifier accepts either the raw file or a `.gz` file and reconstructs the entire parameter covering from it.

Keeping the binary out of Git does not make its leaf claims implicit: every leaf is regenerated/replayed from the full [0,1]^8 root. The recorded tree has no unresolved frontier. A fresh regeneration is preferable to trusting the JSON summary alone.

## Discovery is not verification

The optional command

```sh
python discover_width.py --seeds 0,1,2,20261005
```

also needs SciPy (tested version 1.17.0). It returns floating-point candidate placements around area 1.628313908. These are finite-position witnesses, not continuous-motion proofs and not certified global upper bounds. The exact certificate proves the weaker but sufficient 1.644 bound independently of those outputs.

The polynomial template's exact maximum is reconstructed as

```text
189405071954415/116319753199426
```

and checked by rational LDL/Gaussian elimination. Its domain conditions are checked on each box that uses it; it is not assumed to majorize the envelope outside that domain.

## What the computation contributes to closure

The two-direction reduction is valid for every potentially improving body: the second direction has cosine 481/769>5/8, so the existing two-strip bound forces both motions to visit it whenever the body has area greater than 8/5. The eight placement variables cover independent left/right motions and every normalized width-at-most-two body.

Therefore all global maximizers have width greater than two. The existing [CW4 theorem](../curvature-only-wide-hulls.md) already proves optimality and exact uniqueness for such hulls **provided** their open-quarter curvature measure is dominated by dtheta. The remaining sufficient structural task is that global curvature/enclosure theorem, not another narrow-width estimate. A result for only one maximizer proves the value; uniqueness requires every maximizer or an equality-preserving recovery.

The proof, code and historical dependencies remain subject to independent review. No best-known-bound or novelty claim is made.
