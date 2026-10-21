# Native node primitive cancellation

This module formalizes the local calculus in manuscript page 10, equation (2.8).
It is a prerequisite of the global primitive construction, not that construction.
The source is the pinned `references/acyclic_cluster_HMS.pdf`, SHA256
`4426e18f96290d63d0650817dc07834e58217516248e7dd10c45470d0a10b666`.

## Mathematical interface

The ambient space is `E = ℂ × ℂ`, considered over `ℝ`. The explicit open domain is
the accepted `nodeLogDomain = {p | 1 - p.1 * p.2 ∈ Complex.slitPlane}`. It contains
every `(0,v)`, including `(0,0)`; it is not the whole node `uv ≠ 1`.

`L p = Complex.log (1-u*v)`, `A p = Real.log ‖u‖`, `S p = (L p).re`, and
`T p = (L p).im`. The quotient `Q` is the accepted `nodeLogQuotient`, with
`Q(0,v) = -v`. The regular covector is

```text
lambda k = -Im(Q * du + (k : ℂ) * fderiv ℝ L).
```

The native alternating representation `oneForm` uses `Fin 1` and
`ContinuousAlternatingMap.ofSubsingleton`. Both representations are smooth on
the explicit domain for every real `k`.

The derivative contract is

```text
fderiv ℝ L (u,v) (δu,δv) = (v*δu + u*δv)/(u*v-1).
```

At each nonzero `u`, a normalized local logarithm germ proves
`dA(δu,δv) = Re(δu/u)`. This requires no global logarithm or argument condition
on `u`. Product differentiation of the literal function `(A+k)*T` yields, on
`nodeLogDomain` with `u ≠ 0`, equality of native covectors and alternating forms:

```text
A*dT - S*dtheta - d((A+k)*T) = lambda k,
dtheta(δu,δv) = Im(δu/u).
```

The sign of `k` remains inside the minus imaginary part. At every `(0,v)` and
every tangent vector, the boundary value is `(1+k)*Im(v*δu)`. The numerical
check uses `k=1`, `v=I`, and `(δu,δv)=(1,0)`, giving `2`.

## Finite-product consumer

The consumer uses `IndependentNodeChart.Vector seed I` and its accepted raw
coordinate projections. These are the node coordinates `u=a_i`, `v=b_i/Q_i`,
not the later coordinates defined using a hyperbolic sine.

`logDomain` intersects the accepted node-chart domain with the inverse image of
`nodeLogDomain` for every node. On this open set, finite sums of native
covector pullbacks and their `Fin 1` alternating forms are smooth. The summed
cancellation retains both the branch conditions and nonzero first coordinates.
Each summand may have its own real parameter.

Every center with all first coordinates zero, arbitrary second coordinates,
and complementary coordinates equal to one belongs to this open set. The
consumer includes arbitrary tangent directions at simultaneous zeros and the
empty-index case.

## Validation and ownership

The delivery artifact records the exact compiled theorem inventory, managed
module and consumer receipts, complete inherited and fresh per-root transitive
axiom results, source/import/checker identities, and verified private publication.
The allowed axioms are only `propext`, `Classical.choice`, and `Quot.sound`.
Compilation and independent statement-fidelity acceptance are separate checks.

The accepted 52-file baseline is commit
`6b99d39f5a9102c9749100054a66a7475769eb4b`, tree
`6b1ab37d6c02686c6dae873dc5570e550679e44f`. Publication adds only this interface,
`ClusterSkeleton/NodePrimitiveCancellation.lean`, and its consumer. Accepted
sources, root imports, the live audit, upstream sources, and retained extras
remain owned by their existing maintainers.

No cutoff localization, manuscript `H`, or identification with a full primitive
is assumed. Residual matrix terms are not discarded. Construction and gluing of
the global primitive, its exterior derivative, the complete flow, and the
same-flow skeleton equality remain open under their existing owners. Root
`df1a0cdf-af80-4485-9c04-b045ff0f3ffb` through scheduler successor 56 retains
shared integration and source-provenance recovery; this author retains repairs
and collection of the independent review outcome.
