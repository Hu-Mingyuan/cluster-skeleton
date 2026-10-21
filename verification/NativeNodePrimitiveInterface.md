# Native regularized node primitive

This is the regular singular block in Lemma 2.4, manuscript pp. 9–11,
particularly (2.8). It does not construct the full local or global primitive,
its exterior derivative, a complete flow, or the skeleton. Those obligations
remain with the existing root through successor72.

## Exact domain and maps

For any actual `Seed S`, unimodularity proof, and independent finite set `I`,
`locus S I` is exactly the intersection of `candidateChartLocus S I` with
the preimages of `nodeLogDomain` under the existing raw pairs
`(q.a i, normalizedPartner q i)`, for every mutable index in `I`.
Independence ensures all indices in `I` are mutable.

`nodeMap` merely names this pair. It is not a new chart. Its normalization
is the accepted `q.b i / Q_i`; the nonvanishing theorem for the actual negative
exchange monomial on the independent locus supplies the denominator proof.
The ambient coordinate inclusion and native chain rule prove smoothness.
`isOpen_locus` uses continuity on that locus and finite intersections.
All points retain the literal complex exchange equations and induced topology.
Frozen coordinates are variables, and logarithmic rows include all columns.

## Native form and identities

`nodeDifferential` is the actual Mathlib `mfderiv` of `nodeMap`.
`lambda` composes the accepted `NodePrimitiveCancellation.lambda` with this
map. `block` sums over the finite subtype `i : I` and packages the sum using
FsFltz `covectorForm`, a native alternating `Fin 1` form.

`nodeDifferential_inChart` proves actual tangent transport in every native
chart, assuming chart-target membership and inverse-point membership in the
independent locus. `contDiffAt_block_inChart` proves smooth coefficients at
every such inverse point in `locus`. It differentiates the actual composite
node map in the chart and transports its derivative by the native chain rule.
No smoothness of the totalized expression outside this locus is asserted.

`pullback_differential` supplies the actual scalar chain rule. `node_real_logRow`
uses the accepted localization Laurent-log bridge, with frozen columns.
`lambda_torus` combines these with the accepted Euclidean cancellation and
`PrimitiveResidual.tau_eq_nodeAngle_differential`. `block_torus` is equality
of native alternating forms in the actual tangent fiber. The correction is
literally `(log(norm(a_i))+kappa)*Im(nodeLog_i)`.

`nodeDifferential_fst` identifies the first derivative component with the
actual coordinate differential. `lambda_boundary` proves for every native
`tangent v`, every real `kappa`, and every `a_i=0` on the independent locus:

```
lambda_i(q)(v) = (1+kappa) * Im(normalizedPartner(q,i) * da_i(v)).
```

This includes zero normalized partners. No division by `a_i` occurs in this
boundary proof. `block_empty` includes the empty index set.

## Consumers and evidence

The source-matched consumer covers arbitrary native charts and tangent
vectors, torus cancellation, empty sums, and zero normalized partners.
Its four-dimensional determinant-one seed has two independent mutable nodes
and two nonzero frozen variables. An actual family lets both frozen values
vary; a specialization gives two simultaneous zero coordinates and normalized
partners equal to `Complex.I`. A tangent constructed from the existing chosen
chart has node derivative `(1,0)`, proved from that chart's literal formula.
The resulting boundary evaluation at `kappa=1` is `2`, fixing the sign.

The delivery artifact records exact theorem inventory, managed module and
consumer receipts, immutable file modes and hashes, source/import/olean and
checker identities, all inherited per-root axiom results, fresh combined and
new/private/generated roots, and all nine attribution-sensitive supplements.
Only `propext`, `Classical.choice`, and `Quot.sound` are allowed. The native
collector is unmodified; live `verification/AxiomAudit.lean` is unchanged and
the separate optimization remains unadopted.

The immutable publication base is PrimitiveResidual
`ef911d06bb059c0953e732d60b067517062b4986` (58 entries). The exact three
NodePrimitiveCancellation files are borrowed from
`d1929fdf31e625c3fde77cbb028ff8d8800fc82b`, and the exact nine
scalar/dominance/localization files from
`dc8d4604a13e94d45f677ee0b4b38b5556c14c1a`.
All 70 inputs retain their bytes and Git modes. The only authored paths are
`ClusterSkeleton/NativeNodePrimitive.lean`,
`verification/NativeNodePrimitiveConsumer.lean`, and this interface: 73 entries.
Workspace extras are preserved. Private publication and independent acceptance
are separately evidenced; compilation alone is not acceptance.
