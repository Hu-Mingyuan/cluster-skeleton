# Surviving correction and native H split

This construction is the regular-correction step in Lemma 2.4 and (2.7)–(2.8),
`acyclic_cluster_HMS.pdf`, pages 9–11. It uses the literal exchange-point subtype,
its inherited topology, and the accepted native smooth atlas.

`surviving S I` consists of mutable j outside I with B[j,i]=0 for every i in I.
`regularH` is exactly the sum of the existing `PrimitiveLocalization.correction`
over this set. `literal_formula` retains the full row, the accepted character,
mutable-neighbor dominance, and all four cutoff factors. Frozen coordinates
remain variable original coordinates.

`support_nonzero` proves nonvanishing of a surviving vertex and each coordinate
with nonzero row coefficient. In `contMDiffAt_row`, zero coefficients disappear
before any logarithmic differentiation. In character nonvanishing and denominator
nonvanishing, zero exponents contribute one before nonzero powers are used.
Dominance is treated factor by factor using its mutable-neighbor support.
The accepted local periodic angle lift handles the principal argument cut.
No smoothness of the entire logarithmic-coordinate vector at a boundary is used.
`contMDiffOn_regularH` proves native real smoothness on the whole candidate locus,
including zero strata, for every positive delta and arbitrary epsilon and kappa.

`contDiffAt_differential_inChart` establishes local coefficient smoothness for
an actual differential on an open candidate locus. Its proof applies the native
chain rule at inverse-chart points and identifies the germ with the actual
ordinary derivative of the chart expression. `regularForm` converts
`differentialCovector regularH` to the pinned covector form. `regularForm_smooth`
works in every native chart with target membership and inverse point in the locus.
Neither theorem assumes global smoothness of a totalized function outside it.

`H_eq_sum` identifies the existing H with the existing correction summands,
using `Complex.log_im`. `H_split` partitions all mutable indices exactly: zero
indices use the accepted affine germ, neighbors use the accepted zero germ,
and every surviving correction is retained. `H_eventuallyEq` gives an actual
neighborhood germ at each torus q in the previously constructed open U_p.
`differential_H_split` transports it to equality of native differential covectors.
The affine sum uses `(A_i+kappa)*Im(nodeLog_i)` for all zero indices. These claims
hold for epsilon>0, kappa>=2epsilon+1 and delta>0, including the required delta<pi.
No H germ at a singular boundary point is asserted.

The consumer exercises arbitrary native tangent vectors and arbitrary charts.
A six-coordinate determinant-one block matrix has mutable vertices 0,2,4 and
variable frozen coordinates 1,3,5. Actual points with zero set {0,2} retain the
correction at 4. Varying frozen coordinate 5 changes regularH, with explicit
nonzero value at phase pi/8 and zero value at phase zero. Empty I gives the original
H; an empty surviving set gives zero.

Only this interface, `ClusterSkeleton/RegularCorrection.lean`, and
`verification/RegularCorrectionConsumer.lean` are authored. The 64 entries of
accepted TorusCorrection base 02d8147d9504291816aaa29b34dd29b1afb9c8c9 and the three
exact PrimitiveLocalization additions from dc8d4604a13e94d45f677ee0b4b38b5556c14c1a
are immutable. The publication manifest contains exactly 70 files, preserving
all input bytes and Git modes. Unrelated local audit extras remain untouched;
the live audit is unchanged and its optimization remains unadopted.

The source-bound delivery records managed module/consumer receipts, theorem
inventory, native import/olean/pin identities, all inherited and fresh per-root
axiom results, nine explicit attribution supplements, and private publication.
Every overlapping root is reconciled by name and axiom set. The consumer uses
unmodified native Lean.collectAxioms for combined modules, private/generated
roots and local declarations. Only propext, Classical.choice and Quot.sound
are permitted. Mathematical acceptance is an independent maintainer decision;
the author retains repairs and collection of the terminal reviewer outcome.

Actual local/global alpha construction, d-alpha, complete flow and skeleton
remain outside this result. Root through existing successor72 retains sole
shared integration, final primitive assembly and audit-adoption ownership.
