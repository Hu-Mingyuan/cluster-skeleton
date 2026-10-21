# Constructed native local primitive

This module constructs the local one-form in manuscript Lemma 2.4, equations
(2.7)–(2.8), on the actual complex exchange-point subtype and its inherited
topology. The full integer matrix is skew-symmetric and determinant one; only
the mutable quiver is acyclic. Frozen coordinates remain nonzero variables.

For each actual point p, its proved independent zero set I indexes
`neighborhood = PrimitiveLocalization.neighborhood ∩ NativeNodePrimitive.locus`.
`isOpen_neighborhood` and `mem_neighborhood` construct an open cover without a
supplied neighborhood witness. `mem_node_locus` uses `(0,w)` in the principal-log
domain for every normalized partner w, including zero. `node_domains` exposes
all normalization, character, logarithm and torus-row bridges simultaneously.

`eta` is exactly `residual I + block kappa I - regularForm I` in the pinned
native alternating one-form type. `locallySmooth_eta` proves local coefficient
smoothness in every native chart, requiring inverse-chart membership only in
its own open domain. It combines the accepted coefficient proofs without
asserting smoothness of any totalization outside its domain.

`mdifferentiableAt_affine` proves native differentiability by composition with
the actual normalized node map. `singularH_eq_sum` reindexes the full accepted
zero-index sum. `differential_H_eq_sum` applies native finite-sum and addition
rules to these proved derivatives and to the smooth surviving correction,
then uses the accepted H-germ equality. `eta_eq_torus` combines the actual beta
matrix decomposition, node cancellation, and differential split.
`evalOne_eta` gives the full matrix expression on arbitrary native tangents;
frozen columns and the minus sign on dH are retained.

`local_cover` and `agree_on_torus` expose the constructed cover and local family
in the form required by accepted LocalFormGluing. `eta_zero_partners` gives the
actual boundary value when all normalized partners vanish. The consumer uses
a six-coordinate determinant-one family with zero set {0,2}, zero normalized
partners, and a surviving nonconstant correction at vertex 4. Its frozen fifth
coordinate varies with phase. It exercises all charts, arbitrary tangents,
nonempty torus intersections, empty I and an inhabited dimension-zero seed.
The explicit family and nonconstancy calculation reuse the accepted regular
correction consumer, now applied to the constructed local eta.

The parameter contract is epsilon > 0, kappa >= 2*epsilon+1, and 0 < delta < pi.
Some intermediate statements hold for all delta > 0 or arbitrary epsilon and
kappa; the final packaged cover retains the full requested contract.

Only LocalPrimitive.lean, LocalPrimitiveConsumer.lean and this interface are
new authored files. The immutable 82-entry accepted union is preserved;
publication uses the exact 73-entry NativeNodePrimitive base plus nine accepted
additions and these three files. The source-bound delivery records managed
checks, complete inherited and fresh per-root native axiom results, nine
mandatory supplements, lazy equations, exact source/import/olean/checker
identities, and private publication. The optimized audit remains unadopted.

Unresolved and outside this bounded construction: global gluing into a single
alpha, the global identity d-alpha = omega, construction of the complete
Liouville flow, and equality of the independently defined coordinate cap with
the dynamical skeleton for that same flow. These are obligations, not proved
theorems here. The existing root and scheduler successor retain integration
ownership. Independent acceptance and actual terminal reviewer collection are
required before this mission is accepted.
