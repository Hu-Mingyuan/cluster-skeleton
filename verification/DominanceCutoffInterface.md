# Dominance cutoff and localization

`ClusterSkeleton.DominanceCutoff` imports the accepted `CoordinateLoci` directly.
It implements manuscript page 10, equation (2.5), and only the first dominance
localization step in Lemma 2.4. Shared imports and all accepted sources are unchanged.

For every positive real epsilon, `chi epsilon x` is the native Mathlib function
`Real.smoothTransition ((-2*x-epsilon)/epsilon)`. `contDiff_chi` proves native
real C-infinity regularity. `chi_nonneg`, `chi_le_one`, `chi_eq_one_iff`, and
`chi_eq_zero_iff` give the range and exact thresholds; `exists_chi` packages
the actual construction without a cutoff-existence premise.

`mutableNeighbors S i` is precisely the mutable vertices j with `S.B i j != 0`.
`dominance S epsilon i A` is the product of `chi epsilon (A i-A j)` over that
finite set. `dominance_of_no_neighbors`, `contDiff_dominance`,
`dominance_nonneg`, `dominance_le_one`, `dominance_eq_one_of`, and
`dominance_eq_zero_iff` supply its product and threshold API. `adjacent_exclusion`
uses full skew symmetry and positive epsilon to prove that adjacent mutable
dominance factors cannot both be nonzero. Frozen neighbors never enter this
product; frozen coordinates in the underlying exchange model remain variables.

For an actual exchange point p, `localizationNeighborhood S epsilon p` is the
single finite intersection of the strict inequalities
`norm(q.a i) < exp(-epsilon) * norm(q.a j)` for i in p.zeroSet and mutable
neighbors j. `mem_localizationNeighborhood` uses the accepted
`p.zeroSet_independent` to show that p belongs. `isOpen_localizationNeighborhood`
uses literal coordinate continuity in the inherited topology. `logNorms_sub_lt`
derives the logarithmic separation only on the initial torus. `localization`
proves both simultaneous assertions on this same neighborhood's torus part:
all factors indexed by p.zeroSet equal one, and every mutable neighbor's factor
equals zero. There is no separation/localization premise and no determinant
hypothesis in this module.

The standalone consumer imports the unchanged root, accepted GlobalSymplectic,
and the new module. It checks arbitrary dimension and epsilon, both plateaus,
smoothness and range, empty mutable-neighbor products, adjacent exclusion, and
actual zero-set localization. It includes an inhabited d=0 exchange model and
the same literal A2 boundary data as the accepted NodeNondegeneracy consumer.
The A2 boundary point is outside the torus, its localized torus part is nonempty
by accepted density, and both dominance values are proved there. Determinant
one is used only by that accepted density result, not by localization.

The consumer uses native `Lean.collectAxioms` for each new module declaration
by defining-module attribution, including private/generated declarations, each
consumer declaration, and all nine explicit inherited attribution-sensitive
supplements. It fails on absent modules or supplements and on any axiom other
than `propext`, `Classical.choice`, or `Quot.sound`. Complete unchanged inherited
per-root evidence is carried in the delivery manifest, retaining its exact
source, import closures, consumers, checker identities, and results.

The cutoffs h, rho, and vartheta, H, the primitive and its exterior-derivative
identity, the complete native flow, and the full same-flow skeleton remain open.
This module does not prove primitive extension or inhabit GeometryTarget.
Root mission df1a0cdf-af80-4485-9c04-b045ff0f3ffb retains integration through
the existing successor44; the separately owned audit optimization is not adopted.
