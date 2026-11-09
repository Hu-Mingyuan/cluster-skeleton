# Cluster skeleton geometry

Lean formalization of the Liouville geometry of unimodular acyclic cluster models. On the actual space of complex exchange points, the project constructs a smooth exact symplectic structure, a complete two-sided Liouville flow, and proves that its full dynamical skeleton is the coordinate cap, equivalently the union `⋃_{I independent} Λ_I` of the reference strata.

Frozen coordinates remain variable elements of `ℂ*`. The full skew-symmetric integer matrix has determinant one; only the mutable quiver must be acyclic.

## Current target: skew-symmetrizable generalization

The current PDFs state the general target for integral unimodular `E` and an arbitrary positive rational diagonal `D` with `E D` skew-symmetric. The exchange equations use the **columns of E**. This generalization is in progress; the existing Lean code and receipts still certify only the `D = I` baseline. See [the current objective](docs/roadmap.md).

## Verified baseline: skew-symmetric case

The formalized skeleton is the coordinate cap and the union of the independent-set strata `Λ_I`. Independent node charts have torus exponent `d - 2|I|`. The complete library, final theorem consumers, and transitive axiom audit pass: 58 modules and 1,492 declarations, using only `propext`, `Classical.choice`, and `Quot.sound`.

## Read the mathematics

- [Target theorem (PDF)](target-theorem.pdf): precise hypotheses, definitions, quantifiers, and scope.
- [Proof blueprint (PDF)](proof-blueprint.pdf): the geometric argument, including zero strata, completeness, and both skeleton inclusions.
- [Definitions and statement guide](docs/target-theorem.md): distinguish an object definition, a target proposition, and its proof.
- [Proof-to-code map](docs/proof-blueprint.md): the Lean implementation of each step.
- [Verification records](verification/README.md): reproducible checks, axiom policy, and source provenance.

Editable LaTeX sources for both current PDFs are in [`docs/tex`](docs/tex). The [proof correspondence audit](docs/skeleton-audit.md) records the stratified identity, chart dimension and convention matching. This publication includes the relevant geometry; the source manuscript's later categorical arguments are outside its scope.

## Definitions are separate from proofs

| Role | Where to look | Meaning |
| --- | --- | --- |
| Existing foundations | Pinned Mathlib and [FsFltz](https://github.com/bohanfang/fs-fltz-minimal) | Native topology, manifolds, derivatives, forms, and flows |
| Project objects | [`Seed.lean`](ClusterSkeleton/Seed.lean), [`CapSet.lean`](ClusterSkeleton/CapSet.lean), [`TrappedSet.lean`](ClusterSkeleton/TrappedSet.lean) | Define the exchange points, coordinate cap, and trapped set independently |
| Formulation | [`GeometryTarget.lean`](ClusterSkeleton/GeometryTarget.lean) | `FirstGeometricTarget` states the goal; defining it does not prove it |
| Constructions and proofs | [`FullSkeleton.lean`](ClusterSkeleton/FullSkeleton.lean) and its imports | Construct the witnesses and prove `FullSkeleton.firstGeometricTarget` |

The cap equality is `FullSkeleton.trappedSet_eq_coordinateCap`; its stratified form is `FullSkeleton.trappedSet_eq_iUnion_lambdaStratum`. The final quantified existence theorem is `FullSkeleton.firstGeometricTarget : FirstGeometricTarget`, in namespace `ClusterSkeleton`. Neither a pre-existing flow nor either skeleton inclusion is assumed. Auxiliary cutoff parameters are instantiated by `ε = 1`, `κ = 3`, `δ = 1`.

Here **skeleton** means the set of points whose forward orbit has compact closure in the exchange variety. The coordinate cap is defined by `|a_f| = 1` for frozen indices and `|a_i| ≤ 1`, `(1 - |a_i|²)b_i = 0` for mutable indices. Their equality is a theorem about the same constructed flow.

## Stratified form and node-chart rank

[`CapStrata.lean`](ClusterSkeleton/CapStrata.lean) defines the reference stratum `lambdaStratum S I` (`Λ_I`: `b_i = 0` and `|a_i| ≤ 1` for mutable `i ∈ I`, `|a_j| = 1` for `j ∉ I`) and proves

```lean
coordinateCap_eq_iUnion_lambdaStratum :
  coordinateCap S = ⋃ I : {I : Finset (Fin d) // S.Independent I}, lambdaStratum S I.val
```

together with `lambdaStratum_subset_coordinateCap`, `coordinateCap_subset_lambdaStratum_strictCapIndices`, `isClosed_lambdaStratum` and `isCompact_lambdaStratum`. Composed with the cap equality, this gives the reference's identity for the same flow:

```lean
FullSkeleton.trappedSet_eq_iUnion_lambdaStratum :
  trappedSet (NativeCompleteFlow.completeFlow S hdet hε hκ hδ).flow
    = ⋃ I : {I : Finset (Fin d) // S.Independent I}, lambdaStratum S I.val
```

The independent node charts carry the explicit torus exponent `d - 2|I|`: `IndependentNodeChart.complementRank_eq_sub_two_mul_card` proves `SplitIntegerRows.complementRank (independentRowRightInverse S I) = d - 2 * I.card`, with `IndependentNodeChart.two_mul_card_le : 2 * I.card ≤ d` ([`IndependentNodeSmooth.lean`](ClusterSkeleton/IndependentNodeSmooth.lean)).

These restatements close gaps **G1** and **G2** of [`docs/skeleton-audit.md`](docs/skeleton-audit.md). They add no hypothesis and change no existing statement; the scope remains skew-symmetric unimodular with mutable acyclicity and variable frozen coordinates, and no weighted or principal-coefficient claim is made.

## Reproduce the checks

Use Linux or Ubuntu under WSL on Windows, with Elan (`lake` and `lean` on `PATH`), Git, Python 3, and Bash 4 or newer installed. The repository is public:

```sh
git clone https://github.com/Hu-Mingyuan/cluster-skeleton.git
cd cluster-skeleton
bash scripts/fetch-cache.sh
python3 scripts/verify.py
```

The cache command obtains the pinned dependencies. Subsequent checks can run only `python3 scripts/verify.py`. The default library entry point imports the final theorem. Verification builds the library, checks transitive axiom dependencies, rejects modified dependency checkouts, and confirms that source hashes remain unchanged during verification. Only `propext`, `Classical.choice`, and `Quot.sound` are permitted. Success ends with `FULL_GEOMETRIC_TARGET_VERIFIED`. The [verification guide](verification/README.md) describes the checked scope and the included final receipt and logs.

| Dependency | Pinned revision |
| --- | --- |
| Lean | `leanprover/lean4:v4.34.1` |
| Mathlib | `d13f23b723b8a846827a245b89c10fc7d3f11612` |
| FsFltz | `1a3d387cfacc746e25aad31e5b27b1803103e7cb` |

## Attribution and scope

The geometric problem comes from the supplied *acyclic_cluster_HMS* manuscript; its hash and selected scope are recorded in [`docs/sources.json`](docs/sources.json). The rewritten exposition follows the actual Lean construction. Introducing a Lean definition is not in itself a claim of a new mathematical concept.

[Bohan Fang's fs-fltz-minimal](https://github.com/bohanfang/fs-fltz-minimal) is an unmodified pinned dependency, licensed upstream under Apache-2.0. Its geometric interfaces use native Mathlib structures.

The theorem concerns real smooth symplectic geometry. Holomorphic extension of the complex form, finite type, cap-product descriptions, generalized cocores, and categorical HMS are outside its scope.

The repository is public. No GitHub Pages deployment is configured.
