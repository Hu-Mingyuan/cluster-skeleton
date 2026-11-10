# Cluster skeleton geometry

Lean formalization of the Liouville geometry of unimodular acyclic cluster models. On the actual space of complex exchange points, the project constructs a smooth exact symplectic structure, a complete two-sided Liouville flow, and proves that its full dynamical skeleton is the coordinate cap, equivalently the union `⋃_{I independent} Λ_I` of the reference strata.

The input is **skew-symmetrizable**: an integral exchange matrix `E` with `det E = 1`, an arbitrary positive rational diagonal symmetrizer `D`, and the requirement that `K = E D` be skew-symmetric. The exchange equations use the **columns of E**: `P_i^± = ∏_j z_j^{[±E_ji]_+}`. Frozen coordinates remain variable elements of `ℂ*`; only the mutable quiver must be acyclic. The skew-symmetric case is `D = I`, and it is recovered as a theorem.

## Verified result: the skew-symmetrizable theorem

`ClusterSkeleton.FullSkeleton.firstGeometricTarget : FirstGeometricTarget` is universally quantified over every dimension `d` and every weighted seed `S : Seed d`, with `S.Unimodular` (`det E = 1`) as its only hypothesis. The logarithmic form in the target has coefficient `K = E D` with the manuscript's factor `1/2` and sign. The formalized skeleton is the coordinate cap and the union of the independent-set strata `Λ_I`; independent node charts have torus exponent `d - 2|I|`.

The complete library, the final theorem consumers and the transitive axiom audit pass: **65 modules and 1,811 audited declarations, 72 `#print axioms` roots, 73 hashed inputs**, using only `propext`, `Classical.choice`, and `Quot.sound`. Verified at accepted source commit `a575aa236b485672f0606bba6ebc80571671f8a9`, receipts of 10 November 2026.

Two consumers sit beside the universal theorem and never replace it:

- **The `D = I` recovery is a theorem.** `ClusterSkeleton.SkewSeed.skeleton_recovery` is quantified over every skew-symmetric integral seed `S : SkewSeed d` with `det B = 1` as its only hypothesis. Because `SkewSeed.toSeed` reads it with `E := B` and `D = 1`, the weighted form matrix is `K = B` itself — no transpose, no sign change, no time reversal. On the **old** carrier it gives density of the old initial torus, the forward-orbit skeleton identity `Skel = C_B` in both the cap form and the stratified form `⋃_I Λ_I` over the old independence predicate, and compactness of the old cap and of each old stratum. The smooth presentation, primitive, two-form, field and flow enter existentially through `LiouvilleSkeletonTarget S.toSeed`, exactly as the manuscript quantifies them; see [the statement review](verification/statement-review.md) for the exact boundary.
- **A genuinely non-skew input is covered by the same theorem.** `ClusterSkeleton.Examples.nonSkewSeed` is the manuscript's seed with `E = [[0,1,−1,0],[−2,0,0,−1],[1,0,0,0],[0,1,0,0]]`, `D = diag(1,2,1,2)` and mutable set `{0,1}`; `E 0 1 = 1` while `E 1 0 = −2`, so `E` itself is not skew-symmetric and the `D = I` library cannot express this input. `Examples.nonSkewSeed_target_of_firstGeometricTarget` obtains its geometry by instantiating the universal theorem, not by a separate argument.

`PdfTargetConsumer.pdf_target` of [`verification/FullSkeletonConsumer.lean`](verification/FullSkeletonConsumer.lean) states every clause of the published theorem — density, the presentation and Liouville datum, `Skel(Φ) = C_E`, the stratified form for the same flow, compactness of every stratum, and the node-chart rank facts — in one Lean type for an arbitrary unimodular seed.

The [verification receipt](verification/publication-check.json) binds this result to the delivered source. Archon has accepted the formalization phase and completed the run; see the [acceptance record](verification/archon-acceptance.json). The [statement review](verification/statement-review.md) describes its mathematical scope.

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

These restatements close gaps **G1** and **G2** of [`docs/skeleton-audit.md`](docs/skeleton-audit.md). They add no hypothesis and change no existing statement. The scope is skew-symmetrizable unimodular with mutable acyclicity and variable frozen coordinates; no principal-coefficient claim is made.

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
