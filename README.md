# Cluster skeleton geometry

Lean formalization of the Liouville geometry of unimodular acyclic cluster models. On the actual space of complex exchange points, the project constructs a smooth exact symplectic structure, a complete two-sided Liouville flow, and proves that its full dynamical skeleton is the coordinate cap.

Frozen coordinates remain variable elements of `ℂ*`. The full skew-symmetric integer matrix has determinant one; only the mutable quiver must be acyclic.

## Current continuation

The working directory has been restored from the final published source `966d31257fd6fc9975ac4004ed9a2b3db5ea38ef`. The existing skew-symmetric determinant-one theorem below is the verified baseline. The proof PDF was replaced on 8 November 2026 using the supplied skeleton appendix; its weighted notation is reference material. Continue from the existing code in the requested skew-symmetric scope; a general weighted extension is not certified by the current theorem. Local Archon must use Claude Fable for planner assignments and Claude Opus for proof workers.

## Read the mathematics

- [Target theorem (PDF)](target-theorem.pdf): precise hypotheses, definitions, quantifiers, and scope.
- [Proof blueprint (PDF)](proof-blueprint.pdf): the geometric argument, including zero strata, completeness, and both skeleton inclusions.
- [Definitions and statement guide](docs/target-theorem.md): distinguish an object definition, a target proposition, and its proof.
- [Proof-to-code map](docs/proof-blueprint.md): the Lean implementation of each step.
- [Verification records](verification/README.md): reproducible checks, axiom policy, and source provenance.

Editable LaTeX sources for both PDFs are in [`docs/tex`](docs/tex). Only the relevant geometry is included in this publication. The complete source research notes and their later categorical arguments are not reproduced.

## Definitions are separate from proofs

| Role | Where to look | Meaning |
| --- | --- | --- |
| Existing foundations | Pinned Mathlib and [FsFltz](https://github.com/bohanfang/fs-fltz-minimal) | Native topology, manifolds, derivatives, forms, and flows |
| Project objects | [`Seed.lean`](ClusterSkeleton/Seed.lean), [`CapSet.lean`](ClusterSkeleton/CapSet.lean), [`TrappedSet.lean`](ClusterSkeleton/TrappedSet.lean) | Define the exchange points, coordinate cap, and trapped set independently |
| Formulation | [`GeometryTarget.lean`](ClusterSkeleton/GeometryTarget.lean) | `FirstGeometricTarget` states the goal; defining it does not prove it |
| Constructions and proofs | [`FullSkeleton.lean`](ClusterSkeleton/FullSkeleton.lean) and its imports | Construct the witnesses and prove `FullSkeleton.firstGeometricTarget` |

The final equality is `FullSkeleton.trappedSet_eq_coordinateCap`. The final quantified existence theorem is `FullSkeleton.firstGeometricTarget : FirstGeometricTarget`, in namespace `ClusterSkeleton`. Neither a pre-existing flow nor either skeleton inclusion is assumed. Auxiliary cutoff parameters are instantiated by `ε = 1`, `κ = 3`, `δ = 1`.

Here **skeleton** means the set of points whose forward orbit has compact closure in the exchange variety. The coordinate cap is defined by `|a_f| = 1` for frozen indices and `|a_i| ≤ 1`, `(1 - |a_i|²)b_i = 0` for mutable indices. Their equality is a theorem about the same constructed flow.

## Reproduce the checks

Use Linux or Ubuntu under WSL on Windows, with Elan (`lake` and `lean` on `PATH`), Git, Python 3, and Bash 4 or newer installed. This repository is private; cloning requires an authenticated GitHub account with access:

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

This repository is maintained privately. No GitHub Pages deployment is configured.
