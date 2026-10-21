# Cluster skeleton geometry

Lean formalization of the Liouville geometry of unimodular acyclic cluster models. On the actual space of complex exchange points, the project constructs a smooth exact symplectic structure, a complete two-sided Liouville flow, and proves that its full dynamical skeleton is the coordinate cap.

Frozen coordinates remain variable elements of `ℂ*`. The full skew-symmetric integer matrix has determinant one; only the mutable quiver must be acyclic.

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

With Elan, Git, and Python 3 installed, from the repository root run:

```sh
bash scripts/fetch-cache.sh
python3 scripts/verify.py
```

The first command obtains the pinned dependency cache. Subsequent checks can run only the second command. The default library entry point imports the final theorem. Verification builds the library, checks transitive axiom dependencies, and records exact source hashes. Only `propext`, `Classical.choice`, and `Quot.sound` are permitted. See the [verification guide](verification/README.md) for the exact checked scope and receipts.

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
