# Cluster skeleton geometry

Lean formalization of the Liouville geometry of unimodular acyclic cluster models. The target is a smooth Liouville primitive on the actual complex exchange variety, a complete two-sided flow, and equality of its full dynamical skeleton with the coordinate cap set in Theorem 2.1 of the supplied manuscript.

## Reading the project

- [Target theorem](docs/target-theorem.md): the exact carrier, hypotheses and quantifier order.
- [Proof blueprint](docs/proof-blueprint.md): the manuscript argument and its Lean dependencies.
- [Verification records](verification/README.md): build and axiom-audit requirements.
- [Source manuscript](references/acyclic_cluster_HMS.pdf): the supplied geometric source.
- [Private automated checks](https://github.com/Hu-Mingyuan/cluster-skeleton/actions): results for each uploaded revision.

## Current scope

The first batch defines the actual exchange-equation carrier with native Mathlib topology, the coordinate cap, and the trapped set of a genuine continuous real flow. It specifies the desired Liouville existence statement using native Mathlib manifolds and the pinned FsFltz geometric interfaces.

The first batch passed Lean compilation and a transitive axiom audit of 27 declarations at commit `14549f35dc0289b775b234a014fac2c7cefd719d`. The [private CI run](https://github.com/Hu-Mingyuan/cluster-skeleton/actions/runs/39431898775) and [source-bound receipt](verification/ci-14549f3.json) record the result. The verified results include zero-set independence for arbitrary finite acyclic mutable quivers, compactness of the coordinate cap, independence of strict cap indices, and the generic compact-forward-invariant inclusion in the trapped set. Later source changes require a fresh build and audit.

**The full Liouville existence and skeleton equality theorem is not yet proved.** `FirstGeometricTarget` is a proposition definition, not a theorem. Node charts, the smooth atlas, the primitive extension, the actual complete flow, and the reverse trapped-set inclusion remain open construction obligations. Holomorphic extension, finite type, cap products and cocores have separate milestones.

## Files

- `ClusterSkeleton/Seed.lean`: the exchange model, acyclicity, unimodularity and explicit nonempty carrier.
- `ClusterSkeleton/ZeroSet.lean`: zero-set independence and the independent nonvanishing-locus cover.
- `ClusterSkeleton/CapSet.lean`: the coordinate cap, coordinate bounds and compactness.
- `ClusterSkeleton/TrappedSet.lean`: relative compactness of forward orbits and the generic compact-invariance lemma.
- `ClusterSkeleton/GeometryTarget.lean`: the carrier-fixed native manifold presentation, actual Liouville-flow interface and open target proposition.
- `docs/roadmap.md`: proof obligations, their order and acceptance criteria.
- `docs/sources.json`: authoritative manuscript hash and pinned library versions.

## Reproducible verification

Lean is pinned to 4.34.1. The Lake manifest pins Mathlib and fs-fltz-minimal. In the installed WSL environment, run:

```sh
cd /mnt/d/HorizonData/workspaces/cluster-skeleton
export ELAN_HOME=/mnt/d/HorizonData/tools/elan
export PATH="$ELAN_HOME/toolchains/leanprover--lean4---v4.34.1/bin:$PATH"
# For a fresh dependency checkout only:
bash scripts/fetch-cache.sh
python3 scripts/verify.py
```

Once the pinned dependency cache is installed, subsequent checks need only `python3 scripts/verify.py`. This builds the modules and audits the transitive axioms of the listed declarations. The allowlist is `propext`, `Classical.choice` and `Quot.sound`. The source hashes and exact audited names are saved with the result. The target statement still needs mathematical review independently of successful compilation.

## Reference library

[Bohan Fang's fs-fltz-minimal](https://github.com/bohanfang/fs-fltz-minimal) is used as an unmodified pinned Lake dependency under its Apache-2.0 license. Its `Smooth` and `Liouville` interfaces use native Mathlib derivatives, tangent spaces and flows.

## Horizon

The local Horizon project is named **Cluster skeleton geometry**. The current bounded batch is being developed and verified in this checkout. This checkout is mirrored to the private repository Hu-Mingyuan/cluster-skeleton. No public site or background Horizon proof run has been started.
