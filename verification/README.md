# Verify the formalization

The receipts below certify the skew-symmetrizable (weighted) library: integral `E` with `det E = 1`, an arbitrary positive rational diagonal `D` with `K = E D` skew-symmetric, column exchange exponents `P_i^± = ∏_j z_j^{[±E_ji]_+}`. Verified at accepted source commit `a575aa236b485672f0606bba6ebc80571671f8a9`, receipts of 10 November 2026. This records a verified result, not an acceptance decision.

From the repository root on Linux or Ubuntu under WSL, with Elan (`lake` and `lean` on `PATH`), Git, Python 3, and Bash 4 or newer installed:

```sh
bash scripts/fetch-cache.sh
python3 scripts/verify.py
```

The cache command obtains dependency sources and compiled artifacts at the revisions in `lake-manifest.json`. The verifier uses ordinary Lake:

```sh
lake --rehash build ClusterSkeleton
lake env lean verification/FullSkeletonConsumer.lean
lake env lean verification/AxiomAudit.lean
```

Success ends with `FULL_GEOMETRIC_TARGET_VERIFIED`. The [CI workflow](../.github/workflows/lean.yml) runs the same checks.

## Checked theorem and source

The final existence theorem is `ClusterSkeleton.FullSkeleton.firstGeometricTarget`. Its witnesses construct the smooth presentation, primitive, Liouville field, and complete flow on the actual exchange space. `FullSkeleton.trappedSet_eq_coordinateCap` proves the full skeleton equality for that same flow, and `FullSkeleton.trappedSet_eq_iUnion_lambdaStratum` restates it as the union `⋃_{I independent} Λ_I` of the strata defined in `ClusterSkeleton/CapStrata.lean`.

`FullSkeleton.firstGeometricTarget : FirstGeometricTarget` is universally quantified over `(d, S)` with `S.Unimodular` as its only hypothesis and no instance argument.

Two results sit beside it and never replace it. `ClusterSkeleton.SkewSeed.skeleton_recovery` is the **proved recovery of the `D = I` case**: quantified over every skew-symmetric integral `S : SkewSeed d` with `det B = 1` as its only hypothesis, it gives, on the **old** exchange-point carrier, density of the old initial torus, the forward-orbit skeleton identity `Skel = C_B` in both the cap form and the stratified form `⋃_I Λ_I` over the old independence predicate, and compactness of the old cap and of each old stratum; the smooth presentation, primitive, two-form, field and completeness enter existentially through `LiouvilleSkeletonTarget S.toSeed`, since `SkewSeed.toSeed` has `E := B` and `D = 1`, so `K = B` with no sign change. `ClusterSkeleton.Examples.nonSkewSeed_target_of_firstGeometricTarget` is a **supplementary consumer** at the manuscript's genuinely non-skew seed (`E 0 1 = 1`, `E 1 0 = −2`, `D = diag(1,2,1,2)`), obtained by instantiating the universal theorem.

[FullSkeletonConsumer.lean](FullSkeletonConsumer.lean) applies these proofs to the coordinate conditions and the complete Liouville manifold, and `PdfTargetConsumer.pdf_target` states every clause of the published theorem in one Lean type for an arbitrary unimodular seed. [AxiomAudit.lean](AxiomAudit.lean) checks all 65 project modules in the root-import environment, including private and generated declarations, two explicit generated-declaration supplements, and 72 direct theorem/construction roots. The 72 roots cover the final target and its witnesses, the recovery theorem, the non-skew instance, the separate manuscript clauses (stratified cap, stratum compactness and closedness, torus density, the node chart and its two rank facts) and the weighted linear algebra of `Seed`, `SeedAlgebra` and `SymmetrizerAlgebra`. The module audit covers 1,811 declarations; the receipt and log record the exact counts. The verifier additionally requires `SkewSeed.skeleton_recovery` and `Examples.nonSkewSeed_target_of_firstGeometricTarget` to appear in the report, so neither can silently drop out of the receipt.

Only `propext`, `Classical.choice`, and `Quot.sound` are permitted as transitive axioms. Missing audit results, `sorryAx`, additional axioms, and explicit project `axiom` or `opaque` declarations fail verification.

The verifier also checks:

- Lean 4.34.1 and every locked dependency revision.
- Clean dependency worktrees, including absence of untracked non-ignored files, before and after the checks.
- All 65 mathematical source files against [accepted-library.json](accepted-library.json).
- Identical hashes for all 73 compilation and audit inputs before and after verification.

The accepted-library manifest binds the reviewed mathematical source to its accepted source commit. The final receipt covers the delivered library together with the default import, consumer, audit, dependency configuration, and verifier.

## Included final evidence

The [final receipt](publication-check.json) records the result, toolchain, dependency revisions, source hashes, audit coverage, and SHA-256 hashes of these logs:

- [toolchain.log](toolchain.log): Lean version.
- [build.log](build.log): full library compilation.
- [final-consumer.log](final-consumer.log): final theorem consumers; a successful Lean check can produce an empty log.
- [axioms.log](axioms.log): module, generated-declaration, and final-root transitive axiom checks.

The committed receipt and logs were produced by `python3 scripts/verify.py` after the reviewed integration of the weighted library, at accepted source commit `a575aa236b485672f0606bba6ebc80571671f8a9`, following a managed `horizon-lean-check ClusterSkeleton` pass. All 73 input hashes match the delivered files, and every one of the 72 audited roots reports exactly `[propext, Classical.choice, Quot.sound]`.

The receipt and matching logs are retained in the repository. Re-running the verifier replaces them with the new result. It first sets the receipt status to `running`, so a failed or interrupted invocation cannot leave an old success marked as its result. A successful receipt has `status: passed`, `dependency_worktrees_clean: true`, and `source_stability_verified: true`, and its input hashes must match the delivered files.

[GitHub Actions](https://github.com/Hu-Mingyuan/cluster-skeleton/actions/workflows/lean.yml) also preserves the outputs for each run. The committed evidence remains available independently of CI artifact retention.

## Mathematical meaning and documents

The [statement review](statement-review.md) checks the definitions, quantifiers, and constructed witnesses against the intended real-geometric target. It distinguishes that review from compilation and from a line-by-line independent reproof of every lemma. The [theorem guide](../docs/target-theorem.md) and [proof map](../docs/proof-blueprint.md) identify the implemented claims.

The [document check](document-check.json) binds the current PDFs to their editable LaTeX sources and records document compilation and visual inspection. It is not a Lean proof receipt. The generalized target is in [the active objective](../docs/roadmap.md); the Lean statements it asks for are verified by the receipt above, and acceptance of the objective remains a maintainer's decision.
