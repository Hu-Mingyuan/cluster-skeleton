# Verify the formalization

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

The final existence theorem is `ClusterSkeleton.FullSkeleton.firstGeometricTarget`. Its witnesses construct the smooth presentation, primitive, Liouville field, and complete flow on the actual exchange space. `FullSkeleton.trappedSet_eq_coordinateCap` proves the full skeleton equality for that same flow.

[FullSkeletonConsumer.lean](FullSkeletonConsumer.lean) applies these proofs to the coordinate conditions and the complete Liouville manifold. [AxiomAudit.lean](AxiomAudit.lean) checks all 57 project modules in the root-import environment, including private and generated declarations, two explicit generated-declaration supplements, and eight direct final theorem/construction roots. The module audit covers 1,480 declarations; the receipt and log record the exact counts.

Only `propext`, `Classical.choice`, and `Quot.sound` are permitted as transitive axioms. Missing audit results, `sorryAx`, additional axioms, and explicit project `axiom` or `opaque` declarations fail verification.

The verifier also checks:

- Lean 4.34.1 and every locked dependency revision.
- Clean dependency worktrees, including absence of untracked non-ignored files, before and after the checks.
- All 57 mathematical source files against [accepted-library.json](accepted-library.json).
- Identical hashes for all 65 compilation and audit inputs before and after verification.

The accepted-library manifest binds the reviewed mathematical source to its accepted source commit. The final receipt covers the delivered library together with the default import, consumer, audit, dependency configuration, and verifier.

## Included final evidence

The [final receipt](publication-check.json) records the result, toolchain, dependency revisions, source hashes, audit coverage, and SHA-256 hashes of these logs:

- [toolchain.log](toolchain.log): Lean version.
- [build.log](build.log): full library compilation.
- [final-consumer.log](final-consumer.log): final theorem consumers; a successful Lean check can produce an empty log.
- [axioms.log](axioms.log): module, generated-declaration, and final-root transitive axiom checks.

The receipt and matching logs are retained in the repository. Re-running the verifier replaces them with the new result. It first sets the receipt status to `running`, so a failed or interrupted invocation cannot leave an old success marked as its result. A successful receipt has `status: passed`, `dependency_worktrees_clean: true`, and `source_stability_verified: true`, and its input hashes must match the delivered files.

[GitHub Actions](https://github.com/Hu-Mingyuan/cluster-skeleton/actions/workflows/lean.yml) also preserves the outputs for each run. The committed evidence remains available independently of CI artifact retention.

## Mathematical meaning and documents

The [statement review](statement-review.md) checks the definitions, quantifiers, and constructed witnesses against the intended real-geometric target. It distinguishes that review from compilation and from a line-by-line independent reproof of every lemma. The [theorem guide](../docs/target-theorem.md) and [proof map](../docs/proof-blueprint.md) identify the implemented claims.

The [document check](document-check.json) binds the three-page theorem PDF and thirteen-page proof PDF to their editable LaTeX sources and records all-page visual inspection. The result is the real smooth Liouville structure, complete flow, and full trapped-set equality described there; the broader categorical claims in the original notes are outside this theorem.
