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

The final existence theorem is `ClusterSkeleton.FullSkeleton.firstGeometricTarget`. Its witnesses construct the smooth presentation, primitive, Liouville field, and complete flow on the actual exchange space. `FullSkeleton.trappedSet_eq_coordinateCap` proves the full skeleton equality for that same flow, and `FullSkeleton.trappedSet_eq_iUnion_lambdaStratum` restates it as the union `⋃_{I independent} Λ_I` of the strata defined in `ClusterSkeleton/CapStrata.lean`.

[FullSkeletonConsumer.lean](FullSkeletonConsumer.lean) applies these proofs to the coordinate conditions and the complete Liouville manifold. [AxiomAudit.lean](AxiomAudit.lean) checks all 58 project modules in the root-import environment, including private and generated declarations, two explicit generated-declaration supplements, and eleven direct final theorem/construction roots. The eleven roots are the eight original ones together with `FullSkeleton.trappedSet_eq_iUnion_lambdaStratum`, `coordinateCap_eq_iUnion_lambdaStratum` and `IndependentNodeChart.complementRank_eq_sub_two_mul_card`. The module audit covers 1,492 declarations; the receipt and log record the exact counts.

Only `propext`, `Classical.choice`, and `Quot.sound` are permitted as transitive axioms. Missing audit results, `sorryAx`, additional axioms, and explicit project `axiom` or `opaque` declarations fail verification.

The verifier also checks:

- Lean 4.34.1 and every locked dependency revision.
- Clean dependency worktrees, including absence of untracked non-ignored files, before and after the checks.
- All 58 mathematical source files against [accepted-library.json](accepted-library.json).
- Identical hashes for all 66 compilation and audit inputs before and after verification.

The accepted-library manifest binds the reviewed mathematical source to its accepted source commit. The final receipt covers the delivered library together with the default import, consumer, audit, dependency configuration, and verifier.

## Included final evidence

The [final receipt](publication-check.json) records the result, toolchain, dependency revisions, source hashes, audit coverage, and SHA-256 hashes of these logs:

- [toolchain.log](toolchain.log): Lean version.
- [build.log](build.log): full library compilation.
- [final-consumer.log](final-consumer.log): final theorem consumers; a successful Lean check can produce an empty log.
- [axioms.log](axioms.log): module, generated-declaration, and final-root transitive axiom checks.

The committed receipt and logs were produced by `python3 scripts/verify.py` on the publication host after the G1/G2 integration, at accepted source commit `4c02c1e5bbc68907552632344ae04017d82a30b4`. Earlier receipts in this repository's history were produced by [CI run 40066281409](https://github.com/Hu-Mingyuan/cluster-skeleton/actions/runs/40066281409). All 66 input hashes match the delivered files.

The receipt and matching logs are retained in the repository. Re-running the verifier replaces them with the new result. It first sets the receipt status to `running`, so a failed or interrupted invocation cannot leave an old success marked as its result. A successful receipt has `status: passed`, `dependency_worktrees_clean: true`, and `source_stability_verified: true`, and its input hashes must match the delivered files.

[GitHub Actions](https://github.com/Hu-Mingyuan/cluster-skeleton/actions/workflows/lean.yml) also preserves the outputs for each run. The committed evidence remains available independently of CI artifact retention.

## Mathematical meaning and documents

The [statement review](statement-review.md) checks the definitions, quantifiers, and constructed witnesses against the intended real-geometric target. It distinguishes that review from compilation and from a line-by-line independent reproof of every lemma. The [theorem guide](../docs/target-theorem.md) and [proof map](../docs/proof-blueprint.md) identify the implemented claims.

The [document check](document-check.json) binds the three-page theorem PDF and thirteen-page proof PDF to their editable LaTeX sources and records all-page visual inspection. It predates the G1/G2 integration: the `docs/tex/` sources now also state the stratified identity and the `d - 2|I|` torus rank, while the two PDFs are unchanged, because the publication host has no LaTeX toolchain. Regenerating the PDFs and refreshing this check is the one open documentation step. The result is the real smooth Liouville structure, complete flow, and full trapped-set equality described there; the broader categorical claims in the original notes are outside this theorem.
