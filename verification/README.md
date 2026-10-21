# Verification and provenance

## Publication result — 21 October 2026

The isolated standard Lake build and the standalone final consumer passed. The publication audit checked 1,480 declarations attributed to all 57 project modules in the root-import environment, two explicit generated-declaration supplements, and eight direct final theorem/construction roots. Only the three allowed foundational axioms occurred. This new root-import audit does not replace or claim the scope of Horizon's larger historical multi-context audit.

The committed local receipt has SHA256 `fcfc4f6d65c4796eb10a9217341adfd795c440c06d4f283c87f278567a1f721e`. Its source and log hashes were checked again against the publication files. The PDF compilation and full-page visual checks are recorded in [`document-check.json`](document-check.json).

## Reproducible final-theorem check

From the repository root, with Elan, Git and Python 3 installed:

```sh
bash scripts/fetch-cache.sh
python3 scripts/verify.py
```

The cache step materializes the locked dependencies and obtains their Mathlib artifacts; it does not update dependency revisions. The verifier checks the pinned Lean version and package commits, builds the full `ClusterSkeleton` library, checks `FullSkeletonConsumer.lean`, and runs `AxiomAudit.lean`.

The audit traverses transitive axioms for declarations attributed to every project module, including private and generated declarations. It also checks the final equality and existence theorem roots explicitly:

- `ClusterSkeleton.FullSkeleton.trappedSet_eq_coordinateCap`
- `ClusterSkeleton.FullSkeleton.liouvilleData` and its associated flow, torus, and skeleton statements
- `ClusterSkeleton.FullSkeleton.liouvilleSkeletonTarget_of_parameters`
- `ClusterSkeleton.FullSkeleton.liouvilleSkeletonTarget`
- `ClusterSkeleton.FullSkeleton.firstGeometricTarget`

Only `propext`, `Classical.choice`, and `Quot.sound` are allowed. A reachable `sorryAx` or an extra geometric axiom fails the audit. Explicit project `axiom` and `opaque` declarations are rejected as well.

The machine-readable result is [`publication-check.json`](publication-check.json). Read its `status`, exact source hashes, final theorem names, module counts, and dependency revisions; only `status: passed` is a successful check. A new invocation first replaces any old success status with `running`, so an interrupted or failed check cannot masquerade as fresh success. Build, final-consumer, toolchain, and axiom logs are preserved locally and as private CI artifacts.

The default library entry point imports the final theorem. Private GitHub Actions uses the same verification script. [Check the workflow status](https://github.com/Hu-Mingyuan/cluster-skeleton/actions) for the particular uploaded revision; a pending or failing run is not a passing verification.

## Exact source provenance

The mathematical library was exported from the accepted private Horizon source commit:

- Commit: `03f558f67301b9514c92ef1833dca1bd56b45ab7`.
- Tree: `073177fc635f99a05cc2da8a4ee626ce2f52ddba`.
- [`accepted-library.json`](accepted-library.json) records a byte comparison and hashes for all 57 mathematical library files.

The publication adds the final default import, a reproducible final-root audit, updated documentation, and the rewritten PDFs. The accepted development commit is provenance; it is not a substitute for checking the publication's exact source hashes. The publication build uses an isolated directory and pinned dependency artifacts, without reusing any project's compiled Lean modules from the Horizon workspace.

## Mathematical statement review

[`statement-review.md`](statement-review.md) records the independent statement review and its scope. The Lean kernel checks derivations; it does not decide whether the chosen definitions express the intended problem. The definitions, quantified statement, and paper proof must therefore be reviewed separately.

The result is a real smooth Liouville structure with complete flow and full trapped-set equality on the literal exchange space. It does not certify every assertion in the original broader notes.

## Historical development material

[`ci-14549f3.json`](ci-14549f3.json) is an older, first-batch receipt for 27 declarations. It is retained as history and does **not** certify the later final theorem.

Other `*Consumer.lean` files and `*Interface.md` notes record development-stage consumer contracts. The standard publication command checks the final consumer and the full library; it does not claim to re-run every historical intermediate consumer. Horizon runtime configuration, credentials, and operational transcripts are not included. No GitHub Pages publication is configured.
