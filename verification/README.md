# Verification records

On a fresh checkout, obtain the pinned dependency cache with `bash scripts/fetch-cache.sh`. For subsequent checks, run `python3 scripts/verify.py` from the repository root. Elan, Git and Python 3 are required. Lean and library revisions are pinned by the committed toolchain and Lake manifest.

The script builds the project, checks the selected declarations' transitive axiom dependencies, rejects proof placeholders in the project sources, and records exact source hashes. The permitted axioms are `propext`, `Classical.choice` and `Quot.sound`. The receipt is `first-batch.json`; logs are kept locally and as private CI artifacts.

The private GitHub workflow performs the same check on pushes and pull requests. A failing or pending workflow is not verification. The target proposition remains unproved even when all first-batch checks pass. The target's fidelity to the manuscript requires mathematical review in addition to kernel checking.

Local Horizon registration receipts and runtime configuration are not part of the repository. No GitHub Pages publication is configured.

## Validated first batch

Commit `14549f35dc0289b775b234a014fac2c7cefd719d` passed [private CI](https://github.com/Hu-Mingyuan/cluster-skeleton/actions/runs/39431898775), including compilation and all 27 audited declarations. Its immutable [receipt](ci-14549f3.json) contains hashes for nine project Lean sources, checked against the local checkout. The complete Liouville existence and skeleton equality target remains open.
