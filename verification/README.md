# Verification records

Run `bash scripts/fetch-cache.sh` and `python3 scripts/verify.py` from the repository root. Elan, Git and Python 3 are required. Lean and library revisions are pinned by the committed toolchain and Lake manifest.

The script builds the project, checks the selected declarations' transitive axiom dependencies, rejects proof placeholders in the project sources, and records exact source hashes. The permitted axioms are `propext`, `Classical.choice` and `Quot.sound`. The receipt is `first-batch.json`; logs are kept locally and as private CI artifacts.

The private GitHub workflow performs the same check on pushes and pull requests. A failing or pending workflow is not verification. The target proposition remains unproved even when all first-batch checks pass. The target's fidelity to the manuscript requires mathematical review in addition to kernel checking.

Local Horizon registration receipts and runtime configuration are not part of the repository. No GitHub Pages publication is configured.
