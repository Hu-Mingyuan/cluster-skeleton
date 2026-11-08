# Operator handoff after the stratified skeleton acceptance

The formalization phase was accepted on 8 November 2026 at verification head
`eeefb7b54647fdb9be610c8b99528d407857c34d`, with accepted Lean source commit
`4c02c1e5bbc68907552632344ae04017d82a30b4`. Gaps **G1** (the stratified
`⋃_{I independent} Λ_I` identity) and **G2** (the literal `d - 2|I|` torus
exponent) are closed and machine-checked; see
[verification records](../verification/README.md) and the G1/G2 sections of
[the audit](skeleton-audit.md).

Two steps remain. Both need a host operator: the publication host that produced
the accepted evidence has neither a Git push credential nor a LaTeX toolchain,
so no automated session can perform them. Neither step affects the mathematics,
and neither leaves any accepted theorem conditional.

## 1. Deliver the accepted head to the origin default branch

`origin` is `http://127.0.0.1:3030/horizonadmin/cluster-skeleton-workspace.git`.
Its `refs/heads/main` is still at `3856e9c9` (20 October 2026). On the
publication host `git ls-remote origin` fails with `could not read Username`
and a push returns HTTP 401, so the accepted work has been delivered only on
host-written recovery refs.

The accepted verification head is available at

```
refs/heads/horizon/recovery/bd065120-1b7d-44fd-a5da-163e05110e6a/eeefb7b54647fdb9be610c8b99528d407857c34d
```

From a checkout with push rights, fast-forward the default branch to the current
tip of local `main`, which is this commit and has `eeefb7b5` as an ancestor:

```sh
git fetch <publication-host-remote> 'refs/heads/main:refs/remotes/host/main'
git push origin host/main:refs/heads/main   # fast-forward only; do not force
```

Alternatively, confirm that recovery-ref delivery is the accepted delivery route
for this project, in which case no push is required and this step is closed by
that decision.

## 2. Regenerate both PDFs in place

The editable sources in [`docs/tex`](tex) state the stratified identity and the
`d - 2|I|` torus rank. The two committed PDFs predate them:

| File | Needs rebuilding from |
| --- | --- |
| [`target-theorem.pdf`](../target-theorem.pdf) | `docs/tex/target-theorem.tex` |
| [`proof-blueprint.pdf`](../proof-blueprint.pdf) | `docs/tex/proof-blueprint.tex` |

Both use `docs/tex/preamble.tex`. On the publication host `pdflatex`, `latexmk`,
`lualatex`, `xelatex` and `tectonic` are all absent. On a host with LaTeX,
overwrite the two PDFs in place at the repository root. Use the same toolchain
that produced the committed ones, **XeLaTeX on TeX Live 2024**, as recorded in
`verification/document-check.json`; a different engine can change the output
even where the source is unchanged.

Overwriting in place is deliberate: it is what the project roadmap asked for.
Do not add new PDF filenames.

Then rewrite [`verification/document-check.json`](../verification/document-check.json)
rather than only refreshing its hashes. That file has not been updated since
commit `2c239b0`, and **four of its five recorded hashes are already stale**:

| Recorded entry | State today |
| --- | --- |
| `docs/tex/preamble.tex` | matches |
| `docs/tex/target-theorem.tex` | stale, source edited for G1/G2 |
| `docs/tex/proof-blueprint.tex` | stale, source edited for G1/G2 |
| `target-theorem.pdf` | stale, PDF already replaced at commit `262e47e` |
| `proof-blueprint.pdf` | stale, PDF already replaced at commit `262e47e` |

So the file does not describe the currently committed PDFs at all, and its
"all 16 rendered pages visually inspected" line refers to PDFs that are no
longer in the tree. The page counts it records, 3 and 13, should also be
re-checked rather than assumed. A fresh visual inspection of the regenerated
PDFs is needed, not a hash refresh.

This affects typesetting and visual QA only. `document-check.json` is outside
the Lean verification scope and is not referenced by
`verification/publication-check.json`, so none of this touches the accepted
formalization.

## What must not be redone

The Lean library, its receipt and its axiom audit are complete and were
independently reproduced at `eeefb7b5`: a full `ClusterSkeleton` build passes,
`verification/AxiomAudit.lean` regenerates `verification/axioms.log`
byte-for-byte, `verification/FullSkeletonConsumer.lean` passes with no output,
and all 58 library files match `verification/accepted-library.json`. Re-running
`python3 scripts/verify.py` after step 2 is optional and will replace the
receipt with an equivalent one; the Lean inputs are unchanged by either step
above.
