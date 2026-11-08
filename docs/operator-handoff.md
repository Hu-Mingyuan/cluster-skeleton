# Operator handoff after the stratified skeleton acceptance

The formalization phase was accepted on 8 November 2026 at verification head
`eeefb7b54647fdb9be610c8b99528d407857c34d`, with accepted Lean source commit
`4c02c1e5bbc68907552632344ae04017d82a30b4`. Gaps **G1** (the stratified
`⋃_{I independent} Λ_I` identity) and **G2** (the literal `d - 2|I|` torus
exponent) are closed and machine-checked; see
[verification records](../verification/README.md) and the G1/G2 sections of
[the audit](skeleton-audit.md).

Two steps remain, and step 2 is already half done off-host. Both need a host
operator: the publication host that produced the accepted evidence has neither a
Git push credential nor a LaTeX toolchain, so no automated session can perform
them. Neither step affects the mathematics, and neither leaves any accepted
theorem conditional.

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
`d - 2|I|` torus rank. Use **XeLaTeX on TeX Live 2024**, the toolchain recorded
for the committed PDFs; a different engine can change the output even where the
source is unchanged. Overwrite in place at the repository root, as the project
roadmap asked. Do not add new PDF filenames. Both documents use
`docs/tex/preamble.tex`.

### 2a. `target-theorem.pdf` — done off-host, awaiting the rest

A regenerated [`target-theorem.pdf`](../target-theorem.pdf) was placed in the
publication checkout at 22:59:29 UTC on 8 November 2026 and is committed here.
It was built elsewhere, since this host has no LaTeX: its metadata reports
`/Producer (xdvipdfmx (20220710))`, the XeTeX driver, consistent with the
recorded engine.

It is a genuine rebuild of the current source, not the old file: it runs to
4 pages where the previous one had 3, it carries the new
`Reference strata` definition and the `Skel = ⋃_{I independent} Λ_I` equality,
and its Lean-correspondence table now lists `lambdaStratum`,
`coordinateCap_eq_iUnion_lambdaStratum`,
`FullSkeleton.trappedSet_eq_iUnion_lambdaStratum`, the chart-rank row for
`IndependentNodeChart.complementRank_eq_sub_two_mul_card` and its companion
`two_mul_card_le`. That content check was made by extracting the PDF text; **no
page-by-page visual inspection was performed**, so the visual QA for this file
is still outstanding and is part of step 2c.

### 2b. `proof-blueprint.pdf` — still stale

[`proof-blueprint.pdf`](../proof-blueprint.pdf) has not been rebuilt. It still
dates from 17:29 UTC, before the stratified restatement, while its source
`docs/tex/proof-blueprint.tex` refers to the new declarations in seven places.
Rebuild it from that source with the same engine.

### 2c. Rewrite `verification/document-check.json`

Rewrite [`verification/document-check.json`](../verification/document-check.json)
rather than only refreshing its hashes. That file has not changed since commit
`2c239b0`, and it was already inaccurate before this work began:

| Recorded entry | State today |
| --- | --- |
| `docs/tex/preamble.tex` | matches |
| `docs/tex/target-theorem.tex` | stale, source edited for G1/G2 |
| `docs/tex/proof-blueprint.tex` | stale, source edited for G1/G2 |
| `target-theorem.pdf` | stale; superseded again by the 22:59 rebuild |
| `proof-blueprint.pdf` | stale, PDF already replaced at commit `262e47e` |

Both PDFs had in fact been replaced at commit `262e47e` without the check being
updated, so its `"All 16 rendered pages visually inspected"` line refers to
files that are no longer in the tree, and its page counts of 3 and 13 are both
questionable: the rebuilt theorem PDF has 4 pages. Record a fresh inspection of
both regenerated documents, with their real page counts and hashes, rather than
editing the old numbers.

This step affects typesetting and visual QA only. `document-check.json` is
outside the Lean verification scope and is not referenced by
`verification/publication-check.json`, so none of it touches the accepted
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
