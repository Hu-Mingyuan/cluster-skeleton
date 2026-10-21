# Native local form gluing contract

Owned source: `ClusterSkeleton/LocalFormGluing.lean` and
`verification/LocalFormGluingConsumer.lean`. Publication parent is the accepted
55-file TorusPrimitive commit `a4362fb3aa4e8162c59574190adc82955520d85a`.
Its files and modes are preserved; only these two files and this interface are
added. Unrelated workspace extras are retained but excluded from publication.

## Mathematical interface

For any pinned `FsFltz.Geometry.SmoothManifold n`, degree `k`, index type,
indexed open cover `U`, native dependent-fiber forms `eta i`, and dense set `D`,
`LocallySmooth M (U i) (eta i)` means exactly:

```
∀ a y, y ∈ (chartAt (Model n) a).target →
  (chartAt (Model n) a).symm y ∈ U i →
  ContDiffAt ℝ ∞ (M.formInChart a (eta i)) y
```

There is no global smoothness assumption on the totalized local forms.
`eqOn_overlap_of_dense` derives their equality on each full open overlap from
agreement only on its intersection with `D`. It proves coefficient continuity
in one fixed native chart, applies density there, and reconstructs the actual
tangent-fiber form using `formInChart_comp_chartTangentMap`. Both differentials
are the pinned native `mfderiv`; dependent tangent fibers are not identified
by an arbitrary transport.

`glue` selects one covering index separately at each point. `glue_eq` proves
all local restrictions; `glue_eq_selection` proves independence from any
subordinate selection. `isSmoothForm_glue` uses a neighborhood in one open
domain and native chart coefficient germs. `eq_glue_of_restrictions` proves
uniqueness even among all native forms. `existsUnique_smooth_gluing` packages
existence and uniqueness among smooth forms. `glue_eq_on_dense` preserves
agreement with any specified form on `D`. `glue_eval` works with arbitrary
tuples in the original tangent fiber, for every degree including zero.

`smoothAtlas_existsUnique_gluing` specializes this contract to the accepted
atlas on the actual complex exchange-point subtype, using the proved
`dense_initialTorus`. Its local family, local smoothness, and initial-torus
agreement are explicit supplied hypotheses. The carrier and induced topology,
variable nonzero frozen coordinates, full skew integer determinant-one matrix,
and mutable-only acyclicity remain those of the accepted `Seed` presentation.

## Consumers

The degree-one example uses the native real model with two domains
`x₀ < 1` and `-1 < x₀`. Their overlap contains zero; points with coordinate
`2` and `-2` witness proper overlap and exclusive portions of both domains.
Each local form is the coordinate covector on its own domain and zero outside.
The totalizations differ, and the smoothness proof uses only local constant
coefficient germs. The dense set omits zero, which lies in the overlap;
overlap equality at that omitted point is obtained through the general theorem.
The glued form evaluates to `v₀` on every native tangent vector.

Additional consumers cover uniqueness, restriction to the dense set, dimension
zero (all one-form evaluations vanish), and an empty index type on any empty
native manifold. No nonemptiness assumption is needed in the generic theorem.
The exchange-point degree-one consumer remains a reusable conditional theorem.

## Verification and scope

Exact managed check receipts, full file/mode and theorem manifests, pinned
source/import/output identities, complete inherited 740-root evidence plus all
new private/generated roots and nine supplements, and verified private
publication are supplied in the source-bound delivery artifact. The consumer
uses native `Lean.collectAxioms` per selected root and rejects everything except
`propext`, `Classical.choice`, and `Quot.sound`. The live audit is unchanged.
Independent mathematical acceptance is separate from these compilation checks.

The manuscript source is the existing October 20, 2026 PDF, pages 9–11,
Lemma 2.4 and equations (2.7)–(2.8). These motivate later gluing but do not
provide a local primitive family as an input to this delivery. Construction
of that family, global primitive/exterior-derivative identities, a complete
Liouville flow, and the full same-flow skeleton remain open. The existing root
through successor67 owns final source composition and audit adoption.
