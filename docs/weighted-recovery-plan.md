# The `D = I` recovery statement: what stage A delivers and what stage C must prove

Scope: acceptance check 2 of `docs/roadmap.md`, "a proved recovery of the old
`D = I` theorem, preserving the actual geometry and convention/sign matching",
for objective `7d3240fc-f412-49c4-88c8-a9d1a5a1bdaf` revision 2.

Prescribed by the delivered stage-A semantic review
`docs/reviews/stage-a-semantic-audit.md` §4, "The exact recovery theorem stage C
must prove", and RISK R1 (commit `4fe163223e348afdd4e0214970c451b797bb06c8`,
branch `weighted/stage-a-audit`). Base tree: stage A commit
`de58cd2c5a12942c6571c816d922ffd0bb837ac8`, reproduced here from the repository
file API because that commit object is not reachable from this checkout.

Everything below is `(S : SkewSeed d)`, the structure of the accepted
skew-symmetric library, and `S.toSeed` is its weighted reading
(`E := S.B`, `D := 1`, hence `K = B` with **no** sign change and **no**
transpose).

## 1. The recovery statement, in the review's (a) + (b) + (c) shape

### (a) The instantiation — **stage C**

```lean
theorem SkewSeed.liouvilleSkeletonTarget {d : ℕ} (S : SkewSeed d)
    (hdet : S.Unimodular) : LiouvilleSkeletonTarget S.toSeed :=
  FullSkeleton.liouvilleSkeletonTarget S.toSeed (S.toSeed_unimodular hdet)
```

Not provable at stage A: `FullSkeleton.liouvilleSkeletonTarget` is the weighted
theorem, and the chain `TorusPrimitive … GlobalPrimitive … FullSkeleton` is being
rewritten by stage B2. The only stage-A input it needs is delivered here as
`SkewSeed.toSeed_unimodular` (`ClusterSkeleton/SkewSeedRecovery.lean:97`), a
one-line consumer of the existing `toSeed_unimodular_iff`.

### (b) Convention and sign matching — **delivered**

```lean
theorem SkewSeed.torus_anchor_old_matrix {d : ℕ} (S : SkewSeed d)
    (P : SmoothPresentation S.toSeed) (p : (S.toSeed).Point)
    (v w : P.manifold.Tangent p) :
    P.logarithmicImaginaryValue p v w =
      ((1 / 2 : ℂ) * ∑ i : Fin d, ∑ j : Fin d, (S.B i j : ℂ) *
        ((P.coordinateDifferential i p v / p.a i) *
          (P.coordinateDifferential j p w / p.a j) -
         (P.coordinateDifferential i p w / p.a i) *
          (P.coordinateDifferential j p v / p.a j))).im
```

`ClusterSkeleton/SkewSeedRecovery.lean:122`. The literal shape of
`GeometryTarget.SmoothPresentation.logarithmicImaginaryValue`
(`ClusterSkeleton/GeometryTarget.lean:79-86`), with its `1/2` factor, and with
`(S.K i j : ℂ)` replaced by the old integer entry `(S.B i j : ℂ)`. This is the
clause that certifies "no sign flip": the weighted form at `D = 1, E := B` is
pointwise the baseline's `Im Ω_T`, not its negative, so the Liouville field and
flow are not time-reversed. Since `trappedSet` is a *forward*-orbit condition
and is not invariant under time reversal, this is the pivotal clause of
acceptance check 2.

Stage C uses it together with the weighted torus anchor in
`FullSkeleton.torus_anchor`: the recovered form on `initialTorus S.toSeed` is the
old form written with the old matrix.

### (c) The old objects on the old carrier — **delivered**

The old loci are defined on `S.Point`, i.e. on the carrier of the *old* exchange
equations (with the swapped monomials), with the reference's ambient predicates:

| old object | declaration | line |
| --- | --- | --- |
| `T = {z_1⋯z_n ≠ 0}` | `SkewSeed.initialTorus S` | 136 |
| `C_B` | `SkewSeed.coordinateCap S` | 141 |
| `Λ_I` | `SkewSeed.lambdaStratum S I` | 147 |

and they are identified with the weighted loci of `S.toSeed` along
`SkewSeed.pointHomeomorph`:

```lean
theorem image_initialTorus   : pointHomeomorph S '' initialTorus S   = ClusterSkeleton.initialTorus S.toSeed
theorem image_coordinateCap  : pointHomeomorph S '' coordinateCap S  = ClusterSkeleton.coordinateCap S.toSeed
theorem image_lambdaStratum  : pointHomeomorph S '' lambdaStratum S I = ClusterSkeleton.lambdaStratum S.toSeed I
theorem preimage_initialTorus, preimage_coordinateCap, preimage_lambdaStratum  -- the three preimage forms
theorem coordinateCap_eq_iUnion_lambdaStratum :
    coordinateCap S = ⋃ I : {I : Finset (Fin d) // S.Independent I}, lambdaStratum S I.val
theorem isCompact_lambdaStratum (I) (hI : I ⊆ S.mutable) : IsCompact (lambdaStratum S I)
theorem trappedSet_conjFlow (Φ : Flow ℝ ((S.toSeed).Point)) :
    trappedSet (conjFlow S Φ) = pointHomeomorph S ⁻¹' trappedSet Φ
```

so that the old stratified skeleton identity `Skel = C_B = ⋃_I Λ_I` on the old
carrier is the image of (a) under `pointHomeomorph`. The last step is packaged
as

```lean
theorem trappedSet_conjFlow_eq_coordinateCap (Φ : Flow ℝ ((S.toSeed).Point))
    (h : trappedSet Φ = ClusterSkeleton.coordinateCap S.toSeed) :
    trappedSet (conjFlow S Φ) = coordinateCap S
```

(`:318`): stage C feeds it the weighted skeleton identity from
`FullSkeleton.liouvilleData_trappedSet` and reads off the old identity on the
old carrier, then rewrites with `coordinateCap_eq_iUnion_lambdaStratum` for the
stratified form.

## 2. Smooth-structure route: **decision — state recovery directly for `S.toSeed`**

Chosen route: the review's recommended one. Recovery is stated as (a) + (b) +
(c) above, directly for `S.toSeed`, with the old loci and the old trapped set
transported along `pointHomeomorph` as *topological* objects.
**No transported smooth structure is claimed**, and
`SkewSeed.transportPresentation` is deliberately **not** delivered.

Reason, as required by RISK R1(2):

* `pointHomeomorph` is a homeomorphism, not a diffeomorphism, and pushing
  `SmoothPresentation` along it is **not** cheap in this Mathlib. Mathlib does
  supply the charted-space push-forward
  `Homeomorph.chartedSpace` (`Mathlib/Geometry/Manifold/ChartedSpace.lean:610`,
  via `IsLocalHomeomorph.chartedSpace`), but it supplies **no**
  `IsManifold`/`HasGroupoid` transport for it: its only use anywhere in Mathlib
  is `Mathlib/Geometry/Manifold/Instances/Quotient.lean:51`, and no groupoid
  compatibility lemma accompanies it. The `smooth` field of
  `SmoothPresentation` would therefore need a from-scratch
  `HasGroupoid (contDiffGroupoid ∞ 𝓘(ℝ, Model (2*d)))` proof for the
  conjugated atlas, plus transports of `inclusion_smooth` (a `ContMDiff`
  statement) and `inclusion_immersion` (injectivity of an `mfderiv`). That is a
  separate construction, not a corollary of `pointHomeomorph_val = rfl`.
* It is not needed. What acceptance check 2 and `docs/tex/target-theorem.tex`
  (lines 150–155: "the exchange space, the sign of the form, and the same-flow
  skeleton identity") pin is the exchange space, the form sign and the skeleton
  set. (b) pins the form sign with the old matrix, (c) pins the exchange space
  and the skeleton set on the old carrier, and (a) supplies the existential
  smooth structure on `S.toSeed` — which has the *same* point type and the same
  topology as the old carrier up to `pointHomeomorph`, with
  `pointHomeomorph_val` and `pointHomeomorph_symm_val` both `rfl`.
* Per RISK R1(1) the old smooth structure must therefore **not** be implicitly
  claimed anywhere: the recovery statement quantifies the smooth structure
  existentially through `LiouvilleSkeletonTarget S.toSeed`, exactly as the PDF
  does (`∀(n,E,D̃,M) ∃(smooth structure, λ, Z, Φ)`), and term identity of the
  flow with the baseline's constructed flow is **not** claimed (the atlases and
  `TorusCorrection.H` differ; see the review's RISK R1(1) and R3).

## 3. Equivalent reformulations and additions, relative to the prescribed shapes

* **`SkewSeed.Point.a` / `SkewSeed.Point.b`** (`:74`, `:77`) are new. The old
  predicates are written with `p.a j` and `p.b i`, but `SkewSeed.Point` is a
  subtype of a *different* predicate than `Seed.Point`, so `Seed.Point.a` and
  `Seed.Point.b` do not apply to it, and `ClusterSkeleton/SkewSeed.lean` is
  owned by another mission and is not edited. These are the same two
  projections (`p.1.1`, `p.1.2`), with
  `pointHomeomorph_a`/`_b`/`_symm_a`/`_symm_b` (`:82`–`:92`) all `rfl`.
* **`conjFlow S Φ`** (`:244`) replaces the review's notation
  `Φ.conj (pointHomeomorph S)`: Mathlib has no `Flow` conjugation or transport
  along a homeomorphism between two different carriers.
  `Mathlib/Dynamics/Flow.lean` offers only `Homeomorph.flow` (the discrete
  `ℤ`-flow of a self-homeomorphism, line 154) and `Flow.IsSemiconjugacy`
  (line 267), neither of which produces a `Flow ℝ S.Point` from a
  `Flow ℝ ((S.toSeed).Point)`. `conjFlow` is built from
  `Homeomorph.continuous` on both sides and the group laws of `Φ`;
  `pointHomeomorph_conjFlow` (`:263`) records that `pointHomeomorph` really is
  a conjugation of the two flows.
* **`forwardOrbit_conjFlow`** is delivered in all three forms the mission
  allows: the image form (`:269`), the preimage form (`:282`) and the forward
  image form (`:291`).
* **`isCompact_lambdaStratum`** (`:221`) carries the hypothesis
  `hI : I ⊆ S.mutable`, matching its weighted source
  `CapStrata.isCompact_lambdaStratum`, which needs it for the inclusion into
  the cap. `isCompact_coordinateCap` (`:228`) is added for the cap itself; it
  needs no hypothesis.
* **`coordinateCap_eq_iUnion_lambdaStratum`** (`:206`) is indexed by
  `{I : Finset (Fin d) // S.Independent I}`, the *old* independence predicate.
  This is the same index set as the weighted one, because
  `toSeed_independent_iff` is `Iff.rfl`; no transport of the index set is
  needed, as the review notes.
* **`toSeed_K_matrix`** (`:112`) is delivered in the prescribed matrix form, and
  the pointwise ℂ-cast lemma `toSeed_K_complex` (`:104`) is delivered as well
  and is the `simp` lemma that discharges (b).
* Inside `namespace ClusterSkeleton.SkewSeed` the new old-carrier loci shadow
  the weighted ones, so the weighted loci are written
  `_root_.ClusterSkeleton.initialTorus` etc. in the source. The statements are
  the ones displayed above.

## 4. Remaining stage-C obligations

1. **Clause (a):** `SkewSeed.liouvilleSkeletonTarget`, from the weighted
   `FullSkeleton.liouvilleSkeletonTarget` and `SkewSeed.toSeed_unimodular`.
   Blocked until stage B2/C finish rewriting `TorusPrimitive … GlobalPrimitive …
   FullSkeleton` for the weighted seed; one line once they do.
2. **The old skeleton identity as the image of (a):** destructure the
   existential of `LiouvilleSkeletonTarget S.toSeed`, feed its flow to
   `trappedSet_conjFlow_eq_coordinateCap`, and rewrite with
   `coordinateCap_eq_iUnion_lambdaStratum` for the stratified form
   `Skel = C_B = ⋃_I Λ_I` on `S.Point`.
3. **Clause (b) on the torus:** combine `torus_anchor_old_matrix` with
   `FullSkeleton.torus_anchor` on `initialTorus S.toSeed`, and transport the
   torus along `image_initialTorus` / `preimage_initialTorus` where the old
   carrier is wanted.
4. **Import wiring:** add `import ClusterSkeleton.SkewSeedRecovery` to
   `ClusterSkeleton.lean`. Deliberately not done here —
   `ClusterSkeleton.lean` is outside this mission's file whitelist; the
   integration mission owns it.
5. **Not an obligation of this route, and must not be claimed:** a transported
   smooth structure on `S.Point`, or term identity of the recovered flow with
   the baseline's constructed flow. See §2 and the review's RISK R1.
6. **Still open from the review, outside this mission:** RISK R3 — the signs of
   `TorusCorrection.H` and `TorusPrimitive.alpha` must be re-derived in stage B
   from the *column* convention; defect D1's docstring, corrected on this
   branch, is the sentence that derivation reads.

## 5. Everything proved on this branch, with `file:line`

All in `ClusterSkeleton/SkewSeedRecovery.lean`, namespace
`ClusterSkeleton.SkewSeed`, all for `(S : SkewSeed d)`.

| line | declaration | content |
| --- | --- | --- |
| 74 | `Point.a` | ambient original coordinates of an old point |
| 77 | `Point.b` | mutation partners of an old point |
| 82 | `pointHomeomorph_a` | `(pointHomeomorph S p).a j = p.a j`, `rfl` |
| 86 | `pointHomeomorph_b` | `(pointHomeomorph S p).b i = p.b i`, `rfl` |
| 89 | `pointHomeomorph_symm_a` | the same for the inverse, `rfl` |
| 92 | `pointHomeomorph_symm_b` | the same for the inverse, `rfl` |
| 97 | `toSeed_unimodular` | `S.Unimodular → (S.toSeed).Unimodular` |
| 104 | `toSeed_K_complex` | `(((S.toSeed).K i j : ℚ) : ℂ) = (S.B i j : ℂ)` |
| 112 | `toSeed_K_matrix` | `(S.toSeed).K.map (↑) = S.B.map (↑)` over ℂ |
| 122 | `torus_anchor_old_matrix` | **(b)**: the form coefficient is the old `S.B` |
| 136 | `initialTorus` | old `T` on `S.Point` |
| 141 | `coordinateCap` | old `C_B` on `S.Point` |
| 147 | `lambdaStratum` | old `Λ_I` on `S.Point` |
| 153 | `mem_initialTorus_iff` | membership transport, `Iff.rfl` |
| 158 | `mem_coordinateCap_iff` | membership transport, `Iff.rfl` |
| 163 | `mem_lambdaStratum_iff` | membership transport, `Iff.rfl` |
| 168 | `preimage_initialTorus` | preimage form |
| 173 | `preimage_coordinateCap` | preimage form |
| 178 | `preimage_lambdaStratum` | preimage form |
| 183 | `image_of_preimage` | private: image from preimage, via surjectivity |
| 187 | `image_initialTorus` | image form |
| 192 | `image_coordinateCap` | image form |
| 197 | `image_lambdaStratum` | image form |
| 206 | `coordinateCap_eq_iUnion_lambdaStratum` | old cap `= ⋃_I` old strata |
| 221 | `isCompact_lambdaStratum` | old stratum compact |
| 228 | `isCompact_coordinateCap` | old cap compact |
| 244 | `conjFlow` | the conjugate flow on the old carrier |
| 256 | `conjFlow_apply` | its defining formula, `rfl` |
| 263 | `pointHomeomorph_conjFlow` | `pointHomeomorph` conjugates the two flows |
| 269 | `forwardOrbit_conjFlow` | forward orbits, image form |
| 282 | `forwardOrbit_conjFlow_preimage` | forward orbits, preimage form |
| 291 | `image_forwardOrbit_conjFlow` | forward orbits, forward image form |
| 301 | `trappedSet_conjFlow` | **the skeleton set transports** |
| 309 | `image_trappedSet_conjFlow` | the same, image direction |
| 318 | `trappedSet_conjFlow_eq_coordinateCap` | the old skeleton identity, given the weighted one |

Docstring corrections (statements, names and proofs unchanged):

* **D1** `ClusterSkeleton/NodeCoordinates.lean:73` (docstring from `:60`) —
  `exchangeCharacter_eq_zpow_product`: the docstring said the quantity is the
  reference's inverse character `1/t_i`; with stage A's column convention it is
  the reference character `t_i = z^{c_i} = ∏_j z_j^{E_{ji}}` itself. The module
  header (`:13`) now states the column convention too.
* **D2** `ClusterSkeleton/ZeroSet.lean:31` `Seed.Point.outgoing_ne_zero`
  (docstring from `:22`) and `ClusterSkeleton/CapIndependence.lean:63`
  `coordinateCap_outgoing_not_interior` (docstring from `:54`): the hypothesis `0 < S.B i j`
  (`= 0 < S.E j i`) is an arrow `j → i`, i.e. `j` occurs in `P_i^+` and is a
  *predecessor* of `i`, not an outgoing neighbour. Both docstrings now say so;
  the stale names are retained, with the reason, because renaming would ripple
  into files other missions own.

## 6. Checks

`horizon-lean-check ClusterSkeleton.SkewSeedRecovery
ClusterSkeleton.NodeCoordinates ClusterSkeleton.ZeroSet
ClusterSkeleton.CapIndependence` — all pass. No `sorry`. Every declaration
listed in §5 was audited with `#print axioms` in a scratch file run through
`lake env lean` (deleted before committing) and depends only on
`propext`, `Classical.choice`, `Quot.sound`; the private `image_of_preimage` is
covered transitively by its three public consumers.

The stage-A tree does not build as a whole at this commit, and is not expected
to: the stage-B/C modules `TorusPrimitive … GlobalPrimitive … FullSkeleton` have
not yet been adapted to the weighted seed. That is stage B2's and stage C's
work, not this mission's.
