import ClusterSkeleton.FullSkeleton
import ClusterSkeleton.SkewSeedRecovery

/-!
# Recovery of the old `D = I` skeleton theorem

The weighted library proves `LiouvilleSkeletonTarget S` for every unimodular
weighted seed. This file reads that theorem back on the old skew-symmetric
input, which is acceptance check 2 of `docs/roadmap.md`: the old theorem is
recovered *with its geometry*, not merely as a formal consequence.

The route is the one decided in `docs/weighted-recovery-plan.md` §2, following
`docs/reviews/stage-a-semantic-audit.md` §4:

* **(a)** `SkewSeed.liouvilleSkeletonTarget` instantiates the weighted theorem
  at `S.toSeed` (`E := B`, `D := 1`), whose only hypothesis is unimodularity of
  the old matrix.
* **(b)** `liouvilleData_torus_anchor_old_matrix` writes the anchored two-form
  of *that very* Liouville datum with the **old integer matrix** `S.B`, with no
  transpose, no sign change and no extra factor. The forward-orbit trapped set
  is not invariant under time reversal, so this clause is what makes the
  recovery a recovery of the old dynamics rather than of its time reverse.
* **(c)** `liouvilleData_trappedSet_conjFlow` and its stratified form put the
  skeleton identity back on the **old carrier** `S.Point`, for the flow
  conjugate to the same constructed flow, and `dense_initialTorus` transports
  density of the old torus. Both use only `SkewSeed.pointHomeomorph`.

`skeleton_recovery` packages (b) and (c) for one presentation and one Liouville
datum.

No transported smooth structure on `S.Point` is claimed — `pointHomeomorph` is a
homeomorphism, not a diffeomorphism — and no term identity of the recovered flow
with the baseline library's constructed flow is claimed; see
`docs/weighted-recovery-plan.md` §2 and the review's RISK R1. The smooth
structure enters existentially, through `LiouvilleSkeletonTarget S.toSeed`,
exactly as in `docs/tex/target-theorem.tex`.
-/

noncomputable section
set_option autoImplicit false
open scoped Manifold ContDiff Topology BigOperators
open Set FsFltz.Geometry FsFltz.Geometry.SmoothManifold

namespace ClusterSkeleton.SkewSeed

variable {d : ℕ} {ε κ δ : ℝ}

/-! ### (a) The instantiation of the weighted theorem -/

/-- **Recovery, clause (a).** The old skew-symmetric input satisfies the first
geometric target in its weighted reading `S.toSeed`, under its own
unimodularity hypothesis and nothing else. -/
theorem liouvilleSkeletonTarget (S : SkewSeed d) (hdet : S.Unimodular) :
    LiouvilleSkeletonTarget S.toSeed :=
  FullSkeleton.liouvilleSkeletonTarget S.toSeed (S.toSeed_unimodular hdet)

/-! ### (c) Density of the old torus

The old torus is the preimage of the weighted one along `pointHomeomorph`, so
density transports along the inverse homeomorphism. -/

/-- The old initial torus `T = {z_1 ⋯ z_n ≠ 0}` is dense in the old carrier. -/
theorem dense_initialTorus (S : SkewSeed d) (hdet : S.Unimodular) :
    Dense (initialTorus S) := by
  have h := ((pointHomeomorph S).symm.isDenseEmbedding.dense_image).mpr
    (_root_.ClusterSkeleton.dense_initialTorus S.toSeed (S.toSeed_unimodular hdet))
  rwa [Homeomorph.image_eq_preimage_symm, Homeomorph.symm_symm,
    preimage_initialTorus] at h

/-! ### (b) and (c) for the constructed Liouville datum

Everything below is stated for the presentation `SmoothAtlas.presentation` and
the Liouville datum `FullSkeleton.liouvilleData` of the weighted library, i.e.
for the same witnesses that clause (a) produces, at arbitrary admissible cutoff
parameters. -/

/-- **Recovery, clause (b).** The anchored two-form of the constructed Liouville
datum is, on the weighted initial torus, the old logarithmic two-form written
with the **old integer matrix** `(S.B i j : ℂ)`: no transpose, no sign change,
no extra factor. Combination of the weighted anchor
`FullSkeleton.torus_anchor` with `torus_anchor_old_matrix`. -/
theorem liouvilleData_torus_anchor_old_matrix (S : SkewSeed d)
    (hdet : S.Unimodular) (hε : 0 < ε) (hκ : 2 * ε + 1 ≤ κ) (hδ : 0 < δ)
    (p : (S.toSeed).Point)
    (hp : p ∈ _root_.ClusterSkeleton.initialTorus S.toSeed)
    (v w : (SmoothAtlas.presentation S.toSeed
      (S.toSeed_unimodular hdet)).manifold.Tangent p) :
    evalTwo
      ((SmoothAtlas.presentation S.toSeed
          (S.toSeed_unimodular hdet)).manifold.exteriorDerivative
        (FullSkeleton.liouvilleData S.toSeed
          (S.toSeed_unimodular hdet) hε hκ hδ).primitive) p v w =
      ((1 / 2 : ℂ) * ∑ i : Fin d, ∑ j : Fin d, (S.B i j : ℂ) *
        (((SmoothAtlas.presentation S.toSeed
              (S.toSeed_unimodular hdet)).coordinateDifferential i p v / p.a i) *
          ((SmoothAtlas.presentation S.toSeed
              (S.toSeed_unimodular hdet)).coordinateDifferential j p w / p.a j) -
         ((SmoothAtlas.presentation S.toSeed
              (S.toSeed_unimodular hdet)).coordinateDifferential i p w / p.a i) *
          ((SmoothAtlas.presentation S.toSeed
              (S.toSeed_unimodular hdet)).coordinateDifferential j p v
                / p.a j))).im := by
  rw [FullSkeleton.torus_anchor S.toSeed (S.toSeed_unimodular hdet) hε hκ hδ
    p hp v w]
  exact torus_anchor_old_matrix S _ p v w

/-- **Recovery, clause (c).** The flow on the old carrier conjugate to the
constructed complete flow has exactly the old coordinate cap `C_B` as its
dynamical skeleton. -/
theorem liouvilleData_trappedSet_conjFlow (S : SkewSeed d)
    (hdet : S.Unimodular) (hε : 0 < ε) (hκ : 2 * ε + 1 ≤ κ) (hδ : 0 < δ) :
    trappedSet (conjFlow S (FullSkeleton.liouvilleData S.toSeed
        (S.toSeed_unimodular hdet) hε hκ hδ).completeFlow.flow) =
      coordinateCap S :=
  trappedSet_conjFlow_eq_coordinateCap S _
    (FullSkeleton.liouvilleData_trappedSet S.toSeed
      (S.toSeed_unimodular hdet) hε hκ hδ)

/-- **Recovery, clause (c), stratified form.** The same skeleton, as the union
of the old strata `Λ_I` over the old independent subsets of the mutable
vertices. -/
theorem liouvilleData_trappedSet_conjFlow_iUnion (S : SkewSeed d)
    (hdet : S.Unimodular) (hε : 0 < ε) (hκ : 2 * ε + 1 ≤ κ) (hδ : 0 < δ) :
    trappedSet (conjFlow S (FullSkeleton.liouvilleData S.toSeed
        (S.toSeed_unimodular hdet) hε hκ hδ).completeFlow.flow) =
      ⋃ I : {I : Finset (Fin d) // S.Independent I}, lambdaStratum S I.val :=
  (liouvilleData_trappedSet_conjFlow S hdet hε hκ hδ).trans
    (coordinateCap_eq_iUnion_lambdaStratum S)

/-! ### The packaged recovery statement -/

/-- **The recovery of the old `D = I` theorem, at given cutoff parameters.**
See `skeleton_recovery` for the uniform statement. -/
theorem skeleton_recovery_of_parameters (S : SkewSeed d) (hdet : S.Unimodular)
    (hε : 0 < ε) (hκ : 2 * ε + 1 ≤ κ) (hδ : 0 < δ) :
    Dense (initialTorus S) ∧
    ∃ (P : SmoothPresentation S.toSeed) (L : LiouvilleData P),
      (∀ p : (S.toSeed).Point,
          p ∈ _root_.ClusterSkeleton.initialTorus S.toSeed → ∀ v w,
          evalTwo (P.manifold.exteriorDerivative L.primitive) p v w =
            ((1 / 2 : ℂ) * ∑ i : Fin d, ∑ j : Fin d, (S.B i j : ℂ) *
              ((P.coordinateDifferential i p v / p.a i) *
                (P.coordinateDifferential j p w / p.a j) -
               (P.coordinateDifferential i p w / p.a i) *
                (P.coordinateDifferential j p v / p.a j))).im) ∧
      trappedSet (conjFlow S L.completeFlow.flow) = coordinateCap S ∧
      trappedSet (conjFlow S L.completeFlow.flow) =
        ⋃ I : {I : Finset (Fin d) // S.Independent I}, lambdaStratum S I.val := by
  refine ⟨dense_initialTorus S hdet, SmoothAtlas.presentation S.toSeed
    (S.toSeed_unimodular hdet), FullSkeleton.liouvilleData S.toSeed
    (S.toSeed_unimodular hdet) hε hκ hδ, ?_,
    liouvilleData_trappedSet_conjFlow S hdet hε hκ hδ,
    liouvilleData_trappedSet_conjFlow_iUnion S hdet hε hκ hδ⟩
  intro p hp v w
  exact liouvilleData_torus_anchor_old_matrix S hdet hε hκ hδ p hp v w

/-- **The recovery of the old `D = I` theorem.** For every skew-symmetric seed
with `det B = 1` — the hypothesis of the old library, and the only hypothesis
here — the old initial torus is dense, and there are a smooth presentation of
the exchange space and a Liouville datum on it whose anchored two-form is the
old logarithmic form written with the old integer matrix `S.B`, and whose
complete flow, read on the old carrier along `pointHomeomorph`, has exactly the
old coordinate cap `C_B = ⋃_I Λ_I` as its dynamical skeleton.

The smooth structure is existential, as in `docs/tex/target-theorem.tex`; no
transported smooth structure on `S.Point` and no term identity with the baseline
library's constructed flow is claimed. -/
theorem skeleton_recovery (S : SkewSeed d) (hdet : S.Unimodular) :
    Dense (initialTorus S) ∧
    ∃ (P : SmoothPresentation S.toSeed) (L : LiouvilleData P),
      (∀ p : (S.toSeed).Point,
          p ∈ _root_.ClusterSkeleton.initialTorus S.toSeed → ∀ v w,
          evalTwo (P.manifold.exteriorDerivative L.primitive) p v w =
            ((1 / 2 : ℂ) * ∑ i : Fin d, ∑ j : Fin d, (S.B i j : ℂ) *
              ((P.coordinateDifferential i p v / p.a i) *
                (P.coordinateDifferential j p w / p.a j) -
               (P.coordinateDifferential i p w / p.a i) *
                (P.coordinateDifferential j p v / p.a j))).im) ∧
      trappedSet (conjFlow S L.completeFlow.flow) = coordinateCap S ∧
      trappedSet (conjFlow S L.completeFlow.flow) =
        ⋃ I : {I : Finset (Fin d) // S.Independent I}, lambdaStratum S I.val :=
  skeleton_recovery_of_parameters S hdet (ε := 1) (κ := 3) (δ := 1)
    (by norm_num) (by norm_num) (by norm_num)

end ClusterSkeleton.SkewSeed
