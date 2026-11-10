import ClusterSkeleton.CapIndependence
import ClusterSkeleton.CoordinateLoci

/-!
# The stratified description of the coordinate cap

The reference writes the skeleton as `⋃_{I ⊂ M independent} Λ_I` with
`Λ_I = {z_i' = 0, |z_i| ≤ 1 (i ∈ I), |z_j| = 1 (j ∉ I)}`. This file defines the
stratum `Λ_I` on the actual exchange points and identifies the independently
defined coordinate cap with the union of the strata indexed by the independent
subsets of the mutable vertices. Frozen coordinates remain variables of modulus
one, so they are constrained by the second family exactly as in the reference.

Independence is not used for either inclusion: it only indexes the union by the
same family the reference uses. The index set actually realized by a cap point
is `Seed.Point.strictCapIndices`, whose independence is the already accepted
`coordinateCap_strictCapIndices_independent`.
-/

set_option autoImplicit false

namespace ClusterSkeleton

open Set

/-- The reference's stratum `Λ_I`. -/
def lambdaStratum {d : ℕ} (S : Seed d) (I : Finset (Fin d)) : Set S.Point :=
  {p | (∀ i : S.Mutable, (i : Fin d) ∈ I → ‖p.a i‖ ≤ 1 ∧ p.b i = 0) ∧
       (∀ j : Fin d, j ∉ I → ‖p.a j‖ = 1)}

/-- Every stratum indexed by a set of mutable vertices sits inside the cap. -/
theorem lambdaStratum_subset_coordinateCap {d : ℕ} {S : Seed d}
    {I : Finset (Fin d)} (hI : I ⊆ S.mutable) :
    lambdaStratum S I ⊆ coordinateCap S := by
  intro p hp
  refine ⟨fun f hf => hp.2 f (fun hfI => hf (hI hfI)), fun i => ?_⟩
  by_cases hi : (i : Fin d) ∈ I
  · exact ⟨(hp.1 i hi).1, by rw [(hp.1 i hi).2, mul_zero]⟩
  · have h1 := hp.2 (i : Fin d) hi
    refine ⟨le_of_eq h1, ?_⟩
    rw [h1]
    norm_num

/-- A cap point lies in the stratum indexed by its own strict disk directions. -/
theorem coordinateCap_subset_lambdaStratum_strictCapIndices {d : ℕ} {S : Seed d}
    {p : S.Point} (hp : p ∈ coordinateCap S) :
    p ∈ lambdaStratum S p.strictCapIndices := by
  refine ⟨fun i hi => ?_,
    fun j hj => norm_eq_one_of_not_strict S hp j hj⟩
  have hlt : ‖p.a i‖ < 1 := ((p.mem_strictCapIndices (i : Fin d)).mp hi).2
  exact ⟨hlt.le, coordinateCap_b_eq_zero hp i hlt⟩

/-- The cap is exactly the union of the strata over the independent subsets.
This is the reference's stratified form of the skeleton. -/
theorem coordinateCap_eq_iUnion_lambdaStratum {d : ℕ} (S : Seed d) :
    coordinateCap S =
      ⋃ I : {I : Finset (Fin d) // S.Independent I}, lambdaStratum S I.val := by
  refine Subset.antisymm (fun p hp => ?_) (fun p hp => ?_)
  · exact mem_iUnion.mpr
      ⟨⟨p.strictCapIndices, coordinateCap_strictCapIndices_independent hp⟩,
        coordinateCap_subset_lambdaStratum_strictCapIndices hp⟩
  · obtain ⟨I, hI⟩ := mem_iUnion.mp hp
    exact lambdaStratum_subset_coordinateCap I.property.1 hI

/-- Each stratum is closed in the inherited topology of the actual point set. -/
theorem isClosed_lambdaStratum {d : ℕ} (S : Seed d) (I : Finset (Fin d)) :
    IsClosed (lambdaStratum S I) := by
  have hb : ∀ i : S.Mutable, Continuous (fun p : S.Point => p.b i) := by
    intro i
    change Continuous (fun p : S.Point => p.val.2 i)
    exact (continuous_apply i).comp (continuous_snd.comp continuous_subtype_val)
  have h1 : IsClosed {p : S.Point |
      ∀ i : S.Mutable, (i : Fin d) ∈ I → ‖p.a i‖ ≤ 1 ∧ p.b i = 0} := by
    simp only [ofPred_forall]
    refine isClosed_iInter fun i => isClosed_iInter fun _ => ?_
    exact (isClosed_le (continuous_originalCoordinate S (i : Fin d)).norm
      continuous_const).inter (isClosed_eq (hb i) continuous_const)
  have h2 : IsClosed {p : S.Point | ∀ j : Fin d, j ∉ I → ‖p.a j‖ = 1} := by
    simp only [ofPred_forall]
    exact isClosed_iInter fun j => isClosed_iInter fun _ =>
      isClosed_eq (continuous_originalCoordinate S j).norm continuous_const
  exact h1.inter h2

/-- Each stratum is compact, the reference's per-stratum compactness. -/
theorem isCompact_lambdaStratum {d : ℕ} (S : Seed d) (I : Finset (Fin d))
    (hI : I ⊆ S.mutable) : IsCompact (lambdaStratum S I) :=
  (isCompact_coordinateCap S).of_isClosed_subset (isClosed_lambdaStratum S I)
    (lambdaStratum_subset_coordinateCap hI)

end ClusterSkeleton
