import ClusterSkeleton.CapSet
import Mathlib.Tactic.Omega

/-!
# Independence of the disk directions in the coordinate cap

This is the acyclic exchange-equation argument in the converse direction of
Proposition 2.6. It applies to the strict-interior coordinates of a cap point,
including its zero coordinates. It does not yet prove flow invariance.
-/

namespace ClusterSkeleton

open scoped BigOperators

variable {d : ℕ} {S : Seed d}

/-- The mutable coordinates strictly inside their closed unit disks. -/
noncomputable def Seed.Point.strictCapIndices (p : S.Point) : Finset (Fin d) := by
  classical
  exact S.mutable.filter fun i => ‖p.a i‖ < 1

@[simp] theorem Seed.Point.mem_strictCapIndices (p : S.Point) (i : Fin d) :
    i ∈ p.strictCapIndices ↔ i ∈ S.mutable ∧ ‖p.a i‖ < 1 := by
  classical
  simp [Seed.Point.strictCapIndices]

private theorem norm_positiveMonomial_lt_one {p : S.Point}
    (hp : p ∈ coordinateCap S) (i j : Fin d)
    (hij : 0 < S.B i j) (hj : ‖p.a j‖ < 1) :
    ‖S.positiveMonomial p.a i‖ < 1 := by
  classical
  have hn : (S.B i j).toNat ≠ 0 := by omega
  have hrest :
      ∏ k ∈ (Finset.univ : Finset (Fin d)).erase j,
        ‖p.a k‖ ^ (S.B i k).toNat ≤ 1 :=
    Finset.prod_le_one₀ (fun k _ => pow_nonneg (norm_nonneg _) _)
      (fun k _ => pow_le_one₀ (norm_nonneg _) (coordinateCap_norm_a_le hp k))
  simp only [Seed.positiveMonomial, norm_prod, norm_pow]
  calc
    (∏ k : Fin d, ‖p.a k‖ ^ (S.B i k).toNat) =
        (∏ k ∈ (Finset.univ : Finset (Fin d)).erase j,
          ‖p.a k‖ ^ (S.B i k).toNat) * ‖p.a j‖ ^ (S.B i j).toNat :=
      (Finset.prod_erase_mul _ _ (Finset.mem_univ j)).symm
    _ ≤ 1 * ‖p.a j‖ ^ (S.B i j).toNat :=
      mul_le_mul_of_nonneg_right hrest (pow_nonneg (norm_nonneg _) _)
    _ < 1 := by simpa using pow_lt_one₀ (norm_nonneg _) hj hn

/-- A strict-interior mutable coordinate has no strict-interior outgoing neighbor. -/
theorem coordinateCap_outgoing_not_interior {p : S.Point}
    (hp : p ∈ coordinateCap S) :
    ∀ i : S.Mutable, ‖p.a i‖ < 1 →
      ∀ j : S.Mutable, 0 < S.B i j → ¬ ‖p.a j‖ < 1 := by
  intro i
  induction i using S.acyclic.induction with
  | h i ih =>
    intro hi j hij hj
    have hQ : ‖S.negativeMonomial p.a i‖ = 1 := by
      simp only [Seed.negativeMonomial, norm_prod, norm_pow]
      apply Finset.prod_eq_one
      intro k _
      by_cases hneg : S.B i k < 0
      · have hkunit : ‖p.a k‖ = 1 := by
          by_cases hkm : k ∈ S.mutable
          · have hki : 0 < S.B k i := by
              have hskew := S.skew i k
              omega
            have hknot : ¬ ‖p.a k‖ < 1 := by
              intro hk
              exact ih ⟨k, hkm⟩ hki hk i hki hi
            exact le_antisymm (coordinateCap_norm_a_le hp k) (le_of_not_gt hknot)
          · exact hp.1 k hkm
        simp [hkunit]
      · have hn : (-S.B i k).toNat = 0 := by omega
        simp [hn]
    have hP := norm_positiveMonomial_lt_one hp (i : Fin d) (j : Fin d) hij hj
    have hsum : S.positiveMonomial p.a i + S.negativeMonomial p.a i = 0 := by
      simpa [coordinateCap_b_eq_zero hp i hi] using (p.exchange i).symm
    have heq := eq_neg_of_add_eq_zero_left hsum
    rw [heq, norm_neg, hQ] at hP
    exact lt_irrefl 1 hP

/-- All strict disk directions form an independent subset of the mutable quiver. -/
theorem coordinateCap_strictCapIndices_independent {p : S.Point}
    (hp : p ∈ coordinateCap S) : S.Independent p.strictCapIndices := by
  constructor
  · intro i hi
    exact ((p.mem_strictCapIndices i).mp hi).1
  · intro i hi j hj
    obtain ⟨him, hi'⟩ := (p.mem_strictCapIndices i).mp hi
    obtain ⟨hjm, hj'⟩ := (p.mem_strictCapIndices j).mp hj
    have hnotpos : ¬ 0 < S.B i j := by
      intro hpos
      exact coordinateCap_outgoing_not_interior hp ⟨i, him⟩ hi' ⟨j, hjm⟩ hpos hj'
    have hnotneg : ¬ S.B i j < 0 := by
      intro hneg
      have hpos : 0 < S.B j i := by
        have hskew := S.skew i j
        omega
      exact coordinateCap_outgoing_not_interior hp ⟨j, hjm⟩ hj' ⟨i, him⟩ hpos hi'
    omega

end ClusterSkeleton
