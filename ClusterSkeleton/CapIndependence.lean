import ClusterSkeleton.CapSet
import Lean.Elab.Tactic.Omega

/-!
# Independence of the disk directions in the coordinate cap

This is the acyclic exchange-equation argument in the converse direction of
Proposition 2.6. It applies to the strict-interior coordinates of a cap point,
including its zero coordinates. It does not yet prove flow invariance.

As for the zero set, only the sign combinatorics of `E` is used, through
`Seed.E_pos_of_neg` and `Seed.E_eq_zero_iff`; the positive symmetrizer weights
play no role. Exponents are the column exponents `S.B i j = S.E j i`.
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
  have hij' : 0 < S.E j i := hij
  have hn : (S.E j i).toNat ≠ 0 := by omega
  have hrest :
      ∏ k ∈ (Finset.univ : Finset (Fin d)).erase j,
        ‖p.a k‖ ^ (S.E k i).toNat ≤ 1 :=
    Finset.prod_le_one₀ (fun k _ => pow_nonneg (norm_nonneg _) _)
      (fun k _ => pow_le_one₀ (norm_nonneg _) (coordinateCap_norm_a_le hp k))
  simp only [Seed.positiveMonomial, norm_prod, norm_pow]
  calc
    (∏ k : Fin d, ‖p.a k‖ ^ (S.E k i).toNat) =
        (∏ k ∈ (Finset.univ : Finset (Fin d)).erase j,
          ‖p.a k‖ ^ (S.E k i).toNat) * ‖p.a j‖ ^ (S.E j i).toNat :=
      (Finset.prod_erase_mul _ _ (Finset.mem_univ j)).symm
    _ ≤ 1 * ‖p.a j‖ ^ (S.E j i).toNat :=
      mul_le_mul_of_nonneg_right hrest (pow_nonneg (norm_nonneg _) _)
    _ < 1 := by simpa using pow_lt_one₀ (norm_nonneg _) hj hn

/-- A strict-interior mutable coordinate has no strict-interior outgoing neighbor. -/
theorem coordinateCap_outgoing_not_interior {p : S.Point}
    (hp : p ∈ coordinateCap S) :
    ∀ i : S.Mutable, ‖p.a i‖ < 1 →
      ∀ j : S.Mutable, 0 < S.B i j → ¬ ‖p.a j‖ < 1 := by
  intro i
  induction i using S.acyclic_exponent.induction with
  | h i ih =>
    intro hi j hij hj
    have hQ : ‖S.negativeMonomial p.a i‖ = 1 := by
      simp only [Seed.negativeMonomial, norm_prod, norm_pow]
      apply Finset.prod_eq_one
      intro k _
      by_cases hneg : S.E k (i : Fin d) < 0
      · have hkunit : ‖p.a k‖ = 1 := by
          by_cases hkm : k ∈ S.mutable
          · have hki : 0 < S.B k (i : Fin d) := S.E_pos_of_neg hneg
            have hknot : ¬ ‖p.a k‖ < 1 := by
              intro hk
              exact ih ⟨k, hkm⟩ hki hk i hki hi
            exact le_antisymm (coordinateCap_norm_a_le hp k) (le_of_not_gt hknot)
          · exact hp.1 k hkm
        simp [hkunit]
      · have hn : (-S.E k (i : Fin d)).toNat = 0 := by omega
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
    have hnotpos : ¬ 0 < S.E j i := by
      intro hpos
      exact coordinateCap_outgoing_not_interior hp ⟨i, him⟩ hi' ⟨j, hjm⟩ hpos hj'
    have hnotneg : ¬ S.E j i < 0 := by
      intro hneg
      have hpos : 0 < S.E i j := S.E_pos_of_neg hneg
      exact coordinateCap_outgoing_not_interior hp ⟨j, hjm⟩ hj' ⟨i, him⟩ hpos hi'
    have hji : S.E j i = 0 := by omega
    exact (S.E_eq_zero_iff j i).mp hji

/-- Outside the strict disk directions every original coordinate has modulus one,
including the independently variable frozen coordinates. This is a cap-equation
fact; it is stated here so that the stratified description of the cap does not
depend on the flow modules. -/
theorem norm_eq_one_of_not_strict (S : Seed d) {p : S.Point}
    (hp : p ∈ coordinateCap S) (j : Fin d) (hj : j ∉ p.strictCapIndices) :
    ‖p.a j‖ = 1 := by
  by_cases hm : j ∈ S.mutable
  · have hn : ¬ ‖p.a j‖ < 1 := fun h => hj ((p.mem_strictCapIndices j).mpr ⟨hm, h⟩)
    exact le_antisymm (coordinateCap_norm_a_le hp j) (le_of_not_gt hn)
  · exact hp.1 j hm

end ClusterSkeleton
