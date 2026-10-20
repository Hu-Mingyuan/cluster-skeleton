import ClusterSkeleton.Seed
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Lean.Elab.Tactic.Omega

/-!
# Independent zero sets

This proves the first assertion of Lemma 2.2 for arbitrary acyclic orientations
and arbitrary arrow multiplicities. Neither unimodularity nor bipartiteness is
used. The induction is over predecessors in the mutable directed graph.
-/

namespace ClusterSkeleton.Seed.Point

variable {d : ℕ} {S : Seed d} (p : S.Point)

/-- A zero mutable coordinate has no zero outgoing mutable neighbor. -/
theorem outgoing_ne_zero :
    ∀ i : S.Mutable, p.a i = 0 →
      ∀ j : S.Mutable, 0 < S.B i j → p.a j ≠ 0 := by
  intro i
  induction i using S.acyclic.induction with
  | h i ih =>
    intro hi j hij hj
    have hQ : S.negativeMonomial p.a i ≠ 0 := by
      apply Finset.prod_ne_zero_iff.mpr
      intro k _
      by_cases hneg : S.B i k < 0
      · apply pow_ne_zero
        by_cases hkm : k ∈ S.mutable
        · intro hk0
          have hki : 0 < S.B k i := by
            have hskew := S.skew i k
            omega
          exact ih ⟨k, hkm⟩ hki hk0 i hki hi
        · exact p.frozen_ne_zero k hkm
      · have hexp : (-S.B i k).toNat = 0 := by omega
        simp [hexp]
    have hP : S.positiveMonomial p.a i = 0 := by
      apply Finset.prod_eq_zero (Finset.mem_univ (j : Fin d))
      have hexp : (S.B i j).toNat ≠ 0 := by omega
      simp [hj, zero_pow hexp]
    have heq := p.exchange i
    rw [hi, zero_mul, hP, zero_add] at heq
    exact hQ heq.symm

/-- All matrix entries between zero coordinates vanish, including the diagonal. -/
theorem matrix_eq_zero_of_coordinates_zero (i j : Fin d)
    (hi : p.a i = 0) (hj : p.a j = 0) : S.B i j = 0 := by
  have him : i ∈ S.mutable := by
    by_contra h
    exact p.frozen_ne_zero i h hi
  have hjm : j ∈ S.mutable := by
    by_contra h
    exact p.frozen_ne_zero j h hj
  have hnotpos : ¬ 0 < S.B i j := by
    intro hpos
    exact p.outgoing_ne_zero ⟨i, him⟩ hi ⟨j, hjm⟩ hpos hj
  have hnotneg : ¬ S.B i j < 0 := by
    intro hneg
    have hpos : 0 < S.B j i := by
      have hskew := S.skew i j
      omega
    exact p.outgoing_ne_zero ⟨j, hjm⟩ hj ⟨i, him⟩ hpos hi
  omega

/-- Lemma 2.2 (independence assertion): the full zero set is independent. -/
theorem zeroSet_independent : S.Independent p.zeroSet := by
  classical
  constructor
  · intro i hi
    exact (p.mem_zeroSet i).mp hi |>.1
  · intro i hi j hj
    exact p.matrix_eq_zero_of_coordinates_zero i j
      ((p.mem_zeroSet i).mp hi).2 ((p.mem_zeroSet j).mp hj).2

/-- Every point lies in the open-chart nonvanishing locus indexed by its zero set.
The construction of the algebraic node-chart isomorphism is a separate task. -/
theorem exists_independent_nonvanishing_locus :
    ∃ I : Finset (Fin d), S.Independent I ∧ ∀ j, j ∉ I → p.a j ≠ 0 := by
  refine ⟨p.zeroSet, p.zeroSet_independent, ?_⟩
  intro j hj hj0
  apply hj
  apply (p.mem_zeroSet j).mpr
  refine ⟨?_, hj0⟩
  by_contra hjm
  exact p.frozen_ne_zero j hjm hj0

end ClusterSkeleton.Seed.Point
