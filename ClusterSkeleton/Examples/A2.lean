import ClusterSkeleton.ZeroSet
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FinCases

/-!
# A nontrivial seed satisfying the full hypotheses

The coefficient-free A₂ seed has two mutable vertices and one arrow 0 → 1.
It is a skew-symmetrizable seed with the trivial symmetrizer `D = 1`, so it is
also skew-symmetric; the genuinely weighted example is `Examples/NonSkew`.
This file is a sanity check of the concrete seed, exchange equations, and the
proved zero-set theorem; it does not assert the geometric target.
-/

namespace ClusterSkeleton.Examples

/-- The A₂ exchange matrix in the manuscript's arrow convention. -/
def a2Matrix : Matrix (Fin 2) (Fin 2) ℤ := !![0, 1; -1, 0]

/-- A genuine two-dimensional complex cluster model with all vertices mutable,
presented as a weighted seed with the trivial symmetrizer. -/
def a2Seed : Seed 2 where
  E := a2Matrix
  mutable := Finset.univ
  D := fun _ => 1
  D_pos := by
    intro i
    norm_num
  skewSymmetrizable := by
    intro i j
    fin_cases i <;> fin_cases j <;> norm_num [a2Matrix]
  acyclic := by
    apply (measure (fun i : {i : Fin 2 // i ∈ (Finset.univ : Finset (Fin 2))} =>
      i.1.val)).wf.mono
    intro i j hij
    rcases i with ⟨i, hi⟩
    rcases j with ⟨j, hj⟩
    change i.val < j.val
    fin_cases i <;> fin_cases j <;> norm_num [a2Matrix] at hij
    all_goals norm_num

/-- Unimodularity is checked on the full concrete integer matrix. -/
theorem a2Seed_unimodular : a2Seed.Unimodular := by
  norm_num [Seed.Unimodular, a2Seed, a2Matrix, Matrix.det_fin_two]

/-- The trivial symmetrizer is the identity: this example is the unweighted one. -/
theorem a2Seed_D_eq_one (i : Fin 2) : a2Seed.D i = 1 := rfl

/-- With `D = 1` the weighted form matrix is the exchange matrix itself. -/
theorem a2Seed_K_eq (i j : Fin 2) : a2Seed.K i j = (a2Matrix i j : ℚ) := by
  simp [Seed.K, a2Seed]

/-- The actual equations forbid simultaneous vanishing of the adjacent coordinates. -/
theorem a2_not_both_zero (p : a2Seed.Point) : ¬ (p.a 0 = 0 ∧ p.a 1 = 0) := by
  rintro ⟨h0, h1⟩
  have h := p.matrix_eq_zero_of_coordinates_zero 0 1 h0 h1
  norm_num [a2Seed, a2Matrix] at h

end ClusterSkeleton.Examples
