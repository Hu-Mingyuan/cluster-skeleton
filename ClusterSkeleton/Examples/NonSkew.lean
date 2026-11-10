import ClusterSkeleton.ZeroSet
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FinCases

/-!
# A genuinely skew-symmetrizable seed that is not skew-symmetric

This is the concrete input of Section 4 of `target-theorem.pdf`:
```
E = [[0,1,-1,0],[-2,0,0,-1],[1,0,0,0],[0,1,0,0]],   D = diag(1,2,1,2),   M = {0,1}
```
in Lean's zero-based indexing. We check `det E = 1`, positivity of the weights,
skew-symmetry of `K = E * D`, acyclicity of the mutable block, and the failure
of skew-symmetry of `E` itself (`E 0 1 = 1` while `E 1 0 = -2`).

This example checks that the weighted seed interface is genuinely broader than
the skew-symmetric one; it does not replace any statement quantified over all
admissible inputs.
-/

open scoped Matrix

namespace ClusterSkeleton.Examples

/-- The non-skew integral exchange matrix. -/
def nonSkewMatrix : Matrix (Fin 4) (Fin 4) ℤ :=
  !![0, 1, -1, 0;
    -2, 0, 0, -1;
     1, 0, 0, 0;
     0, 1, 0, 0]

/-- The positive rational weights `diag(1,2,1,2)`. -/
def nonSkewWeights : Fin 4 → ℚ := ![1, 2, 1, 2]

/-- The mutable vertices `{0,1}`, in zero-based indexing. -/
def nonSkewMutable : Finset (Fin 4) := {0, 1}

/-- The weighted seed of the reference's concrete example. -/
def nonSkewSeed : Seed 4 where
  E := nonSkewMatrix
  mutable := nonSkewMutable
  D := nonSkewWeights
  D_pos := by
    intro i
    fin_cases i <;> norm_num [nonSkewWeights]
  skewSymmetrizable := by
    intro i j
    fin_cases i <;> fin_cases j <;>
      norm_num [nonSkewMatrix, nonSkewWeights]
  acyclic := by
    apply (measure (fun i : {i : Fin 4 // i ∈ nonSkewMutable} => i.1.val)).wf.mono
    intro i j hij
    rcases i with ⟨i, hi⟩
    rcases j with ⟨j, hj⟩
    change i.val < j.val
    simp only [nonSkewMutable, Finset.mem_insert, Finset.mem_singleton] at hi hj
    rcases hi with rfl | rfl <;> rcases hj with rfl | rfl
    · exact absurd hij (by norm_num [nonSkewMatrix])
    · norm_num
    · exact absurd hij (by norm_num [nonSkewMatrix])
    · exact absurd hij (by norm_num [nonSkewMatrix])

@[simp] theorem nonSkewSeed_E : nonSkewSeed.E = nonSkewMatrix := rfl

@[simp] theorem nonSkewSeed_D : nonSkewSeed.D = nonSkewWeights := rfl

@[simp] theorem nonSkewSeed_mutable : nonSkewSeed.mutable = nonSkewMutable := rfl

/-- Unimodularity of the concrete integral matrix: `det E = 1`. -/
theorem nonSkewSeed_unimodular : nonSkewSeed.Unimodular := by
  norm_num [Seed.Unimodular, nonSkewMatrix, Matrix.det_succ_row_zero,
    Fin.sum_univ_succ, Matrix.det_fin_three, Fin.succAbove]

/-- The exchange matrix is genuinely not skew-symmetric: `E 0 1 = 1` but
`E 1 0 = -2`, so the weights cannot be discarded. -/
theorem nonSkewSeed_not_skew : ¬ ∀ i j, nonSkewSeed.E i j = -nonSkewSeed.E j i := by
  intro h
  have h01 := h 0 1
  norm_num [nonSkewMatrix] at h01

/-- The two witnessing entries, as cited by the reference. -/
theorem nonSkewSeed_entries : nonSkewSeed.E 0 1 = 1 ∧ nonSkewSeed.E 1 0 = -2 := by
  norm_num [nonSkewMatrix]

/-- The weights genuinely differ, so this is not a rescaling of a skew matrix
by a single constant. -/
theorem nonSkewSeed_weights_ne : nonSkewSeed.D 0 ≠ nonSkewSeed.D 1 := by
  norm_num [nonSkewWeights]

/-- The weighted form matrix is skew-symmetric, as the structure field asserts. -/
theorem nonSkewSeed_K_transpose : nonSkewSeed.Kᵀ = -nonSkewSeed.K :=
  nonSkewSeed.K_transpose

/-- Its determinant is the product of the weights, `1 * 2 * 1 * 2 = 4`. -/
theorem nonSkewSeed_det_K : nonSkewSeed.K.det = 4 := by
  rw [nonSkewSeed.det_K_of_unimodular nonSkewSeed_unimodular]
  norm_num [nonSkewWeights, Fin.prod_univ_succ]

end ClusterSkeleton.Examples
