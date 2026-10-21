import ClusterSkeleton.NodeCoordinates
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.Basis.Prod
import Mathlib.LinearAlgebra.Matrix.Basis

/-!
# Completion of prescribed split integer rows

For finite integer matrices `R * C = 1`, the rows of `R` extend, unchanged,
to a basis of the coordinate lattice. The complement is a basis of the kernel
of right multiplication by `C`. No ordering or cardinality subtraction is needed:
the new index is the sum of the prescribed index and `Fin complementRank`.
The two rectangular change matrices are inverse in both orders.
-/

open scoped BigOperators

namespace ClusterSkeleton
namespace SplitIntegerRows

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
variable (R : Matrix ι κ ℤ) (C : Matrix κ ι ℤ) (h : R * C = 1)

omit [DecidableEq κ] in
include h in
/-- Right multiplication by `C` retracts the prescribed row embedding. -/
theorem retract_embed (u : ι → ℤ) :
    C.vecMulLinear (R.vecMulLinear u) = u := by
  simp only [Matrix.vecMulLinear_apply, Matrix.vecMul_vecMul, h, Matrix.vecMul_one]

/-- Explicit splitting into the specified rows and the kernel of the retraction. -/
noncomputable def splittingEquiv :
    ((ι → ℤ) × LinearMap.ker C.vecMulLinear) ≃ₗ[ℤ] (κ → ℤ) :=
  LinearEquiv.ofBijective (R.vecMulLinear.coprod (LinearMap.ker C.vecMulLinear).subtype) (by
    constructor
    · intro x y hxy
      have hfirst : x.1 = y.1 := by
        have hx := congrArg C.vecMulLinear hxy
        simpa only [LinearMap.coprod_apply, map_add, retract_embed R C h,
          Submodule.subtype_apply, LinearMap.mem_ker.mp x.2.property,
          LinearMap.mem_ker.mp y.2.property, add_zero] using hx
      apply Prod.ext hfirst
      apply Subtype.ext
      have hx : R.vecMulLinear x.1 + (x.2 : κ → ℤ) =
          R.vecMulLinear y.1 + (y.2 : κ → ℤ) := hxy
      rw [hfirst] at hx
      exact add_left_cancel hx
    · intro v
      refine ⟨(C.vecMulLinear v, ⟨v - R.vecMulLinear (C.vecMulLinear v), ?_⟩), ?_⟩
      · rw [LinearMap.mem_ker, map_sub, retract_embed R C h, sub_self]
      · change R.vecMulLinear (C.vecMulLinear v) +
          (v - R.vecMulLinear (C.vecMulLinear v)) = v
        abel)

omit [DecidableEq κ] in
@[simp] theorem splittingEquiv_apply (u : ι → ℤ) (k : LinearMap.ker C.vecMulLinear) :
    splittingEquiv R C h (u, k) = R.vecMulLinear u + (k : κ → ℤ) := rfl

omit [DecidableEq κ] in
/-- The prescribed coordinates of the inverse splitting are the retraction. -/
@[simp] theorem splittingEquiv_symm_fst (v : κ → ℤ) :
    ((splittingEquiv R C h).symm v).1 = C.vecMulLinear v := by
  have hv := congrArg C.vecMulLinear ((splittingEquiv R C h).apply_symm_apply v)
  change C.vecMulLinear (R.vecMulLinear ((splittingEquiv R C h).symm v).1 +
    (((splittingEquiv R C h).symm v).2 : κ → ℤ)) = C.vecMulLinear v at hv
  simpa only [map_add, retract_embed R C h,
    LinearMap.mem_ker.mp ((splittingEquiv R C h).symm v).2.property,
    add_zero] using hv

/-- The finite rank and basis supplied by the PID theorem for the kernel. -/
noncomputable def kernelBasisData :
    Σ n : ℕ, Module.Basis (Fin n) ℤ (LinearMap.ker C.vecMulLinear) :=
  Submodule.basisOfPid (Pi.basisFun ℤ κ) (LinearMap.ker C.vecMulLinear)

/-- Number of additional basis vectors. -/
noncomputable abbrev complementRank : ℕ := (kernelBasisData C).1

/-- Completed row index, retaining each original index literally as `Sum.inl`. -/
abbrev Index := ι ⊕ Fin (complementRank C)

/-- An actual basis of the full integer coordinate lattice. -/
noncomputable def basis : Module.Basis (Index C) ℤ (κ → ℤ) :=
  ((Pi.basisFun ℤ ι).prod (kernelBasisData C).2).map (splittingEquiv R C h)

omit [DecidableEq κ] in
/-- Each specified vector is preserved exactly, not just its span. -/
@[simp] theorem basis_inl (i : ι) : basis R C h (Sum.inl i) = R.row i := by
  unfold basis
  rw [Module.Basis.map_apply, Module.Basis.prod_apply]
  simp [Pi.basisFun_apply]

/-- Rows of the completed basis in the original coordinate lattice. -/
noncomputable def forwardMatrix : Matrix (Index C) κ ℤ :=
  ((Pi.basisFun ℤ κ).toMatrix (basis R C h)).transpose

/-- Original coordinate vectors expressed in the completed basis. -/
noncomputable def inverseMatrix : Matrix κ (Index C) ℤ :=
  ((basis R C h).toMatrix (Pi.basisFun ℤ κ)).transpose

omit [DecidableEq κ] in
/-- The forward matrix has the prescribed rows, with their original labels. -/
@[simp] theorem forwardMatrix_inl (i : ι) (j : κ) :
    forwardMatrix R C h (Sum.inl i) j = R i j := by
  simp [forwardMatrix, Matrix.transpose_apply, Module.Basis.toMatrix_apply]

/-- The inverse matrix retains the original right inverse in its prescribed columns. -/
@[simp] theorem inverseMatrix_inl (j : κ) (i : ι) :
    inverseMatrix R C h j (Sum.inl i) = C j i := by
  change ((Pi.basisFun ℤ ι).prod (kernelBasisData C).2).repr
    ((splittingEquiv R C h).symm ((Pi.basisFun ℤ κ) j)) (Sum.inl i) = C j i
  rw [Module.Basis.prod_repr_inl, Pi.basisFun_repr, splittingEquiv_symm_fst]
  simp [Pi.basisFun_apply]

omit [DecidableEq κ] in
/-- First inverse identity (on the completed row indices). -/
theorem forward_mul_inverse : forwardMatrix R C h * inverseMatrix R C h = 1 := by
  rw [forwardMatrix, inverseMatrix, ← Matrix.transpose_mul,
    Module.Basis.toMatrix_mul_toMatrix_flip, Matrix.transpose_one]

/-- Second inverse identity (on the original coordinate indices). -/
theorem inverse_mul_forward : inverseMatrix R C h * forwardMatrix R C h = 1 := by
  rw [forwardMatrix, inverseMatrix, ← Matrix.transpose_mul,
    Module.Basis.toMatrix_mul_toMatrix_flip, Matrix.transpose_one]

end SplitIntegerRows

section SeedSpecialization

variable {d : ℕ} (S : Seed d) (I : Finset (Fin d))
variable (hdet : S.Unimodular) (hI : S.Independent I)

/-- Completed indices for the rows of `B` restricted to the complement of `I`. -/
abbrev IndependentRowBasisIndex :=
  SplitIntegerRows.Index (independentRowRightInverse S I)

/-- Basis completion of the actual restricted seed rows, using the accepted splitting. -/
noncomputable def independentRowBasis :
    Module.Basis (IndependentRowBasisIndex S I) ℤ ({j : Fin d // j ∉ I} → ℤ) :=
  SplitIntegerRows.basis (independentRowMatrix S I) (independentRowRightInverse S I)
    (independentRowMatrix_mul_rightInverse hdet hI)

/-- Each prescribed seed row is unchanged as an integer vector. -/
@[simp] theorem independentRowBasis_inl (i : {i : Fin d // i ∈ I}) :
    independentRowBasis S I hdet hI (Sum.inl i) = (independentRowMatrix S I).row i :=
  SplitIntegerRows.basis_inl _ _ _ i

/-- Exponent matrix for subsequent Laurent coordinate construction. -/
noncomputable def independentRowForwardMatrix :
    Matrix (IndependentRowBasisIndex S I) {j : Fin d // j ∉ I} ℤ :=
  SplitIntegerRows.forwardMatrix (independentRowMatrix S I) (independentRowRightInverse S I)
    (independentRowMatrix_mul_rightInverse hdet hI)

/-- Inverse exponent matrix. -/
noncomputable def independentRowInverseMatrix :
    Matrix {j : Fin d // j ∉ I} (IndependentRowBasisIndex S I) ℤ :=
  SplitIntegerRows.inverseMatrix (independentRowMatrix S I) (independentRowRightInverse S I)
    (independentRowMatrix_mul_rightInverse hdet hI)

@[simp] theorem independentRowForwardMatrix_inl (i : {i : Fin d // i ∈ I})
    (j : {j : Fin d // j ∉ I}) :
    independentRowForwardMatrix S I hdet hI (Sum.inl i) j = S.B i j :=
  SplitIntegerRows.forwardMatrix_inl _ _ _ i j

@[simp] theorem independentRowInverseMatrix_inl (j : {j : Fin d // j ∉ I})
    (i : {i : Fin d // i ∈ I}) :
    independentRowInverseMatrix S I hdet hI j (Sum.inl i) = S.B⁻¹ j i :=
  SplitIntegerRows.inverseMatrix_inl _ _ _ j i

/-- Both exponent matrices compose to identity on the completed index. -/
theorem independentRowForward_mul_inverse :
    independentRowForwardMatrix S I hdet hI * independentRowInverseMatrix S I hdet hI = 1 :=
  SplitIntegerRows.forward_mul_inverse _ _ _

/-- Both exponent matrices compose to identity on the original complementary index. -/
theorem independentRowInverse_mul_forward :
    independentRowInverseMatrix S I hdet hI * independentRowForwardMatrix S I hdet hI = 1 :=
  SplitIntegerRows.inverse_mul_forward _ _ _

end SeedSpecialization
end ClusterSkeleton
