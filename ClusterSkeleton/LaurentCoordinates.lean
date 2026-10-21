import Mathlib.Data.Matrix.Mul
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Algebra.GroupWithZero
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Laurent changes of coordinates on complex tori

Rows are output characters: for A : Matrix I J ℤ the associated map goes
from J-coordinates to I-coordinates. Thus applying B and then A corresponds
to A * B. All topologies below are the native product or subtype topologies.
No basis completion or exchange-space chart is assumed here.
-/

namespace ClusterSkeleton
namespace LaurentCoordinates

open scoped BigOperators

variable {I J K : Type*} [Fintype I] [Fintype J] [Fintype K]

/-- The complex torus with coordinates indexed by J, using native complex units. -/
abbrev UnitTorus (J : Type*) := J → ℂˣ

/-- The same torus as a product of punctured complex lines. -/
abbrev NonzeroTorus (J : Type*) := J → {z : ℂ // z ≠ 0}

/-- Integer rows act as Laurent characters, including negative exponents. -/
def monomialMap (A : Matrix I J ℤ) (z : UnitTorus J) : UnitTorus I :=
  fun i => ∏ j, z j ^ A i j

omit [Fintype I] in
@[simp] theorem monomialMap_apply (A : Matrix I J ℤ) (z : UnitTorus J) (i : I) :
    monomialMap A z i = ∏ j, z j ^ A i j := rfl

omit [Fintype I] in
/-- Evaluating a prescribed row recovers that exact character. -/
theorem monomialMap_row (A : Matrix I J ℤ) (i : I) (r : J → ℤ)
    (h : ∀ j, A i j = r j) (z : UnitTorus J) :
    monomialMap A z i = ∏ j, z j ^ r j := by
  simp only [monomialMap, h]

private theorem zpow_sum {L : Type*} (s : Finset L) (f : L → ℤ) (z : ℂˣ) :
    z ^ (∑ j ∈ s, f j) = ∏ j ∈ s, z ^ f j := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih => simp [ha, zpow_add, ih]

omit [Fintype I] in
/-- Composition order is ordinary matrix multiplication, with no transpose. -/
theorem monomialMap_mul (A : Matrix I J ℤ) (B : Matrix J K ℤ) (z : UnitTorus K) :
    monomialMap (A * B) z = monomialMap A (monomialMap B z) := by
  funext i
  simp only [monomialMap, Matrix.mul_apply, zpow_sum]
  rw [Finset.prod_comm]
  apply Finset.prod_congr rfl
  intro j _
  rw [← Finset.prod_zpow]
  apply Finset.prod_congr rfl
  intro k _
  rw [← zpow_mul, mul_comm (B j k) (A i j)]

@[simp] theorem monomialMap_one [DecidableEq I] (z : UnitTorus I) :
    monomialMap (1 : Matrix I I ℤ) z = z := by
  funext i
  simp [monomialMap, Matrix.one_apply]

omit [Fintype I] in
/-- Every integer Laurent map is continuous on the complex torus. -/
theorem continuous_monomialMap (A : Matrix I J ℤ) : Continuous (monomialMap A) := by
  apply continuous_pi
  intro i
  exact continuous_finsetProd _ fun j _ => (continuous_apply j).zpow (A i j)

theorem monomialMap_left_inv [DecidableEq J] (A : Matrix I J ℤ) (B : Matrix J I ℤ)
    (hBA : B * A = 1) (z : UnitTorus J) :
    monomialMap B (monomialMap A z) = z := by
  rw [← monomialMap_mul, hBA, monomialMap_one]

theorem monomialMap_right_inv [DecidableEq I] (A : Matrix I J ℤ) (B : Matrix J I ℤ)
    (hAB : A * B = 1) (z : UnitTorus I) :
    monomialMap A (monomialMap B z) = z := by
  rw [← monomialMap_mul, hAB, monomialMap_one]

/-- Mutually inverse integer exponent matrices give an actual homeomorphism. -/
def monomialHomeomorph [DecidableEq I] [DecidableEq J]
    (A : Matrix I J ℤ) (B : Matrix J I ℤ) (hAB : A * B = 1) (hBA : B * A = 1) :
    UnitTorus J ≃ₜ UnitTorus I where
  toFun := monomialMap A
  invFun := monomialMap B
  left_inv := monomialMap_left_inv A B hBA
  right_inv := monomialMap_right_inv A B hAB
  continuous_toFun := continuous_monomialMap A
  continuous_invFun := continuous_monomialMap B

@[simp] theorem monomialHomeomorph_apply [DecidableEq I] [DecidableEq J]
    (A : Matrix I J ℤ) (B : Matrix J I ℤ) (hAB : A * B = 1) (hBA : B * A = 1)
    (z : UnitTorus J) (i : I) :
    monomialHomeomorph A B hAB hBA z i = ∏ j, z j ^ A i j := rfl

@[simp] theorem monomialHomeomorph_symm_apply [DecidableEq I] [DecidableEq J]
    (A : Matrix I J ℤ) (B : Matrix J I ℤ) (hAB : A * B = 1) (hBA : B * A = 1)
    (z : UnitTorus I) (j : J) :
    (monomialHomeomorph A B hAB hBA).symm z j = ∏ i, z i ^ B j i := rfl

/-- Coordinatewise identification with punctured lines, with inherited topology. -/
noncomputable def unitsToNonzero (J : Type*) : UnitTorus J ≃ₜ NonzeroTorus J :=
  Homeomorph.piCongrRight fun _ => unitsHomeomorphNeZero

omit [Fintype J] in
@[simp] theorem unitsToNonzero_apply (z : UnitTorus J) (j : J) :
    (unitsToNonzero J z j).val = (z j : ℂ) := rfl

omit [Fintype J] in
@[simp] theorem unitsToNonzero_symm_apply (z : NonzeroTorus J) (j : J) :
    ((unitsToNonzero J).symm z j : ℂ) = (z j).val := by
  have h := congrArg (fun w : NonzeroTorus J => (w j).val)
    ((unitsToNonzero J).apply_symm_apply z)
  exact h

/-- The Laurent map on nonzero complex-coordinate subtypes. -/
noncomputable def nonzeroMonomialMap (A : Matrix I J ℤ) :
    NonzeroTorus J → NonzeroTorus I :=
  fun z => unitsToNonzero I (monomialMap A ((unitsToNonzero J).symm z))

omit [Fintype I] in
/-- Its values are the actual complex Laurent characters of the given rows. -/
@[simp] theorem nonzeroMonomialMap_apply (A : Matrix I J ℤ) (z : NonzeroTorus J) (i : I) :
    (nonzeroMonomialMap A z i).val = ∏ j, (z j).val ^ A i j := by
  simp [nonzeroMonomialMap, monomialMap]

omit [Fintype I] in
theorem nonzeroMonomialMap_row (A : Matrix I J ℤ) (i : I) (r : J → ℤ)
    (h : ∀ j, A i j = r j) (z : NonzeroTorus J) :
    (nonzeroMonomialMap A z i).val = ∏ j, (z j).val ^ r j := by
  simp only [nonzeroMonomialMap_apply, h]

omit [Fintype I] in
theorem continuous_nonzeroMonomialMap (A : Matrix I J ℤ) :
    Continuous (nonzeroMonomialMap A) :=
  (unitsToNonzero I).continuous.comp
    ((continuous_monomialMap A).comp (unitsToNonzero J).symm.continuous)

omit [Fintype I] in
theorem nonzeroMonomialMap_mul (A : Matrix I J ℤ) (B : Matrix J K ℤ)
    (z : NonzeroTorus K) :
    nonzeroMonomialMap (A * B) z =
      nonzeroMonomialMap A (nonzeroMonomialMap B z) := by
  simp only [nonzeroMonomialMap, Homeomorph.symm_apply_apply, monomialMap_mul]

@[simp] theorem nonzeroMonomialMap_one [DecidableEq I] (z : NonzeroTorus I) :
    nonzeroMonomialMap (1 : Matrix I I ℤ) z = z := by
  simp only [nonzeroMonomialMap, monomialMap_one, Homeomorph.apply_symm_apply]

theorem nonzeroMonomialMap_left_inv [DecidableEq J]
    (A : Matrix I J ℤ) (B : Matrix J I ℤ) (hBA : B * A = 1) (z : NonzeroTorus J) :
    nonzeroMonomialMap B (nonzeroMonomialMap A z) = z := by
  rw [← nonzeroMonomialMap_mul, hBA, nonzeroMonomialMap_one]

theorem nonzeroMonomialMap_right_inv [DecidableEq I]
    (A : Matrix I J ℤ) (B : Matrix J I ℤ) (hAB : A * B = 1) (z : NonzeroTorus I) :
    nonzeroMonomialMap A (nonzeroMonomialMap B z) = z := by
  rw [← nonzeroMonomialMap_mul, hAB, nonzeroMonomialMap_one]

/-- The native homeomorphism of products of punctured complex lines. -/
noncomputable def nonzeroMonomialHomeomorph [DecidableEq I] [DecidableEq J]
    (A : Matrix I J ℤ) (B : Matrix J I ℤ) (hAB : A * B = 1) (hBA : B * A = 1) :
    NonzeroTorus J ≃ₜ NonzeroTorus I :=
  ((unitsToNonzero J).symm.trans (monomialHomeomorph A B hAB hBA)).trans
    (unitsToNonzero I)

@[simp] theorem nonzeroMonomialHomeomorph_apply [DecidableEq I] [DecidableEq J]
    (A : Matrix I J ℤ) (B : Matrix J I ℤ) (hAB : A * B = 1) (hBA : B * A = 1)
    (z : NonzeroTorus J) (i : I) :
    (nonzeroMonomialHomeomorph A B hAB hBA z i).val = ∏ j, (z j).val ^ A i j :=
  nonzeroMonomialMap_apply A z i

@[simp] theorem nonzeroMonomialHomeomorph_symm_apply [DecidableEq I] [DecidableEq J]
    (A : Matrix I J ℤ) (B : Matrix J I ℤ) (hAB : A * B = 1) (hBA : B * A = 1)
    (z : NonzeroTorus I) (j : J) :
    ((nonzeroMonomialHomeomorph A B hAB hBA).symm z j).val = ∏ i, (z i).val ^ B j i :=
  nonzeroMonomialMap_apply B z j

end LaurentCoordinates
end ClusterSkeleton
