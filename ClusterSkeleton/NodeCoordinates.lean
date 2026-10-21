import ClusterSkeleton.CoordinateLoci
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Normalized node coordinates on actual independent loci

These are the first algebraic steps of Lemma 2.2. Both exchange monomials are
units on an independent coordinate locus, so the normalization uses no undefined
boundary ratios. An integral right inverse is proved below; completing the
rows to an integral basis and constructing the final product chart remain separate.
-/

open scoped BigOperators

namespace ClusterSkeleton

variable {d : ℕ} {S : Seed d} {I : Finset (Fin d)}

/-- Incident coordinates outside I are nonzero; those inside I have exponent zero. -/
theorem positiveMonomial_ne_zero_on_independent_locus
    (hI : S.Independent I) {p : S.Point} (hp : p ∈ candidateChartLocus S I)
    {i : Fin d} (hi : i ∈ I) : S.positiveMonomial p.a i ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro j _
  by_cases hj : j ∈ I
  · simp [hI.2 i hi j hj]
  · exact pow_ne_zero _ (hp j hj)

theorem negativeMonomial_ne_zero_on_independent_locus
    (hI : S.Independent I) {p : S.Point} (hp : p ∈ candidateChartLocus S I)
    {i : Fin d} (hi : i ∈ I) : S.negativeMonomial p.a i ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro j _
  by_cases hj : j ∈ I
  · simp [hI.2 i hi j hj]
  · exact pow_ne_zero _ (hp j hj)

/-- This expression is used only where its negative monomial is proved nonzero. -/
noncomputable def normalizedPartner (p : S.Point) (i : S.Mutable) : ℂ :=
  p.b i / S.negativeMonomial p.a i

/-- The exchange character is a genuine nonzero Laurent character on the locus. -/
noncomputable def exchangeCharacter (p : S.Point) (i : Fin d) : ℂ :=
  S.positiveMonomial p.a i / S.negativeMonomial p.a i

/-- The numerator/denominator exponent convention is exactly integer exponentiation.
This algebraic identity is valid with the total field convention even at zero. -/
theorem pow_toNat_div_pow_neg_toNat (z : ℂ) (n : ℤ) :
    z ^ n.toNat / z ^ (-n).toNat = z ^ n := by
  cases n with
  | ofNat n => simp
  | negSucc n => simp

/-- The exchange ratio is the Laurent monomial with the actual signed matrix row. -/
theorem exchangeCharacter_eq_zpow_product (p : S.Point) (i : Fin d) :
    exchangeCharacter p i = ∏ j, p.a j ^ (S.B i j) := by
  unfold exchangeCharacter Seed.positiveMonomial Seed.negativeMonomial
  rw [← Finset.prod_div_distrib]
  apply Finset.prod_congr rfl
  intro j _
  exact pow_toNat_div_pow_neg_toNat (p.a j) (S.B i j)
theorem exchangeCharacter_ne_zero_on_independent_locus
    (hI : S.Independent I) {p : S.Point} (hp : p ∈ candidateChartLocus S I)
    {i : Fin d} (hi : i ∈ I) : exchangeCharacter p i ≠ 0 :=
  div_ne_zero (positiveMonomial_ne_zero_on_independent_locus hI hp hi)
    (negativeMonomial_ne_zero_on_independent_locus hI hp hi)

/-- The exact normalized node equation, using the actual mutation partner. -/
theorem normalized_node_equation
    (hI : S.Independent I) {p : S.Point} (hp : p ∈ candidateChartLocus S I)
    (i : S.Mutable) (hi : (i : Fin d) ∈ I) :
    p.a i * normalizedPartner p i = 1 + exchangeCharacter p i := by
  have hQ := negativeMonomial_ne_zero_on_independent_locus hI hp hi
  unfold normalizedPartner exchangeCharacter
  rw [← mul_div_assoc, p.exchange i, add_div, div_self hQ, add_comm]

/-- The resulting pair lies in the literal node model `uv ≠ 1`. -/
theorem normalized_node_product_ne_one
    (hI : S.Independent I) {p : S.Point} (hp : p ∈ candidateChartLocus S I)
    (i : S.Mutable) (hi : (i : Fin d) ∈ I) :
    p.a i * normalizedPartner p i ≠ 1 := by
  rw [normalized_node_equation hI hp i hi]
  intro h
  have hq : exchangeCharacter p i = 0 := by
    exact add_left_cancel (a := (1 : ℂ)) (by simpa using h)
  exact exchangeCharacter_ne_zero_on_independent_locus hI hp hi hq

/-- Restricting an independent row to the complementary coordinates retains
an explicit integral right inverse from the inverse of the full unimodular
matrix. This is the splitting identity behind primitive lattice extension. -/
theorem independent_rows_inverse_pairing (hdet : S.Unimodular)
    (hI : S.Independent I) (i k : {i : Fin d // i ∈ I}) :
    (∑ j : {j : Fin d // j ∉ I}, S.B i j * S.B⁻¹ j k) =
      if i = k then 1 else 0 := by
  classical
  have hunit : IsUnit S.B.det := by
    rw [show S.B.det = 1 from hdet]
    exact isUnit_one
  have hsum :
      (∑ j : Fin d, S.B i j * S.B⁻¹ j k) =
        ∑ j : {j : Fin d // j ∉ I}, S.B i j * S.B⁻¹ j k := by
    refine Finset.sum_congr_set {j : Fin d | j ∉ I}
      (fun j => S.B i j * S.B⁻¹ j k)
      (fun j => S.B i j * S.B⁻¹ j k) (fun _ _ => rfl) ?_
    intro j hj
    have hjI : j ∈ I := by simpa using hj
    rw [hI.2 i.val i.property j hjI, zero_mul]
  have hfull := congrFun (congrFun (Matrix.mul_nonsing_inv S.B hunit) i.val) k.val
  rw [Matrix.mul_apply, hsum] at hfull
  simpa only [Matrix.one_apply, Subtype.coe_inj] using hfull
/-- The specified character rows on the complementary coordinate lattice. -/
def independentRowMatrix (S : Seed d) (I : Finset (Fin d)) :
    Matrix {i : Fin d // i ∈ I} {j : Fin d // j ∉ I} ℤ :=
  fun i j => S.B i j

/-- An integral right inverse obtained from the full inverse matrix. -/
noncomputable def independentRowRightInverse (S : Seed d) (I : Finset (Fin d)) :
    Matrix {j : Fin d // j ∉ I} {i : Fin d // i ∈ I} ℤ :=
  fun j i => S.B⁻¹ j i

/-- The independent-row map has an actual integral splitting. -/
theorem independentRowMatrix_mul_rightInverse (hdet : S.Unimodular)
    (hI : S.Independent I) :
    independentRowMatrix S I * independentRowRightInverse S I = 1 := by
  ext i k
  rw [Matrix.mul_apply, Matrix.one_apply]
  exact independent_rows_inverse_pairing hdet hI i k

/-- In particular the prescribed restricted rows are linearly independent over ℤ. -/
theorem independent_rows_linearIndependent (hdet : S.Unimodular)
    (hI : S.Independent I) :
    LinearIndependent ℤ (independentRowMatrix S I).row := by
  apply Matrix.vecMul_injective_iff.mp
  intro x y h
  have h' := congrArg (fun v => (independentRowRightInverse S I).vecMul v) h
  simpa only [Matrix.vecMul_vecMul,
    independentRowMatrix_mul_rightInverse hdet hI, Matrix.vecMul_one] using h'
end ClusterSkeleton
