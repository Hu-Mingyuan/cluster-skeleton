import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-!
# Weighted symmetrizer linear algebra

This module is the finite-dimensional linear algebra behind the weighted
(skew-symmetrizable) skeleton argument of `docs/tex/proof-blueprint.tex`. It is
deliberately **Mathlib-only**: it imports no `ClusterSkeleton` module, so that it
can be developed and consumed independently of the seed structure.

## The weighted exchange matrix

The blueprint fixes an integral completion `E ∈ GL_n(ℤ)` and a positive rational
diagonal `D = diag (d_j)` such that `K = E D` is skew-symmetric, i.e.

```
∀ i j, (E i j : ℚ) * D j = -((E j i : ℚ) * D i).
```

`K` is defined here over an arbitrary characteristic-zero field `F` by casting,
so both `ℝ` and `ℂ` instantiate every statement.

* `E_diag_zero`, `E_pos_iff_neg`, `E_neg_iff_pos`, `E_eq_zero_iff`: the integral
  sign facts that positivity of the weights forces on `E` (used by the zero-set
  argument).
* `K_apply_skew`, `K_transpose`: skewness of `K` over `F`.
* `det_K`, `det_K_ne_zero`, `isUnit_det_K`, `K_mul_inv`, `K_inv_mul`:
  `det K = det E * ∏ D`, hence invertibility of `K` when `det E = 1`.
* `K_mulVec_single`, `sum_K_col`, `sum_K_row`: `K e_i = d_i c_i` and the two
  transposed sum identities `∑_j K_{ji} u_j = d_i ∑_j E_{ji} u_j` and
  `∑_l K_{il} θ_l = -d_i ∑_l E_{li} θ_l`, which is the torus split identity
  `eq:acyclic-ltor-split`.
* `vecMul_single_K`, `vecMul_E_col_inv_K`, `sum_E_col_mul_inv_mulVec`:
  `c_iᵀ K⁻¹ = -e_iᵀ / d_i` and the angle-equation consequence
  `∑_j E_{ji} (K⁻¹ x)_j = -x_i / d_i`.

## Residual-block nondegeneracy

The second half proves the nondegeneracy step of the blueprint section
*Weighted form on the actual node charts*: a nonsingular skew form whose first
block row is `(0, Δ, 0)` with `Δ` an invertible diagonal has a nonsingular
residual block `C`. See `residualBlock_eq_zero_of_mulVec_eq_zero`,
`isUnit_det_residualBlock`, `det_residualBlock_ne_zero` and the reindexed
versions `isUnit_det_residualBlock_reindex`, `det_residualBlock_ne_zero_reindex`
(for a consumer holding `Pᵀ K P` on an arbitrary index type together with an
equivalence to `I ⊕ I ⊕ R`).

Positivity of the determinant of a nonsingular real skew-symmetric matrix is
deliberately **not** proved here: it needs the Pfaffian identity `det = Pf²`,
which Mathlib does not have, and no consumer of this module requires it.
-/

set_option autoImplicit false

namespace ClusterSkeleton.SymmetrizerAlgebra

open Matrix

/-! ### The weighted exchange matrix `K = E D` -/

/-- The weighted exchange matrix `K = E D` of the blueprint, over a field `F`:
`K i j = E i j * D j`. -/
def K (F : Type*) [Field F] {d : ℕ} (E : Matrix (Fin d) (Fin d) ℤ) (D : Fin d → ℚ) :
    Matrix (Fin d) (Fin d) F :=
  Matrix.of fun i j => (E i j : F) * (D j : F)

@[simp]
theorem K_apply (F : Type*) [Field F] {d : ℕ} (E : Matrix (Fin d) (Fin d) ℤ) (D : Fin d → ℚ)
    (i j : Fin d) : K F E D i j = (E i j : F) * (D j : F) := rfl

section Integral

variable {d : ℕ} {E : Matrix (Fin d) (Fin d) ℤ} {D : Fin d → ℚ}

/-- Positivity of the weights forces the diagonal of `E` to vanish. -/
theorem E_diag_zero (hD : ∀ i, 0 < D i)
    (hK : ∀ i j, (E i j : ℚ) * D j = -((E j i : ℚ) * D i)) (i : Fin d) : E i i = 0 := by
  have h := hK i i
  have h0 : (E i i : ℚ) * D i = 0 := by linarith
  have : (E i i : ℚ) = 0 := by
    rcases mul_eq_zero.1 h0 with h1 | h2
    · exact h1
    · exact absurd h2 (ne_of_gt (hD i))
  exact_mod_cast this

/-- Positivity of the weights forces opposite signs: `0 < E i j ↔ E j i < 0`. -/
theorem E_pos_iff_neg (hD : ∀ i, 0 < D i)
    (hK : ∀ i j, (E i j : ℚ) * D j = -((E j i : ℚ) * D i)) (i j : Fin d) :
    0 < E i j ↔ E j i < 0 := by
  constructor
  · intro h
    have h1 : (0 : ℚ) < (E i j : ℚ) * D j := mul_pos (by exact_mod_cast h) (hD j)
    rw [hK i j] at h1
    have h2 : (E j i : ℚ) * D i < 0 := by linarith
    rcases mul_neg_iff.1 h2 with ⟨_, hneg⟩ | ⟨hneg, _⟩
    · exact absurd hneg (not_lt.2 (le_of_lt (hD i)))
    · exact_mod_cast hneg
  · intro h
    have h1 : (E j i : ℚ) * D i < 0 := mul_neg_of_neg_of_pos (by exact_mod_cast h) (hD i)
    have h2 : (0 : ℚ) < (E i j : ℚ) * D j := by rw [hK i j]; linarith
    rcases mul_pos_iff.1 h2 with ⟨hpos, _⟩ | ⟨_, hneg⟩
    · exact_mod_cast hpos
    · exact absurd hneg (not_lt.2 (le_of_lt (hD j)))

/-- The companion sign statement `E i j < 0 ↔ 0 < E j i`. -/
theorem E_neg_iff_pos (hD : ∀ i, 0 < D i)
    (hK : ∀ i j, (E i j : ℚ) * D j = -((E j i : ℚ) * D i)) (i j : Fin d) :
    E i j < 0 ↔ 0 < E j i :=
  (E_pos_iff_neg hD hK j i).symm

/-- Positivity of the weights forces `E i j = 0 ↔ E j i = 0`. -/
theorem E_eq_zero_iff (hD : ∀ i, 0 < D i)
    (hK : ∀ i j, (E i j : ℚ) * D j = -((E j i : ℚ) * D i)) (i j : Fin d) :
    E i j = 0 ↔ E j i = 0 := by
  have key : ∀ a b : Fin d, E a b = 0 → E b a = 0 := by
    intro a b h
    have h1 := hK a b
    rw [h] at h1
    push_cast at h1
    have h2 : (E b a : ℚ) * D a = 0 := by linarith
    have : (E b a : ℚ) = 0 := by
      rcases mul_eq_zero.1 h2 with h3 | h4
      · exact h3
      · exact absurd h4 (ne_of_gt (hD a))
    exact_mod_cast this
  exact ⟨key i j, key j i⟩

end Integral

/-! ### Skewness of `K` -/

section Field

variable {d : ℕ} {E : Matrix (Fin d) (Fin d) ℤ} {D : Fin d → ℚ}

/-- The skew-symmetry hypothesis, transported to an arbitrary characteristic-zero
field by casting. -/
theorem K_apply_skew (F : Type*) [Field F] [CharZero F]
    (hK : ∀ i j, (E i j : ℚ) * D j = -((E j i : ℚ) * D i)) (i j : Fin d) :
    K F E D i j = -(K F E D j i) := by
  have h : (((E i j : ℚ) * D j : ℚ) : F) = ((-((E j i : ℚ) * D i) : ℚ) : F) := by rw [hK i j]
  push_cast at h
  simpa using h

/-- `K` is skew-symmetric: `Kᵀ = -K`. -/
theorem K_transpose (F : Type*) [Field F] [CharZero F]
    (hK : ∀ i j, (E i j : ℚ) * D j = -((E j i : ℚ) * D i)) :
    (K F E D)ᵀ = -(K F E D) := by
  ext i j
  simpa using K_apply_skew F hK j i

/-! ### The determinant of `K` -/

/-- `K = E · diag D`. -/
theorem K_eq_mul_diagonal (F : Type*) [Field F] :
    K F E D = (E.map fun a : ℤ => (a : F)) * Matrix.diagonal fun j => (D j : F) := by
  ext i j
  simp [Matrix.mul_diagonal]

/-- `det K = det E * ∏ d_i`. -/
theorem det_K (F : Type*) [Field F] [CharZero F] :
    (K F E D).det = (E.det : F) * ∏ i, (D i : F) := by
  rw [K_eq_mul_diagonal F, Matrix.det_mul, Matrix.det_diagonal, Int.cast_det]

/-- `det K ≠ 0` as soon as `det E` is nonzero in `F`, the weights being positive. -/
theorem det_K_ne_zero (F : Type*) [Field F] [CharZero F] (hD : ∀ i, 0 < D i)
    (hE : (E.det : F) ≠ 0) : (K F E D).det ≠ 0 := by
  rw [det_K F]
  refine mul_ne_zero hE (Finset.prod_ne_zero_iff.2 ?_)
  intro i _
  exact_mod_cast ne_of_gt (hD i)

/-- For a unimodular completion `E`, `K` is invertible. -/
theorem isUnit_det_K (F : Type*) [Field F] [CharZero F] (hD : ∀ i, 0 < D i) (hE : E.det = 1) :
    IsUnit (K F E D).det :=
  isUnit_iff_ne_zero.2 (det_K_ne_zero F hD (by rw [hE]; norm_num))

theorem K_mul_inv (F : Type*) [Field F] [CharZero F] (hD : ∀ i, 0 < D i) (hE : E.det = 1) :
    K F E D * (K F E D)⁻¹ = 1 :=
  Matrix.mul_nonsing_inv _ (isUnit_det_K F hD hE)

theorem K_inv_mul (F : Type*) [Field F] [CharZero F] (hD : ∀ i, 0 < D i) (hE : E.det = 1) :
    (K F E D)⁻¹ * K F E D = 1 :=
  Matrix.nonsing_inv_mul _ (isUnit_det_K F hD hE)

/-! ### `K e_i = d_i c_i` and the transposed sum identities -/

/-- `K e_i = d_i c_i`, where `c_i` is the `i`-th column of `E`. -/
theorem K_mulVec_single (F : Type*) [Field F] (i : Fin d) :
    (K F E D).mulVec (Pi.single i 1) = (D i : F) • fun j => (E j i : F) := by
  funext j
  simp [Matrix.mulVec, dotProduct_single, mul_comm]

/-- The transposed identity `∑_j K_{ji} u_j = d_i ∑_j E_{ji} u_j`, i.e. `Kᵀ u = D c(u)`.
This is the first half of the torus split identity `eq:acyclic-ltor-split`
(with `u_j = log |z_j|` and `v_i = c_i(u)`). -/
theorem sum_K_col (F : Type*) [Field F] (u : Fin d → F) (i : Fin d) :
    ∑ j, K F E D j i * u j = (D i : F) * ∑ j, (E j i : F) * u j := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [K_apply]
  ring

/-- The row identity `∑_l K_{il} θ_l = -d_i ∑_l E_{li} θ_l`, i.e. `K θ = -D c(θ)`.
This is the second half of the torus split identity `eq:acyclic-ltor-split`
(with `θ_l = arg z_l` and `η_i = c_i(θ)`). -/
theorem sum_K_row (F : Type*) [Field F] [CharZero F]
    (hK : ∀ i j, (E i j : ℚ) * D j = -((E j i : ℚ) * D i)) (θ : Fin d → F) (i : Fin d) :
    ∑ l, K F E D i l * θ l = -(D i : F) * ∑ l, (E l i : F) * θ l := by
  have h : ∑ l, K F E D i l * θ l = -∑ l, K F E D l i * θ l := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [K_apply_skew F hK i l]
    ring
  rw [h, sum_K_col F θ i]
  ring

/-! ### `c_iᵀ K⁻¹ = -e_iᵀ / d_i` -/

/-- `(-d_i⁻¹ e_i)ᵀ K = c_iᵀ`: the row form of the identity solved below. -/
theorem vecMul_single_K (F : Type*) [Field F] [CharZero F] (hD : ∀ i, 0 < D i)
    (hK : ∀ i j, (E i j : ℚ) * D j = -((E j i : ℚ) * D i)) (i : Fin d) :
    Matrix.vecMul (Pi.single i (-((D i : F)⁻¹))) (K F E D) = fun j => (E j i : F) := by
  have hDi : ((D i : ℚ) : F) ≠ 0 := by exact_mod_cast ne_of_gt (hD i)
  funext j
  rw [Matrix.single_vecMul]
  simp only [Pi.smul_apply, smul_eq_mul, Matrix.row_apply, K_apply]
  have h : (E i j : F) * (D j : F) = -((E j i : F) * (D i : F)) := by
    simpa using K_apply_skew F hK i j
  rw [h]
  field_simp

/-- `c_iᵀ K⁻¹ = -e_iᵀ / d_i`. -/
theorem vecMul_E_col_inv_K (F : Type*) [Field F] [CharZero F] (hD : ∀ i, 0 < D i)
    (hK : ∀ i j, (E i j : ℚ) * D j = -((E j i : ℚ) * D i)) (hE : E.det = 1) (i : Fin d) :
    Matrix.vecMul (fun j => (E j i : F)) (K F E D)⁻¹ = -((D i : F)⁻¹) • Pi.single i (1 : F) := by
  have hsingle : Pi.single i (-((D i : F)⁻¹)) = -((D i : F)⁻¹) • Pi.single i (1 : F) := by
    funext j
    by_cases h : j = i <;> simp [h]
  calc Matrix.vecMul (fun j => (E j i : F)) (K F E D)⁻¹
      = Matrix.vecMul (Matrix.vecMul (Pi.single i (-((D i : F)⁻¹))) (K F E D)) (K F E D)⁻¹ := by
        rw [vecMul_single_K F hD hK i]
    _ = Matrix.vecMul (Pi.single i (-((D i : F)⁻¹))) (K F E D * (K F E D)⁻¹) :=
        Matrix.vecMul_vecMul _ _ _
    _ = Pi.single i (-((D i : F)⁻¹)) := by rw [K_mul_inv F hD hE, Matrix.vecMul_one]
    _ = -((D i : F)⁻¹) • Pi.single i (1 : F) := hsingle

/-- The angle-equation consequence `∑_j E_{ji} (K⁻¹ x)_j = -x_i / d_i`. -/
theorem sum_E_col_mul_inv_mulVec (F : Type*) [Field F] [CharZero F] (hD : ∀ i, 0 < D i)
    (hK : ∀ i j, (E i j : ℚ) * D j = -((E j i : ℚ) * D i)) (hE : E.det = 1) (i : Fin d)
    (x : Fin d → F) :
    ∑ j, (E j i : F) * ((K F E D)⁻¹.mulVec x) j = -(x i) / (D i : F) := by
  have h1 : (fun j => (E j i : F)) ⬝ᵥ ((K F E D)⁻¹.mulVec x)
      = Matrix.vecMul (fun j => (E j i : F)) (K F E D)⁻¹ ⬝ᵥ x :=
    Matrix.dotProduct_mulVec _ _ _
  rw [vecMul_E_col_inv_K F hD hK hE i] at h1
  have h2 : (-((D i : F)⁻¹) • Pi.single i (1 : F)) ⬝ᵥ x = -(x i) / (D i : F) := by
    rw [smul_dotProduct, single_dotProduct, one_mul, smul_eq_mul, div_eq_mul_inv]
    ring
  rw [show (∑ j, (E j i : F) * ((K F E D)⁻¹.mulVec x) j)
      = (fun j => (E j i : F)) ⬝ᵥ ((K F E D)⁻¹.mulVec x) from rfl, h1, h2]

end Field

/-! ### Residual-block nondegeneracy -/

section ResidualBlock

variable {F : Type*} [Field F] {I R : Type*} [Fintype I] [DecidableEq I] [Fintype R]
  [DecidableEq R]

/-- The residual `R × R` block `C` of a form on `I ⊕ I ⊕ R`. -/
def residualBlock (M : Matrix (I ⊕ I ⊕ R) (I ⊕ I ⊕ R) F) : Matrix R R F :=
  Matrix.of fun r r' => M (Sum.inr (Sum.inr r)) (Sum.inr (Sum.inr r'))

omit [Field F] [Fintype I] [DecidableEq I] [Fintype R] [DecidableEq R] in
@[simp]
theorem residualBlock_apply (M : Matrix (I ⊕ I ⊕ R) (I ⊕ I ⊕ R) F) (r r' : R) :
    residualBlock M r r' = M (Sum.inr (Sum.inr r)) (Sum.inr (Sum.inr r')) := rfl

/-- **Residual-block nondegeneracy, kernel form.** Let `M` be a nonsingular skew form on
`I ⊕ I ⊕ R` whose first block row is `(0, Δ, 0)` with `Δ = diag δ` and `δ i ≠ 0`.
Then the residual block `C` has trivial kernel. -/
theorem residualBlock_eq_zero_of_mulVec_eq_zero
    {M : Matrix (I ⊕ I ⊕ R) (I ⊕ I ⊕ R) F} (hskew : Mᵀ = -M) (hM : IsUnit M.det)
    {δ : I → F} (hδ : ∀ i, δ i ≠ 0)
    (h11 : ∀ i i', M (Sum.inl i) (Sum.inl i') = 0)
    (h13 : ∀ i r, M (Sum.inl i) (Sum.inr (Sum.inr r)) = 0)
    (h12 : ∀ i i', M (Sum.inl i) (Sum.inr (Sum.inl i')) = if i = i' then δ i else 0)
    {x : R → F} (hx : (residualBlock M).mulVec x = 0) : x = 0 := by
  have hsk : ∀ a b, M a b = -(M b a) := by
    intro a b
    have h := congrFun (congrFun hskew b) a
    simpa using h
  -- the only two off-diagonal blocks of the first row/column that we need
  have hJI : ∀ j i', M (Sum.inr (Sum.inl j)) (Sum.inl i') = -(if i' = j then δ i' else 0) := by
    intro j i'
    rw [hsk (Sum.inr (Sum.inl j)) (Sum.inl i'), h12 i' j]
  have hRI : ∀ s i', M (Sum.inr (Sum.inr s)) (Sum.inl i') = 0 := by
    intro s i'
    rw [hsk (Sum.inr (Sum.inr s)) (Sum.inl i'), h13 i' s, neg_zero]
  -- the `J`-row solution for the `I`-block of the test vector
  set S : I → F := fun j => ∑ r : R, M (Sum.inr (Sum.inl j)) (Sum.inr (Sum.inr r)) * x r with hS
  set v : I ⊕ I ⊕ R → F := Sum.elim (fun j => (δ j)⁻¹ * S j) (Sum.elim 0 x) with hv
  have hMv : M.mulVec v = 0 := by
    funext k
    simp only [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, hv, Sum.elim_inl, Sum.elim_inr,
      Pi.zero_apply, mul_zero, Finset.sum_const_zero, zero_add]
    rcases k with i | i | s
    · simp [h11, h13]
    · have hδS : δ i * ((δ i)⁻¹ * S i) = S i := by
        rw [← mul_assoc, mul_inv_cancel₀ (hδ i), one_mul]
      have h1 : ∑ i' : I, M (Sum.inr (Sum.inl i)) (Sum.inl i') * ((δ i')⁻¹ * S i')
          = -(S i) := by
        simp only [hJI]
        rw [show (∑ i' : I, -(if i' = i then δ i' else 0) * ((δ i')⁻¹ * S i'))
            = ∑ i' : I, (if i' = i then -(δ i' * ((δ i')⁻¹ * S i')) else 0) from
          Finset.sum_congr rfl fun i' _ => by
            by_cases h : i' = i <;> simp [h]]
        rw [Finset.sum_ite_eq' Finset.univ i fun i' => -(δ i' * ((δ i')⁻¹ * S i'))]
        simp [hδS]
      rw [h1, hS]
      ring
    · have h1 : ∑ i' : I, M (Sum.inr (Sum.inr s)) (Sum.inl i') * ((δ i')⁻¹ * S i') = 0 := by
        simp [hRI]
      have h2 : ∑ r : R, M (Sum.inr (Sum.inr s)) (Sum.inr (Sum.inr r)) * x r = 0 := by
        have := congrFun hx s
        simpa [Matrix.mulVec, dotProduct] using this
      rw [h1, h2, add_zero]
  have hv0 : v = 0 := by
    have h1 : M⁻¹.mulVec (M.mulVec v) = v := by
      rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hM, Matrix.one_mulVec]
    rw [hMv, Matrix.mulVec_zero] at h1
    exact h1.symm
  funext r
  have h := congrFun hv0 (Sum.inr (Sum.inr r))
  simpa [hv] using h

/-- **Residual-block nondegeneracy.** The residual block of a nonsingular skew form whose
first block row is `(0, Δ, 0)`, with `Δ = diag δ` invertible, is nonsingular. -/
theorem isUnit_det_residualBlock
    {M : Matrix (I ⊕ I ⊕ R) (I ⊕ I ⊕ R) F} (hskew : Mᵀ = -M) (hM : IsUnit M.det)
    {δ : I → F} (hδ : ∀ i, δ i ≠ 0)
    (h11 : ∀ i i', M (Sum.inl i) (Sum.inl i') = 0)
    (h13 : ∀ i r, M (Sum.inl i) (Sum.inr (Sum.inr r)) = 0)
    (h12 : ∀ i i', M (Sum.inl i) (Sum.inr (Sum.inl i')) = if i = i' then δ i else 0) :
    IsUnit (residualBlock M).det := by
  refine isUnit_iff_ne_zero.2 fun hdet => ?_
  obtain ⟨y, hy, hy0⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hdet
  exact hy (residualBlock_eq_zero_of_mulVec_eq_zero hskew hM hδ h11 h13 h12 hy0)

/-- The determinant form of `isUnit_det_residualBlock`. -/
theorem det_residualBlock_ne_zero
    {M : Matrix (I ⊕ I ⊕ R) (I ⊕ I ⊕ R) F} (hskew : Mᵀ = -M) (hM : IsUnit M.det)
    {δ : I → F} (hδ : ∀ i, δ i ≠ 0)
    (h11 : ∀ i i', M (Sum.inl i) (Sum.inl i') = 0)
    (h13 : ∀ i r, M (Sum.inl i) (Sum.inr (Sum.inr r)) = 0)
    (h12 : ∀ i i', M (Sum.inl i) (Sum.inr (Sum.inl i')) = if i = i' then δ i else 0) :
    (residualBlock M).det ≠ 0 :=
  isUnit_iff_ne_zero.1 (isUnit_det_residualBlock hskew hM hδ h11 h13 h12)

omit [Fintype I] [DecidableEq I] [Fintype R] [DecidableEq R] in
/-- The skewness hypothesis is inherited by an `Equiv`-reindexing. -/
theorem transpose_submatrix_eq_neg {m n : Type*} {M : Matrix n n F} (hskew : Mᵀ = -M)
    (e : m ≃ n) :
    (M.submatrix e e)ᵀ = -(M.submatrix e e) := by
  ext a b
  have h := congrFun (congrFun hskew (e a)) (e b)
  simpa using h

/-- **Residual-block nondegeneracy, reindexed.** The version a consumer uses when the skew
form lives on an arbitrary index type `n` (e.g. `Pᵀ K P` on `Fin d`) together with an
equivalence `e : n ≃ I ⊕ I ⊕ R` splitting the coordinates into the `x`-block, the `t`-block
and the residual block. -/
theorem isUnit_det_residualBlock_reindex {n : Type*} [Fintype n] [DecidableEq n]
    (e : n ≃ I ⊕ I ⊕ R) {M : Matrix n n F} (hskew : Mᵀ = -M) (hM : IsUnit M.det)
    {δ : I → F} (hδ : ∀ i, δ i ≠ 0)
    (h11 : ∀ i i', M (e.symm (Sum.inl i)) (e.symm (Sum.inl i')) = 0)
    (h13 : ∀ i r, M (e.symm (Sum.inl i)) (e.symm (Sum.inr (Sum.inr r))) = 0)
    (h12 : ∀ i i', M (e.symm (Sum.inl i)) (e.symm (Sum.inr (Sum.inl i')))
      = if i = i' then δ i else 0) :
    IsUnit (Matrix.of fun r r' : R =>
      M (e.symm (Sum.inr (Sum.inr r))) (e.symm (Sum.inr (Sum.inr r')))).det :=
  isUnit_det_residualBlock (M := M.submatrix e.symm e.symm)
    (transpose_submatrix_eq_neg hskew e.symm)
    (by rw [Matrix.det_submatrix_equiv_self]; exact hM) hδ h11 h13 h12

/-- The determinant form of `isUnit_det_residualBlock_reindex`. -/
theorem det_residualBlock_ne_zero_reindex {n : Type*} [Fintype n] [DecidableEq n]
    (e : n ≃ I ⊕ I ⊕ R) {M : Matrix n n F} (hskew : Mᵀ = -M) (hM : IsUnit M.det)
    {δ : I → F} (hδ : ∀ i, δ i ≠ 0)
    (h11 : ∀ i i', M (e.symm (Sum.inl i)) (e.symm (Sum.inl i')) = 0)
    (h13 : ∀ i r, M (e.symm (Sum.inl i)) (e.symm (Sum.inr (Sum.inr r))) = 0)
    (h12 : ∀ i i', M (e.symm (Sum.inl i)) (e.symm (Sum.inr (Sum.inl i')))
      = if i = i' then δ i else 0) :
    (Matrix.of fun r r' : R =>
      M (e.symm (Sum.inr (Sum.inr r))) (e.symm (Sum.inr (Sum.inr r')))).det ≠ 0 :=
  isUnit_iff_ne_zero.1 (isUnit_det_residualBlock_reindex e hskew hM hδ h11 h13 h12)

end ResidualBlock

end ClusterSkeleton.SymmetrizerAlgebra
