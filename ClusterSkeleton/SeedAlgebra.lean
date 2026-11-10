import ClusterSkeleton.Seed
import ClusterSkeleton.SymmetrizerAlgebra
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Seed-level weighted linear algebra for the weighted dynamics chain

This module is the stage-C prerequisite of the skew-symmetrizable objective: it
specializes the Mathlib-only matrix algebra of
`ClusterSkeleton.SymmetrizerAlgebra` to a concrete `Seed d`, over `ℝ` and over
`ℂ`, and packages once the inverse facts that the dynamics modules need.

Nothing here bundles a new structure: every statement is about a fixed
`(S : Seed d)`, with `hdet : S.Unimodular` only where invertibility is used.

## Conventions

* `S.E` is the integral exchange matrix, `S.D` the positive rational
  symmetrizer, and `S.K i j = (S.E i j : ℚ) * S.D j` the weighted form matrix,
  which is skew-symmetric (`Seed.K_transpose`).
* The exponent matrix is `S.B = S.Eᵀ`, so **`S.B i j` is by definition the
  column exponent `S.E j i`**. The two expressions are definitionally equal at
  default transparency (`exact`, `rfl`, `change` cross them; `rw` and
  `simp only` do not), so each statement below is phrased in one orientation and
  kept there; `Seed.B_apply` is the bridge when a rewrite has to cross.
* `Kreal`, `Breal`, `Ereal` (and the `ℂ` mirrors `Kcomplex`, `Bcomplex`,
  `Ecomplex`) are the entrywise casts. `Breal` is the matrix that the baseline
  `D = I` dynamics invert; `Kreal` is the matrix the weighted dynamics invert.

## The identities the blueprint uses

With `u_j = log‖z_j‖`, `θ_j = arg z_j`, `v_i = c_i(u) = ∑_j E_{ji} u_j =
∑_j (S.B i j) u_j` and `η_i = c_i(θ)`, the weighted identities of
`docs/tex/proof-blueprint.tex` are

| blueprint | here |
| --- | --- |
| `∑_j K_{ji} u_j = d_i v_i` | `sum_K_col` |
| `∑_l K_{il} θ_l = -d_i η_i` | `sum_K_row` |
| `K e_i = d_i c_i` | `K_mulVec_single` |
| `K^T = -K` | `Kreal_transpose`, `sum_sum_K_antisymm` |
| `c_i(K⁻¹ x) = -x_i / d_i` | `c_inv_K`, `Breal_mulVec_inv_K` |

The scalar form of the first two is `K_eq_neg_D_mul_B`: `K_{ij} = -d_i B_{ij}`,
i.e. `Kreal = -(diagonal d) * Breal` (`Kreal_eq_neg_diagonal_mul_Breal`).
Consequently a `K`-system and a `B`-system are interchangeable up to the
weights, which is `Kreal_mulVec_eq_iff`; that is the lemma that lets a baseline
proof which inverted the integer matrix keep its shape. Where a baseline proof
cancelled the integer matrix by `det B = 1`, the weighted proof cancels `K` by
`Kreal_vecMul_injective` / `Kreal_mulVec_injective`, which rest on
`isUnit_det_Kreal` rather than on a determinant equal to `1`; the integer
cancellation itself is still available as `det_Breal` and
`Breal_vecMul_injective`.

## The one-norm inverse bounds

`exists_inverse_bound_Breal` is `TorusLiouvilleDynamics.full_matrix_inverse_bound`
lifted to the seed level, and `exists_inverse_bound_Kreal` is its `K`-analogue;
both come from `exists_inverse_bound_of_isUnit`, the same argument for an
arbitrary real square matrix with invertible determinant. Neither discards
frozen columns and neither needs `0 < d`.
-/

set_option autoImplicit false

open scoped BigOperators Matrix

namespace ClusterSkeleton.SeedAlgebra

variable {d : ℕ} (S : Seed d)

/-! ### The cast matrices -/

/-- The weighted form matrix over `ℝ`. -/
def Kreal : Matrix (Fin d) (Fin d) ℝ := Matrix.of fun i j => (S.K i j : ℝ)

/-- The weighted form matrix over `ℂ`. -/
def Kcomplex : Matrix (Fin d) (Fin d) ℂ := Matrix.of fun i j => (S.K i j : ℂ)

/-- The exponent matrix over `ℝ`; this is the matrix the baseline `D = I`
dynamics invert. -/
def Breal : Matrix (Fin d) (Fin d) ℝ := Matrix.of fun i j => (S.B i j : ℝ)

/-- The exponent matrix over `ℂ`. -/
def Bcomplex : Matrix (Fin d) (Fin d) ℂ := Matrix.of fun i j => (S.B i j : ℂ)

/-- The exchange matrix over `ℝ`; its `i`-th column is the blueprint's `c_i`. -/
def Ereal : Matrix (Fin d) (Fin d) ℝ := Matrix.of fun i j => (S.E i j : ℝ)

/-- The exchange matrix over `ℂ`. -/
def Ecomplex : Matrix (Fin d) (Fin d) ℂ := Matrix.of fun i j => (S.E i j : ℂ)

@[simp] theorem Kreal_apply (i j : Fin d) : Kreal S i j = (S.K i j : ℝ) := rfl

@[simp] theorem Kcomplex_apply (i j : Fin d) : Kcomplex S i j = (S.K i j : ℂ) := rfl

@[simp] theorem Breal_apply (i j : Fin d) : Breal S i j = (S.B i j : ℝ) := rfl

@[simp] theorem Bcomplex_apply (i j : Fin d) : Bcomplex S i j = (S.B i j : ℂ) := rfl

@[simp] theorem Ereal_apply (i j : Fin d) : Ereal S i j = (S.E i j : ℝ) := rfl

@[simp] theorem Ecomplex_apply (i j : Fin d) : Ecomplex S i j = (S.E i j : ℂ) := rfl

/-- The exponent matrix is the transpose of the exchange matrix, over `ℝ`. -/
theorem Breal_eq_transpose : Breal S = (Ereal S)ᵀ := rfl

theorem Bcomplex_eq_transpose : Bcomplex S = (Ecomplex S)ᵀ := rfl

/-- `Breal S i j` is the column entry `Ereal S j i`. The two sides are
definitionally equal; this lemma names the fact so that a `rw` can cross the
two orientations. -/
theorem Breal_apply_eq_Ereal (i j : Fin d) : Breal S i j = Ereal S j i := rfl

theorem Bcomplex_apply_eq_Ecomplex (i j : Fin d) : Bcomplex S i j = Ecomplex S j i := rfl

/-- The row expansion of a `B`-system, exponent orientation. -/
theorem Breal_mulVec_apply (z : Fin d → ℝ) (i : Fin d) :
    (Breal S).mulVec z i = ∑ j, (S.B i j : ℝ) * z j := rfl

/-- The row expansion of a `B`-system, column orientation: this is the
blueprint's `c_i(z)`. -/
theorem Breal_mulVec_apply_E (z : Fin d → ℝ) (i : Fin d) :
    (Breal S).mulVec z i = ∑ j, (S.E j i : ℝ) * z j := rfl

theorem Bcomplex_mulVec_apply (z : Fin d → ℂ) (i : Fin d) :
    (Bcomplex S).mulVec z i = ∑ j, (S.B i j : ℂ) * z j := rfl

theorem Bcomplex_mulVec_apply_E (z : Fin d → ℂ) (i : Fin d) :
    (Bcomplex S).mulVec z i = ∑ j, (S.E j i : ℂ) * z j := rfl

/-- The row expansion of a `K`-system. -/
theorem Kreal_mulVec_apply (z : Fin d → ℝ) (i : Fin d) :
    (Kreal S).mulVec z i = ∑ j, (S.K i j : ℝ) * z j := rfl

theorem Kcomplex_mulVec_apply (z : Fin d → ℂ) (i : Fin d) :
    (Kcomplex S).mulVec z i = ∑ j, (S.K i j : ℂ) * z j := rfl

/-! ### The bridge to `SymmetrizerAlgebra` -/

/-- `Kreal` is the `SymmetrizerAlgebra` matrix `K ℝ E D`: every statement of that
module specializes along this equality, with `hD := S.D_pos`,
`hK := S.skewSymmetrizable` and `hE := hdet`. -/
theorem Kreal_eq_symmetrizerK : Kreal S = SymmetrizerAlgebra.K ℝ S.E S.D := by
  ext i j
  simp only [Kreal_apply, SymmetrizerAlgebra.K_apply, Seed.K_apply]
  push_cast
  ring

theorem Kcomplex_eq_symmetrizerK : Kcomplex S = SymmetrizerAlgebra.K ℂ S.E S.D := by
  ext i j
  simp only [Kcomplex_apply, SymmetrizerAlgebra.K_apply, Seed.K_apply]
  push_cast
  ring

/-! ### Skewness, factorization and determinant -/

/-- `K` is skew-symmetric over `ℝ`: `Kᵀ = -K`. -/
theorem Kreal_transpose : (Kreal S)ᵀ = -Kreal S := by
  rw [Kreal_eq_symmetrizerK]
  exact SymmetrizerAlgebra.K_transpose ℝ S.skewSymmetrizable

theorem Kcomplex_transpose : (Kcomplex S)ᵀ = -Kcomplex S := by
  rw [Kcomplex_eq_symmetrizerK]
  exact SymmetrizerAlgebra.K_transpose ℂ S.skewSymmetrizable

/-- The entrywise skewness `K_{ij} = -K_{ji}` over `ℝ`. -/
theorem Kreal_skew (i j : Fin d) : Kreal S i j = -(Kreal S j i) := by
  rw [Kreal_eq_symmetrizerK]
  exact SymmetrizerAlgebra.K_apply_skew ℝ S.skewSymmetrizable i j

theorem Kcomplex_skew (i j : Fin d) : Kcomplex S i j = -(Kcomplex S j i) := by
  rw [Kcomplex_eq_symmetrizerK]
  exact SymmetrizerAlgebra.K_apply_skew ℂ S.skewSymmetrizable i j

/-- `K = E · diag D` over `ℝ`. -/
theorem Kreal_eq_Ereal_mul_diagonal :
    Kreal S = Ereal S * Matrix.diagonal fun j => (S.D j : ℝ) := by
  ext i j
  simp [Kreal, Ereal, Seed.K, Matrix.mul_diagonal]

theorem Kcomplex_eq_Ecomplex_mul_diagonal :
    Kcomplex S = Ecomplex S * Matrix.diagonal fun j => (S.D j : ℂ) := by
  ext i j
  simp [Kcomplex, Ecomplex, Seed.K, Matrix.mul_diagonal]

/-- The weighted determinant `det K = det E * ∏ d_i`, over `ℝ`. -/
theorem det_Kreal : (Kreal S).det = (S.E.det : ℝ) * ∏ i, (S.D i : ℝ) := by
  rw [Kreal_eq_symmetrizerK]
  exact SymmetrizerAlgebra.det_K ℝ

theorem det_Kcomplex : (Kcomplex S).det = (S.E.det : ℂ) * ∏ i, (S.D i : ℂ) := by
  rw [Kcomplex_eq_symmetrizerK]
  exact SymmetrizerAlgebra.det_K ℂ

/-- Under unimodularity the weighted determinant is the product of the weights. -/
theorem det_Kreal_of_unimodular (hdet : S.Unimodular) :
    (Kreal S).det = ∏ i, (S.D i : ℝ) := by
  rw [det_Kreal, show S.E.det = 1 from hdet, Int.cast_one, one_mul]

theorem det_Kcomplex_of_unimodular (hdet : S.Unimodular) :
    (Kcomplex S).det = ∏ i, (S.D i : ℂ) := by
  rw [det_Kcomplex, show S.E.det = 1 from hdet, Int.cast_one, one_mul]

theorem det_Kreal_ne_zero (hdet : S.Unimodular) : (Kreal S).det ≠ 0 := by
  rw [Kreal_eq_symmetrizerK]
  exact SymmetrizerAlgebra.det_K_ne_zero ℝ S.D_pos (by rw [hdet]; norm_num)

theorem det_Kcomplex_ne_zero (hdet : S.Unimodular) : (Kcomplex S).det ≠ 0 := by
  rw [Kcomplex_eq_symmetrizerK]
  exact SymmetrizerAlgebra.det_K_ne_zero ℂ S.D_pos (by rw [hdet]; norm_num)

theorem isUnit_det_Kreal (hdet : S.Unimodular) : IsUnit (Kreal S).det :=
  isUnit_iff_ne_zero.2 (det_Kreal_ne_zero S hdet)

theorem isUnit_det_Kcomplex (hdet : S.Unimodular) : IsUnit (Kcomplex S).det :=
  isUnit_iff_ne_zero.2 (det_Kcomplex_ne_zero S hdet)

/-! ### The baseline integer inverse: `det B = 1` -/

/-- The exponent matrix has determinant `1` over `ℝ`: both exponent orientations
have the determinant of `E`. This is the fact the baseline dynamics use to
invert the integer matrix, and it stays valid in the weighted setting. -/
theorem det_Breal (hdet : S.Unimodular) : (Breal S).det = 1 := by
  have h := (Int.castRingHom ℝ).map_det S.B
  change ((S.B.det : ℤ) : ℝ) = (Breal S).det at h
  rw [← h, S.B_det hdet, Int.cast_one]

theorem det_Bcomplex (hdet : S.Unimodular) : (Bcomplex S).det = 1 := by
  have h := (Int.castRingHom ℂ).map_det S.B
  change ((S.B.det : ℤ) : ℂ) = (Bcomplex S).det at h
  rw [← h, S.B_det hdet, Int.cast_one]

theorem isUnit_det_Breal (hdet : S.Unimodular) : IsUnit (Breal S).det := by
  rw [det_Breal S hdet]; exact isUnit_one

theorem isUnit_det_Bcomplex (hdet : S.Unimodular) : IsUnit (Bcomplex S).det := by
  rw [det_Bcomplex S hdet]; exact isUnit_one

theorem Breal_mul_inv (hdet : S.Unimodular) : Breal S * (Breal S)⁻¹ = 1 :=
  Matrix.mul_nonsing_inv _ (isUnit_det_Breal S hdet)

theorem Breal_inv_mul (hdet : S.Unimodular) : (Breal S)⁻¹ * Breal S = 1 :=
  Matrix.nonsing_inv_mul _ (isUnit_det_Breal S hdet)

/-- Multiplication by the exponent matrix is injective on column vectors. -/
theorem Breal_mulVec_injective (hdet : S.Unimodular) :
    Function.Injective (Breal S).mulVec :=
  Matrix.mulVec_injective_iff_isUnit.2
    ((Matrix.isUnit_iff_isUnit_det _).2 (isUnit_det_Breal S hdet))

/-- Multiplication by the exponent matrix is injective on row vectors. -/
theorem Breal_vecMul_injective (hdet : S.Unimodular) :
    Function.Injective (Breal S).vecMul :=
  Matrix.vecMul_injective_iff_isUnit.2
    ((Matrix.isUnit_iff_isUnit_det _).2 (isUnit_det_Breal S hdet))

/-- Recovering the solution of a `B`-system from the inverse. -/
theorem eq_inv_mulVec_of_Breal_mulVec (hdet : S.Unimodular) {y b : Fin d → ℝ}
    (h : (Breal S).mulVec y = b) : y = (Breal S)⁻¹.mulVec b := by
  rw [← h, Matrix.mulVec_mulVec, Breal_inv_mul S hdet, Matrix.one_mulVec]

/-! ### The weighted identities in seed form -/

/-- The scalar weighted identity `K_{ij} = -d_i B_{ij}`: the form coefficient is
the exponent coefficient scaled by the weight of its **row**, with a sign. -/
theorem K_eq_neg_D_mul_B (i j : Fin d) :
    (S.K i j : ℝ) = -(S.D i : ℝ) * (S.B i j : ℝ) := by
  have h : S.K i j = -(S.D i) * (S.B i j : ℚ) := by
    have hs := S.skewSymmetrizable i j
    have hB : ((S.B i j : ℤ) : ℚ) = ((S.E j i : ℤ) : ℚ) := rfl
    rw [Seed.K_apply, hs, hB]
    ring
  rw [h]
  push_cast
  ring

theorem K_eq_neg_D_mul_B_complex (i j : Fin d) :
    (S.K i j : ℂ) = -(S.D i : ℂ) * (S.B i j : ℂ) := by
  have h : S.K i j = -(S.D i) * (S.B i j : ℚ) := by
    have hs := S.skewSymmetrizable i j
    have hB : ((S.B i j : ℤ) : ℚ) = ((S.E j i : ℤ) : ℚ) := rfl
    rw [Seed.K_apply, hs, hB]
    ring
  rw [h]
  push_cast
  ring

/-- The transposed scalar identity `K_{ji} = d_i B_{ij}`. -/
theorem K_transpose_eq_D_mul_B (i j : Fin d) :
    (S.K j i : ℝ) = (S.D i : ℝ) * (S.B i j : ℝ) := by
  have hq : S.K j i = -S.K i j := S.K_skew j i
  rw [hq, Rat.cast_neg, K_eq_neg_D_mul_B S i j]
  ring

theorem K_transpose_eq_D_mul_B_complex (i j : Fin d) :
    (S.K j i : ℂ) = (S.D i : ℂ) * (S.B i j : ℂ) := by
  have hq : S.K j i = -S.K i j := S.K_skew j i
  rw [hq, Rat.cast_neg, K_eq_neg_D_mul_B_complex S i j]
  ring

/-- The matrix form of `K_eq_neg_D_mul_B`: `K = -(diag d) · B`. -/
theorem Kreal_eq_neg_diagonal_mul_Breal :
    Kreal S = -((Matrix.diagonal fun i => (S.D i : ℝ)) * Breal S) := by
  ext i j
  simp only [Kreal_apply, Matrix.neg_apply, Matrix.diagonal_mul, Breal_apply]
  rw [K_eq_neg_D_mul_B S i j]
  ring

theorem Kcomplex_eq_neg_diagonal_mul_Bcomplex :
    Kcomplex S = -((Matrix.diagonal fun i => (S.D i : ℂ)) * Bcomplex S) := by
  ext i j
  simp only [Kcomplex_apply, Matrix.neg_apply, Matrix.diagonal_mul, Bcomplex_apply]
  rw [K_eq_neg_D_mul_B_complex S i j]
  ring

/-- The row identity `∑_l K_{il} θ_l = -d_i ∑_l B_{il} θ_l`, i.e. `K θ = -d η`:
this is the second half of the blueprint's torus split identity
`eq:acyclic-ltor-split`, with `θ_l = arg z_l` and `η_i = c_i(θ)`. -/
theorem sum_K_row (x : Fin d → ℝ) (i : Fin d) :
    ∑ j, (S.K i j : ℝ) * x j = -(S.D i : ℝ) * ∑ j, (S.B i j : ℝ) * x j := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [K_eq_neg_D_mul_B S i j]
  ring

theorem sum_K_row_complex (x : Fin d → ℂ) (i : Fin d) :
    ∑ j, (S.K i j : ℂ) * x j = -(S.D i : ℂ) * ∑ j, (S.B i j : ℂ) * x j := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [K_eq_neg_D_mul_B_complex S i j]
  ring

/-- The column identity `∑_j K_{ji} u_j = d_i ∑_j B_{ij} u_j = d_i v_i`, i.e.
`Kᵀ u = d v`: the first half of `eq:acyclic-ltor-split`, with `u_j = log‖z_j‖`
and `v_i = c_i(u)`. -/
theorem sum_K_col (u : Fin d → ℝ) (i : Fin d) :
    ∑ j, (S.K j i : ℝ) * u j = (S.D i : ℝ) * ∑ j, (S.B i j : ℝ) * u j := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [K_transpose_eq_D_mul_B S i j]
  ring

theorem sum_K_col_complex (u : Fin d → ℂ) (i : Fin d) :
    ∑ j, (S.K j i : ℂ) * u j = (S.D i : ℂ) * ∑ j, (S.B i j : ℂ) * u j := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [K_transpose_eq_D_mul_B_complex S i j]
  ring

/-- `K e_i = d_i c_i`, where `c_i` is the `i`-th column of `E`, i.e. the `i`-th
row of the exponent matrix. -/
theorem K_mulVec_single (i : Fin d) :
    (Kreal S).mulVec (Pi.single i 1) = fun j => (S.D i : ℝ) * (S.B i j : ℝ) := by
  funext j
  have h : (Kreal S).mulVec (Pi.single i 1) j = (S.K j i : ℝ) := by
    simp [Matrix.mulVec]
  rw [h, K_transpose_eq_D_mul_B S i j]

theorem K_mulVec_single_complex (i : Fin d) :
    (Kcomplex S).mulVec (Pi.single i 1) = fun j => (S.D i : ℂ) * (S.B i j : ℂ) := by
  funext j
  have h : (Kcomplex S).mulVec (Pi.single i 1) j = (S.K j i : ℂ) := by
    simp [Matrix.mulVec]
  rw [h, K_transpose_eq_D_mul_B_complex S i j]

/-- The bilinear antisymmetry of the weighted form. -/
theorem sum_sum_K_antisymm (v w : Fin d → ℝ) :
    ∑ i, ∑ j, (S.K i j : ℝ) * v i * w j
      = -∑ i, ∑ j, (S.K i j : ℝ) * w i * v j := by
  have hswap : ∑ i, ∑ j, (S.K i j : ℝ) * w i * v j
      = ∑ i, ∑ j, (S.K j i : ℝ) * w j * v i := Finset.sum_comm
  have hneg : ∑ i, ∑ j, (S.K j i : ℝ) * w j * v i
      = -∑ i, ∑ j, (S.K i j : ℝ) * v i * w j := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hq : S.K j i = -S.K i j := S.K_skew j i
    rw [hq, Rat.cast_neg]
    ring
  rw [hswap, hneg, neg_neg]

theorem sum_sum_K_antisymm_complex (v w : Fin d → ℂ) :
    ∑ i, ∑ j, (S.K i j : ℂ) * v i * w j
      = -∑ i, ∑ j, (S.K i j : ℂ) * w i * v j := by
  have hswap : ∑ i, ∑ j, (S.K i j : ℂ) * w i * v j
      = ∑ i, ∑ j, (S.K j i : ℂ) * w j * v i := Finset.sum_comm
  have hneg : ∑ i, ∑ j, (S.K j i : ℂ) * w j * v i
      = -∑ i, ∑ j, (S.K i j : ℂ) * v i * w j := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hq : S.K j i = -S.K i j := S.K_skew j i
    rw [hq, Rat.cast_neg]
    ring
  rw [hswap, hneg, neg_neg]

/-- The `K`-system is the `B`-system up to the weights: `K y = b` holds exactly
when `B y = -b / d` entrywise. This is the conversion a baseline proof that
inverted the integer matrix uses to keep its shape. -/
theorem Kreal_mulVec_eq_iff (y b : Fin d → ℝ) :
    (Kreal S).mulVec y = b ↔ (Breal S).mulVec y = fun i => -(b i) / (S.D i : ℝ) := by
  have hrow (i : Fin d) :
      (Kreal S).mulVec y i = -(S.D i : ℝ) * (Breal S).mulVec y i := by
    rw [Kreal_mulVec_apply, Breal_mulVec_apply]
    exact sum_K_row S y i
  have hD (i : Fin d) : ((S.D i : ℚ) : ℝ) ≠ 0 := by
    have := S.D_pos i
    exact_mod_cast this.ne'
  constructor
  · intro h
    funext i
    have h0 := hD i
    have hi : -(S.D i : ℝ) * (Breal S).mulVec y i = b i := by
      rw [← hrow i, h]
    rw [← hi]
    field_simp
  · intro h
    funext i
    have h0 := hD i
    have hi : (Breal S).mulVec y i = -(b i) / (S.D i : ℝ) := by rw [h]
    rw [hrow i, hi]
    field_simp

theorem Kcomplex_mulVec_eq_iff (y b : Fin d → ℂ) :
    (Kcomplex S).mulVec y = b ↔
      (Bcomplex S).mulVec y = fun i => -(b i) / (S.D i : ℂ) := by
  have hrow (i : Fin d) :
      (Kcomplex S).mulVec y i = -(S.D i : ℂ) * (Bcomplex S).mulVec y i := by
    rw [Kcomplex_mulVec_apply, Bcomplex_mulVec_apply]
    exact sum_K_row_complex S y i
  have hD (i : Fin d) : ((S.D i : ℚ) : ℂ) ≠ 0 := by
    have := S.D_pos i
    have h : ((S.D i : ℚ) : ℝ) ≠ 0 := by exact_mod_cast this.ne'
    simpa using h
  constructor
  · intro h
    funext i
    have h0 := hD i
    have hi : -(S.D i : ℂ) * (Bcomplex S).mulVec y i = b i := by
      rw [← hrow i, h]
    rw [← hi]
    field_simp
  · intro h
    funext i
    have h0 := hD i
    have hi : (Bcomplex S).mulVec y i = -(b i) / (S.D i : ℂ) := by rw [h]
    rw [hrow i, hi]
    field_simp

/-! ### The inverse of the weighted form matrix -/

theorem Kreal_mul_inv (hdet : S.Unimodular) : Kreal S * (Kreal S)⁻¹ = 1 :=
  Matrix.mul_nonsing_inv _ (isUnit_det_Kreal S hdet)

theorem Kreal_inv_mul (hdet : S.Unimodular) : (Kreal S)⁻¹ * Kreal S = 1 :=
  Matrix.nonsing_inv_mul _ (isUnit_det_Kreal S hdet)

theorem Kcomplex_mul_inv (hdet : S.Unimodular) : Kcomplex S * (Kcomplex S)⁻¹ = 1 :=
  Matrix.mul_nonsing_inv _ (isUnit_det_Kcomplex S hdet)

theorem Kcomplex_inv_mul (hdet : S.Unimodular) : (Kcomplex S)⁻¹ * Kcomplex S = 1 :=
  Matrix.nonsing_inv_mul _ (isUnit_det_Kcomplex S hdet)

/-- `K⁻¹ (K x) = x`. -/
theorem Kreal_inv_mulVec (hdet : S.Unimodular) (x : Fin d → ℝ) :
    (Kreal S)⁻¹.mulVec ((Kreal S).mulVec x) = x := by
  rw [Matrix.mulVec_mulVec, Kreal_inv_mul S hdet, Matrix.one_mulVec]

/-- `K (K⁻¹ x) = x`: the solution of the angular system `K θ̇ = -∂_u H`. -/
theorem Kreal_mulVec_inv (hdet : S.Unimodular) (x : Fin d → ℝ) :
    (Kreal S).mulVec ((Kreal S)⁻¹.mulVec x) = x := by
  rw [Matrix.mulVec_mulVec, Kreal_mul_inv S hdet, Matrix.one_mulVec]

theorem Kcomplex_inv_mulVec (hdet : S.Unimodular) (x : Fin d → ℂ) :
    (Kcomplex S)⁻¹.mulVec ((Kcomplex S).mulVec x) = x := by
  rw [Matrix.mulVec_mulVec, Kcomplex_inv_mul S hdet, Matrix.one_mulVec]

theorem Kcomplex_mulVec_inv (hdet : S.Unimodular) (x : Fin d → ℂ) :
    (Kcomplex S).mulVec ((Kcomplex S)⁻¹.mulVec x) = x := by
  rw [Matrix.mulVec_mulVec, Kcomplex_mul_inv S hdet, Matrix.one_mulVec]

/-- Multiplication by the weighted form matrix is injective on column vectors. -/
theorem Kreal_mulVec_injective (hdet : S.Unimodular) :
    Function.Injective (Kreal S).mulVec :=
  Matrix.mulVec_injective_iff_isUnit.2
    ((Matrix.isUnit_iff_isUnit_det _).2 (isUnit_det_Kreal S hdet))

/-- Multiplication by the weighted form matrix is injective on row vectors. This
is the cancellation that replaces the baseline `det B = 1` cancellation in the
radial matrix equation. -/
theorem Kreal_vecMul_injective (hdet : S.Unimodular) :
    Function.Injective (Kreal S).vecMul :=
  Matrix.vecMul_injective_iff_isUnit.2
    ((Matrix.isUnit_iff_isUnit_det _).2 (isUnit_det_Kreal S hdet))

/-- Recovering the solution of a `K`-system from the inverse. -/
theorem eq_inv_mulVec_of_Kreal_mulVec (hdet : S.Unimodular) {y b : Fin d → ℝ}
    (h : (Kreal S).mulVec y = b) : y = (Kreal S)⁻¹.mulVec b := by
  rw [← h, Matrix.mulVec_mulVec, Kreal_inv_mul S hdet, Matrix.one_mulVec]

/-- `c_iᵀ K⁻¹ = -e_iᵀ / d_i`, the row form of the blueprint's inverse identity. -/
theorem vecMul_Ecol_inv_Kreal (hdet : S.Unimodular) (i : Fin d) :
    Matrix.vecMul (fun j => (S.E j i : ℝ)) (Kreal S)⁻¹
      = -((S.D i : ℝ)⁻¹) • Pi.single i (1 : ℝ) := by
  rw [Kreal_eq_symmetrizerK]
  exact SymmetrizerAlgebra.vecMul_E_col_inv_K ℝ S.D_pos S.skewSymmetrizable hdet i

theorem vecMul_Ecol_inv_Kcomplex (hdet : S.Unimodular) (i : Fin d) :
    Matrix.vecMul (fun j => (S.E j i : ℂ)) (Kcomplex S)⁻¹
      = -((S.D i : ℂ)⁻¹) • Pi.single i (1 : ℂ) := by
  rw [Kcomplex_eq_symmetrizerK]
  exact SymmetrizerAlgebra.vecMul_E_col_inv_K ℂ S.D_pos S.skewSymmetrizable hdet i

/-- **The inverse identity** `c_i(K⁻¹ x) = -x_i / d_i` of the blueprint, stated in
the column orientation `c_i = E e_i`. -/
theorem c_inv_K (hdet : S.Unimodular) (i : Fin d) (x : Fin d → ℝ) :
    ∑ j, (S.E j i : ℝ) * ((Kreal S)⁻¹.mulVec x) j = -(x i) / (S.D i : ℝ) := by
  rw [Kreal_eq_symmetrizerK]
  exact SymmetrizerAlgebra.sum_E_col_mul_inv_mulVec ℝ S.D_pos S.skewSymmetrizable hdet i x

theorem c_inv_K_complex (hdet : S.Unimodular) (i : Fin d) (x : Fin d → ℂ) :
    ∑ j, (S.E j i : ℂ) * ((Kcomplex S)⁻¹.mulVec x) j = -(x i) / (S.D i : ℂ) := by
  rw [Kcomplex_eq_symmetrizerK]
  exact SymmetrizerAlgebra.sum_E_col_mul_inv_mulVec ℂ S.D_pos S.skewSymmetrizable hdet i x

/-- `c_inv_K` in the exponent orientation: `B (K⁻¹ x) = -x / d`. This is the form
the dynamics modules consume, because `(Breal S).mulVec` is literally the
blueprint's `c(·)`. -/
theorem Breal_mulVec_inv_K (hdet : S.Unimodular) (x : Fin d → ℝ) :
    (Breal S).mulVec ((Kreal S)⁻¹.mulVec x) = fun i => -(x i) / (S.D i : ℝ) := by
  funext i
  rw [Breal_mulVec_apply_E]
  exact c_inv_K S hdet i x

theorem Bcomplex_mulVec_inv_K (hdet : S.Unimodular) (x : Fin d → ℂ) :
    (Bcomplex S).mulVec ((Kcomplex S)⁻¹.mulVec x) = fun i => -(x i) / (S.D i : ℂ) := by
  funext i
  rw [Bcomplex_mulVec_apply_E]
  exact c_inv_K_complex S hdet i x

/-! ### The one-norm inverse bounds -/

/-- A fixed inverse gives a uniform one-norm bound on the solutions of a square
real linear system. This is the seed-free core of
`TorusLiouvilleDynamics.full_matrix_inverse_bound`; in particular it discards no
columns and does not require `0 < d`. -/
theorem exists_inverse_bound_of_isUnit {n : ℕ} (R : Matrix (Fin n) (Fin n) ℝ)
    (hu : IsUnit R.det) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y b : Fin n → ℝ, R.mulVec y = b →
      (∑ j, |y j|) ≤ C * ∑ j, |b j| := by
  classical
  set C : ℝ := ∑ i : Fin n, ∑ j : Fin n, |R⁻¹ i j| with hCdef
  have hC : 0 ≤ C :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => abs_nonneg _
  refine ⟨C, hC, fun y b he => ?_⟩
  have hy : y = R⁻¹.mulVec b := by
    rw [← he, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul R hu, Matrix.one_mulVec]
  rw [hy]
  calc
    (∑ i : Fin n, |R⁻¹.mulVec b i|) ≤
        ∑ i : Fin n, ∑ j : Fin n, |R⁻¹ i j| * |b j| := by
      refine Finset.sum_le_sum fun i _ => ?_
      simpa only [Matrix.mulVec, dotProduct, abs_mul] using
        (Finset.abs_sum_le_sum_abs (s := Finset.univ) (f := fun j => R⁻¹ i j * b j))
    _ ≤ ∑ i : Fin n, ∑ j : Fin n, |R⁻¹ i j| * (∑ k : Fin n, |b k|) := by
      refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
      exact mul_le_mul_of_nonneg_left
        (Finset.single_le_sum (fun k _ => abs_nonneg (b k)) (Finset.mem_univ j)) (abs_nonneg _)
    _ = C * ∑ j : Fin n, |b j| := by simp [hCdef, Finset.sum_mul]

/-- The baseline integer bound, lifted to the seed level: a solution of the
`B`-system has one-norm controlled by the one-norm of the right-hand side. This
is `TorusLiouvilleDynamics.full_matrix_inverse_bound` in `Seed` form, proved once
so that the weighted dynamics can reuse it. -/
theorem exists_inverse_bound_Breal (hdet : S.Unimodular) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y b : Fin d → ℝ,
      (∀ i, ∑ j, (S.B i j : ℝ) * y j = b i) → (∑ j, |y j|) ≤ C * ∑ j, |b j| := by
  obtain ⟨C, hC, hbound⟩ :=
    exists_inverse_bound_of_isUnit (Breal S) (isUnit_det_Breal S hdet)
  refine ⟨C, hC, fun y b hyb => hbound y b ?_⟩
  funext i
  rw [Breal_mulVec_apply]
  exact hyb i

/-- The weighted analogue of `exists_inverse_bound_Breal` for the `K`-system. -/
theorem exists_inverse_bound_Kreal (hdet : S.Unimodular) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y b : Fin d → ℝ,
      (∀ i, ∑ j, (S.K i j : ℝ) * y j = b i) → (∑ j, |y j|) ≤ C * ∑ j, |b j| := by
  obtain ⟨C, hC, hbound⟩ :=
    exists_inverse_bound_of_isUnit (Kreal S) (isUnit_det_Kreal S hdet)
  refine ⟨C, hC, fun y b hyb => hbound y b ?_⟩
  funext i
  rw [Kreal_mulVec_apply]
  exact hyb i

end ClusterSkeleton.SeedAlgebra
