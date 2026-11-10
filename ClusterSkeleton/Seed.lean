import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.Order.WellFoundedSet

/-!
# The actual affine acyclic cluster model, skew-symmetrizable case

The data and exchange equations are those of Section 1 of
`target-theorem.pdf`: an integral matrix `E`, a mutable set with acyclic
mutable block, and a positive rational diagonal `D` such that `K = E * D` is
skew-symmetric. `E` itself is **not** assumed skew-symmetric and `D` is **not**
assumed to be the identity. Frozen coordinates remain variable and nonzero.
Unimodularity is a separate hypothesis: zero-set independence does not need it.

The exchange monomials use **column** exponents, `P_i^± = ∏_j z_j^{[±E_ji]_+}`.
The abbreviation `S.B := S.Eᵀ` names the exponent matrix, so that `S.B i j` is
by definition the column exponent `S.E j i`; it is a notational convenience and
carries no skew-symmetry.
-/

open scoped BigOperators Matrix

namespace ClusterSkeleton

/-- An integral exchange matrix with an acyclic mutable quiver, together with a
positive rational symmetrizer. The arrow convention is `E i j > 0` for an arrow
from `i` to `j`, and `K = E * D` is skew-symmetric, i.e. `E i j * D j =
-(E j i * D i)`. On the finite mutable type, well-foundedness is equivalent to
no directed cycles. -/
structure Seed (d : ℕ) where
  /-- The integral exchange matrix; it is in general not skew-symmetric. -/
  E : Matrix (Fin d) (Fin d) ℤ
  /-- The mutable vertices. -/
  mutable : Finset (Fin d)
  /-- The diagonal symmetrizer, with arbitrary positive rational entries. -/
  D : Fin d → ℚ
  /-- All symmetrizer weights are positive; no two of them need agree. -/
  D_pos : ∀ i, 0 < D i
  /-- `K = E * D` is skew-symmetric. -/
  skewSymmetrizable : ∀ i j, (E i j : ℚ) * D j = -((E j i : ℚ) * D i)
  /-- The mutable block has no directed cycle. -/
  acyclic : WellFounded (fun i j : {i // i ∈ mutable} => 0 < E i j)

namespace Seed

variable {d : ℕ} (S : Seed d)

/-- The mutable vertices. All remaining vertices are frozen. -/
abbrev Mutable := {i : Fin d // i ∈ S.mutable}

/-- Unimodularity of the whole exchange matrix, including frozen indices. -/
def Unimodular : Prop := S.E.det = 1

/-- The exponent matrix of the exchange monomials: `Bexp i j` is the exponent of
the coordinate `j` in the monomials attached to the vertex `i`, i.e. the column
entry `E j i`. It is *not* skew-symmetric when `D ≠ 1`. -/
abbrev Bexp : Matrix (Fin d) (Fin d) ℤ := S.Eᵀ

/-- Short name for the exponent matrix `Bexp = Eᵀ`. By definition
`S.B i j = S.E j i`, so the exchange space is the column-convention space. -/
abbrev B : Matrix (Fin d) (Fin d) ℤ := S.Bexp

theorem B_apply (i j : Fin d) : S.B i j = S.E j i := rfl

theorem Bexp_apply (i j : Fin d) : S.Bexp i j = S.E j i := rfl

/-- The weighted form matrix `K = E * D`, with rational entries. -/
def K : Matrix (Fin d) (Fin d) ℚ := fun i j => (S.E i j : ℚ) * S.D j

@[simp] theorem K_apply (i j : Fin d) : S.K i j = (S.E i j : ℚ) * S.D j := rfl

theorem D_ne_zero (i : Fin d) : S.D i ≠ 0 := (S.D_pos i).ne'

/-- `K` is skew-symmetric; this is exactly the symmetrizability field. -/
theorem K_transpose : S.Kᵀ = -S.K := by
  ext i j
  simpa using S.skewSymmetrizable j i

theorem K_skew (i j : Fin d) : S.K i j = -S.K j i := by
  simpa using S.skewSymmetrizable i j

private theorem pos_of_mul_pos_right {a c : ℚ} (h : 0 < a * c) (hc : 0 < c) :
    0 < a := by
  have h' := div_pos h hc
  rwa [mul_div_assoc, div_self hc.ne', mul_one] at h'

private theorem eq_zero_of_mul_eq_zero_right {a c : ℚ} (h : a * c = 0)
    (hc : 0 < c) : a = 0 :=
  (mul_eq_zero.mp h).resolve_right hc.ne'

/-- The diagonal of the exchange matrix vanishes: no vertex has a loop.
This replaces the former use of `skew i i`. -/
@[simp] theorem E_diag_zero (i : Fin d) : S.E i i = 0 := by
  have h := S.skewSymmetrizable i i
  have h2 : ((S.E i i : ℚ)) * S.D i = 0 := by linarith
  have := eq_zero_of_mul_eq_zero_right h2 (S.D_pos i)
  exact_mod_cast this

/-- An arrow `i → j` is exactly a reverse arrow `j → i` with the opposite sign.
This replaces the former sign half of `skew`. -/
theorem E_neg_of_pos {i j : Fin d} (h : 0 < S.E i j) : S.E j i < 0 := by
  have hsym := S.skewSymmetrizable i j
  have hpos : (0 : ℚ) < (S.E i j : ℚ) * S.D j :=
    mul_pos (by exact_mod_cast h) (S.D_pos j)
  rw [hsym, neg_pos] at hpos
  have hneg : (0 : ℚ) < (-(S.E j i : ℚ)) * S.D i := by
    rw [neg_mul]; linarith
  have := pos_of_mul_pos_right hneg (S.D_pos i)
  have : (S.E j i : ℚ) < 0 := by linarith
  exact_mod_cast this

theorem E_pos_of_neg {i j : Fin d} (h : S.E j i < 0) : 0 < S.E i j := by
  have hsym := S.skewSymmetrizable i j
  have hneg : (S.E j i : ℚ) * S.D i < 0 := by
    have : (S.E j i : ℚ) < 0 := by exact_mod_cast h
    nlinarith [S.D_pos i]
  have hpos : (0 : ℚ) < (S.E i j : ℚ) * S.D j := by rw [hsym]; linarith
  have := pos_of_mul_pos_right hpos (S.D_pos j)
  exact_mod_cast this

/-- Sign opposition of the exchange matrix. -/
theorem E_pos_iff_neg (i j : Fin d) : 0 < S.E i j ↔ S.E j i < 0 :=
  ⟨fun h => S.E_neg_of_pos h, fun h => S.E_pos_of_neg h⟩

/-- Vanishing of the exchange matrix is a symmetric condition. -/
theorem E_eq_zero_iff (i j : Fin d) : S.E i j = 0 ↔ S.E j i = 0 := by
  have hforward : ∀ a b : Fin d, S.E a b = 0 → S.E b a = 0 := by
    intro a b h
    have hsym := S.skewSymmetrizable a b
    rw [h] at hsym
    have h2 : ((S.E b a : ℚ)) * S.D a = 0 := by
      push_cast at hsym
      linarith
    have := eq_zero_of_mul_eq_zero_right h2 (S.D_pos a)
    exact_mod_cast this
  exact ⟨hforward i j, hforward j i⟩

theorem E_ne_zero_iff (i j : Fin d) : S.E i j ≠ 0 ↔ S.E j i ≠ 0 :=
  not_congr (S.E_eq_zero_iff i j)

/-- The same three sign facts in the exponent orientation, where `S.B i j` is the
column exponent `S.E j i`. These are the forms used by the combinatorial proofs. -/
@[simp] theorem B_diag_zero (i : Fin d) : S.B i i = 0 := S.E_diag_zero i

theorem B_pos_iff_neg (i j : Fin d) : 0 < S.B i j ↔ S.B j i < 0 :=
  S.E_pos_iff_neg j i

theorem B_eq_zero_iff (i j : Fin d) : S.B i j = 0 ↔ S.B j i = 0 :=
  S.E_eq_zero_iff j i

/-- **The weighted node coefficient.** The form matrix in the exponent
orientation: `K i j = -(d i) * B i j`, i.e. `E i j * D j = -(D i) * E j i`. This
is the symmetrizability field read against the exponent matrix `B = Eᵀ`, and it
is the pointwise form of the reference identity
`∑_j K_ij dlog z_j = -d_i dlog t_i` (the `x_i` row of the weighted node form).
With `D = 1` it degenerates to `K = -B`. -/
theorem K_eq_neg_D_mul_B (i j : Fin d) : S.K i j = -(S.D i) * (S.B i j : ℚ) := by
  rw [K_apply, B_apply, S.skewSymmetrizable i j]
  ring

/-- The summed form of `K_eq_neg_D_mul_B`: the `i`-row of `K` is `-d_i` times
the `i`-row of the exponent matrix. -/
theorem sum_K_row_eq (i : Fin d) (x : Fin d → ℚ) :
    ∑ j, S.K i j * x j = -(S.D i) * ∑ j, (S.B i j : ℚ) * x j := by
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by rw [S.K_eq_neg_D_mul_B i j, mul_assoc]

/-- Both exponent orientations have the same determinant, so unimodularity of `E`
is unimodularity of the exponent matrix. -/
theorem B_det (hdet : S.Unimodular) : S.B.det = 1 := by
  rw [show S.B = S.Eᵀ from rfl, Matrix.det_transpose]
  exact hdet

theorem K_eq_map_mul_diagonal :
    S.K = (S.E.map (fun x : ℤ => (x : ℚ))) * Matrix.diagonal S.D := by
  ext i j
  simp [K, Matrix.mul_diagonal]

/-- The weighted determinant: `det K = det E * ∏ d_i`. -/
theorem det_K : S.K.det = (S.E.det : ℚ) * ∏ i, S.D i := by
  rw [K_eq_map_mul_diagonal, Matrix.det_mul, Matrix.det_diagonal, Int.cast_det]

/-- Under unimodularity the weighted form matrix is nonsingular, with
determinant the product of the weights. -/
theorem det_K_of_unimodular (hdet : S.Unimodular) :
    S.K.det = ∏ i, S.D i := by
  rw [det_K, show S.E.det = 1 from hdet, Int.cast_one, one_mul]

theorem det_K_ne_zero (hdet : S.Unimodular) : S.K.det ≠ 0 := by
  rw [det_K_of_unimodular S hdet]
  exact Finset.prod_ne_zero_iff.mpr fun i _ => S.D_ne_zero i

theorem isUnit_det_K (hdet : S.Unimodular) : IsUnit S.K.det :=
  (isUnit_iff_ne_zero).mpr (S.det_K_ne_zero hdet)

/-- The positive exchange monomial, with literal column exponents.
A nonpositive exponent contributes `a j ^ 0 = 1`. -/
def positiveMonomial (a : Fin d → ℂ) (i : Fin d) : ℂ :=
  ∏ j, a j ^ (S.E j i).toNat

/-- The negative exchange monomial, with literal column exponents.
A nonnegative column entry contributes `1`. -/
def negativeMonomial (a : Fin d → ℂ) (i : Fin d) : ℂ :=
  ∏ j, a j ^ (-S.E j i).toNat

theorem positiveMonomial_eq_prod_B (a : Fin d → ℂ) (i : Fin d) :
    S.positiveMonomial a i = ∏ j, a j ^ (S.B i j).toNat := rfl

theorem negativeMonomial_eq_prod_B (a : Fin d → ℂ) (i : Fin d) :
    S.negativeMonomial a i = ∏ j, a j ^ (-S.B i j).toNat := rfl

/-- The actual complex points of the exchange equations, with the inherited
subtype topology from the indicated complex coordinate space. -/
abbrev Point :=
  {x : (Fin d → ℂ) × (S.Mutable → ℂ) //
    (∀ i : S.Mutable,
      x.1 i * x.2 i = S.positiveMonomial x.1 i + S.negativeMonomial x.1 i) ∧
    (∀ f, f ∉ S.mutable → x.1 f ≠ 0)}

namespace Point

variable {S} (p : S.Point)

/-- Original coordinates, including variable frozen coordinates. -/
def a : Fin d → ℂ := p.1.1

/-- Mutation partners exist only for mutable vertices. -/
def b : S.Mutable → ℂ := p.1.2

theorem exchange (i : S.Mutable) :
    p.a i * p.b i = S.positiveMonomial p.a i + S.negativeMonomial p.a i :=
  p.2.1 i

theorem frozen_ne_zero (f : Fin d) (hf : f ∉ S.mutable) : p.a f ≠ 0 :=
  p.2.2 f hf

/-- The finite set of vanishing mutable coordinates. -/
noncomputable def zeroSet : Finset (Fin d) := by
  classical
  exact S.mutable.filter (fun i => p.a i = 0)

@[simp] theorem mem_zeroSet (i : Fin d) :
    i ∈ p.zeroSet ↔ i ∈ S.mutable ∧ p.a i = 0 := by
  classical
  simp [zeroSet]

end Point

/-- An actual point of every seed variety: original coordinates are `1`, and
all mutable partners are `2`. In particular the carrier cannot be vacuous. -/
def unitPoint : S.Point :=
  ⟨((fun _ => 1), (fun _ => 2)), by
    constructor
    · intro i
      simp [positiveMonomial, negativeMonomial, one_add_one_eq_two]
    · intro f _
      exact one_ne_zero⟩

@[simp] theorem unitPoint_a (j : Fin d) : S.unitPoint.a j = 1 := rfl

@[simp] theorem unitPoint_b (i : S.Mutable) : S.unitPoint.b i = 2 := rfl

theorem point_nonempty : Nonempty S.Point := ⟨S.unitPoint⟩

/-- Independence means no exchange-matrix entries between the chosen mutable vertices. -/
def Independent (I : Finset (Fin d)) : Prop :=
  I ⊆ S.mutable ∧ ∀ i ∈ I, ∀ j ∈ I, S.E i j = 0

variable {S} in
/-- Independence in the exponent orientation. Because `S.E i j = 0 ↔ S.E j i = 0`
this is the same condition; it is the form the monomial proofs use. -/
theorem Independent.exponent_eq_zero {I : Finset (Fin d)} (hI : S.Independent I)
    {i j : Fin d} (hi : i ∈ I) (hj : j ∈ I) : S.B i j = 0 :=
  hI.2 j hj i hi

/-- For a finite relation, well-foundedness exactly excludes nonempty directed cycles.
This connects the acyclicity field to the usual directed-graph convention. -/
theorem wellFounded_iff_no_directed_cycle {α : Type*} [Finite α]
    (r : α → α → Prop) :
    WellFounded r ↔ ∀ i, ¬ Relation.TransGen r i i := by
  constructor
  · intro h i hi
    exact h.transGen.irrefl.irrefl i hi
  · intro h
    let _ : IsStrictOrder α (Relation.TransGen r) :=
      { irrefl := h, trans := fun _ _ _ => Relation.TransGen.trans }
    have hw : WellFounded (Relation.TransGen r) :=
      Set.wellFoundedOn_univ.mp Set.finite_univ.wellFoundedOn
    exact hw.mono (fun _ _ hi => Relation.TransGen.single hi)

/-- Acyclicity in the exponent orientation: `0 < S.B i j` is `0 < S.E j i`.
Reversing a directed cycle produces a directed cycle, so on the finite mutable
type both orientations are well founded simultaneously. This is the induction
principle used by the zero-set and cap arguments. -/
theorem acyclic_exponent : WellFounded (fun i j : S.Mutable => 0 < S.B i j) := by
  classical
  have hno := (wellFounded_iff_no_directed_cycle
    (fun i j : S.Mutable => 0 < S.E i j)).mp S.acyclic
  refine (wellFounded_iff_no_directed_cycle _).mpr fun i hi => hno i ?_
  have hswap :
      Relation.TransGen (Function.swap (fun i j : S.Mutable => 0 < S.E i j)) i i := hi
  exact Relation.transGen_swap.mp hswap

end Seed
end ClusterSkeleton
