import ClusterSkeleton.Seed
import Mathlib.Topology.Homeomorph.Defs

/-!
# The old skew-symmetric seed and its weighted reading

`SkewSeed` is the structure of the accepted `D = I` library, verbatim: an
integral skew-symmetric matrix `B` with an acyclic mutable quiver, and exchange
monomials written with the **rows** of `B`.

## The convention choice of `toSeed`

`SkewSeed.toSeed` uses `E := B` and `D := 1` (not `E := Bᵀ`). Consequently

* the weighted form matrix is `K i j = E i j * D j = B i j`, i.e.
  **`K = B` with no sign change**: the logarithmic two-form of the weighted
  library, whose coefficient is `K`, is literally the old form, not its
  negative. The Liouville primitive, field, flow and the forward-orbit
  skeleton identity therefore transport without a time reversal.
* the two exchange monomials are **interchanged**:
  `toSeed.positiveMonomial = SkewSeed.negativeMonomial` and
  `toSeed.negativeMonomial = SkewSeed.positiveMonomial`
  (`toSeed_positiveMonomial`, `toSeed_negativeMonomial`), because
  `[B j i]_+ = [-B i j]_+` by skew symmetry. Their sum is unchanged, so the two
  carriers are the same subset of the ambient coordinate space
  (`carrier_set_eq`) and the canonical identity map is a homeomorphism
  (`pointHomeomorph`).

The alternative choice `E := Bᵀ` would make the monomials definitionally equal
but give `K = -B`, flipping the sign of the two-form and hence reversing the
Liouville flow; the forward-orbit skeleton is not invariant under a time
reversal, so that choice would not recover the old theorem. This is why the
carrier identification above is proved instead.
-/

open scoped BigOperators

namespace ClusterSkeleton

/-- An integral skew-symmetric exchange matrix with an acyclic mutable quiver.
The arrow convention is `B i j > 0` for an arrow from `i` to `j`.
On the finite mutable type, well-foundedness is equivalent to no directed cycles.
This is the structure of the accepted skew-symmetric library, unchanged. -/
structure SkewSeed (d : ℕ) where
  B : Matrix (Fin d) (Fin d) ℤ
  mutable : Finset (Fin d)
  skew : ∀ i j, B i j = -B j i
  acyclic : WellFounded (fun i j : {i // i ∈ mutable} => 0 < B i j)

namespace SkewSeed

variable {d : ℕ} (S : SkewSeed d)

/-- The mutable vertices. All remaining vertices are frozen. -/
abbrev Mutable := {i : Fin d // i ∈ S.mutable}

/-- Unimodularity of the whole exchange matrix, including frozen indices. -/
def Unimodular : Prop := S.B.det = 1

/-- The positive exchange monomial of the old library, with **row** exponents. -/
def positiveMonomial (a : Fin d → ℂ) (i : Fin d) : ℂ :=
  ∏ j, a j ^ (S.B i j).toNat

/-- The negative exchange monomial of the old library, with **row** exponents. -/
def negativeMonomial (a : Fin d → ℂ) (i : Fin d) : ℂ :=
  ∏ j, a j ^ (-S.B i j).toNat

/-- The old library's exchange-equation point set. -/
abbrev Point :=
  {x : (Fin d → ℂ) × (S.Mutable → ℂ) //
    (∀ i : S.Mutable,
      x.1 i * x.2 i = S.positiveMonomial x.1 i + S.negativeMonomial x.1 i) ∧
    (∀ f, f ∉ S.mutable → x.1 f ≠ 0)}

/-- The old independence condition. -/
def Independent (I : Finset (Fin d)) : Prop :=
  I ⊆ S.mutable ∧ ∀ i ∈ I, ∀ j ∈ I, S.B i j = 0

/-- Every skew-symmetric seed is a weighted seed with the trivial symmetrizer.
The exchange matrix is retained as `E := B`, so `K = B` **with no sign change**
and the two exchange monomials are interchanged; see the module docstring. -/
def toSeed : Seed d where
  E := S.B
  mutable := S.mutable
  D := fun _ => 1
  D_pos := fun _ => one_pos
  skewSymmetrizable := by
    intro i j
    rw [S.skew i j]
    push_cast
    ring
  acyclic := S.acyclic

@[simp] theorem toSeed_E : (S.toSeed).E = S.B := rfl

@[simp] theorem toSeed_mutable : (S.toSeed).mutable = S.mutable := rfl

@[simp] theorem toSeed_D (i : Fin d) : (S.toSeed).D i = 1 := rfl

/-- The weighted form matrix of the image seed is the old exchange matrix
itself: `K = B`, with no sign change and no transpose. -/
@[simp] theorem toSeed_K (i j : Fin d) : (S.toSeed).K i j = (S.B i j : ℚ) := by
  simp [Seed.K]

/-- Unimodularity is the same condition for both readings. -/
theorem toSeed_unimodular_iff : (S.toSeed).Unimodular ↔ S.Unimodular := Iff.rfl

/-- Independence is the same condition for both readings. -/
theorem toSeed_independent_iff (I : Finset (Fin d)) :
    (S.toSeed).Independent I ↔ S.Independent I := Iff.rfl

/-- Column exponents of `E = B` are the negated row exponents, by skew symmetry. -/
theorem toSeed_positiveMonomial (a : Fin d → ℂ) (i : Fin d) :
    (S.toSeed).positiveMonomial a i = S.negativeMonomial a i := by
  unfold Seed.positiveMonomial SkewSeed.negativeMonomial
  simp only [toSeed_E]
  refine Finset.prod_congr rfl fun j _ => ?_
  have h : -S.B i j = S.B j i := by rw [S.skew i j]; ring
  rw [h]

theorem toSeed_negativeMonomial (a : Fin d → ℂ) (i : Fin d) :
    (S.toSeed).negativeMonomial a i = S.positiveMonomial a i := by
  unfold Seed.negativeMonomial SkewSeed.positiveMonomial
  simp only [toSeed_E]
  refine Finset.prod_congr rfl fun j _ => ?_
  have h : S.B i j = -S.B j i := S.skew i j
  rw [h]

/-- The two monomials are interchanged, so their sum — the only thing the
exchange equation uses — is unchanged. -/
theorem toSeed_monomial_sum (a : Fin d → ℂ) (i : Fin d) :
    (S.toSeed).positiveMonomial a i + (S.toSeed).negativeMonomial a i =
      S.positiveMonomial a i + S.negativeMonomial a i := by
  rw [toSeed_positiveMonomial, toSeed_negativeMonomial, add_comm]

/-- The defining predicates of the two carriers agree at every ambient point. -/
theorem carrier_predicate_iff (x : (Fin d → ℂ) × (S.Mutable → ℂ)) :
    ((∀ i : S.Mutable,
        x.1 i * x.2 i = S.positiveMonomial x.1 i + S.negativeMonomial x.1 i) ∧
      (∀ f, f ∉ S.mutable → x.1 f ≠ 0)) ↔
    ((∀ i : (S.toSeed).Mutable,
        x.1 i * x.2 i =
          (S.toSeed).positiveMonomial x.1 i + (S.toSeed).negativeMonomial x.1 i) ∧
      (∀ f, f ∉ (S.toSeed).mutable → x.1 f ≠ 0)) := by
  constructor
  · exact fun h => ⟨fun i => (h.1 i).trans (toSeed_monomial_sum S x.1 i).symm, h.2⟩
  · exact fun h => ⟨fun i => (h.1 i).trans (toSeed_monomial_sum S x.1 i), h.2⟩

/-- The two carriers are literally the same subset of the ambient coordinate
space: the exchange monomials are interchanged and their sum is preserved. -/
theorem carrier_set_eq :
    {x : (Fin d → ℂ) × (S.Mutable → ℂ) |
        (∀ i : S.Mutable,
          x.1 i * x.2 i = S.positiveMonomial x.1 i + S.negativeMonomial x.1 i) ∧
        (∀ f, f ∉ S.mutable → x.1 f ≠ 0)} =
      {x : (Fin d → ℂ) × (S.Mutable → ℂ) |
        (∀ i : (S.toSeed).Mutable,
          x.1 i * x.2 i =
            (S.toSeed).positiveMonomial x.1 i + (S.toSeed).negativeMonomial x.1 i) ∧
        (∀ f, f ∉ (S.toSeed).mutable → x.1 f ≠ 0)} :=
  Set.ext fun x => carrier_predicate_iff S x

/-- The canonical identity map on ambient coordinates is a homeomorphism from the
old carrier to the weighted carrier. All coordinates, and hence the initial
torus, the coordinate cap and every forward orbit, are preserved. -/
def pointHomeomorph : S.Point ≃ₜ (S.toSeed).Point where
  toFun p := ⟨p.val, (carrier_predicate_iff S p.val).mp p.property⟩
  invFun p := ⟨p.val, (carrier_predicate_iff S p.val).mpr p.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := continuous_subtype_val.subtype_mk _
  continuous_invFun := continuous_subtype_val.subtype_mk _

@[simp] theorem pointHomeomorph_val (p : S.Point) :
    (pointHomeomorph S p).val = p.val := rfl

@[simp] theorem pointHomeomorph_symm_val (p : (S.toSeed).Point) :
    ((pointHomeomorph S).symm p).val = p.val := rfl

end SkewSeed
end ClusterSkeleton
