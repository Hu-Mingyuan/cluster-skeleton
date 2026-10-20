import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Order.WellFoundedSet

/-!
# The actual affine acyclic cluster model

The data and exchange equations are those of Section 2 of
`acyclic_cluster_HMS.pdf`. Frozen coordinates remain variable and nonzero.
Unimodularity is a separate hypothesis: zero-set independence does not need it.
-/

open scoped BigOperators

namespace ClusterSkeleton

/-- An integral skew-symmetric exchange matrix with an acyclic mutable quiver.
The arrow convention is `B i j > 0` for an arrow from `i` to `j`.
On the finite mutable type, well-foundedness is equivalent to no directed cycles.
-/
structure Seed (d : ℕ) where
  B : Matrix (Fin d) (Fin d) ℤ
  mutable : Finset (Fin d)
  skew : ∀ i j, B i j = -B j i
  acyclic : WellFounded (fun i j : {i // i ∈ mutable} => 0 < B i j)

namespace Seed

variable {d : ℕ} (S : Seed d)

/-- The mutable vertices. All remaining vertices are frozen. -/
abbrev Mutable := {i : Fin d // i ∈ S.mutable}

/-- Unimodularity of the whole exchange matrix, including frozen indices. -/
def Unimodular : Prop := S.B.det = 1

/-- The positive exchange monomial. A nonpositive exponent contributes `a j ^ 0 = 1`. -/
def positiveMonomial (a : Fin d → ℂ) (i : Fin d) : ℂ :=
  ∏ j, a j ^ (S.B i j).toNat

/-- The negative exchange monomial. A nonnegative matrix entry contributes `1`. -/
def negativeMonomial (a : Fin d → ℂ) (i : Fin d) : ℂ :=
  ∏ j, a j ^ (-S.B i j).toNat

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
      simp [positiveMonomial, negativeMonomial]
    · intro f _
      exact one_ne_zero⟩

@[simp] theorem unitPoint_a (j : Fin d) : S.unitPoint.a j = 1 := rfl

@[simp] theorem unitPoint_b (i : S.Mutable) : S.unitPoint.b i = 2 := rfl

theorem point_nonempty : Nonempty S.Point := ⟨S.unitPoint⟩

/-- Independence means no exchange-matrix entries between the chosen mutable vertices. -/
def Independent (I : Finset (Fin d)) : Prop :=
  I ⊆ S.mutable ∧ ∀ i ∈ I, ∀ j ∈ I, S.B i j = 0

/-- For a finite relation, well-foundedness exactly excludes nonempty directed cycles.
This connects the acyclicity field to the usual directed-graph convention. -/
theorem wellFounded_iff_no_directed_cycle {α : Type*} [Finite α]
    (r : α → α → Prop) :
    WellFounded r ↔ ∀ i, ¬ Relation.TransGen r i i := by
  constructor
  · intro h i hi
    exact h.transGen.irrefl.irrefl i hi
  · intro h
    letI : IsStrictOrder α (Relation.TransGen r) :=
      { irrefl := h, trans := fun _ _ _ => Relation.TransGen.trans }
    have hw : WellFounded (Relation.TransGen r) :=
      Set.wellFoundedOn_univ.mp Set.finite_univ.wellFoundedOn
    exact hw.mono (fun _ _ hi => Relation.TransGen.single hi)

end Seed
end ClusterSkeleton
