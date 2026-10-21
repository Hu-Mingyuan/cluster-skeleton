import ClusterSkeleton.CoordinateLoci
import Mathlib.Topology.Homeomorph.Defs
import Mathlib.Topology.Algebra.GroupWithZero
import Mathlib.Tactic.FunProp

/-!
# The actual initial torus chart

The chart and its inverse use the original coordinates. The inverse reconstructs
all mutable partners from the exchange equations. No smooth structure or torus
identification is assumed.
-/

namespace ClusterSkeleton

open scoped BigOperators

variable {d : ℕ}

/-- The product of punctured complex coordinate lines with its native topology. -/
abbrev CoordinateTorus (d : ℕ) := Fin d → {z : ℂ // z ≠ 0}

/-- Forget the nonvanishing proofs in a coordinate torus point. -/
def torusCoordinates (a : CoordinateTorus d) : Fin d → ℂ := fun j => (a j).val

theorem continuous_torusCoordinates :
    Continuous (torusCoordinates : CoordinateTorus d → (Fin d → ℂ)) :=
  continuous_pi fun j => continuous_subtype_val.comp (continuous_apply j)

theorem continuous_positiveMonomial (S : Seed d) (i : Fin d) :
    Continuous (fun a : Fin d → ℂ => S.positiveMonomial a i) := by
  unfold Seed.positiveMonomial
  fun_prop

theorem continuous_negativeMonomial (S : Seed d) (i : Fin d) :
    Continuous (fun a : Fin d → ℂ => S.negativeMonomial a i) := by
  unfold Seed.negativeMonomial
  fun_prop

/-- Reconstruct the actual exchange point from its nonzero original coordinates. -/
noncomputable def pointOfCoordinateTorus (S : Seed d) (a : CoordinateTorus d) : S.Point :=
  ⟨(torusCoordinates a, fun i =>
      (S.positiveMonomial (torusCoordinates a) i +
       S.negativeMonomial (torusCoordinates a) i) / (a i).val), by
    constructor
    · intro i
      exact mul_div_cancel₀ _ (a i).property
    · intro f _
      exact (a f).property⟩

@[simp] theorem pointOfCoordinateTorus_a (S : Seed d) (a : CoordinateTorus d)
    (j : Fin d) : (pointOfCoordinateTorus S a).a j = (a j).val := rfl

@[simp] theorem pointOfCoordinateTorus_b (S : Seed d) (a : CoordinateTorus d)
    (i : S.Mutable) : (pointOfCoordinateTorus S a).b i =
      (S.positiveMonomial (torusCoordinates a) i +
       S.negativeMonomial (torusCoordinates a) i) / (a i).val := rfl

theorem pointOfCoordinateTorus_mem (S : Seed d) (a : CoordinateTorus d) :
    pointOfCoordinateTorus S a ∈ initialTorus S := fun j => (a j).property

theorem continuous_pointOfCoordinateTorus (S : Seed d) :
    Continuous (pointOfCoordinateTorus S) := by
  apply Continuous.subtype_mk
  apply Continuous.prodMk continuous_torusCoordinates
  apply continuous_pi
  intro i
  exact (((continuous_positiveMonomial S i).comp continuous_torusCoordinates).add
    ((continuous_negativeMonomial S i).comp continuous_torusCoordinates)).div
    (continuous_subtype_val.comp (continuous_apply (i : Fin d))) (fun a => (a i).property)

/-- The actual initial torus is homeomorphic to the product of punctured lines.
Its inverse is the explicit rational reconstruction of the mutation partners. -/
noncomputable def initialTorusHomeomorph (S : Seed d) :
    ↥(initialTorus S) ≃ₜ CoordinateTorus d where
  toFun p := fun j => ⟨p.val.a j, p.property j⟩
  invFun a := ⟨pointOfCoordinateTorus S a, pointOfCoordinateTorus_mem S a⟩
  left_inv p := by
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · funext i
      change (S.positiveMonomial p.val.a i + S.negativeMonomial p.val.a i) /
        p.val.a i = p.val.b i
      rw [← p.val.exchange i]
      exact mul_div_cancel_left₀ _ (p.property i)
  right_inv a := by
    funext j
    apply Subtype.ext
    rfl
  continuous_toFun := by
    apply continuous_pi
    intro j
    exact ((continuous_originalCoordinate S j).comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (continuous_pointOfCoordinateTorus S).subtype_mk _

end ClusterSkeleton
