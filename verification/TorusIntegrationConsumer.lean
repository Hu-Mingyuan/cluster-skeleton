import ClusterSkeleton
import Lean.Util.CollectAxioms

noncomputable section
open ClusterSkeleton ClusterSkeleton.TorusNondegeneracy

namespace TorusNondegeneracyConsumer

-- This consumer supplies no presentation or tangent-coordinate assumption.
def coordinates {d : ℕ} (S : Seed d) (hdet : S.Unimodular)
    (p : S.Point) (hp : p ∈ initialTorus S) :
    (SmoothAtlas.presentation S hdet).manifold.Tangent p ≃L[ℝ] (Fin d → ℂ) :=
  smoothAtlas_logarithmicTangentEquiv S hdet p hp

theorem coordinate_formula {d : ℕ} (S : Seed d) (hdet : S.Unimodular)
    (p : S.Point) (hp : p ∈ initialTorus S)
    (v : (SmoothAtlas.presentation S hdet).manifold.Tangent p) (j : Fin d) :
    coordinates S hdet p hp v j =
      (SmoothAtlas.presentation S hdet).coordinateDifferential j p v / p.a j :=
  smoothAtlas_logarithmicTangentEquiv_apply S hdet p hp v j

theorem concrete {d : ℕ} (S : Seed d) (hdet : S.Unimodular)
    (p : S.Point) (hp : p ∈ initialTorus S)
    (v : (SmoothAtlas.presentation S hdet).manifold.Tangent p)
    (h : ∀ w, (SmoothAtlas.presentation S hdet).logarithmicImaginaryValue p v w = 0) :
    v = 0 :=
  smoothAtlas_logarithmicImaginaryValue_nondegenerate S hdet p hp v h

def dimension_zero_coordinates (S : Seed 0) (hdet : S.Unimodular)
    (p : S.Point) (hp : p ∈ initialTorus S) :
    (SmoothAtlas.presentation S hdet).manifold.Tangent p ≃L[ℝ] (Fin 0 → ℂ) :=
  coordinates S hdet p hp

theorem dimension_zero (S : Seed 0) (hdet : S.Unimodular)
    (p : S.Point) (hp : p ∈ initialTorus S)
    (v : (SmoothAtlas.presentation S hdet).manifold.Tangent p)
    (h : ∀ w, (SmoothAtlas.presentation S hdet).logarithmicImaginaryValue p v w = 0) :
    v = 0 := concrete S hdet p hp v h

-- An inhabited zero-dimensional seed, with determinant of the empty matrix equal to one.
def emptySeed : Seed 0 where
  B := 0
  mutable := ∅
  skew i := Fin.elim0 i
  acyclic := ⟨fun i => Fin.elim0 i.val⟩

theorem emptySeed_unimodular : emptySeed.Unimodular := by
  unfold Seed.Unimodular
  exact Matrix.det_isEmpty

theorem emptySeed_tangent_zero (v : (SmoothAtlas.presentation emptySeed emptySeed_unimodular).manifold.Tangent
    emptySeed.unitPoint) : v = 0 := by
  apply concrete emptySeed emptySeed_unimodular emptySeed.unitPoint
    (by intro j; exact Fin.elim0 j) v
  intro w
  simp [SmoothPresentation.logarithmicImaginaryValue]

end TorusNondegeneracyConsumer

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for (name, _) in env.constants.toList do
    if name.toString.startsWith "TorusNondegeneracyConsumer." then
      let axs ← collectAxioms name
      for ax in axs do
        unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
          throwError "Forbidden axiom {ax} in {name}"
      logInfo m!"CONSUMER AUDIT {name}: {axs}"
