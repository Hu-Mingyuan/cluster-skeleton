import ClusterSkeleton
import ClusterSkeleton.GlobalSymplectic
import Lean.Util.CollectAxioms

noncomputable section
open scoped BigOperators
open ClusterSkeleton FsFltz.Geometry

namespace GlobalSymplecticConsumer

variable {d : ℕ} (S : Seed d) (hdet : S.Unimodular)

theorem empty_nodes_independent : S.Independent ∅ := by
  simp [Seed.Independent]

theorem original_coordinates (p : S.Point) : p.a = p.1.1 := by
  simp [Seed.Point.a]

theorem partner_coordinates (p : S.Point) : p.b = p.1.2 := by
  simp [Seed.Point.b]

theorem smooth :
    (SmoothAtlas.presentation S hdet).manifold.IsSmoothForm (GlobalTwoForm.omega S hdet) :=
  GlobalTwoForm.isSmoothForm_omega S hdet

theorem closed (p : S.Point) :
    (SmoothAtlas.presentation S hdet).manifold.exteriorDerivative
      (GlobalTwoForm.omega S hdet) p = 0 :=
  GlobalTwoForm.exteriorDerivative_omega S hdet p

theorem kernel_trivial (p : S.Point)
    (a : (SmoothAtlas.presentation S hdet).manifold.Tangent p)
    (ha : ∀ b, SmoothManifold.evalTwo (GlobalTwoForm.omega S hdet) p a b = 0) : a = 0 :=
  GlobalSymplectic.nondegenerate_omega S hdet p a ha

theorem nondegenerate (p : S.Point) :
    (SmoothAtlas.presentation S hdet).manifold.Nondegenerate (GlobalTwoForm.omega S hdet) p :=
  GlobalSymplectic.nondegenerate_omega S hdet p

theorem symplectic :
    (SmoothAtlas.presentation S hdet).manifold.IsSymplecticOn
      (GlobalTwoForm.omega S hdet) Set.univ :=
  GlobalSymplectic.isSymplecticOn_omega S hdet

theorem existence :
    ∃ omega : (SmoothAtlas.presentation S hdet).manifold.Form 2,
      omega = GlobalTwoForm.omega S hdet ∧
      (SmoothAtlas.presentation S hdet).manifold.IsSymplecticOn omega Set.univ :=
  GlobalSymplectic.exists_symplectic_form S hdet

theorem zeroSet_restriction (p : S.Point) :
    GlobalTwoForm.omega S hdet p =
      NodeTwoForm.localForm S p.zeroSet hdet p.zeroSet_independent p :=
  GlobalTwoForm.omega_eq_localForm S hdet p.zeroSet p.zeroSet_independent p
    (NodeNondegeneracy.zeroSet_chart_mem S p)

theorem exact_normalization (p : S.Point) (hp : p ∈ initialTorus S)
    (v w : (SmoothAtlas.presentation S hdet).manifold.Tangent p) :
    SmoothManifold.evalTwo (GlobalTwoForm.omega S hdet) p v w =
      ((1 / 2 : ℂ) * ∑ i : Fin d, ∑ j : Fin d, (S.B i j : ℂ) *
        (((SmoothAtlas.presentation S hdet).coordinateDifferential i p v / p.a i) *
          ((SmoothAtlas.presentation S hdet).coordinateDifferential j p w / p.a j) -
        ((SmoothAtlas.presentation S hdet).coordinateDifferential i p w / p.a i) *
          ((SmoothAtlas.presentation S hdet).coordinateDifferential j p v / p.a j))).im :=
  GlobalTwoForm.omega_torus S hdet p hp v w

/-- An explicit determinant-one, inhabited zero-dimensional exchange model. -/
def emptySeed : Seed 0 where
  B := 0
  mutable := ∅
  skew i := Fin.elim0 i
  acyclic := ⟨fun i => Fin.elim0 i.val⟩

theorem emptySeed_unimodular : emptySeed.Unimodular := Matrix.det_isEmpty

def emptyPoint : emptySeed.Point := emptySeed.unitPoint

theorem empty_inhabited : Nonempty emptySeed.Point := ⟨emptyPoint⟩

theorem empty_symplectic :
    (SmoothAtlas.presentation emptySeed emptySeed_unimodular).manifold.IsSymplecticOn
      (GlobalTwoForm.omega emptySeed emptySeed_unimodular) Set.univ :=
  symplectic emptySeed emptySeed_unimodular

theorem empty_nondegenerate :
    (SmoothAtlas.presentation emptySeed emptySeed_unimodular).manifold.Nondegenerate
      (GlobalTwoForm.omega emptySeed emptySeed_unimodular) emptyPoint :=
  nondegenerate emptySeed emptySeed_unimodular emptyPoint

theorem empty_value (v w :
    (SmoothAtlas.presentation emptySeed emptySeed_unimodular).manifold.Tangent emptyPoint) :
    SmoothManifold.evalTwo (GlobalTwoForm.omega emptySeed emptySeed_unimodular)
      emptyPoint v w = 0 := by
  rw [exact_normalization emptySeed emptySeed_unimodular emptyPoint
    (by intro j; exact Fin.elim0 j)]
  simp

end GlobalSymplecticConsumer

-- Native per-root transitive collection. Select by defining module and by
-- explicit previously required generated roots, including changed attribution.
-- The full inherited manifests are also carried with exact source identities.
open Lean Elab Command in
run_cmd do
  -- #check uses a temporary environment. Realize these inherited equations
  -- with Lean's native generator in the environment that is actually audited.
  liftTermElabM do
    for name in #[`ClusterSkeleton.Seed.Independent,
        `ClusterSkeleton.Seed.Point.a, `ClusterSkeleton.Seed.Point.b] do
      unless (← Lean.Meta.getEqnsFor? name).isSome do
        throwError "Cannot realize inherited equations for {name}"
  let env ← getEnv
  let modules := #[`ClusterSkeleton.GlobalSymplectic, `ClusterSkeleton.GlobalTwoForm,
    `ClusterSkeleton.NodeNondegeneracy, `ClusterSkeleton.NodeTwoForm]
  let supplements := #[`FsFltz.Geometry.SmoothManifold.evalTwo.eq_1,
    `ClusterSkeleton.SmoothPresentation.logarithmicImaginaryValue.eq_1,
    `ClusterSkeleton.IndependentNodeChart.rawParameters.eq_1,
    `ClusterSkeleton.SmoothAtlas.rawChart.congr_simp,
    `ContinuousAlternatingMap.restrictScalars.congr_simp,
    `ClusterSkeleton.NodeTwoForm.boundaryLog.eq_1,
    `ClusterSkeleton.Seed.Independent.eq_1,
    `ClusterSkeleton.Seed.Point.a.eq_1,
    `ClusterSkeleton.Seed.Point.b.eq_1]
  for mod in modules do
    unless env.header.moduleNames.contains mod do
      throwError "Missing defining module {mod}"
  for name in supplements do
    unless env.contains name do
      throwError "Missing attribution-sensitive root {name}"
  let entries := env.constants.toList.mergeSort (fun a b => a.1.toString ≤ b.1.toString)
  let mut counts : Array Nat := #[0,0,0,0,0]
  for (name, _) in entries do
    let idx := env.getModuleIdxFor? name
    let defining := idx.bind fun i => modules.idxOf? env.header.moduleNames[i]!
    let nodeNamed := name.toString.startsWith "ClusterSkeleton.NodeNondegeneracy." ||
      name.toString.startsWith "_private.ClusterSkeleton.NodeNondegeneracy."
    if defining.isSome || nodeNamed || idx.isNone || supplements.contains name then
      let axs ← collectAxioms name
      for ax in axs do
        unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
          throwError "Forbidden axiom {ax} in {name}"
      logInfo m!"AUDIT {name}: {axs}"
      counts := counts.modify (defining.getD 4) (· + 1)
  for i in [:4] do
    if counts[i]! == 0 then throwError "No declarations audited for {modules[i]!}"
    logInfo m!"AUDITED {modules[i]!}: {counts[i]!}"
  logInfo m!"AUDITED consumer/supplements: {counts[4]!}"
