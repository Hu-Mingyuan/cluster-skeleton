import ClusterSkeleton.NodeTwoForm
import Lean.Util.CollectAxioms

noncomputable section
open scoped Manifold ContDiff
open ClusterSkeleton ClusterSkeleton.NodeTwoForm
open ClusterSkeleton.IndependentNodeChart
open FsFltz.Geometry
namespace NodeTwoFormConsumer

variable {d : ℕ} (S : Seed d) (hdet : S.Unimodular)
variable (I : Finset (Fin d)) (hI : S.Independent I)

/-- No presentation, extension, or tangent-coordinate certificate is supplied. -/
def coordinates (p : S.Point) (hp : p ∈ candidateChartLocus S I) :
    (SmoothAtlas.presentation S hdet).manifold.Tangent p ≃L[ℝ] Vector S I :=
  tangentEquiv S I hdet hI p hp

theorem exact_tangent (p : S.Point) (hp : p ∈ candidateChartLocus S I)
    (v : (SmoothAtlas.presentation S hdet).manifold.Tangent p) :
    coordinates S hdet I hI p hp v =
      letI := SmoothAtlas.charts S hdet
      mfderiv (𝓘(ℝ, FsFltz.Geometry.Model (2 * d))) (𝓘(ℝ, Vector S I))
        (SmoothAtlas.rawChart S hdet I hI) p v := rfl

theorem torus (p : S.Point) (hp : p ∈ initialTorus S)
    (a b : (SmoothAtlas.presentation S hdet).manifold.Tangent p) :
    SmoothManifold.evalTwo (localForm S I hdet hI) p a b =
      (SmoothAtlas.presentation S hdet).logarithmicImaginaryValue p a b :=
  localForm_torus S I hdet hI p hp a b

theorem full_domain_smooth :
    ContDiffOn ℝ ∞ (realForm S I hdet hI) (domain S I) :=
  contDiffOn_realForm S I hdet hI

theorem actual_zeroSet_domain (p : S.Point) : p ∈ candidateChartLocus S p.zeroSet := by
  intro j hj hz
  have hm : j ∈ S.mutable := by
    by_contra hf
    exact p.frozen_ne_zero j hf hz
  exact hj ((p.mem_zeroSet j).mpr ⟨hm,hz⟩)

/-- A boundary consumer at the actual zero-coordinate set, including the origin of each node. -/
theorem actual_boundary (p : S.Point)
    (a b : (SmoothAtlas.presentation S hdet).manifold.Tangent p) :
    let x := SmoothAtlas.rawChart S hdet p.zeroSet p.zeroSet_independent p
    let A := tangentMap S p.zeroSet hdet p.zeroSet_independent p a
    let B := tangentMap S p.zeroSet hdet p.zeroSet_independent p b
    SmoothManifold.evalTwo (localForm S p.zeroSet hdet p.zeroSet_independent) p a b =
      (-(∑ i, ((A.1 i).1 * (B.1 i).2 - (B.1 i).1 * (A.1 i).2)) +
        matrixValue (fun k l => (residualMatrix S p.zeroSet hdet p.zeroSet_independent k l : ℂ))
          (boundaryLog S p.zeroSet x A) (boundaryLog S p.zeroSet x B)).im := by
  apply localForm_boundary
  intro i
  exact ((p.mem_zeroSet i).mp i.property).2

/-- An inhabited zero-dimensional specialization, not an empty-carrier shortcut. -/
def emptySeed : Seed 0 where
  B := 0
  mutable := ∅
  skew i := Fin.elim0 i
  acyclic := ⟨fun i => Fin.elim0 i.val⟩
theorem emptySeed_unimodular : emptySeed.Unimodular := Matrix.det_isEmpty

theorem empty_independent : emptySeed.Independent ∅ := by
  constructor
  · exact Finset.empty_subset _
  · intro i; exact Fin.elim0 i

def empty_coordinates :
    (SmoothAtlas.presentation emptySeed emptySeed_unimodular).manifold.Tangent emptySeed.unitPoint ≃L[ℝ]
      Vector emptySeed ∅ :=
  coordinates emptySeed emptySeed_unimodular ∅ empty_independent emptySeed.unitPoint
    (by intro j; exact Fin.elim0 j)

theorem empty_torus (a b :
    (SmoothAtlas.presentation emptySeed emptySeed_unimodular).manifold.Tangent emptySeed.unitPoint) :
    SmoothManifold.evalTwo (localForm emptySeed ∅ emptySeed_unimodular empty_independent)
      emptySeed.unitPoint a b = 0 := by
  rw [torus emptySeed emptySeed_unimodular ∅ empty_independent emptySeed.unitPoint
    (by intro j; exact Fin.elim0 j)]
  simp [SmoothPresentation.logarithmicImaginaryValue]

end NodeTwoFormConsumer

-- All defining-module declarations, including private/generated declarations;
-- additionally include every current consumer declaration and named namespace root.
-- The unchanged global audit is intentionally not run by this consumer.
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut moduleCount : Nat := 0
  let mut consumerCount : Nat := 0
  let entries := env.constants.toList.mergeSort (fun a b => a.1.toString ≤ b.1.toString)
  for (name, _) in entries do
    let idx := env.getModuleIdxFor? name
    let moduleRoot := match idx with
      | some i => env.header.moduleNames[i]! == `ClusterSkeleton.NodeTwoForm
      | none => false
    let currentRoot := idx.isNone
    let namedRoot := name.toString.startsWith "ClusterSkeleton.NodeTwoForm." ||
      name.toString.startsWith "_private.ClusterSkeleton.NodeTwoForm."
    if moduleRoot || currentRoot || namedRoot then
      let axs ← collectAxioms name
      for ax in axs do
        unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
          throwError "Forbidden axiom {ax} in {name}"
      logInfo m!"AUDIT {name}: {axs}"
      if moduleRoot || namedRoot then moduleCount := moduleCount + 1
      else consumerCount := consumerCount + 1
  if moduleCount == 0 || consumerCount == 0 then
    throwError "Missing module or consumer declarations: {moduleCount}, {consumerCount}"
  logInfo m!"AUDITED NodeTwoForm={moduleCount} consumer={consumerCount}"
