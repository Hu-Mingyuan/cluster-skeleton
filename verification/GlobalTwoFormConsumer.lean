import ClusterSkeleton
import ClusterSkeleton.GlobalTwoForm
import Lean.Util.CollectAxioms

noncomputable section
open scoped Manifold ContDiff BigOperators
open ClusterSkeleton FsFltz.Geometry
namespace GlobalTwoFormConsumer

variable {d : ℕ} (S : Seed d) (hdet : S.Unimodular)
variable (I J : Finset (Fin d)) (hI : S.Independent I) (hJ : S.Independent J)

theorem compatibility : NodeTwoForm.LocalCompatibility S I hdet hI :=
  GlobalTwoForm.localCompatibility S hdet I hI

theorem overlap (p : S.Point) (hIp : p ∈ candidateChartLocus S I)
    (hJp : p ∈ candidateChartLocus S J) :
    NodeTwoForm.localForm S I hdet hI p = NodeTwoForm.localForm S J hdet hJ p :=
  compatibility S hdet I hI J hJ p hIp hJp

def form : (SmoothAtlas.presentation S hdet).manifold.Form 2 := GlobalTwoForm.omega S hdet

theorem smooth : (SmoothAtlas.presentation S hdet).manifold.IsSmoothForm (form S hdet) :=
  GlobalTwoForm.isSmoothForm_omega S hdet

theorem closed (p : S.Point) :
    (SmoothAtlas.presentation S hdet).manifold.exteriorDerivative (form S hdet) p = 0 :=
  GlobalTwoForm.exteriorDerivative_omega S hdet p

theorem restriction (p : S.Point) (hp : p ∈ candidateChartLocus S I) :
    form S hdet p = NodeTwoForm.localForm S I hdet hI p :=
  GlobalTwoForm.omega_eq_localForm S hdet I hI p hp

theorem exact_normalization (p : S.Point) (hp : p ∈ initialTorus S)
    (v w : (SmoothAtlas.presentation S hdet).manifold.Tangent p) :
    SmoothManifold.evalTwo (form S hdet) p v w =
      ((1 / 2 : ℂ) * ∑ i : Fin d, ∑ j : Fin d, (S.B i j : ℂ) *
        (((SmoothAtlas.presentation S hdet).coordinateDifferential i p v / p.a i) *
          ((SmoothAtlas.presentation S hdet).coordinateDifferential j p w / p.a j) -
        ((SmoothAtlas.presentation S hdet).coordinateDifferential i p w / p.a i) *
          ((SmoothAtlas.presentation S hdet).coordinateDifferential j p v / p.a j))).im :=
  GlobalTwoForm.omega_torus S hdet p hp v w

theorem exact_target : NodeTwoForm.GlobalClosedExtension S hdet :=
  GlobalTwoForm.globalClosedExtension S hdet

/-- Specialize to the actual zero set, without a boundary nondegeneracy premise. -/
theorem actual_zeroSet (p : S.Point) :
    form S hdet p = NodeTwoForm.localForm S p.zeroSet hdet p.zeroSet_independent p := by
  apply restriction
  intro j hj hz
  apply hj
  apply (p.mem_zeroSet j).mpr
  refine ⟨?_, hz⟩
  by_contra hf
  exact p.frozen_ne_zero j hf hz

/-- Inhabited zero-dimensional seed; no positivity hypothesis is hidden. -/
def emptySeed : Seed 0 where
  B := 0
  mutable := ∅
  skew i := Fin.elim0 i
  acyclic := ⟨fun i => Fin.elim0 i.val⟩
theorem emptySeed_unimodular : emptySeed.Unimodular := Matrix.det_isEmpty

def emptyPoint : emptySeed.Point := emptySeed.unitPoint

theorem empty_target : NodeTwoForm.GlobalClosedExtension emptySeed emptySeed_unimodular :=
  exact_target emptySeed emptySeed_unimodular

theorem empty_smooth :
    (SmoothAtlas.presentation emptySeed emptySeed_unimodular).manifold.IsSmoothForm
      (form emptySeed emptySeed_unimodular) := smooth emptySeed emptySeed_unimodular

theorem empty_closed :
    (SmoothAtlas.presentation emptySeed emptySeed_unimodular).manifold.exteriorDerivative
      (form emptySeed emptySeed_unimodular) emptyPoint = 0 :=
  closed emptySeed emptySeed_unimodular emptyPoint

theorem empty_value (v w :
    (SmoothAtlas.presentation emptySeed emptySeed_unimodular).manifold.Tangent emptyPoint) :
    SmoothManifold.evalTwo (form emptySeed emptySeed_unimodular) emptyPoint v w = 0 := by
  rw [exact_normalization emptySeed emptySeed_unimodular emptyPoint
    (by intro j; exact Fin.elim0 j)]
  simp

end GlobalTwoFormConsumer

-- The accepted inherited manifest is carried with the source-composition
-- evidence. Audit every defining-module and current consumer declaration,
-- including private/generated entries, and all three attribution-sensitive
-- NodeTwoForm roots explicitly. No namespace-only coverage inference is used.
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let modules := #[`ClusterSkeleton.GlobalTwoForm, `ClusterSkeleton.NodeTwoForm]
  let supplements := #[`ClusterSkeleton.IndependentNodeChart.rawParameters.eq_1,
    `ClusterSkeleton.SmoothAtlas.rawChart.congr_simp,
    `ContinuousAlternatingMap.restrictScalars.congr_simp]
  for mod in modules do
    unless env.header.moduleNames.contains mod do
      throwError "Missing defining module {mod}"
  for name in supplements do
    unless env.contains name do
      throwError "Missing attribution-sensitive root {name}"
  let entries := env.constants.toList.mergeSort (fun a b => a.1.toString ≤ b.1.toString)
  let mut counts : Array Nat := #[0,0,0]
  for (name, _) in entries do
    let idx := env.getModuleIdxFor? name
    let defining := idx.bind fun i => modules.idxOf? env.header.moduleNames[i]!
    if defining.isSome || idx.isNone || supplements.contains name then
      let axs ← collectAxioms name
      for ax in axs do
        unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
          throwError "Forbidden axiom {ax} in {name}"
      logInfo m!"AUDIT {name}: {axs}"
      let group := defining.getD 2
      counts := counts.modify group (· + 1)
  for i in [:2] do
    if counts[i]! == 0 then throwError "No declarations audited for {modules[i]!}"
    logInfo m!"AUDITED {modules[i]!}: {counts[i]!}"
  logInfo m!"AUDITED consumer/supplements: {counts[2]!}"
