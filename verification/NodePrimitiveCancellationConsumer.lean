import ClusterSkeleton.NodePrimitiveCancellation
import ClusterSkeleton.NodeTwoForm
import Lean.Util.CollectAxioms

/-!
Finite sums of pullbacks of the regular node summands in the accepted RAW
node vector space. No statement identifies this sum with the full primitive;
in particular the residual matrix terms are not discarded.
-/
noncomputable section
open scoped ContDiff Topology BigOperators
open Set ClusterSkeleton ClusterSkeleton.NodePrimitiveCancellation

namespace NodePrimitiveCancellationConsumer
open IndependentNodeChart
variable {d : ℕ} (seed : Seed d) (I : Finset (Fin d))

abbrev Index := {i : Fin d // i ∈ I}

/-- The accepted raw node projection, without a coordinate change. -/
def projection (i : Index I) : Vector seed I →L[ℝ] E :=
  (ContinuousLinearMap.proj i).comp (ContinuousLinearMap.fst ℝ _ _)

@[simp] theorem projection_apply (i : Index I) (x : Vector seed I) :
    projection seed I i x = x.1 i := rfl

/-- The projection really uses a_i and b_i/Q_i in the accepted chart. -/
theorem projection_rawChart (hdet : seed.Unimodular) (hI : seed.Independent I)
    (p : seed.Point) (i : Index I) :
    projection seed I i (SmoothAtlas.rawChart seed hdet I hI p) =
      (p.a i, p.b ⟨i, hI.1 i.property⟩ / seed.negativeMonomial p.a i) := rfl

/-- One open intersection, including simultaneous zero coordinates. -/
def logDomain : Set (Vector seed I) :=
  domain seed I ∩ {x | ∀ i, projection seed I i x ∈ nodeLogDomain}

theorem isOpen_logDomain : IsOpen (logDomain seed I) := by
  apply (isOpen_domain seed I).inter
  simp only [Set.ofPred_forall]
  exact isOpen_iInter_of_finite fun i =>
    isOpen_nodeLogDomain.preimage (projection seed I i).continuous

/-- Independent real parameters are permitted in each summand. -/
def summedCovector (k : Index I → ℝ) (x : Vector seed I) : Vector seed I →L[ℝ] ℝ :=
  ∑ i, (lambda (k i) (projection seed I i x)).comp (projection seed I i)

def summedForm (k : Index I → ℝ) (x : Vector seed I) :
    Vector seed I [⋀^Fin 1]→L[ℝ] ℝ :=
  ContinuousAlternatingMap.ofSubsingleton ℝ _ ℝ (0 : Fin 1) (summedCovector seed I k x)

@[simp] theorem summedCovector_apply (k : Index I → ℝ) (x t : Vector seed I) :
    summedCovector seed I k x t = ∑ i, lambda (k i) (x.1 i) (t.1 i) := by
  simp [summedCovector]

@[simp] theorem summedForm_apply (k : Index I → ℝ) (x : Vector seed I)
    (t : Fin 1 → Vector seed I) :
    summedForm seed I k x t = summedCovector seed I k x (t 0) := rfl

/-- The alternating representation is literally the sum of native pullbacks. -/
theorem summedForm_eq_sum_pullbacks (k : Index I → ℝ) (x : Vector seed I) :
    summedForm seed I k x = ∑ i,
      (oneForm (k i) (projection seed I i x)).compContinuousLinearMap (projection seed I i) := by
  ext t
  simp [summedForm_apply, summedCovector_apply,
    ContinuousAlternatingMap.sum_apply, ContinuousAlternatingMap.compContinuousLinearMap_apply]

theorem contDiffOn_summedCovector (k : Index I → ℝ) :
    ContDiffOn ℝ ∞ (summedCovector seed I k) (logDomain seed I) := by
  intro x hx
  apply ContDiffAt.contDiffWithinAt
  apply ContDiffAt.sum
  intro i _
  exact ((contDiffAt_lambda (k i) (hx.2 i)).comp x
    (projection seed I i).contDiff.contDiffAt).clm_comp contDiffAt_const

theorem contDiffOn_summedForm (k : Index I → ℝ) :
    ContDiffOn ℝ ∞ (summedForm seed I k) (logDomain seed I) :=
  (ContinuousAlternatingMap.ofSubsingletonLIE (𝕜 := ℝ) (E := Vector seed I) (F := ℝ)
    (0 : Fin 1)).toContinuousLinearEquiv.contDiff.comp_contDiffOn
      (contDiffOn_summedCovector seed I k)

/-- Sum of the native pullbacks of the literal cancellation identity. -/
theorem summed_cancellation (k : Index I → ℝ) {x : Vector seed I}
    (hx : x ∈ logDomain seed I) (hu : ∀ i, (x.1 i).1 ≠ 0) :
    (∑ i, (A (x.1 i) • fderiv ℝ T (x.1 i) - S (x.1 i) • dtheta (x.1 i) -
      fderiv ℝ (fun p => (A p + k i) * T p) (x.1 i)).comp (projection seed I i)) =
        summedCovector seed I k x := by
  apply Finset.sum_congr rfl
  intro i _
  rw [cancellation (k i) (p := x.1 i) (hx.2 i) (hu i)]
  rfl

theorem summed_cancellation_oneForm (k : Index I → ℝ) {x : Vector seed I}
    (hx : x ∈ logDomain seed I) (hu : ∀ i, (x.1 i).1 ≠ 0) :
    ContinuousAlternatingMap.ofSubsingleton ℝ _ ℝ (0 : Fin 1)
      (∑ i, (A (x.1 i) • fderiv ℝ T (x.1 i) - S (x.1 i) • dtheta (x.1 i) -
        fderiv ℝ (fun p => (A p + k i) * T p) (x.1 i)).comp (projection seed I i)) =
          summedForm seed I k x := by
  rw [summed_cancellation seed I k hx hu]
  rfl

/-- All zero first coordinates, arbitrary second coordinates, unit free coordinates. -/
def center (v : Index I → ℂ) : Vector seed I := (fun i => (0, v i), fun _ => 1)

theorem center_mem (v : Index I → ℂ) : center seed I v ∈ logDomain seed I := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro i
    simp [center]
  · intro j
    simp [center]
  · intro i
    exact zero_mem_nodeLogDomain (v i)

/-- The open domain contains every such center, even when the index set is empty. -/
theorem center_neighborhood (v : Index I → ℂ) :
    logDomain seed I ∈ nhds (center seed I v) :=
  (isOpen_logDomain seed I).mem_nhds (center_mem seed I v)

theorem contDiffAt_summedForm_center (k : Index I → ℝ) (v : Index I → ℂ) :
    ContDiffAt ℝ ∞ (summedForm seed I k) (center seed I v) :=
  (contDiffOn_summedForm seed I k).contDiffAt (center_neighborhood seed I v)

theorem summed_zero (k : Index I → ℝ) (x t : Vector seed I)
    (hu : ∀ i, (x.1 i).1 = 0) :
    summedCovector seed I k x t = ∑ i, (1 + k i) * ((x.1 i).2 * (t.1 i).1).im := by
  rw [summedCovector_apply]
  apply Finset.sum_congr rfl
  intro i _
  have hi : x.1 i = (0, (x.1 i).2) := Prod.ext (hu i) rfl
  rw [hi, lambda_zero]

theorem summedForm_center (k : Index I → ℝ) (v : Index I → ℂ)
    (t : Fin 1 → Vector seed I) :
    summedForm seed I k (center seed I v) t =
      ∑ i, (1 + k i) * (v i * ((t 0).1 i).1).im := by
  exact summed_zero seed I k (center seed I v) (t 0) (fun _ => rfl)

theorem empty_sum (k : Index (∅ : Finset (Fin d)) → ℝ)
    (x : Vector seed ∅) : summedCovector seed ∅ k x = 0 := by
  simp [summedCovector, Index]

theorem empty_center_mem (v : Index (∅ : Finset (Fin d)) → ℂ) :
    center seed ∅ v ∈ logDomain seed ∅ := center_mem seed ∅ v

end NodePrimitiveCancellationConsumer

-- Native per-root audit of owned, private/generated, and attribution-sensitive roots.
open Lean Elab Command in
run_cmd do
  liftTermElabM do
    for name in #[`ClusterSkeleton.Seed.Independent,
        `ClusterSkeleton.Seed.Point.a, `ClusterSkeleton.Seed.Point.b,
        `ClusterSkeleton.NodeTwoForm.boundaryLog] do
      unless (← Lean.Meta.getEqnsFor? name).isSome do
        throwError "Cannot realize inherited equations for {name}"
  let env ← getEnv
  let mod := `ClusterSkeleton.NodePrimitiveCancellation
  let supplements := #[`FsFltz.Geometry.SmoothManifold.evalTwo.eq_1,
    `ClusterSkeleton.SmoothPresentation.logarithmicImaginaryValue.eq_1,
    `ClusterSkeleton.IndependentNodeChart.rawParameters.eq_1,
    `ClusterSkeleton.SmoothAtlas.rawChart.congr_simp,
    `ContinuousAlternatingMap.restrictScalars.congr_simp,
    `ClusterSkeleton.NodeTwoForm.boundaryLog.eq_1,
    `ClusterSkeleton.Seed.Independent.eq_1,
    `ClusterSkeleton.Seed.Point.a.eq_1,
    `ClusterSkeleton.Seed.Point.b.eq_1]
  unless env.header.moduleNames.contains mod do throwError "Missing module {mod}"
  for name in supplements do
    unless env.contains name do throwError "Missing generated root {name}"
  let entries := env.constants.toList.mergeSort (fun a b => a.1.toString ≤ b.1.toString)
  let mut moduleCount : Nat := 0
  let mut otherCount : Nat := 0
  for (name, _) in entries do
    let idx := env.getModuleIdxFor? name
    let defining := idx.any fun i => env.header.moduleNames[i]! == mod
    let named := name.toString.startsWith "ClusterSkeleton.NodePrimitiveCancellation." ||
      name.toString.startsWith "_private.ClusterSkeleton.NodePrimitiveCancellation."
    if defining || named || idx.isNone || supplements.contains name then
      let axs ← collectAxioms name
      for ax in axs do
        unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
          throwError "Forbidden axiom {ax} in {name}"
      logInfo m!"AUDIT {name}: {axs}"
      if defining || named then moduleCount := moduleCount + 1
      else otherCount := otherCount + 1
  if moduleCount == 0 || otherCount == 0 then throwError "Empty audit selection"
  logInfo m!"AUDITED {mod}: {moduleCount}"
  logInfo m!"AUDITED consumer/supplements: {otherCount}"
