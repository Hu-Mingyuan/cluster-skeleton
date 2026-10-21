import ClusterSkeleton.LocalFormGluing
import ClusterSkeleton.TorusPrimitive

noncomputable section
open scoped Manifold ContDiff Topology
open Set FsFltz.Geometry FsFltz.Geometry.SmoothManifold
open ClusterSkeleton ClusterSkeleton.LocalFormGluing

namespace LocalFormGluingConsumer

/-- The native model manifold, including dimension zero. -/
abbrev modelManifold (d : ℕ) : SmoothManifold d where
  Point := Model d
  topology := inferInstance
  charts := inferInstance
  hausdorff := inferInstance
  secondCountable := inferInstance
  smooth := inferInstance

theorem model_formInChart {d k : ℕ} (omega : (modelManifold d).Form k)
    (a y : Model d) : (modelManifold d).formInChart a omega y = omega y := by
  change (omega y).compContinuousLinearMap
    (mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model d) id y) = omega y
  rw [mfderiv_id]
  ext vs
  rfl

def covector : Model 1 [⋀^Fin 1]→L[ℝ] ℝ :=
  ContinuousAlternatingMap.ofSubsingleton ℝ (Model 1) ℝ (0 : Fin 1)
    (EuclideanSpace.proj (0 : Fin 1))

theorem covector_apply (vs : Fin 1 → Model 1) : covector vs = vs 0 0 := rfl

def domain : Bool → Set (Model 1)
  | false => {x | x 0 < 1}
  | true => {x | -1 < x 0}

theorem open_domain (i : Bool) : IsOpen (domain i) := by
  cases i
  · exact isOpen_lt (EuclideanSpace.proj (0 : Fin 1)).continuous continuous_const
  · exact isOpen_lt continuous_const (EuclideanSpace.proj (0 : Fin 1)).continuous

theorem covers (x : Model 1) : ∃ i, x ∈ domain i := by
  by_cases hx : x 0 < 1
  · exact ⟨false, hx⟩
  · refine ⟨true, ?_⟩
    change -1 < x 0
    linarith

/-- The two totalizations jump at their own boundaries. -/
def localForm (i : Bool) : (modelManifold 1).Form 1 :=
  fun x => @ite _ (x ∈ domain i) (Classical.propDecidable _) covector 0

theorem local_eq (i : Bool) (p : Model 1) (hp : p ∈ domain i) :
    localForm i p = covector := ite_eq_left hp

theorem local_eval (i : Bool) (p : Model 1) (hp : p ∈ domain i)
    (v : (modelManifold 1).Tangent p) : evalOne (localForm i) p v = (show Model 1 from v) 0 := by
  change localForm i p (fun _ => v) = _
  rw [local_eq i p hp]
  rfl

theorem local_smooth (i : Bool) : LocallySmooth (modelManifold 1) (domain i) (localForm i) := by
  intro a y _ hy
  change y ∈ domain i at hy
  have hc : (modelManifold 1).formInChart a (localForm i) = localForm i :=
    funext (model_formInChart _ a)
  rw [hc]
  apply contDiffAt_const.congr_of_eventuallyEq
  filter_upwards [(open_domain i).mem_nhds hy] with z hz
  exact ite_eq_left hz

/-- A genuinely proper dense set; its omitted point lies in the overlap. -/
def denseSet : Set (Model 1) := {x | x ≠ 0}

theorem dense_denseSet : Dense denseSet := by
  exact dense_compl_singleton (0 : Model 1)

theorem agree_dense (i j : Bool) (p : Model 1) (_ : p ∈ denseSet)
    (hi : p ∈ domain i) (hj : p ∈ domain j) : localForm i p = localForm j p := by
  exact (local_eq i p hi).trans (local_eq j p hj).symm

theorem proper_overlap :
    (0 : Model 1) ∈ domain false ∩ domain true ∧
    PiLp.single 2 0 (2 : ℝ) ∈ domain true \ domain false ∧
    PiLp.single 2 0 (-2 : ℝ) ∈ domain false \ domain true := by
  norm_num [domain]

theorem totalizations_differ : localForm false ≠ localForm true := by
  intro h
  have he := congrArg (fun f : (modelManifold 1).Form 1 =>
    evalOne f (PiLp.single 2 0 (2 : ℝ)) (PiLp.single 2 0 (1 : ℝ))) h
  norm_num [evalOne, localForm, domain, covector_apply] at he
  change (0 : ℝ) = 1 at he
  exact zero_ne_one he

def glued : (modelManifold 1).Form 1 := glue (modelManifold 1) domain localForm covers

theorem glued_restriction (i : Bool) (p : Model 1) (hp : p ∈ domain i) :
    glued p = localForm i p :=
  glue_eq (modelManifold 1) domain localForm open_domain covers dense_denseSet
    local_smooth agree_dense i p hp

theorem glued_smooth : (modelManifold 1).IsSmoothForm glued :=
  isSmoothForm_glue (modelManifold 1) domain localForm open_domain covers dense_denseSet
    local_smooth agree_dense

theorem glued_eval (p : Model 1) (v : (modelManifold 1).Tangent p) :
    evalOne glued p v = (show Model 1 from v) 0 := by
  obtain ⟨i, hi⟩ := covers p
  change glued p (fun _ => v) = (show Model 1 from v) 0
  rw [glued_restriction i p hi]
  exact local_eval i p hi v

/-- The point omitted from D is recovered by the overlap theorem as well. -/
theorem overlap_at_omitted_point : localForm false 0 = localForm true 0 :=
  eqOn_overlap_of_dense (modelManifold 1) (open_domain false) (open_domain true)
    dense_denseSet (local_smooth false) (local_smooth true) (agree_dense false true)
    0 (by norm_num [domain]) (by norm_num [domain])

theorem glued_unique (theta : (modelManifold 1).Form 1)
    (h : ∀ i p, p ∈ domain i → theta p = localForm i p) : theta = glued :=
  eq_glue_of_restrictions (modelManifold 1) domain localForm covers theta h

theorem glued_dense_value : ∀ p ∈ denseSet, glued p = covector :=
  glue_eq_on_dense (modelManifold 1) domain localForm covers (fun _ => covector)
    (fun i p _ hp => local_eq i p hp)

/-- All positive-degree one-forms in dimension zero vanish fiberwise. -/
theorem dimension_zero_eval (M : SmoothManifold 0) (eta : M.Form 1)
    (p : M.Point) (v : M.Tangent p) : evalOne eta p v = 0 := by
  have hv : v = 0 := PiLp.ext (fun i => Fin.elim0 i)
  rw [hv]
  exact (eta p).map_coord_zero (i := (0 : Fin 1)) rfl

theorem zero_local_smooth {n k : ℕ} (M : SmoothManifold n) (U : Set M.Point) :
    LocallySmooth M U (0 : M.Form k) := by
  intro a y _ _
  have he : M.formInChart a (0 : M.Form k) = fun _ => 0 := by
    funext z
    ext v
    rfl
  rw [he]
  exact contDiffAt_const

/-- Dimension zero still admits a cover, and arbitrary fiber evaluation is zero. -/
theorem dimension_zero_gluing :
    ∃! theta : (modelManifold 0).Form 1, (modelManifold 0).IsSmoothForm theta ∧
      ∀ (_ : Unit) p, p ∈ (univ : Set (Model 0)) → theta p = 0 :=
  existsUnique_smooth_gluing (modelManifold 0) (fun _ : Unit => univ)
    (fun _ => 0) (fun _ => isOpen_univ) (fun _ => ⟨(), mem_univ _⟩) dense_univ
    (fun _ => zero_local_smooth _ _) (fun _ _ _ _ _ _ => rfl)

/-- Empty index types are supported without introducing a default cover index. -/
theorem empty_cover {n k : ℕ} (M : SmoothManifold n) [IsEmpty M.Point]
    (U : Empty → Set M.Point) (eta : Empty → M.Form k) :
    ∃! theta : M.Form k, M.IsSmoothForm theta ∧
      ∀ i p, p ∈ U i → theta p = eta i p := by
  exact existsUnique_smooth_gluing M U eta (fun i => nomatch i)
    (fun p => isEmptyElim p) (D := univ) dense_univ
    (fun i => nomatch i) (fun i => nomatch i)

/-- Actual exchange-point consumer, conditional only on independently supplied
local degree-one smoothness and initial-torus agreement. -/
theorem exchange_oneForm {d : ℕ} (S : Seed d) (hdet : S.Unimodular)
    {ι : Type*} (U : ι → Set S.Point)
    (eta : ι → (SmoothAtlas.presentation S hdet).manifold.Form 1)
    (hopen : ∀ i, IsOpen (U i)) (hcover : ∀ p, ∃ i, p ∈ U i)
    (hs : ∀ i, LocallySmooth (SmoothAtlas.presentation S hdet).manifold (U i) (eta i))
    (he : ∀ i j p, p ∈ initialTorus S → p ∈ U i → p ∈ U j → eta i p = eta j p) :
    ∃! theta : (SmoothAtlas.presentation S hdet).manifold.Form 1,
      (SmoothAtlas.presentation S hdet).manifold.IsSmoothForm theta ∧
        ∀ i p, p ∈ U i → theta p = eta i p :=
  smoothAtlas_existsUnique_gluing S hdet U eta hopen hcover hs he

end LocalFormGluingConsumer

-- Full native per-root coverage of this module and this consumer, including
-- private/generated declarations. Inherited results are carried separately
-- through the complete source-equal 740-root accepted manifest.
open Lean Elab Command in
run_cmd do
  liftTermElabM do
    for name in #[`ClusterSkeleton.Seed.Independent,
        `ClusterSkeleton.Seed.Point.a, `ClusterSkeleton.Seed.Point.b,
        `ClusterSkeleton.NodeTwoForm.boundaryLog,
        `ClusterSkeleton.LocalFormGluing.LocallySmooth,
        `ClusterSkeleton.LocalFormGluing.glue,
        `LocalFormGluingConsumer.covector, `LocalFormGluingConsumer.domain,
        `LocalFormGluingConsumer.localForm, `LocalFormGluingConsumer.denseSet,
        `LocalFormGluingConsumer.glued] do
      unless (← Lean.Meta.getEqnsFor? name).isSome do
        throwError "Cannot realize inherited equations for {name}"
  let env ← getEnv
  let mod := `ClusterSkeleton.LocalFormGluing
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
    let named := name.toString.startsWith "ClusterSkeleton.LocalFormGluing." ||
      name.toString.startsWith "_private.ClusterSkeleton.LocalFormGluing."
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
