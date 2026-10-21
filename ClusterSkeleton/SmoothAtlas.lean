import ClusterSkeleton.IndependentNodeSmooth
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

/-! The smooth atlas on the actual exchange-point subtype. -/

noncomputable section
open scoped Manifold ContDiff
open Set
open FsFltz.Geometry (Model)

namespace ClusterSkeleton
namespace SmoothAtlas
open IndependentNodeChart hiding Model

variable {d : ℕ} (S : Seed d) (hdet : S.Unimodular)
variable (I : Finset (Fin d)) (hI : S.Independent I)

/-- Total inverse for the partial chart; values outside its target are immaterial. -/
def rawInverse (x : Vector S I) : S.Point := by
  classical
  exact if hx : x ∈ domain S I then (backward S I hdet hI (pack S I x hx)).val
  else S.unitPoint

theorem rawInverse_of_mem {x : Vector S I} (hx : x ∈ domain S I) :
    rawInverse S hdet I hI x = (backward S I hdet hI (pack S I x hx)).val :=
  dite_eq_left hx

/-- The accepted homeomorphism as a native open partial homeomorphism. -/
def rawChart : OpenPartialHomeomorph S.Point (Vector S I) where
  toFun p := ambientForward S I hdet hI p.val
  invFun := rawInverse S hdet I hI
  source := candidateChartLocus S I
  target := domain S I
  map_source' p hp := by
    rw [ambientForward_eq S I hdet hI ⟨p, hp⟩]
    exact flatten_mem_domain S I _
  map_target' x hx := by
    rw [rawInverse_of_mem S hdet I hI hx]
    exact (backward S I hdet hI (pack S I x hx)).property
  left_inv' p hp := by
    rw [ambientForward_eq S I hdet hI ⟨p, hp⟩,
      rawInverse_of_mem S hdet I hI (flatten_mem_domain S I _)]
    exact congrArg Subtype.val (backward_forward S I hdet hI ⟨p, hp⟩)
  right_inv' x hx := by
    rw [rawInverse_of_mem S hdet I hI hx]
    rw [ambientForward_eq S I hdet hI (backward S I hdet hI (pack S I x hx))]
    change flatten S I (forward S I hdet hI (backward S I hdet hI (pack S I x hx))) = x
    rw [forward_backward, flatten_pack]
  open_source := isOpen_candidateChartLocus S I
  open_target := isOpen_domain S I
  continuousOn_toFun := by
    rw [continuousOn_iff_continuous_domRestrict]
    have he : (fun p : Locus S I => ambientForward S I hdet hI p.val.val) =
        fun p => flatten S I (homeomorph S I hdet hI p) := by
      funext p
      exact ambientForward_eq S I hdet hI p
    change Continuous (fun p : Locus S I => ambientForward S I hdet hI p.val.val)
    rw [he]
    exact (continuous_flatten S I).comp (homeomorph S I hdet hI).continuous
  continuousOn_invFun := by
    rw [continuousOn_iff_continuous_domRestrict]
    change Continuous (fun x : domain S I => rawInverse S hdet I hI x.val)
    have he : (fun x : domain S I => rawInverse S hdet I hI x.val) =
        fun x => ((homeomorph S I hdet hI).symm ((domainHomeomorph S I).symm x)).val := by
      funext x
      exact rawInverse_of_mem S hdet I hI x.property
    rw [he]
    exact continuous_subtype_val.comp ((homeomorph S I hdet hI).symm.continuous.comp
      (domainHomeomorph S I).symm.continuous)

/-- Every independent locus is a chart with the fixed real model of dimension 2*d. -/
def chart : OpenPartialHomeomorph S.Point (Model (2 * d)) :=
  (rawChart S hdet I hI).trans (modelEquiv S I hdet hI).toHomeomorph.toOpenPartialHomeomorph

@[simp] theorem chart_source : (chart S hdet I hI).source = candidateChartLocus S I := by
  simp [chart, OpenPartialHomeomorph.trans_source, rawChart]

/-- Explicit compatibility with the full accepted node homeomorphism. -/
theorem chart_apply (p : Locus S I) :
    chart S hdet I hI p.val = modelEquiv S I hdet hI
      (flatten S I (homeomorph S I hdet hI p)) := by
  change modelEquiv S I hdet hI (ambientForward S I hdet hI p.val.val) = _
  rw [ambientForward_eq]

/-- Forward coordinates extend smoothly in the actual ambient space. -/
def coordinateExtension : Ambient S → Model (2 * d) :=
  fun p => modelEquiv S I hdet hI (ambientForward S I hdet hI p)

@[simp] theorem chart_eq_extension (p : S.Point) :
    chart S hdet I hI p = coordinateExtension S hdet I hI p.val := rfl

/-- The inverse chart's literal ambient inclusion has a smooth local extension. -/
def inverseExtension : Model (2 * d) → Ambient S :=
  fun x => ambientBackward S I hdet hI ((modelEquiv S I hdet hI).symm x)

theorem chart_target {x : Model (2 * d)} :
    x ∈ (chart S hdet I hI).target ↔ (modelEquiv S I hdet hI).symm x ∈ domain S I := by
  simp [chart, OpenPartialHomeomorph.trans_target, rawChart]

theorem chart_symm_val {x : Model (2 * d)} (hx : x ∈ (chart S hdet I hI).target) :
    ((chart S hdet I hI).symm x).val = inverseExtension S hdet I hI x := by
  have hx' := (chart_target S hdet I hI).mp hx
  change (rawInverse S hdet I hI ((modelEquiv S I hdet hI).symm x)).val = _
  rw [rawInverse_of_mem S hdet I hI hx']
  exact (ambientBackward_eq S I hdet hI (pack S I _ hx')).symm

theorem contDiffAt_coordinateExtension (p : Locus S I) :
    ContDiffAt ℝ ∞ (coordinateExtension S hdet I hI) p.val.val :=
  (modelEquiv S I hdet hI).contDiff.contDiffAt.comp _
    (contDiffAt_ambientForward_real S I hdet hI p)

theorem contDiffAt_inverseExtension {x : Model (2 * d)}
    (hx : x ∈ (chart S hdet I hI).target) :
    ContDiffAt ℝ ∞ (inverseExtension S hdet I hI) x :=
  (contDiffAt_ambientBackward_real S I hdet hI ((chart_target S hdet I hI).mp hx)).comp x
    (modelEquiv S I hdet hI).symm.contDiff.contDiffAt

/-- Pointwise choice only selects a preferred member of the full independent-locus atlas. -/
def chosenIndex (p : S.Point) : {I : Finset (Fin d) // S.Independent I} :=
  ⟨(exists_independent_candidateChartLocus S p).choose,
    (exists_independent_candidateChartLocus S p).choose_spec.1⟩

theorem chosenIndex_mem (p : S.Point) : p ∈ candidateChartLocus S (chosenIndex S p).val :=
  (exists_independent_candidateChartLocus S p).choose_spec.2

/-- Native charts on the inherited topology, with every independent locus in the atlas. -/
@[instance_reducible] def charts : ChartedSpace (Model (2 * d)) S.Point where
  atlas := Set.range (fun I : {I : Finset (Fin d) // S.Independent I} => chart S hdet I.val I.property)
  chartAt p := chart S hdet (chosenIndex S p).val (chosenIndex S p).property
  mem_chart_source p := by simpa using chosenIndex_mem S p
  chart_mem_atlas p := ⟨chosenIndex S p, rfl⟩

/-- Smooth overlaps are compositions of the actual rational/Laurent extensions. -/
theorem contDiffOn_transition (J : Finset (Fin d)) (hJ : S.Independent J) :
    ContDiffOn ℝ ∞ ((chart S hdet I hI).symm.trans (chart S hdet J hJ))
      ((chart S hdet I hI).symm.trans (chart S hdet J hJ)).source := by
  intro x hx
  have hxI : x ∈ (chart S hdet I hI).target := hx.1
  have hxJ : (chart S hdet I hI).symm x ∈ candidateChartLocus S J := by
    simpa only [OpenPartialHomeomorph.symm_symm, Set.mem_preimage, chart_source] using hx.2
  have hg := contDiffAt_coordinateExtension S hdet J hJ
    ⟨(chart S hdet I hI).symm x, hxJ⟩
  rw [chart_symm_val S hdet I hI hxI] at hg
  have hh := hg.comp x (contDiffAt_inverseExtension S hdet I hI hxI)
  apply ContDiffAt.contDiffWithinAt
  apply hh.congr_of_eventuallyEq
  filter_upwards [(chart S hdet I hI).open_target.mem_nhds hxI] with y hy
  change coordinateExtension S hdet J hJ ((chart S hdet I hI).symm y).val =
    coordinateExtension S hdet J hJ (inverseExtension S hdet I hI y)
  rw [chart_symm_val S hdet I hI hy]

/-- All independent charts belong to the constructed atlas. -/
theorem chart_mem_atlas :
    letI := charts S hdet
    chart S hdet I hI ∈ atlas (Model (2 * d)) S.Point := by
  exact ⟨⟨I, hI⟩, rfl⟩

/-- Native real smooth manifold structure, with inherited topology. -/
theorem smooth :
    letI := charts S hdet
    IsManifold (𝓘(ℝ, Model (2 * d))) ∞ S.Point := by
  letI := charts S hdet
  apply isManifold_of_contDiffOn
  intro e e' he he'
  obtain ⟨⟨I, hI⟩, rfl⟩ := he
  obtain ⟨⟨J, hJ⟩, rfl⟩ := he'
  simpa only [modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm,
    Function.comp_id, Function.id_comp, Set.preimage_id, Set.range_id, Set.inter_univ]
    using contDiffOn_transition S hdet I hI J hJ

/-- Inclusion smoothness in every chosen chart, proved from its literal inverse formula. -/
theorem inclusion_smooth :
    letI := charts S hdet
    ContMDiff (𝓘(ℝ, Model (2 * d))) (𝓘(ℝ, Ambient S)) ∞ (fun p : S.Point => p.val) := by
  letI := charts S hdet
  intro p
  let K := chosenIndex S p
  let e := chart S hdet K.val K.property
  have hp : p ∈ e.source := by simpa [e, K] using chosenIndex_mem S p
  have hloc : ContDiffAt ℝ ∞ (fun y => (e.symm y).val) (e p) := by
    apply (contDiffAt_inverseExtension S hdet K.val K.property (e.map_source hp)).congr_of_eventuallyEq
    filter_upwards [e.open_target.mem_nhds (e.map_source hp)] with y hy
    exact chart_symm_val S hdet K.val K.property hy
  apply contMDiffAt_iff.mpr
  refine ⟨continuous_subtype_val.continuousAt, ?_⟩
  simp only [extChartAt_self_eq, extChartAt_coe_symm, extChartAt_coe,
    modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm, Function.comp_id,
    Function.id_comp, Set.range_id]
  change ContDiffWithinAt ℝ ∞ (fun y => (e.symm y).val) Set.univ (e p)
  exact hloc.contDiffWithinAt

/-- The native derivative of the literal ambient inclusion is injective.
The ambient coordinate extension composes with inclusion to the chosen chart,
whose native derivative at its basepoint is the identity. -/
theorem inclusion_immersion :
    letI := charts S hdet
    ∀ p : S.Point, Function.Injective
      (mfderiv (𝓘(ℝ, Model (2 * d))) (𝓘(ℝ, Ambient S)) (fun q : S.Point => q.val) p) := by
  letI := charts S hdet
  letI := smooth S hdet
  intro p
  let K := chosenIndex S p
  let F := coordinateExtension S hdet K.val K.property
  have hF : ContMDiffAt (𝓘(ℝ, Ambient S)) (𝓘(ℝ, Model (2 * d))) ∞ F p.val :=
    (contDiffAt_coordinateExtension S hdet K.val K.property
      ⟨p, chosenIndex_mem S p⟩).contMDiffAt
  have hcomp := mfderiv_comp p (hF.mdifferentiableAt (by simp))
    ((inclusion_smooth S hdet p).mdifferentiableAt (by simp))
  have heq : (F ∘ (fun q : S.Point => q.val)) = extChartAt (𝓘(ℝ, Model (2 * d))) p := rfl
  rw [heq, mfderiv_extChartAt_self] at hcomp
  intro v w hvw
  have h := congrArg (mfderiv (𝓘(ℝ, Ambient S)) (𝓘(ℝ, Model (2 * d))) F p.val) hvw
  change ((mfderiv (𝓘(ℝ, Ambient S)) (𝓘(ℝ, Model (2 * d))) F p.val).comp
      (mfderiv (𝓘(ℝ, Model (2 * d))) (𝓘(ℝ, Ambient S)) (fun q : S.Point => q.val) p)) v =
    ((mfderiv (𝓘(ℝ, Ambient S)) (𝓘(ℝ, Model (2 * d))) F p.val).comp
      (mfderiv (𝓘(ℝ, Model (2 * d))) (𝓘(ℝ, Ambient S)) (fun q : S.Point => q.val) p)) w at h
  rw [← hcomp] at h
  exact h

/-- The concrete smooth presentation, without added chart or immersion assumptions. -/
def presentation : SmoothPresentation S where
  charts := charts S hdet
  smooth := smooth S hdet
  inclusion_smooth := inclusion_smooth S hdet
  inclusion_immersion := inclusion_immersion S hdet

end SmoothAtlas
end ClusterSkeleton
