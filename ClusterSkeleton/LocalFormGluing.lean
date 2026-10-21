import ClusterSkeleton.FormExtensionUniqueness

/-!
# Native local form gluing

Local forms are total functions with dependent tangent fibers. Smoothness is
required only at chart points lying over their own open domains. Density is
used in a fixed coefficient space, followed by native differential cancellation.
No existence of local extensions of the manuscript primitive is assumed here.
-/

noncomputable section
open scoped Manifold ContDiff Topology
open Set FsFltz.Geometry FsFltz.Geometry.SmoothManifold

namespace ClusterSkeleton.LocalFormGluing

variable {n k : ℕ} (M : SmoothManifold n)

/-- Pointwise native coefficient smoothness over a specified domain. -/
def LocallySmooth (U : Set M.Point) (eta : M.Form k) : Prop :=
  ∀ a y, y ∈ (chartAt (Model n) a).target →
    (chartAt (Model n) a).symm y ∈ U →
    ContDiffAt ℝ ∞ (M.formInChart a eta) y

/-- Continuity is asserted in one fixed model coefficient space. -/
theorem continuousOn_coefficients {U : Set M.Point} {eta : M.Form k}
    (h : LocallySmooth M U eta) (a : M.Point) :
    ContinuousOn (fun p => M.formInChart a eta (chartAt (Model n) a p))
      ((chartAt (Model n) a).source ∩ U) := by
  intro p hp
  have hi : (chartAt (Model n) a).symm (chartAt (Model n) a p) ∈ U := by
    rw [(chartAt (Model n) a).left_inv hp.1]
    exact hp.2
  exact ((h a _ ((chartAt (Model n) a).map_source hp.1) hi).continuousAt.comp
    ((chartAt (Model n) a).continuousAt hp.1)).continuousWithinAt

/-- Agreement on the dense part of an open overlap determines the entire
overlap. No global smoothness of the totalizations is needed. -/
theorem eqOn_overlap_of_dense {U V D : Set M.Point}
    (hU : IsOpen U) (hV : IsOpen V) (hD : Dense D)
    {eta theta : M.Form k} (heta : LocallySmooth M U eta)
    (htheta : LocallySmooth M V theta)
    (heq : ∀ p ∈ D, p ∈ U → p ∈ V → eta p = theta p) :
    ∀ p ∈ U, p ∈ V → eta p = theta p := by
  intro p hpU hpV
  let e := chartAt (Model n) p
  let W := (e.source ∩ U) ∩ V
  have hW : IsOpen W := (e.open_source.inter hU).inter hV
  have hc1 : ContinuousOn (fun q => M.formInChart p eta (e q)) W :=
    (continuousOn_coefficients M heta p).mono inter_subset_left
  have hc2 : ContinuousOn (fun q => M.formInChart p theta (e q)) W :=
    (continuousOn_coefficients M htheta p).mono (fun q hq => ⟨hq.1.1, hq.2⟩)
  have hdense : EqOn (fun q => M.formInChart p eta (e q))
      (fun q => M.formInChart p theta (e q)) (W ∩ D) := by
    intro q hq
    have hq' := heq q hq.2 hq.1.1.2 hq.1.2
    have hi : e.symm (e q) = q := e.left_inv hq.1.1.1
    have hf : eta (e.symm (e q)) = theta (e.symm (e q)) := by
      rw [hi]
      exact hq'
    exact congrArg (fun f => f.compContinuousLinearMap
      (M.inverseChartTangentMap p (e q))) hf
  have hd : W ⊆ closure (W ∩ D) := fun q hq => hW.inter_closure ⟨hq, hD q⟩
  have he := hdense.of_subset_closure hc1 hc2 inter_subset_left hd
  have hp : p ∈ e.source := mem_chart_source _ _
  have h := congrArg (fun f => f.compContinuousLinearMap (M.chartTangentMap p p))
    (he ⟨⟨hp, hpU⟩, hpV⟩)
  exact (M.formInChart_comp_chartTangentMap _ p p hp).symm.trans
    (h.trans (M.formInChart_comp_chartTangentMap _ p p hp))

variable {ι : Type*} (U : ι → Set M.Point) (eta : ι → M.Form k)

/-- Pointwise selection requires neither a nonempty index type nor points. -/
def glue (hcover : ∀ p, ∃ i, p ∈ U i) : M.Form k :=
  fun p => eta (hcover p).choose p

variable (hopen : ∀ i, IsOpen (U i)) (hcover : ∀ p, ∃ i, p ∈ U i)
    {D : Set M.Point} (hD : Dense D)
    (hsmooth : ∀ i, LocallySmooth M (U i) (eta i))
    (hagree : ∀ i j p, p ∈ D → p ∈ U i → p ∈ U j → eta i p = eta j p)

include hopen hD hsmooth hagree in
/-- Restriction to every member, regardless of which index was selected. -/
theorem glue_eq (i : ι) (p : M.Point) (hp : p ∈ U i) :
    glue M U eta hcover p = eta i p :=
  eqOn_overlap_of_dense M (hopen _) (hopen i) hD (hsmooth _) (hsmooth i)
    (hagree _ i) p (hcover p).choose_spec hp

include hopen hD hsmooth hagree in
/-- Independence from any supplied choice function subordinate to the cover. -/
theorem glue_eq_selection (select : M.Point → ι)
    (hselect : ∀ p, p ∈ U (select p)) :
    glue M U eta hcover = fun p => eta (select p) p := by
  funext p
  exact glue_eq M U eta hopen hcover hD hsmooth hagree _ p (hselect p)

include hopen hD hsmooth hagree in
/-- Smoothness follows by agreement with a single local form on a neighborhood
of each inverse-chart point. -/
theorem isSmoothForm_glue : M.IsSmoothForm (glue M U eta hcover) := by
  intro a y hy
  let c := chartAt (Model n) a
  obtain ⟨i, hi⟩ := hcover (c.symm y)
  have hs := hsmooth i a y hy hi
  have he : M.formInChart a (glue M U eta hcover) =ᶠ[𝓝 y]
      M.formInChart a (eta i) := by
    have hn := (c.continuousAt_symm hy).preimage_mem_nhds ((hopen i).mem_nhds hi)
    filter_upwards [hn] with z hz
    exact congrArg (fun f => f.compContinuousLinearMap (M.inverseChartTangentMap a z))
      (glue_eq M U eta hopen hcover hD hsmooth hagree i _ hz)
  exact (hs.congr_of_eventuallyEq he).contDiffWithinAt

/-- Local restrictions determine any native form, hence also every smooth one. -/
theorem eq_glue_of_restrictions (theta : M.Form k)
    (hlocal : ∀ i p, p ∈ U i → theta p = eta i p) :
    theta = glue M U eta hcover := by
  funext p
  exact hlocal _ p (hcover p).choose_spec

/-- A specified form need only agree on each covered part of D. -/
theorem glue_eq_on_dense (theta : M.Form k)
    (hlocal : ∀ i p, p ∈ D → p ∈ U i → eta i p = theta p) :
    ∀ p ∈ D, glue M U eta hcover p = theta p := by
  intro p hp
  exact hlocal _ p hp (hcover p).choose_spec

include hopen hcover hD hsmooth hagree in
/-- A usable existence-and-uniqueness theorem with precisely local hypotheses. -/
theorem existsUnique_smooth_gluing :
    ∃! theta : M.Form k, M.IsSmoothForm theta ∧
      ∀ i p, p ∈ U i → theta p = eta i p := by
  refine ⟨glue M U eta hcover, ⟨isSmoothForm_glue M U eta hopen hcover hD hsmooth hagree,
    glue_eq M U eta hopen hcover hD hsmooth hagree⟩, ?_⟩
  intro theta htheta
  exact eq_glue_of_restrictions M U eta hcover theta htheta.2

include hopen hD hsmooth hagree in
/-- Evaluation remains in the original dependent tangent fiber for every degree. -/
theorem glue_eval (i : ι) (p : M.Point) (hp : p ∈ U i)
    (v : Fin k → M.Tangent p) :
    glue M U eta hcover p v = eta i p v := by
  rw [glue_eq M U eta hopen hcover hD hsmooth hagree i p hp]

/-- Conditional infrastructure on the accepted atlas of actual complex exchange
points. The local forms and their local coefficient proofs must be supplied. -/
theorem smoothAtlas_existsUnique_gluing {d k : ℕ} (S : Seed d) (hdet : S.Unimodular)
    {ι : Type*} (U : ι → Set S.Point)
    (eta : ι → (SmoothAtlas.presentation S hdet).manifold.Form k)
    (hopen : ∀ i, IsOpen (U i)) (hcover : ∀ p, ∃ i, p ∈ U i)
    (hsmooth : ∀ i, LocallySmooth (SmoothAtlas.presentation S hdet).manifold (U i) (eta i))
    (hagree : ∀ i j p, p ∈ initialTorus S → p ∈ U i → p ∈ U j → eta i p = eta j p) :
    ∃! theta : (SmoothAtlas.presentation S hdet).manifold.Form k,
      (SmoothAtlas.presentation S hdet).manifold.IsSmoothForm theta ∧
        ∀ i p, p ∈ U i → theta p = eta i p :=
  existsUnique_smooth_gluing (SmoothAtlas.presentation S hdet).manifold U eta hopen hcover
    (dense_initialTorus S hdet) hsmooth hagree

end ClusterSkeleton.LocalFormGluing
