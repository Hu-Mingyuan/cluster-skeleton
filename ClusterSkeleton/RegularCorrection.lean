import ClusterSkeleton.TorusCorrection
import ClusterSkeleton.PrimitiveLocalization

/-! The surviving correction of Lemma 2.4, on the actual independent loci. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology BigOperators
open Set Filter FsFltz.Geometry

namespace ClusterSkeleton.RegularCorrection
open PrimitiveCutoffs DominanceCutoff PrimitiveLocalization
variable {d : ℕ} (S : Seed d)

/-- Mutable vertices outside I whose full row vanishes on I. -/
def surviving (I : Finset (Fin d)) : Finset S.Mutable :=
  Finset.univ.filter fun j => (j : Fin d) ∉ I ∧ ∀ i ∈ I, S.B j i = 0

@[simp] theorem mem_surviving (I : Finset (Fin d)) (j : S.Mutable) :
    j ∈ surviving S I ↔ (j : Fin d) ∉ I ∧ ∀ i ∈ I, S.B j i = 0 := by
  simp [surviving]

/-- The existing literal corrections, with no modified boundary convention.
Each summand carries the symmetrizer weight `d_j` of the weighted
`TorusCorrection.H`; the scalar `correction` itself is unweighted. -/
def regularH (I : Finset (Fin d)) (ε κ δ : ℝ) (p : S.Point) : ℝ :=
  ∑ j ∈ surviving S I, (S.D j : ℝ) * correction ε κ δ j p

theorem support_nonzero {I : Finset (Fin d)} {j : S.Mutable}
    (hj : j ∈ surviving S I) {p : S.Point} (hp : p ∈ candidateChartLocus S I) :
    p.a j ≠ 0 ∧ ∀ k : Fin d, S.B j k ≠ 0 → p.a k ≠ 0 := by
  obtain ⟨hjI, hrow⟩ := (mem_surviving S I j).mp hj
  exact ⟨hp j hjI, fun k hk => hp k (fun hkI => hk (hrow k hkI))⟩

/-- Character exponents on I are removed before nonvanishing is invoked. -/
theorem character_nonzero {I : Finset (Fin d)} {j : S.Mutable}
    (hj : j ∈ surviving S I) {p : S.Point} (hp : p ∈ candidateChartLocus S I) :
    exchangeCharacter p j ≠ 0 := by
  rw [exchangeCharacter_eq_zpow_product]
  apply Finset.prod_ne_zero_iff.mpr
  intro k _
  by_cases h : S.B j k = 0
  · simp [show S.E k j = 0 from h]
  · exact zpow_ne_zero _ ((support_nonzero S hj hp).2 k h)

variable (hdet : S.Unimodular)

theorem contMDiffAt_log_coordinate {p : S.Point} (k : Fin d) (hk : p.a k ≠ 0) :
    letI := SmoothAtlas.charts S hdet
    ContMDiffAt 𝓘(ℝ, Model (2*d)) 𝓘(ℝ, ℝ) ∞ (fun q => logNorms S q k) p := by
  letI := SmoothAtlas.charts S hdet
  exact ((contDiffAt_norm ℂ (n := ∞) hk).log (norm_ne_zero_iff.mpr hk)).comp_contMDiffAt
    (f := fun q : S.Point => q.a k)
    ((ContinuousLinearMap.proj k : (Fin d → ℂ) →L[ℝ] ℂ).contMDiff.comp
      (TorusNondegeneracy.original_smooth S (SmoothAtlas.presentation S hdet)) p)

/-- The full row is smooth; zero coefficients are eliminated individually. -/
theorem contMDiffAt_row {I : Finset (Fin d)} {j : S.Mutable}
    (hj : j ∈ surviving S I) {p : S.Point} (hp : p ∈ candidateChartLocus S I) :
    letI := SmoothAtlas.charts S hdet
    ContMDiffAt 𝓘(ℝ, Model (2*d)) 𝓘(ℝ, ℝ) ∞ (fun q => PrimitiveLocalization.rowLog q j) p := by
  letI := SmoothAtlas.charts S hdet
  unfold PrimitiveLocalization.rowLog
  apply ContMDiffAt.sum
  intro k _
  by_cases h : S.B j k = 0
  · simp only [h, Int.cast_zero, zero_mul]
    exact contMDiffAt_const
  · exact contMDiffAt_const.mul (contMDiffAt_log_coordinate S hdet k
      ((support_nonzero S hj hp).2 k h))

theorem contMDiffAt_dominance {I : Finset (Fin d)} {j : S.Mutable}
    (hj : j ∈ surviving S I) {p : S.Point} (hp : p ∈ candidateChartLocus S I) (ε : ℝ) :
    letI := SmoothAtlas.charts S hdet
    ContMDiffAt 𝓘(ℝ, Model (2*d)) 𝓘(ℝ, ℝ) ∞
      (fun q => dominance S ε j (logNorms S q)) p := by
  letI := SmoothAtlas.charts S hdet
  unfold dominance
  apply ContMDiffAt.prod
  intro k hk
  exact (contDiff_chi ε).comp_contMDiffAt
    ((contMDiffAt_log_coordinate S hdet j (support_nonzero S hj hp).1).sub
      (contMDiffAt_log_coordinate S hdet k
        ((support_nonzero S hj hp).2 k ((mem_mutableNeighbors S j k).mp hk).2)))

theorem contMDiffAt_character {I : Finset (Fin d)} {j : S.Mutable}
    (hj : j ∈ surviving S I) {p : S.Point} (hp : p ∈ candidateChartLocus S I) :
    letI := SmoothAtlas.charts S hdet
    ContMDiffAt 𝓘(ℝ, Model (2*d)) 𝓘(ℝ, ℂ) ∞ (fun q => exchangeCharacter q j) p := by
  letI := SmoothAtlas.charts S hdet
  have hP : ContDiff ℂ ∞ (fun x : Fin d → ℂ => S.positiveMonomial x j) := by
    apply contDiff_prod
    intro k _
    exact (contDiff_apply ℂ ℂ k).pow _
  have hQ : ContDiff ℂ ∞ (fun x : Fin d → ℂ => S.negativeMonomial x j) := by
    apply contDiff_prod
    intro k _
    exact (contDiff_apply ℂ ℂ k).pow _
  have hn : S.negativeMonomial p.a j ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro k _
    by_cases h : S.B j k = 0
    · simp [show S.E k j = 0 from h]
    · exact pow_ne_zero _ ((support_nonzero S hj hp).2 k h)
  exact ((hP.contDiffAt.div hQ.contDiffAt hn).restrict_scalars ℝ).comp_contMDiffAt
    (TorusNondegeneracy.original_smooth S (SmoothAtlas.presentation S hdet) p)

theorem contMDiffAt_correction {I : Finset (Fin d)} {j : S.Mutable}
    (hj : j ∈ surviving S I) {p : S.Point} (hp : p ∈ candidateChartLocus S I)
    (ε κ : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    letI := SmoothAtlas.charts S hdet
    ContMDiffAt 𝓘(ℝ, Model (2*d)) 𝓘(ℝ, ℝ) ∞ (correction ε κ δ j) p := by
  letI := SmoothAtlas.charts S hdet
  have ha : ContMDiffAt 𝓘(ℝ, Model (2*d)) 𝓘(ℝ, ℝ) ∞
      (fun q => vartheta δ (angle q j)) p := by
    simp only [angle, Complex.log_im]
    exact (TorusCorrection.vartheta_arg_contDiffAt hδ
      (neg_ne_zero.mpr (character_nonzero S hj hp))).comp_contMDiffAt
      (f := fun q : S.Point => -exchangeCharacter q j)
      (contMDiffAt_character S hdet hj hp).neg
  exact ((((radial_smooth ε κ).comp_contMDiffAt
    (contMDiffAt_log_coordinate S hdet j (support_nonzero S hj hp).1)).mul
      (contMDiffAt_dominance S hdet hj hp ε)).mul
      (rho_smooth.comp_contMDiffAt (contMDiffAt_row S hdet hj hp))).mul ha

/-- Smooth at boundary points of the torus, on the entire open coordinate locus. -/
theorem contMDiffOn_regularH (I : Finset (Fin d)) (_hI : S.Independent I)
    (ε κ : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    letI := SmoothAtlas.charts S hdet
    ContMDiffOn 𝓘(ℝ, Model (2*d)) 𝓘(ℝ, ℝ) ∞ (regularH S I ε κ δ)
      (candidateChartLocus S I) := by
  letI := SmoothAtlas.charts S hdet
  intro p hp
  exact (ContMDiffAt.sum fun j hj =>
    contMDiffAt_const.mul (contMDiffAt_correction S hdet hj hp ε κ hδ)).contMDiffWithinAt

/-- Local chart calculus uses only regularity on the open locus. -/
theorem contDiffAt_differential_inChart (I : Finset (Fin d)) (f : S.Point → ℝ) :
    letI := SmoothAtlas.charts S hdet
    ContMDiffOn 𝓘(ℝ, Model (2*d)) 𝓘(ℝ, ℝ) ∞ f (candidateChartLocus S I) →
    ∀ (a : S.Point) (y : Model (2*d))
      (hy : y ∈ (chartAt (Model (2*d)) a).target)
      (hp : (chartAt (Model (2*d)) a).symm y ∈ candidateChartLocus S I),
      ContDiffAt ℝ ∞ ((SmoothAtlas.presentation S hdet).manifold.formInChart a
        (covectorForm _ (differentialCovector _ f))) y := by
  letI := SmoothAtlas.charts S hdet
  letI := SmoothAtlas.smooth S hdet
  intro hf a y hy hp
  let M := (SmoothAtlas.presentation S hdet).manifold
  let c := chartAt (Model (2*d)) a
  have hfa (p : S.Point) (hp : p ∈ candidateChartLocus S I) :
      ContMDiffAt 𝓘(ℝ, Model (2*d)) 𝓘(ℝ, ℝ) ∞ f p :=
    hf.contMDiffAt ((isOpen_candidateChartLocus S I).mem_nhds hp)
  have hc : ContMDiffAt 𝓘(ℝ, Model (2*d)) 𝓘(ℝ, Model (2*d)) ∞ c.symm y :=
    (contMDiffOn_chart_symm (I := 𝓘(ℝ, Model (2*d))) (x := a)).contMDiffAt
      (c.open_target.mem_nhds hy)
  have hg : ContDiffAt ℝ ∞ (f ∘ c.symm) y := ((hfa _ hp).comp y hc).contDiffAt
  have he : M.formInChart a (covectorForm M (differentialCovector M f)) =ᶠ[𝓝 y]
      fun z => ContinuousAlternatingMap.ofSubsingleton ℝ _ ℝ (0 : Fin 1)
        (fderiv ℝ (f ∘ c.symm) z) := by
    have hn := (c.continuousAt_symm hy).preimage_mem_nhds
      ((isOpen_candidateChartLocus S I).mem_nhds hp)
    filter_upwards [c.open_target.mem_nhds hy, hn] with z hz hzp
    have hd := mfderiv_comp z ((hfa _ hzp).mdifferentiableAt (by simp))
      ((mdifferentiable_chart (I := 𝓘(ℝ, Model (2*d))) a).mdifferentiableAt_symm hz)
    rw [mfderiv_eq_fderiv] at hd
    ext v
    exact congrArg (fun L => L (v 0)) hd.symm
  exact (((ContinuousAlternatingMap.ofSubsingletonLIE
    (𝕜 := ℝ) (E := Model (2*d)) (F := ℝ) (0 : Fin 1)).contDiff.contDiffAt).comp y
      (hg.fderiv_right (by simp))).congr_of_eventuallyEq he

/-- The actual native differential, converted to the pinned one-form interface. -/
def regularForm (I : Finset (Fin d)) (ε κ δ : ℝ) :
    (SmoothAtlas.presentation S hdet).manifold.Form 1 :=
  covectorForm _ (differentialCovector _ (regularH S I ε κ δ))

theorem regularForm_smooth (I : Finset (Fin d)) (hI : S.Independent I)
    (ε κ : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    letI := SmoothAtlas.charts S hdet
    ∀ (a : S.Point) (y : Model (2*d))
      (hy : y ∈ (chartAt (Model (2*d)) a).target)
      (hp : (chartAt (Model (2*d)) a).symm y ∈ candidateChartLocus S I),
      ContDiffAt ℝ ∞ ((SmoothAtlas.presentation S hdet).manifold.formInChart a
        (regularForm S hdet I ε κ δ)) y :=
  contDiffAt_differential_inChart S hdet I _ (contMDiffOn_regularH S hdet I hI ε κ hδ)

variable {S}

/-- The original H and the existing localization corrections agree literally,
each weighted by its symmetrizer entry `d_j`. -/
theorem H_eq_sum (ε κ δ : ℝ) (p : S.Point) :
    TorusCorrection.H S ε κ δ p =
      ∑ j : S.Mutable, (S.D j : ℝ) * correction ε κ δ j p := by
  classical
  simp only [TorusCorrection.H, correction, TorusCorrection.A, logNorms,
    TorusCorrection.rowLog, PrimitiveLocalization.rowLog, TorusCorrection.angular,
    angle, Complex.log_im]
  exact Finset.sum_subtype S.mutable (fun _ => Iff.rfl) _

/-- The affine zero-index sum, with the accepted normalized-node logarithm and
the same symmetrizer weights as `regularH`. -/
def singularH (I : Finset (Fin d)) (κ : ℝ) (p : S.Point) : ℝ :=
  ∑ j ∈ (Finset.univ.filter fun j : S.Mutable => (j : Fin d) ∈ I),
    (S.D j : ℝ) * affineCorrection κ j p

/-- The exact three-way partition: zero, adjacent (zero correction), surviving. -/
theorem H_split {ε κ δ : ℝ} (hε : 0 < ε) (hκ : 2 * ε + 1 ≤ κ) (hδ : 0 < δ)
    {p q : S.Point} (hq : q ∈ neighborhood ε κ δ p) (ht : q ∈ initialTorus S) :
    TorusCorrection.H S ε κ δ q = singularH p.zeroSet κ q + regularH S p.zeroSet ε κ δ q := by
  classical
  rw [H_eq_sum]
  unfold singularH regularH
  rw [← Finset.sum_ite_mem_eq (surviving S p.zeroSet)]
  simp only [Finset.sum_filter]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : (j : Fin d) ∈ p.zeroSet
  · have hnot : j ∉ surviving S p.zeroSet := by simp [hj]
    simp only [hj, hnot, if_true, if_false, add_zero]
    rw [(correction_eventuallyEq hε hκ hδ hq ht j hj).self_of_nhds]
  · by_cases hs : j ∈ surviving S p.zeroSet
    · simp [hj, hs]
    · have hadj : ∃ i ∈ p.zeroSet, S.B i j ≠ 0 := by
        have hn : ¬ ∀ i ∈ p.zeroSet, S.B j i = 0 :=
          fun h => hs ((mem_surviving S p.zeroSet j).mpr ⟨hj, h⟩)
        push_neg at hn
        obtain ⟨i, hi, hij⟩ := hn
        refine ⟨i, hi, ?_⟩
        intro h
        exact hij ((S.B_eq_zero_iff i j).mp h)
      simp only [hj, hs, if_false, add_zero]
      rw [(adjacent_correction_eventuallyEq hε hq ht j hadj).self_of_nhds, mul_zero]

/-- A genuine germ at every torus point of the already constructed open U_p. -/
theorem H_eventuallyEq {ε κ δ : ℝ} (hε : 0 < ε) (hκ : 2 * ε + 1 ≤ κ) (hδ : 0 < δ)
    {p q : S.Point} (hq : q ∈ neighborhood ε κ δ p) (ht : q ∈ initialTorus S) :
    TorusCorrection.H S ε κ δ =ᶠ[𝓝 q]
      fun r => singularH p.zeroSet κ r + regularH S p.zeroSet ε κ δ r := by
  filter_upwards [(isOpen_neighborhood ε κ δ p).mem_nhds hq,
    (isOpen_initialTorus S).mem_nhds ht] with r hr hrt
  exact H_split hε hκ hδ hr hrt

/-- Equality of native covectors, hence valid on every native tangent vector. -/
theorem differential_H_split {ε κ δ : ℝ} (hε : 0 < ε)
    (hκ : 2 * ε + 1 ≤ κ) (hδ : 0 < δ) {p q : S.Point}
    (hq : q ∈ neighborhood ε κ δ p) (ht : q ∈ initialTorus S) :
    differentialCovector (SmoothAtlas.presentation S hdet).manifold (TorusCorrection.H S ε κ δ) q =
    differentialCovector (SmoothAtlas.presentation S hdet).manifold
      (fun r => singularH p.zeroSet κ r + regularH S p.zeroSet ε κ δ r) q := by
  letI := SmoothAtlas.charts S hdet
  exact (H_eventuallyEq hε hκ hδ hq ht).mfderiv_eq

theorem regularH_empty (ε κ δ : ℝ) : regularH S ∅ ε κ δ = TorusCorrection.H S ε κ δ := by
  funext p
  rw [H_eq_sum]
  simp [regularH, surviving]

theorem regularH_no_survivors (I : Finset (Fin d)) (h : surviving S I = ∅)
    (ε κ δ : ℝ) : regularH S I ε κ δ = fun _ => 0 := by
  funext p
  simp [regularH, h]

theorem literal_formula (I : Finset (Fin d)) (ε κ δ : ℝ) (p : S.Point) :
    regularH S I ε κ δ p = ∑ j ∈ surviving S I, (S.D j : ℝ) *
      (radial ε κ (Real.log ‖p.a j‖) *
      dominance S ε j (fun k => Real.log ‖p.a k‖) *
      rho (∑ k : Fin d, (S.B j k : ℝ) * Real.log ‖p.a k‖) *
      vartheta δ (Complex.arg (-exchangeCharacter p j))) := by
  simp only [regularH, correction, PrimitiveLocalization.rowLog, logNorms, angle, Complex.log_im]
  rfl

end ClusterSkeleton.RegularCorrection

