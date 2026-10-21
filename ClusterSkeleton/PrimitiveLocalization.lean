import ClusterSkeleton.PrimitiveCutoffs
import ClusterSkeleton.DominanceCutoff
import ClusterSkeleton.NodeCoordinates
import ClusterSkeleton.NodeLogExtension
import ClusterSkeleton.SmoothAtlas

/-! Simultaneous scalar localization in Lemma 2.4, on actual exchange points.
The per-index factors are independent of any global primitive. -/
noncomputable section
open Set Filter
open scoped Topology BigOperators Manifold
open FsFltz.Geometry (Model)

namespace ClusterSkeleton.PrimitiveLocalization
open PrimitiveCutoffs DominanceCutoff
variable {d : ℕ} {S : Seed d}

/-- The full matrix row, including all frozen coordinates. -/
def rowLog (p : S.Point) (i : Fin d) : ℝ :=
  ∑ j, (S.B i j : ℝ) * logNorms S p j

/-- The principal representative of the manuscript circle-valued angle. -/
def angle (p : S.Point) (i : Fin d) : ℝ :=
  (Complex.log (-exchangeCharacter p i)).im

/-- The accepted raw normalized-node logarithm. -/
def nodeLog (p : S.Point) (i : S.Mutable) : ℂ :=
  Complex.log (1 - p.a i * normalizedPartner p i)

/-- The literal individual scalar correction from (2.7). -/
def correction (ε κ δ : ℝ) (i : S.Mutable) (p : S.Point) : ℝ :=
  radial ε κ (logNorms S p i) * dominance S ε i (logNorms S p) *
    rho (rowLog p i) * vartheta δ (angle p i)

/-- The local affine expression; it is used only on the torus part. -/
def affineCorrection (κ : ℝ) (i : S.Mutable) (p : S.Point) : ℝ :=
  (logNorms S p i + κ) * (nodeLog p i).im

theorem neg_character_node {I : Finset (Fin d)} (hI : S.Independent I)
    {p : S.Point} (hp : p ∈ candidateChartLocus S I)
    (i : S.Mutable) (hi : (i : Fin d) ∈ I) :
    -exchangeCharacter p i = 1 - p.a i * normalizedPartner p i := by
  rw [normalized_node_equation hI hp i hi]
  ring

theorem rowLog_eq_log_re {p : S.Point} (hp : p ∈ initialTorus S) (i : Fin d) :
    rowLog p i = (Complex.log (-exchangeCharacter p i)).re := by
  rw [Complex.log_re, norm_neg, exchangeCharacter_eq_zpow_product, norm_prod]
  rw [Real.log_prod (fun j _ => norm_ne_zero_iff.mpr (zpow_ne_zero _ (hp j)))]
  simp only [norm_zpow, Real.log_zpow, rowLog, logNorms]

theorem continuous_negativeMonomial (i : Fin d) :
    Continuous (fun p : S.Point => S.negativeMonomial p.a i) := by
  apply continuous_finsetProd
  intro j _
  exact (continuous_originalCoordinate S j).pow _

theorem continuousAt_normalizedPartner {I : Finset (Fin d)} (hI : S.Independent I)
    {p : S.Point} (hp : p ∈ candidateChartLocus S I)
    (i : S.Mutable) (hi : (i : Fin d) ∈ I) :
    ContinuousAt (fun q : S.Point => normalizedPartner q i) p := by
  apply ContinuousAt.div
  · exact ((continuous_apply i).comp (continuous_snd.comp continuous_subtype_val)).continuousAt
  · exact (continuous_negativeMonomial (S := S) i.val).continuousAt
  · exact negativeMonomial_ne_zero_on_independent_locus hI hp hi

theorem mem_zero_locus (p : S.Point) : p ∈ candidateChartLocus S p.zeroSet := by
  intro j hj hz
  apply hj
  apply (p.mem_zeroSet j).2
  exact ⟨by by_contra hf; exact p.frozen_ne_zero j hf hz, hz⟩

/-- Strict conditions, expressed without a logarithm of a vanishing radius. -/
def region (ε κ δ : ℝ) (p : S.Point) : Set S.Point :=
  localizationNeighborhood S ε p ∩ candidateChartLocus S p.zeroSet ∩
    {q | ∀ i : S.Mutable, (i : Fin d) ∈ p.zeroSet →
      (q.a i, normalizedPartner q i) ∈ nodeLogDomain ∧
      |(nodeLog q i).re| < 1 ∧
      |(nodeLog q i).im| < angularRadius δ / 2 ∧
      ‖q.a i‖ < Real.exp (-radialLength ε κ - 2 * ε)}

theorem region_mem_nhds (ε κ : ℝ) {δ : ℝ} (hδ : 0 < δ) (p : S.Point) :
    region ε κ δ p ∈ 𝓝 p := by
  have hp := mem_zero_locus p
  have hall : ∀ i : S.Mutable, ∀ hi : (i : Fin d) ∈ p.zeroSet,
      ∀ᶠ q in 𝓝 p, (q.a i, normalizedPartner q i) ∈ nodeLogDomain ∧
        |(nodeLog q i).re| < 1 ∧
        |(nodeLog q i).im| < angularRadius δ / 2 ∧
        ‖q.a i‖ < Real.exp (-radialLength ε κ - 2 * ε) := by
    intro i hi
    have hz : p.a i = 0 := ((p.mem_zeroSet i).1 hi).2
    have hn := continuousAt_normalizedPartner p.zeroSet_independent hp i hi
    have ha : ContinuousAt (fun q : S.Point => q.a i) p :=
      (continuous_originalCoordinate S i).continuousAt
    have hd : (p.a i, normalizedPartner p i) ∈ nodeLogDomain := by
      rw [hz]; exact zero_mem_nodeLogDomain _
    have hl : ContinuousAt (fun q : S.Point => nodeLog q i) p := by
      apply ContinuousAt.comp (f := fun q : S.Point => 1 - q.a i * normalizedPartner q i)
      · exact continuousAt_clog hd
      · exact continuousAt_const.sub (ha.mul hn)
    have hzero : nodeLog p i = 0 := by simp [nodeLog, hz]
    have he := (isOpen_nodeLogDomain.mem_nhds hd)
    have hdom := (ha.prodMk hn).eventually he
    have hr := (Complex.continuous_re.continuousAt.comp hl).abs.eventually_lt_const (show |(nodeLog p i).re| < 1 by simp [hzero])
    have ht := (Complex.continuous_im.continuousAt.comp hl).abs.eventually_lt_const (show |(nodeLog p i).im| < angularRadius δ / 2 by
      simpa [hzero] using half_pos (angularRadius_pos hδ))
    have hrad := ha.norm.eventually_lt_const
      (show ‖p.a i‖ < Real.exp (-radialLength ε κ - 2 * ε) by
        simpa [hz] using Real.exp_pos (-radialLength ε κ - 2 * ε))
    filter_upwards [hdom, hr, ht, hrad] with q h1 h2 h3 h4
    exact ⟨h1, h2, h3, h4⟩
  have hf : ∀ᶠ q in 𝓝 p, ∀ i : S.Mutable, ∀ hi : (i : Fin d) ∈ p.zeroSet,
      (q.a i, normalizedPartner q i) ∈ nodeLogDomain ∧
        |(nodeLog q i).re| < 1 ∧ |(nodeLog q i).im| < angularRadius δ / 2 ∧
        ‖q.a i‖ < Real.exp (-radialLength ε κ - 2 * ε) :=
    eventually_all.mpr (fun i => eventually_all.mpr (hall i))
  filter_upwards [(isOpen_localizationNeighborhood S ε p).mem_nhds
    (mem_localizationNeighborhood S ε p), (isOpen_candidateChartLocus S p.zeroSet).mem_nhds hp,
    hf] with q h1 h2 h3
  exact ⟨⟨h1, h2⟩, h3⟩

/-- One open actual-point neighborhood for all zero indices, including the empty case. -/
def neighborhood (ε κ δ : ℝ) (p : S.Point) : Set S.Point :=
  interior (region ε κ δ p)

theorem isOpen_neighborhood (ε κ δ : ℝ) (p : S.Point) :
    IsOpen (neighborhood ε κ δ p) := isOpen_interior

theorem mem_neighborhood (ε κ : ℝ) {δ : ℝ} (hδ : 0 < δ) (p : S.Point) :
    p ∈ neighborhood ε κ δ p :=
  mem_interior_iff_mem_nhds.mpr (region_mem_nhds ε κ hδ p)

theorem neighborhood_subset_region (ε κ δ : ℝ) (p : S.Point) :
    neighborhood ε κ δ p ⊆ region ε κ δ p := interior_subset

theorem node_bridges {ε κ δ : ℝ} {p q : S.Point}
    (hq : q ∈ neighborhood ε κ δ p) (i : S.Mutable) (hi : (i : Fin d) ∈ p.zeroSet) :
    S.negativeMonomial q.a i ≠ 0 ∧
    -exchangeCharacter q i = 1 - q.a i * normalizedPartner q i ∧
    (q.a i, normalizedPartner q i) ∈ nodeLogDomain ∧
    -exchangeCharacter q i ∈ Complex.slitPlane ∧
    angle q i = (nodeLog q i).im ∧
    (q ∈ initialTorus S → rowLog q i = (nodeLog q i).re) := by
  have hr := neighborhood_subset_region ε κ δ p hq
  have he := neg_character_node p.zeroSet_independent hr.1.2 i hi
  have hd := (hr.2 i hi).1
  refine ⟨negativeMonomial_ne_zero_on_independent_locus p.zeroSet_independent hr.1.2 hi,
    he, hd, ?_, ?_, ?_⟩
  · rw [he]; exact hd
  · simp only [angle, nodeLog, he]
  · intro ht
    rw [rowLog_eq_log_re ht, he]
    rfl

/-- All four plateau equalities hold simultaneously on the torus part. -/
theorem plateaus {ε κ δ : ℝ} (hε : 0 < ε) (hκ : 2 * ε + 1 ≤ κ) (hδ : 0 < δ)
    {p q : S.Point} (hq : q ∈ neighborhood ε κ δ p) (ht : q ∈ initialTorus S)
    (i : S.Mutable) (hi : (i : Fin d) ∈ p.zeroSet) :
    dominance S ε i (logNorms S q) = 1 ∧ rho (rowLog q i) = 1 ∧
    vartheta δ (angle q i) = angle q i ∧
    radial ε κ (logNorms S q i) = logNorms S q i + κ := by
  have hr := neighborhood_subset_region ε κ δ p hq
  have hb := node_bridges hq i hi
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply dominance_eq_one_of S hε
    intro j hj
    exact (logNorms_sub_lt S hr.1.1 ht hi hj).le
  · apply rho_eq_one
    rw [hb.2.2.2.2.2 ht]
    exact (hr.2 i hi).2.1.le
  · apply vartheta_eq_self hδ
    rw [hb.2.2.2.2.1]
    exact (hr.2 i hi).2.2.1.le
  · apply radial_tail (by linarith)
    have hl := Real.log_lt_log (norm_pos_iff.mpr (ht i)) (hr.2 i hi).2.2.2
    rw [Real.log_exp] at hl
    exact hl.le

theorem adjacent_dominance_zero {ε κ δ : ℝ} (hε : 0 < ε)
    {p q : S.Point} (hq : q ∈ neighborhood ε κ δ p) (ht : q ∈ initialTorus S)
    (j : S.Mutable) (hj : ∃ i ∈ p.zeroSet, S.B i j ≠ 0) :
    dominance S ε j (logNorms S q) = 0 := by
  rcases hj with ⟨i, hi, hij⟩
  have hr := neighborhood_subset_region ε κ δ p hq
  have hone : dominance S ε i (logNorms S q) = 1 := by
    apply dominance_eq_one_of S hε
    intro k hk
    exact (logNorms_sub_lt S hr.1.1 ht hi hk).le
  rcases adjacent_exclusion S hε i j ((p.mem_zeroSet i).1 hi).1 j.property hij
    (logNorms S q) with h | h
  · exact (one_ne_zero (hone.symm.trans h)).elim
  · exact h

theorem correction_eq_affine {ε κ δ : ℝ} (hε : 0 < ε)
    (hκ : 2 * ε + 1 ≤ κ) (hδ : 0 < δ) {p q : S.Point}
    (hq : q ∈ neighborhood ε κ δ p) (ht : q ∈ initialTorus S)
    (i : S.Mutable) (hi : (i : Fin d) ∈ p.zeroSet) :
    correction ε κ δ i q = affineCorrection κ i q := by
  obtain ⟨hd, hr, ha, hh⟩ := plateaus hε hκ hδ hq ht i hi
  unfold correction affineCorrection
  rw [hd, hr, ha, hh, mul_one, mul_one, (node_bridges hq i hi).2.2.2.2.1]

theorem adjacent_correction_zero {ε κ δ : ℝ} (hε : 0 < ε) {p q : S.Point}
    (hq : q ∈ neighborhood ε κ δ p) (ht : q ∈ initialTorus S)
    (j : S.Mutable) (hj : ∃ i ∈ p.zeroSet, S.B i j ≠ 0) :
    correction ε κ δ j q = 0 := by
  simp only [correction, adjacent_dominance_zero hε hq ht j hj, mul_zero, zero_mul]

/-- Equality of actual functions on a native open neighborhood of every torus point. -/
theorem correction_eventuallyEq {ε κ δ : ℝ} (hε : 0 < ε)
    (hκ : 2 * ε + 1 ≤ κ) (hδ : 0 < δ) {p q : S.Point}
    (hq : q ∈ neighborhood ε κ δ p) (ht : q ∈ initialTorus S)
    (i : S.Mutable) (hi : (i : Fin d) ∈ p.zeroSet) :
    correction ε κ δ i =ᶠ[𝓝 q] affineCorrection κ i := by
  filter_upwards [(isOpen_neighborhood ε κ δ p).mem_nhds hq,
    (isOpen_initialTorus S).mem_nhds ht] with r hr hrt
  exact correction_eq_affine hε hκ hδ hr hrt i hi

theorem adjacent_correction_eventuallyEq {ε κ δ : ℝ} (hε : 0 < ε)
    {p q : S.Point} (hq : q ∈ neighborhood ε κ δ p) (ht : q ∈ initialTorus S)
    (j : S.Mutable) (hj : ∃ i ∈ p.zeroSet, S.B i j ≠ 0) :
    correction ε κ δ j =ᶠ[𝓝 q] fun _ => 0 := by
  filter_upwards [(isOpen_neighborhood ε κ δ p).mem_nhds hq,
    (isOpen_initialTorus S).mem_nhds ht] with r hr hrt
  exact adjacent_correction_zero hε hr hrt j hj

/-- Native manifold differentials on the constructed actual-point atlas. -/
theorem correction_mfderiv_eq (hdet : S.Unimodular) {ε κ δ : ℝ} (hε : 0 < ε)
    (hκ : 2 * ε + 1 ≤ κ) (hδ : 0 < δ) {p q : S.Point}
    (hq : q ∈ neighborhood ε κ δ p) (ht : q ∈ initialTorus S)
    (i : S.Mutable) (hi : (i : Fin d) ∈ p.zeroSet) :
    letI := SmoothAtlas.charts S hdet
    mfderiv 𝓘(ℝ, Model (2 * d)) 𝓘(ℝ, ℝ) (correction ε κ δ i) q =
      mfderiv 𝓘(ℝ, Model (2 * d)) 𝓘(ℝ, ℝ) (affineCorrection κ i) q := by
  letI := SmoothAtlas.charts S hdet
  exact (correction_eventuallyEq hε hκ hδ hq ht i hi).mfderiv_eq

theorem adjacent_correction_mfderiv_eq_zero (hdet : S.Unimodular) {ε κ δ : ℝ}
    (hε : 0 < ε) {p q : S.Point} (hq : q ∈ neighborhood ε κ δ p)
    (ht : q ∈ initialTorus S) (j : S.Mutable)
    (hj : ∃ i ∈ p.zeroSet, S.B i j ≠ 0) :
    letI := SmoothAtlas.charts S hdet
    mfderiv 𝓘(ℝ, Model (2 * d)) 𝓘(ℝ, ℝ) (correction ε κ δ j) q = 0 := by
  letI := SmoothAtlas.charts S hdet
  calc
    _ = mfderiv 𝓘(ℝ, Model (2 * d)) 𝓘(ℝ, ℝ) (fun _ : S.Point => (0 : ℝ)) q :=
      (adjacent_correction_eventuallyEq hε hq ht j hj).mfderiv_eq
    _ = 0 := mfderiv_const

end ClusterSkeleton.PrimitiveLocalization
