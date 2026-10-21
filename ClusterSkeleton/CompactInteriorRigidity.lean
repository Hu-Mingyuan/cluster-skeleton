import ClusterSkeleton.InteriorPartnerPropagation
import Mathlib.Topology.Sequences
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.InnerProductSpace.Calculus

/-! Compact forward orbits of the actual global native Liouville field.
The coordinate cap is not a premise. -/
noncomputable section
set_option autoImplicit false
set_option linter.style.haveILetI false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped Manifold ContDiff Topology BigOperators
open Set Filter FsFltz.Geometry

namespace ClusterSkeleton.CompactInteriorRigidity
open InteriorPartnerPropagation

/-- The concrete periodic cutoff has the sign of sine on the entire circle. -/
theorem sin_mul_vartheta_nonneg (δ θ : ℝ) :
    0 ≤ Real.sin θ * PrimitiveCutoffs.vartheta δ θ := by
  have h : 0 ≤ Real.sin θ * Real.arcsin (Real.sin θ) := by
    rcases le_total 0 (Real.sin θ) with h | h
    · exact mul_nonneg h (Real.arcsin_nonneg.mpr h)
    · exact mul_nonneg_of_nonpos_of_nonpos h (Real.arcsin_nonpos.mpr h)
  unfold PrimitiveCutoffs.vartheta
  rw [← mul_assoc]
  exact mul_nonneg h (PrimitiveCutoffs.angularWindow_nonneg δ θ)

/-- The polar identity makes the sign argument independent of an angle lift. -/
theorem neg_im_mul_vartheta_arg_nonneg (δ : ℝ) (z : ℂ) :
    0 ≤ -z.im * PrimitiveCutoffs.vartheta δ (Complex.arg (-z)) := by
  have hpolar : ‖z‖ * Real.sin (Complex.arg (-z)) = -z.im := by
    simpa only [norm_neg, Complex.neg_im] using Complex.norm_mul_sin_arg (-z)
  rw [← hpolar, mul_assoc]
  exact mul_nonneg (norm_nonneg z) (sin_mul_vartheta_nonneg δ _)

/-- Native differentiation of the squared distance to the angular equilibrium. -/
theorem angular_distance_sq_hasDerivAt {q : ℝ → ℂ} {δ t c : ℝ}
    (h : HasDerivAt q
      (Complex.I * q t * (c : ℂ) *
        (PrimitiveCutoffs.vartheta δ (Complex.arg (-q t)) : ℂ)) t) :
    HasDerivAt (fun u => ‖q u + 1‖ ^ 2)
      (2 * c * (- (q t).im * PrimitiveCutoffs.vartheta δ (Complex.arg (-q t)))) t := by
  convert (h.add_const (1 : ℂ)).norm_sq using 1
  simp only [Complex.inner, Complex.mul_re,
    Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.add_re, Complex.add_im, Complex.one_re, Complex.one_im,
    Complex.conj_re, Complex.conj_im]
  ring

/-- Convergence to the equilibrium and a nonnegative angular coefficient force
exact equality, without choosing or differentiating a branch of `arg`. -/
theorem angular_scalar_eq_neg_one_of_tendsto
    {q : ℝ → ℂ} {c : ℝ → ℝ} {δ a : ℝ}
    (hd : ∀ t, a ≤ t → HasDerivAt q
      (Complex.I * q t * (c t : ℂ) *
        (PrimitiveCutoffs.vartheta δ (Complex.arg (-q t)) : ℂ)) t)
    (hc : ∀ t, a ≤ t → 0 ≤ c t)
    (hl : Tendsto q atTop (𝓝 (-1))) :
    ∀ t, a ≤ t → q t = -1 := by
  let F : ℝ → ℝ := fun t => ‖q t + 1‖ ^ 2
  let D : ℝ → ℝ := fun t => 2 * c t *
    (-(q t).im * PrimitiveCutoffs.vartheta δ (Complex.arg (-q t)))
  have hF (t : ℝ) (ht : a ≤ t) : HasDerivAt F (D t) t :=
    angular_distance_sq_hasDerivAt (hd t ht)
  have hD (t : ℝ) (ht : a ≤ t) : 0 ≤ D t :=
    mul_nonneg (mul_nonneg (by norm_num) (hc t ht))
      (neg_im_mul_vartheta_arg_nonneg δ (q t))
  have hm : MonotoneOn F (Ici a) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici a)
    · exact fun t ht => (hF t ht).continuousAt.continuousWithinAt
    · exact fun t ht => (hF t (interior_subset ht)).hasDerivWithinAt
    · exact fun t ht => hD t (interior_subset ht)
  have hlim : Tendsto F atTop (𝓝 0) := by
    simpa [F] using (hl.add_const (1 : ℂ)).norm.pow 2
  intro t ht
  have hf : F t ≤ 0 := ge_of_tendsto hlim (by
    filter_upwards [eventually_ge_atTop t] with u hu
    exact hm ht (ht.trans hu) hu)
  have hz : ‖q t + 1‖ = 0 := by
    dsimp [F] at hf
    nlinarith [norm_nonneg (q t + 1)]
  exact eq_neg_of_add_eq_zero_left (norm_eq_zero.mp hz)

/-- Reverse the finite time interval and use the already accepted scalar
Gronwall uniqueness. This covers arbitrary continuous coefficients and collars. -/
theorem angular_scalar_eq_neg_one_backward
    {q c : ℝ → ℂ} {δ a b : ℝ} (hab : a ≤ b)
    (hq : ContinuousOn q (Icc a b)) (hc : ContinuousOn c (Icc a b))
    (hd : ∀ t ∈ Icc a b, HasDerivAt q
      (Complex.I * q t * c t *
        (PrimitiveCutoffs.vartheta δ (Complex.arg (-q t)) : ℂ)) t)
    (hb : q b = -1) : q a = -1 := by
  let r : ℝ → ℂ := fun u => q (b-u)
  let e : ℝ → ℂ := fun u => -c (b-u)
  have hmap : MapsTo (fun u : ℝ => b-u) (Icc 0 (b-a)) (Icc a b) := by
    intro u hu
    constructor <;> dsimp at * <;> linarith [hu.1, hu.2]
  have hr : ContinuousOn r (Icc 0 (b-a)) :=
    hq.comp (continuous_const.sub continuous_id).continuousOn hmap
  have he : ContinuousOn e (Icc 0 (b-a)) :=
    (hc.comp (continuous_const.sub continuous_id).continuousOn hmap).neg
  have hdr (u : ℝ) (hu : u ∈ Ico 0 (b-a)) :
      HasDerivAt r
        (Complex.I * r u * e u *
          (PrimitiveCutoffs.vartheta δ (Complex.arg (-r u)) : ℂ)) u := by
    have h := (hd (b-u) (hmap ⟨hu.1, hu.2.le⟩)).comp_const_sub b u
    convert h using 1
    dsimp [r, e]
    ring
  have h := angular_scalar_eq_neg_one_of_hasDerivAt hr he hdr
    (by simpa [r] using hb) (b-a) ⟨sub_nonneg.mpr hab, le_rfl⟩
  simpa [r] using h

variable {d : ℕ} (S : Seed d)

/-- Along the selected coordinate line the full row sum vanishes by skew symmetry. -/
theorem row_single (i : Fin d) (a : ℝ) :
    (∑ j : Fin d, (S.B i j : ℝ) * (Pi.single i a : Fin d → ℝ) j) = 0 := by
  classical
  have hdiag : S.B i i = 0 := by have hh := S.skew i i; omega
  rw [Finset.sum_eq_single i]
  · simp [hdiag]
  · intro j _ hji
    simp [Pi.single_eq_of_ne hji]
  · simp

/-- In the concrete deep radial region, the amplitude restricted to the
selected coordinate line is exactly the affine function `a + κ`. -/
theorem amplitude_single_deep {ε κ a : ℝ}
    (hε : 0 < ε) (hκ : 2 * ε < κ) (i : Fin d)
    (ha : a ≤ -PrimitiveCutoffs.radialLength ε κ - 2 * ε) :
    TorusLiouvilleDynamics.amplitude S ε κ i (Pi.single i a) = a + κ := by
  classical
  have hdiag : S.B i i = 0 := by have hh := S.skew i i; omega
  have hL := PrimitiveCutoffs.radial_length_pos hκ
  have hdom : DominanceCutoff.dominance S ε i (Pi.single i a) = 1 := by
    apply DominanceCutoff.dominance_eq_one_of S hε
    intro j hj
    have hji : j ≠ i := by
      intro he
      subst j
      exact ((DominanceCutoff.mem_mutableNeighbors S i i).mp hj).2 hdiag
    simp only [Pi.single_eq_same, Pi.single_eq_of_ne hji, sub_zero]
    linarith
  rw [TorusLiouvilleDynamics.amplitude, Pi.single_eq_same, hdom,
    row_single S i a, PrimitiveCutoffs.rho_eq_one (by simp),
    PrimitiveCutoffs.radial_tail hκ ha]
  ring

/-- Strict depth gives a neighborhood on which the restricted amplitude is
exactly affine, so its actual native derivative is one. -/
theorem characterCoefficient_eq_one_deep {ε κ a : ℝ}
    (hε : 0 < ε) (hκ : 2 * ε < κ) (i : Fin d)
    (ha : a < -PrimitiveCutoffs.radialLength ε κ - 2 * ε) :
    characterCoefficient S ε κ i a = 1 := by
  classical
  have he : (fun x : ℝ => TorusLiouvilleDynamics.amplitude S ε κ i (Pi.single i x))
      =ᶠ[𝓝 a] (fun x => x + κ) := by
    filter_upwards [eventually_lt_nhds ha] with x hx
    exact amplitude_single_deep S hε hκ i hx.le
  have hs : HasDerivAt (fun x : ℝ => (Pi.single i x : Fin d → ℝ))
      (Pi.single i (1 : ℝ)) a := by
    simpa using ((ContinuousLinearMap.single ℝ (fun _ : Fin d => ℝ) i).hasFDerivAt
      (x := a)).hasDerivAt
  have hd := (((TorusLiouvilleDynamics.amplitude_smooth S ε κ i).differentiable
    (by simp) (Pi.single i a)).hasFDerivAt).comp_hasDerivAt a hs
  have heq := he.deriv_eq
  rw [show deriv (fun x : ℝ => TorusLiouvilleDynamics.amplitude S ε κ i
      (Pi.single i x)) a = characterCoefficient S ε κ i a by
        simpa [Function.comp_def, characterCoefficient] using hd.deriv] at heq
  simpa using heq

end ClusterSkeleton.CompactInteriorRigidity

namespace ClusterSkeleton.CompactInteriorRigidity

variable {d : ℕ} (S : Seed d) (hdet : S.Unimodular)
variable {ε κ δ t₀ η : ℝ} (hε : 0 < ε) (hκ : 2 * ε + 1 ≤ κ)
  (hδ : 0 < δ) (hη : 0 < η) {γ : ℝ → S.Point}
  (hγ : letI := SmoothAtlas.charts S hdet
    IsMIntegralCurveOn (I := 𝓘(ℝ, Model (2*d))) γ
      (GlobalLiouvilleField.Z S hdet ε κ hδ) (Ioi (t₀ - η)))
  (hK : IsCompact (closure (γ '' Ici t₀)))

include hdet hε hκ hδ hη hγ hK

/-- Compactness excludes positive initial logarithmic radius at every original coordinate. -/
theorem original_norm_le_one (j : Fin d) : ‖(γ t₀).a j‖ ≤ 1 := by
  by_contra h
  exact NativeRadialOrbit.not_isCompact_closure_forward_image S hdet hε hκ hδ hη hγ
    j (lt_of_not_ge h) hK

omit hK in
/-- Strictly interior originals tend to zero, including originals already zero initially. -/
theorem interior_norm_tendsto_zero (j : Fin d) (hj : ‖(γ t₀).a j‖ < 1) :
    Tendsto (fun t => ‖(γ (t₀+t)).a j‖) atTop (𝓝 0) := by
  by_cases hz : (γ t₀).a j = 0
  · apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    have he := (ZeroStratumInvariance.coordinate_zero_iff S hdet hε hκ hδ hγ
      isPreconnected_Ioi (show t₀ ∈ Ioi (t₀-η) by change t₀-η < t₀; linarith)
      (show t₀+t ∈ Ioi (t₀-η) by change t₀-η < t₀+t; linarith) j).mp hz
    simp [he]
  · exact (NativeRadialOrbit.negative_log_laws S hdet hε hκ hδ hη hγ j hz
      (Real.log_neg (norm_pos_iff.mpr hz) hj)).2.2.2.2.2

/-- One compact accumulation point simultaneously vanishes at every initially interior
original. Its topology is the inherited topology of the literal exchange variety. -/
theorem exists_limit_zero_at_interior :
    ∃ p ∈ closure (γ '' Ici t₀), ∀ j : Fin d, ‖(γ t₀).a j‖ < 1 → p.a j = 0 := by
  obtain ⟨p, hp, φ, hφ, hlim⟩ := hK.tendsto_subseq
    (x := fun n : ℕ => γ (t₀ + (n : ℝ)))
    (fun n => subset_closure ⟨t₀ + (n : ℝ), by simp, rfl⟩)
  refine ⟨p, hp, ?_⟩
  intro j hj
  have ht : Tendsto (fun n : ℕ => (φ n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hφ.tendsto_atTop
  have hz := (interior_norm_tendsto_zero S hdet hε hκ hδ hη hγ j hj).comp ht
  have hpj := ((continuous_originalCoordinate S j).norm.tendsto p).comp hlim
  exact norm_eq_zero.mp (tendsto_nhds_unique hpj hz)

/-- Nonzero frozen variables on a compact forward orbit necessarily have unit norm. -/
theorem frozen_norm_eq_one (f : Fin d) (hf : f ∉ S.mutable) : ‖(γ t₀).a f‖ = 1 := by
  apply le_antisymm (original_norm_le_one S hdet hε hκ hδ hη hγ hK f)
  by_contra h
  obtain ⟨p, _, hp⟩ := exists_limit_zero_at_interior S hdet hε hκ hδ hη hγ hK
  exact p.frozen_ne_zero f hf (hp f (lt_of_not_ge h))

/-- Acyclic zero-set independence at the accumulation point forces independence of
all initially strict-interior coordinates, without a cap or partner-zero premise. -/
theorem interior_matrix_eq_zero (i j : Fin d)
    (hi : ‖(γ t₀).a i‖ < 1) (hj : ‖(γ t₀).a j‖ < 1) : S.B i j = 0 := by
  obtain ⟨p, _, hp⟩ := exists_limit_zero_at_interior S hdet hε hκ hδ hη hγ hK
  exact p.matrix_eq_zero_of_coordinates_zero i j (hp i hi) (hp j hj)

/-- All full-row neighbors of an initial strict-interior coordinate have unit norm. -/
theorem initial_neighbor_unit (i j : Fin d) (hi : ‖(γ t₀).a i‖ < 1)
    (hij : S.B i j ≠ 0) : ‖(γ t₀).a j‖ = 1 := by
  apply le_antisymm (original_norm_le_one S hdet hε hκ hδ hη hγ hK j)
  by_contra h
  exact hij (interior_matrix_eq_zero S hdet hε hκ hδ hη hγ hK i j hi (lt_of_not_ge h))

/-- Native zero-log rigidity propagates the unit-neighbor conclusion from compactness. -/
theorem neighbors_unit_forward (i : Fin d) (hi : ‖(γ t₀).a i‖ < 1)
    {t : ℝ} (ht : 0 ≤ t) (j : Fin d) (hij : S.B i j ≠ 0) :
    ‖(γ (t₀+t)).a j‖ = 1 :=
  InteriorPartnerPropagation.unit_norm_forward S hdet hε hκ hδ hη hγ j
    (initial_neighbor_unit S hdet hε hκ hδ hη hγ hK i j hi hij) ht

/-- The genuine angular derivative follows from compactness, the full-row neighbor
conclusion, and the native manifold chain rule; no cap membership is assumed. -/
theorem shifted_character_hasDerivAt (i : S.Mutable)
    (hi : (γ t₀).a i ≠ 0) (hr : ‖(γ t₀).a i‖ < 1)
    {t : ℝ} (ht : 0 ≤ t) :
    HasDerivAt (fun u => exchangeCharacter (γ (t₀+u)) i)
      (Complex.I * exchangeCharacter (γ (t₀+t)) i *
        (InteriorPartnerPropagation.characterCoefficient S ε κ i
          (GlobalLiouvilleField.A S (γ (t₀+t)) i) : ℂ) *
        (PrimitiveCutoffs.vartheta δ (Complex.arg (-exchangeCharacter (γ (t₀+t)) i)) : ℂ)) t := by
  letI := SmoothAtlas.charts S hdet
  have htime : t₀ - η < t₀+t := by linarith
  have hn := NativeRadialOrbit.coordinate_ne_zero S hdet hε hκ hδ hη hγ i hi htime
  have hrow := neighbors_unit_forward S hdet hε hκ hδ hη hγ hK i hr ht
  have hnonzero (j : Fin d) (hj : S.B i j ≠ 0) : (γ (t₀+t)).a j ≠ 0 := by
    intro he
    have hu := hrow j hj
    simp [he] at hu
  have hd := LocalAngularDynamics.hasDerivWithinAt_complex_along_integralCurve
    (SmoothAtlas.presentation S hdet).manifold hγ htime
    (InteriorPartnerPropagation.mdifferentiableAt_character_row S hdet _ i hnonzero)
  have hdA := hd.hasDerivAt (isOpen_Ioi.mem_nhds htime)
  rw [InteriorPartnerPropagation.differential_character_of_unit_neighbors S hdet
    hε hκ hδ _ i hn hrow] at hdA
  convert! hdA.scomp t ((hasDerivAt_id t).const_add t₀) using 1 <;>
    simp [InteriorPartnerPropagation.characterCoefficient, TorusCorrection.angular]

omit hdet hε hκ hδ hη hγ hK in
/-- The actual negative exchange monomial has unit norm when every row neighbor does. -/
theorem negativeMonomial_norm_eq_one (p : S.Point) (i : Fin d)
    (hrow : ∀ j, S.B i j ≠ 0 → ‖p.a j‖ = 1) :
    ‖S.negativeMonomial p.a i‖ = 1 := by
  classical
  simp only [Seed.negativeMonomial, norm_prod, norm_pow]
  apply Finset.prod_eq_one
  intro j _
  by_cases hj : S.B i j = 0
  · simp [hj]
  · simp [hrow j hj]

/-- Compactness bounds the raw partner. The derived unit denominator transfers that
bound to the normalized exchange product, which tends to zero with the original. -/
theorem character_tendsto_neg_one (i : S.Mutable) (hr : ‖(γ t₀).a i‖ < 1) :
    Tendsto (fun t => exchangeCharacter (γ (t₀+t)) i) atTop (𝓝 (-1)) := by
  have hb : Continuous (fun p : S.Point => ‖p.b i‖) :=
    ((continuous_apply i).comp continuous_subtype_val.snd).norm
  obtain ⟨M, hM⟩ := hK.bddAbove_image hb.continuousOn
  have hbound (t : ℝ) (ht : 0 ≤ t) : ‖(γ (t₀+t)).b i‖ ≤ M :=
    hM ⟨γ (t₀+t), subset_closure ⟨t₀+t, by change t₀ ≤ t₀+t; linarith, rfl⟩, rfl⟩
  have heq (t : ℝ) (ht : 0 ≤ t) :
      ‖exchangeCharacter (γ (t₀+t)) i + 1‖ =
        ‖(γ (t₀+t)).a i‖ * ‖(γ (t₀+t)).b i‖ := by
    have hrow := neighbors_unit_forward S hdet hε hκ hδ hη hγ hK i hr ht
    have hQ := negativeMonomial_norm_eq_one S (γ (t₀+t)) i hrow
    have hn : S.negativeMonomial (γ (t₀+t)).a i ≠ 0 :=
      norm_ne_zero_iff.mp (by rw [hQ]; norm_num)
    have he : exchangeCharacter (γ (t₀+t)) i + 1 =
        (γ (t₀+t)).a i * normalizedPartner (γ (t₀+t)) i := by
      unfold exchangeCharacter normalizedPartner
      rw [← mul_div_assoc, (γ (t₀+t)).exchange i, add_div, div_self hn]
    rw [he, norm_mul, normalizedPartner, norm_div, hQ, div_one]
  have hlim : Tendsto (fun t => ‖exchangeCharacter (γ (t₀+t)) i + 1‖)
      atTop (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _))
      (g := fun t => ‖(γ (t₀+t)).a i‖ * M)
    · filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
      rw [heq t ht]
      exact mul_le_mul_of_nonneg_left (hbound t ht) (norm_nonneg _)
    · simpa using (interior_norm_tendsto_zero S hdet hε hκ hδ hη hγ i hr).mul_const M
  have hz : Tendsto (fun t => exchangeCharacter (γ (t₀+t)) i + 1) atTop (𝓝 0) :=
    tendsto_zero_iff_norm_tendsto_zero.mpr hlim
  simpa using hz.sub_const 1

/-- Eventual deep-radius dynamics force the character to equal -1, and native
finite-interval uniqueness propagates that conclusion through the initial collar. -/
theorem character_eq_neg_one_initial (i : S.Mutable)
    (hi : (γ t₀).a i ≠ 0) (hr : ‖(γ t₀).a i‖ < 1) :
    exchangeCharacter (γ t₀) i = -1 := by
  let q : ℝ → ℂ := fun u => exchangeCharacter (γ (t₀+u)) i
  let c : ℝ → ℝ := fun u => InteriorPartnerPropagation.characterCoefficient S ε κ i
    (GlobalLiouvilleField.A S (γ (t₀+u)) i)
  have hd (u : ℝ) (hu : 0 ≤ u) : HasDerivAt q
      (Complex.I * q u * (c u : ℂ) *
        (PrimitiveCutoffs.vartheta δ (Complex.arg (-q u)) : ℂ)) u :=
    shifted_character_hasDerivAt S hdet hε hκ hδ hη hγ hK i hi hr hu
  have hbot := (NativeRadialOrbit.negative_log_laws S hdet hε hκ hδ hη hγ i hi
    (Real.log_neg (norm_pos_iff.mpr hi) hr)).2.2.2.2.1
  obtain ⟨T, hT⟩ := eventually_atTop.mp
    (hbot.eventually_lt_atBot (-PrimitiveCutoffs.radialLength ε κ - 2*ε))
  let b : ℝ := max 0 T
  have hb : 0 ≤ b := le_max_left _ _
  have htail : ∀ u, b ≤ u → q u = -1 :=
    angular_scalar_eq_neg_one_of_tendsto
      (fun u hu => hd u (hb.trans hu))
      (fun u hu => by
        dsimp [c]
        rw [characterCoefficient_eq_one_deep S hε (by linarith) i
          (hT u ((le_max_right _ _).trans hu))]
        norm_num)
      (character_tendsto_neg_one S hdet hε hκ hδ hη hγ hK i hr)
  have hq : ContinuousOn q (Icc 0 b) :=
    fun u hu => (hd u hu.1).continuousAt.continuousWithinAt
  have hc : ContinuousOn (fun u => (c u : ℂ)) (Icc 0 b) := by
    intro u hu
    exact (Complex.continuous_ofReal.continuousAt.comp
      ((InteriorPartnerPropagation.characterCoefficient_continuous S ε κ i).continuousAt.comp
        (NativeRadialOrbit.shifted_hasDerivAt_A S hdet hε hκ hδ hη hγ i hi hu.1).continuousAt)).continuousWithinAt
  have hz := angular_scalar_eq_neg_one_backward hb hq hc (fun u hu => hd u hu.1)
    (htail b le_rfl)
  simpa [q] using hz

/-- Compact forward closure forces both partners of every selected initially
nonzero strict-interior original to vanish. No cap or angular law is supplied. -/
theorem initial_partners_zero (i : S.Mutable)
    (hi : (γ t₀).a i ≠ 0) (hr : ‖(γ t₀).a i‖ < 1) :
    normalizedPartner (γ t₀) i = 0 ∧ (γ t₀).b i = 0 := by
  apply InteriorPartnerPropagation.partners_zero_of_character S (γ t₀) i hi
  · intro j hj hz
    have hu := initial_neighbor_unit S hdet hε hκ hδ hη hγ hK i j hr hj
    simp [hz] at hu
  · exact character_eq_neg_one_initial S hdet hε hκ hδ hη hγ hK i hi hr

end ClusterSkeleton.CompactInteriorRigidity

namespace ClusterSkeleton

/-- The exact mission target, kept separate from any proof. -/
def CompactInteriorRigidityTarget
    {d : ℕ} (S : Seed d) (hdet : S.Unimodular) : Prop :=
  ∀ {ε κ δ t₀ η : ℝ}
    (hε : 0 < ε) (hκ : 2 * ε + 1 ≤ κ)
    (hδ : 0 < δ) (hη : 0 < η)
    {γ : ℝ → S.Point},
    (letI := SmoothAtlas.charts S hdet;
      IsMIntegralCurveOn (I := 𝓘(ℝ, Model (2*d))) γ
        (GlobalLiouvilleField.Z S hdet ε κ hδ)
        (Set.Ioi (t₀ - η))) →
    IsCompact (closure (γ '' Set.Ici t₀)) →
    ∀ i : S.Mutable, (γ t₀).a i ≠ 0 → ‖(γ t₀).a i‖ < 1 →
      normalizedPartner (γ t₀) i = 0 ∧ (γ t₀).b i = 0

/-- Proof of the exact compact-orbit strict-interior rigidity target. -/
theorem compactInteriorRigidityTarget {d : ℕ} (S : Seed d) (hdet : S.Unimodular) :
    CompactInteriorRigidityTarget S hdet := by
  intro ε κ δ t₀ η hε hκ hδ hη γ hγ hK i hi hr
  exact CompactInteriorRigidity.initial_partners_zero S hdet hε hκ hδ hη hγ hK i hi hr

end ClusterSkeleton
