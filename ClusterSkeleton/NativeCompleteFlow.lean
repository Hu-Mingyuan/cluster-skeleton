import ClusterSkeleton.FiniteTimeConfinement
import FsFltz.Geometry.CollarSmoothEvolution
import FsFltz.Geometry.FlowBridge

/-! All-real native solutions and the complete flow of the exact global field. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped Manifold ContDiff Topology
open Set Filter Function FsFltz.Geometry

namespace ClusterSkeleton.NativeCompleteFlow

variable {d : ℕ} (S : Seed d) (hdet : S.Unimodular)

/-- Finite-horizon confinement supplies both splice centers in one compact set.
The uniform lifetime is used only on that compact set, never on the whole manifold. -/
theorem exists_global_integralCurve {ε κ δ : ℝ} (hε : 0 < ε)
    (hκ : 2*ε+1 ≤ κ) (hδ : 0 < δ) (p : S.Point) :
    letI := SmoothAtlas.charts S hdet
    ∃ γ : ℝ → S.Point, γ 0 = p ∧
      IsMIntegralCurve (I := 𝓘(ℝ, Model (2*d))) γ
        (GlobalLiouvilleField.Z S hdet ε κ hδ) := by
  letI := SmoothAtlas.charts S hdet
  letI := SmoothAtlas.smooth S hdet
  let v := GlobalLiouvilleField.Z S hdet ε κ hδ
  have hv := (GlobalLiouvilleField.isSmoothVectorField_Z S hdet hε hκ hδ).contMDiff_section
  have hv₁ := hv.of_le (show (1 : WithTop ℕ∞) ≤ ∞ by simp)
  obtain ⟨a₀, ha₀, hlocal⟩ :=
    CollarFlow.exists_compact_uniform_local_integralCurve hv₁ (isCompact_singleton (x := p))
  have hstart := hlocal p (mem_singleton p)
  let A : Set ℝ := {a | ∃ γ : ℝ → S.Point, γ 0 = p ∧
    IsMIntegralCurveOn γ v (Ioo (-a) a)}
  have ha₀A : a₀ ∈ A := hstart
  suffices hunbdd : ¬ BddAbove A by
    rw [not_bddAbove_iff] at hunbdd
    apply (exists_isMIntegralCurve_iff_exists_isMIntegralCurveOn_Ioo hv₁ p).mpr
    intro a
    obtain ⟨b, ⟨γ, hγ₀, hγ⟩, hab⟩ := hunbdd a
    exact ⟨γ, hγ₀, hγ.mono (Ioo_subset_Ioo (neg_le_neg hab.le) hab.le)⟩
  intro hbdd
  set α := sSup A with hα
  have ha₀α : a₀ ≤ α := le_csSup hbdd ha₀A
  have hαpos : 0 < α := ha₀.trans_le ha₀α
  obtain ⟨K, hK, hconf⟩ :=
    FiniteTimeConfinement.finite_time_compact_confinement S hdet hε hκ hδ p α hαpos.le
  obtain ⟨e, he, hKlocal⟩ := CollarFlow.exists_compact_uniform_local_integralCurve hv₁ hK
  let η := min e a₀
  have hη : 0 < η := lt_min he ha₀
  have hηe : η ≤ e := min_le_left _ _
  have hηα : η ≤ α := (min_le_right _ _).trans ha₀α
  have hlocalK (x : S.Point) (hx : x ∈ K) :
      ∃ γ : ℝ → S.Point, γ 0 = x ∧ IsMIntegralCurveOn γ v (Ioo (-η) η) := by
    obtain ⟨γ, hi, hg⟩ := hKlocal x hx
    exact ⟨γ, hi, hg.mono (Ioo_subset_Ioo (neg_le_neg hηe) hηe)⟩
  obtain ⟨a, ha, hlt⟩ := Real.add_neg_lt_sSup (⟨a₀, ha₀A⟩ : A.Nonempty)
    (ε := -(η/2)) (by linarith)
  rw [← hα, ← sub_eq_add_neg] at hlt
  obtain ⟨γ, h0, hγ⟩ := ha
  have ha : 0 < a := by linarith
  have hcenters : γ (-(α-η/2)) ∈ K ∧ γ (α-η/2) ∈ K := by
    constructor
    · apply hconf γ (Ioo (-a) a) 0 hγ isOpen_Ioo isPreconnected_Ioo
        ⟨by linarith, ha⟩ h0
      · constructor <;> linarith
      · rw [sub_zero, abs_neg, abs_of_nonneg (by linarith : 0 ≤ α-η/2)]
        linarith
    · apply hconf γ (Ioo (-a) a) 0 hγ isOpen_Ioo isPreconnected_Ioo
        ⟨by linarith, ha⟩ h0
      · constructor <;> linarith
      · rw [sub_zero, abs_of_nonneg (by linarith : 0 ≤ α-η/2)]
        linarith
  obtain ⟨γ₁aux, h₁aux, hγ₁⟩ := hlocalK _ hcenters.1
  rw [← isMIntegralCurveOn_comp_add (dt := α-η/2)] at hγ₁
  set γ₁ := γ₁aux ∘ (· + (α-η/2)) with hγ₁def
  have heq₁ : γ₁ (-(α-η/2)) = γ (-(α-η/2)) := by simp [hγ₁def, h₁aux]
  obtain ⟨γ₂aux, h₂aux, hγ₂⟩ := hlocalK _ hcenters.2
  rw [← isMIntegralCurveOn_comp_sub (dt := α-η/2)] at hγ₂
  set γ₂ := γ₂aux ∘ (· - (α-η/2)) with hγ₂def
  have heq₂ : γ₂ (α-η/2) = γ (α-η/2) := by simp [hγ₂def, h₂aux]
  simp_rw [mem_Ioo, ← sub_lt_iff_lt_add, ← lt_sub_iff_add_lt, ← mem_Ioo] at hγ₁
  simp_rw [mem_Ioo, lt_sub_iff_add_lt, sub_lt_iff_lt_add, ← mem_Ioo] at hγ₂
  let γext : ℝ → S.Point := piecewise (Ioo (-(α+η/2)) a)
    (piecewise (Ioo (-a) a) γ γ₁) γ₂
  have hext₀ : γext 0 = p := by
    dsimp only [γext]
    rw [piecewise, ite_eq_left ⟨by linarith, ha⟩, piecewise,
      ite_eq_left ⟨by linarith, ha⟩, h0]
  suffices hext : IsMIntegralCurveOn γext v (Ioo (-(α+η/2)) (α+η/2)) from
    (not_lt.mpr (le_csSup hbdd ⟨γext, hext₀, hext⟩)) (by linarith)
  apply (isMIntegralCurveOn_piecewise (t₀ := α-η/2) hv₁ _ hγ₂
      ⟨⟨by linarith, hlt⟩, ⟨by linarith, by linarith⟩⟩
      (by rw [piecewise, ite_eq_left ⟨by linarith, hlt⟩, ← heq₂])).mono
    (Ioo_subset_Ioo_union_Ioo le_rfl (by linarith) (by linarith))
  exact (isMIntegralCurveOn_piecewise (t₀ := -(α-η/2)) hv₁ hγ hγ₁
      ⟨⟨neg_lt_neg hlt, by linarith⟩, ⟨by linarith, by linarith⟩⟩ heq₁.symm).mono
    (union_comm _ _ ▸ Ioo_subset_Ioo_union_Ioo (by linarith) (by linarith) le_rfl)

/-- Native uniqueness and the pinned joint smooth-dependence theorem bundle the
proved all-real solutions into an actual two-sided flow of exactly `Z`. -/
theorem exists_completeLiouvilleFlow {ε κ δ : ℝ} (hε : 0 < ε)
    (hκ : 2*ε+1 ≤ κ) (hδ : 0 < δ) :
    Nonempty (CompleteLiouvilleFlow (SmoothAtlas.presentation S hdet).manifold
      (GlobalLiouvilleField.Z S hdet ε κ hδ)) := by
  letI := SmoothAtlas.charts S hdet
  letI := SmoothAtlas.smooth S hdet
  have hv := (GlobalLiouvilleField.isSmoothVectorField_Z S hdet hε hκ hδ).contMDiff_section
  have hv₁ := hv.of_le (show (1 : WithTop ℕ∞) ≤ ∞ by simp)
  choose γ hγ₀ hγ using exists_global_integralCurve S hdet hε hκ hδ
  let φ : ℝ → S.Point → S.Point := fun t x => γ x t
  have hself : ∀ x, φ 0 x = x := hγ₀
  have hcomp : ∀ s t x, φ (s+t) x = φ s (φ t x) := by
    intro s t x
    exact (congrFun (isMIntegralCurve_Ioo_eq_of_contMDiff_boundaryless
      (t₀ := 0) hv₁ (hγ (φ t x)) ((hγ x).comp_add t)
      (by simp only [comp_apply, zero_add, hγ₀]; rfl)) s).symm
  have hs := CollarFlow.contMDiff_joint_of_isMIntegralCurve hv φ hself hγ
  let F : Flow ℝ S.Point := ⟨φ, hs.continuous, hcomp, hself⟩
  refine ⟨⟨F, hs, ?_⟩⟩
  intro x
  exact (isMIntegralCurve_iff_chart_solves (SmoothAtlas.presentation S hdet).manifold
    (GlobalLiouvilleField.Z S hdet ε κ hδ) _
    ((hs.comp (contMDiff_id.prodMk contMDiff_const)).mdifferentiable (by simp))).mp (hγ x)

/-- Transparent chosen witness, justified by the preceding existence proof. -/
def completeFlow {ε κ δ : ℝ} (hε : 0 < ε) (hκ : 2*ε+1 ≤ κ) (hδ : 0 < δ) :
    CompleteLiouvilleFlow (SmoothAtlas.presentation S hdet).manifold
      (GlobalLiouvilleField.Z S hdet ε κ hδ) :=
  Classical.choice (exists_completeLiouvilleFlow S hdet hε hκ hδ)

/-- The constructed flow gives a global native solution through every shifted
initial time, with no restrictions on initial zero strata or partners. -/
theorem exists_global_integralCurve_through {ε κ δ : ℝ} (hε : 0 < ε)
    (hκ : 2*ε+1 ≤ κ) (hδ : 0 < δ) (p : S.Point) (t₀ : ℝ) :
    letI := SmoothAtlas.charts S hdet
    ∃ γ : ℝ → S.Point, γ t₀ = p ∧
      IsMIntegralCurve (I := 𝓘(ℝ, Model (2*d))) γ
        (GlobalLiouvilleField.Z S hdet ε κ hδ) := by
  letI := SmoothAtlas.charts S hdet
  let F := completeFlow S hdet hε hκ hδ
  refine ⟨fun t => F.flow (t-t₀) p, ?_, ?_⟩
  · simp only [sub_self, Flow.map_zero_apply]
  · exact isMIntegralCurve_comp_sub.mpr (F.isMIntegralCurve p)

/-- A native solution on an open interval extends through both omitted endpoints.
Agreement is obtained by native uniqueness; no endpoint values are assumed. -/
theorem exists_extension_Ioo {ε κ δ : ℝ} (hε : 0 < ε)
    (hκ : 2*ε+1 ≤ κ) (hδ : 0 < δ) {γ : ℝ → S.Point} {a b t₀ : ℝ}
    (ht₀ : t₀ ∈ Ioo a b)
    (hγ : letI := SmoothAtlas.charts S hdet
      IsMIntegralCurveOn (I := 𝓘(ℝ, Model (2*d))) γ
        (GlobalLiouvilleField.Z S hdet ε κ hδ) (Ioo a b)) :
    ∃ Γ : ℝ → S.Point, (letI := SmoothAtlas.charts S hdet
      IsMIntegralCurve (I := 𝓘(ℝ, Model (2*d))) Γ
        (GlobalLiouvilleField.Z S hdet ε κ hδ)) ∧
      EqOn Γ γ (Ioo a b) ∧ Γ t₀ = γ t₀ := by
  letI := SmoothAtlas.charts S hdet
  letI := SmoothAtlas.smooth S hdet
  obtain ⟨Γ, hi, hΓ⟩ := exists_global_integralCurve_through S hdet hε hκ hδ (γ t₀) t₀
  have hv := (GlobalLiouvilleField.isSmoothVectorField_Z S hdet hε hκ hδ).contMDiff_section
  exact ⟨Γ, hΓ, isMIntegralCurveOn_Ioo_eqOn_of_contMDiff_boundaryless ht₀
    (hv.of_le (by simp)) (hΓ.isMIntegralCurveOn _) hγ hi, hi⟩

end ClusterSkeleton.NativeCompleteFlow
