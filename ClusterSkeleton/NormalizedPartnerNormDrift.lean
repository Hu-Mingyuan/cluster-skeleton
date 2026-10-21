import ClusterSkeleton.BoundaryTangency
import Mathlib.Geometry.Manifold.IntegralCurve.Basic

/-! Native squared-norm dynamics of normalized partners on the open node neighborhoods. -/
noncomputable section
set_option autoImplicit false
set_option linter.style.haveILetI false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology BigOperators ComplexConjugate
open Set Filter FsFltz.Geometry

namespace ClusterSkeleton.NormalizedPartnerNormDrift

variable {d : ℕ} (S : Seed d) (hdet : S.Unimodular)

/-- Smoothness of the actual normalized partner; its monomial denominator is nonzero here. -/
theorem partner_smooth {I : Finset (Fin d)} (hI : S.Independent I)
    (i : S.Mutable) (hi : (i : Fin d) ∈ I) (q : S.Point)
    (hq : q ∈ candidateChartLocus S I) :
    letI := SmoothAtlas.charts S hdet
    ContMDiffAt 𝓘(ℝ, Model (2*d)) 𝓘(ℝ, ℂ) ∞ (fun r => normalizedPartner r i) q := by
  letI := SmoothAtlas.charts S hdet
  exact (ContinuousLinearMap.snd ℝ ℂ ℂ).contDiff.contDiffAt.contMDiffAt.comp q
    (NativeNodePrimitive.nodeMap_smooth S hdet hI i hi q hq)

/-- The second component is the native complex differential of the partner. -/
theorem differential_partner {I : Finset (Fin d)} (hI : S.Independent I)
    (i : S.Mutable) (hi : (i : Fin d) ∈ I) (q : S.Point)
    (hq : q ∈ candidateChartLocus S I)
    (v : (SmoothAtlas.presentation S hdet).manifold.Tangent q) :
    complexDifferential (SmoothAtlas.presentation S hdet).manifold
      (fun r => normalizedPartner r i) q v =
      (NativeNodePrimitive.nodeDifferential S hdet i q v).2 := by
  letI := SmoothAtlas.charts S hdet
  have hc := mfderiv_comp q
    ((ContinuousLinearMap.snd ℝ ℂ ℂ).differentiableAt.mdifferentiableAt)
    ((NativeNodePrimitive.nodeMap_smooth S hdet hI i hi q hq).mdifferentiableAt (by simp))
  rw [mfderiv_eq_fderiv, ContinuousLinearMap.fderiv] at hc
  exact congrArg (fun D => D v) hc

/-- Real smoothness of the literal squared complex norm, including at zero. -/
theorem normSq_smooth : ContDiff ℝ ∞ (fun b : ℂ => Complex.normSq b) := by
  have hr := Complex.reCLM.contDiff (n := ∞)
  have hi := Complex.imCLM.contDiff (n := ∞)
  exact (hr.mul hr).add (hi.mul hi)

/-- Native scalar chain rule, without dividing by the partner. -/
theorem scalarDerivative_normSq {n : ℕ} (M : SmoothManifold n)
    {f : M.Point → ℂ} {q : M.Point}
    (hf : MDifferentiableAt 𝓘(ℝ, Model n) 𝓘(ℝ, ℂ) f q) (v : M.Tangent q) :
    M.scalarDerivative (fun r => Complex.normSq (f r)) q v =
      2 * (conj (f q) * complexDifferential M f q v).re := by
  have hr := Complex.reCLM.hasFDerivAt (x := f q)
  have hi := Complex.imCLM.hasFDerivAt (x := f q)
  have hn := ((hr.mul hr).add (hi.mul hi)).hasMFDerivAt.comp q hf.hasMFDerivAt
  change mfderiv 𝓘(ℝ, Model n) 𝓘(ℝ, ℝ) (fun r => Complex.normSq (f r)) q v = _
  erw [hn.mfderiv]
  change (f q).re * (complexDifferential M f q v).re +
    (f q).re * (complexDifferential M f q v).re +
    ((f q).im * (complexDifferential M f q v).im +
      (f q).im * (complexDifferential M f q v).im) = _
  simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring

theorem partner_normSq_smooth {I : Finset (Fin d)} (hI : S.Independent I)
    (i : S.Mutable) (hi : (i : Fin d) ∈ I) (q : S.Point)
    (hq : q ∈ candidateChartLocus S I) :
    letI := SmoothAtlas.charts S hdet
    ContMDiffAt 𝓘(ℝ, Model (2*d)) 𝓘(ℝ, ℝ) ∞
      (fun r => Complex.normSq (normalizedPartner r i)) q := by
  letI := SmoothAtlas.charts S hdet
  exact normSq_smooth.contDiffAt.contMDiffAt.comp q (partner_smooth S hdet hI i hi q hq)

/-- The removable logarithmic quotient is smooth on the proved principal-log domain. -/
theorem quotient_smooth {ε κ δ : ℝ} (p : S.Point)
    (i : S.Mutable) (hi : (i : Fin d) ∈ p.zeroSet)
    (q : S.Point) (hq : q ∈ LocalPrimitive.neighborhood S ε κ δ p) :
    letI := SmoothAtlas.charts S hdet
    ContMDiffAt 𝓘(ℝ, Model (2*d)) 𝓘(ℝ, ℂ) ∞
      (fun r => nodeLogQuotient (r.a i, normalizedPartner r i)) q := by
  letI := SmoothAtlas.charts S hdet
  exact (contDiffOn_nodeLogQuotient.contDiffAt
    (isOpen_nodeLogDomain.mem_nhds (hq.2.2 i hi))).contMDiffAt.comp q
      (NativeNodePrimitive.nodeMap_smooth S hdet p.zeroSet_independent i hi q hq.2.1)

/-- Algebraic extraction of the partner derivative uses only a nonzero original coordinate. -/
theorem partner_drift_of_ne_zero {ε κ δ : ℝ} (hε : 0 < ε) (hκ : 2*ε+1 ≤ κ)
    (hδ : 0 < δ) (p q : S.Point)
    (hq : q ∈ LocalPrimitive.neighborhood S ε κ δ p)
    (i : S.Mutable) (hi : (i : Fin d) ∈ p.zeroSet) (ha : q.a i ≠ 0) :
    BoundaryTangency.drift S hdet ε κ hδ (fun r => normalizedPartner r i) q =
      (q.a i * normalizedPartner q i - 1) * nodeLogQuotient (q.a i, normalizedPartner q i) -
        normalizedPartner q i *
          ((SmoothAtlas.presentation S hdet).coordinateDifferential i q
            (GlobalLiouvilleField.Z S hdet ε κ hδ q) / q.a i) := by
  have hp := BoundaryTangency.nodeProduct_drift S hdet hε hκ hδ p q hq i hi
  unfold BoundaryTangency.drift at hp ⊢
  rw [BoundaryTangency.differential_nodeProduct S hdet p.zeroSet_independent i hi q hq.2.1,
    ← differential_partner S hdet p.zeroSet_independent i hi q hq.2.1] at hp
  change normalizedPartner q i * _ + q.a i * _ =
    (q.a i * normalizedPartner q i - 1) * Complex.log (1 - q.a i * normalizedPartner q i) at hp
  rw [← mul_nodeLogQuotient (q.a i, normalizedPartner q i)] at hp
  apply (mul_left_cancel₀ ha)
  field_simp
  linear_combination hp

/-- A real pairing eliminates the angular component, even for a zero partner. -/
theorem pairing_sub (b c u : ℂ) (κ : ℝ) (hu : u.re = -κ) :
    2 * (conj b * (c - b * u)).re = 2 * (conj b * c).re + 2 * κ * Complex.normSq b := by
  simp only [Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im,
    Complex.conj_re, Complex.conj_im, Complex.normSq_apply, hu]
  ring

/-- Norm drift at selected nonzero coordinates, allowing every other mutable zero. -/
theorem normSq_drift_of_ne_zero {ε κ δ : ℝ} (hε : 0 < ε) (hκ : 2*ε+1 ≤ κ)
    (hδ : 0 < δ) (p q : S.Point)
    (hq : q ∈ LocalPrimitive.neighborhood S ε κ δ p)
    (i : S.Mutable) (hi : (i : Fin d) ∈ p.zeroSet) (ha : q.a i ≠ 0) :
    (SmoothAtlas.presentation S hdet).manifold.scalarDerivative
      (fun r => Complex.normSq (normalizedPartner r i)) q
      (GlobalLiouvilleField.Z S hdet ε κ hδ q) =
      2 * (conj (normalizedPartner q i) * (q.a i * normalizedPartner q i - 1) *
        nodeLogQuotient (q.a i, normalizedPartner q i)).re +
          2 * κ * Complex.normSq (normalizedPartner q i) := by
  letI := SmoothAtlas.charts S hdet
  rw [scalarDerivative_normSq _
    ((partner_smooth S hdet p.zeroSet_independent i hi q hq.2.1).mdifferentiableAt (by simp))]
  change 2 * (conj (normalizedPartner q i) *
    BoundaryTangency.drift S hdet ε κ hδ (fun r => normalizedPartner r i) q).re = _
  rw [partner_drift_of_ne_zero S hdet hε hκ hδ p q hq i hi ha]
  have hu := BoundaryTangency.deep_radius S hdet hε hκ hδ p q hq i hi ha
  rw [GlobalLiouvilleField.L_eq_logarithmicComponents S hdet ε κ hδ q i ha] at hu
  simpa only [mul_assoc] using pairing_sub (normalizedPartner q i)
    ((q.a i * normalizedPartner q i - 1) * nodeLogQuotient (q.a i, normalizedPartner q i))
    ((SmoothAtlas.presentation S hdet).coordinateDifferential i q
      (GlobalLiouvilleField.Z S hdet ε κ hδ q) / q.a i) κ hu

/-- Both sides are continuous on the actual OPEN neighborhood, so torus density
extends the scalar identity across all simultaneous zero coordinates. -/
theorem normSq_drift {ε κ δ : ℝ} (hε : 0 < ε) (hκ : 2*ε+1 ≤ κ)
    (hδ : 0 < δ) (p q : S.Point)
    (hq : q ∈ LocalPrimitive.neighborhood S ε κ δ p)
    (i : S.Mutable) (hi : (i : Fin d) ∈ p.zeroSet) :
    (SmoothAtlas.presentation S hdet).manifold.scalarDerivative
      (fun r => Complex.normSq (normalizedPartner r i)) q
      (GlobalLiouvilleField.Z S hdet ε κ hδ q) =
      2 * (conj (normalizedPartner q i) * (q.a i * normalizedPartner q i - 1) *
        nodeLogQuotient (q.a i, normalizedPartner q i)).re +
          2 * κ * Complex.normSq (normalizedPartner q i) := by
  letI := SmoothAtlas.charts S hdet
  let U := LocalPrimitive.neighborhood S ε κ δ p
  have hU : IsOpen U := LocalPrimitive.isOpen_neighborhood S ε κ δ p
  have hf : ContMDiffOn 𝓘(ℝ, Model (2*d)) 𝓘(ℝ, ℝ) ∞
      (fun r => Complex.normSq (normalizedPartner r i)) U :=
    fun r hr => (partner_normSq_smooth S hdet p.zeroSet_independent i hi r hr.2.1).contMDiffWithinAt
  have hD := GlobalLiouvilleField.contMDiffOn_scalarDerivative
    (SmoothAtlas.presentation S hdet).manifold
    (GlobalLiouvilleField.isSmoothVectorField_Z S hdet hε hκ hδ) hU hf
  have hb : ContinuousOn (fun r : S.Point => normalizedPartner r i) U :=
    fun r hr => (partner_smooth S hdet p.zeroSet_independent i hi r hr.2.1).continuousAt.continuousWithinAt
  have ha := (continuous_originalCoordinate S i).continuousOn (s := U)
  have hQ : ContinuousOn (fun r : S.Point => nodeLogQuotient (r.a i, normalizedPartner r i)) U :=
    fun r hr => (quotient_smooth S hdet p i hi r hr).continuousAt.continuousWithinAt
  have hR := ((Complex.reCLM.continuous.comp_continuousOn
    (((Complex.conjCLE.continuous.comp_continuousOn hb).mul
      ((ha.mul hb).sub (continuousOn_const (c := (1 : ℂ))))).mul hQ)).const_mul 2).add
        (hf.continuousOn.const_mul (2*κ))
  have he : EqOn
      (fun r => (SmoothAtlas.presentation S hdet).manifold.scalarDerivative
        (fun s => Complex.normSq (normalizedPartner s i)) r
        (GlobalLiouvilleField.Z S hdet ε κ hδ r))
      (fun r => 2 * (conj (normalizedPartner r i) * (r.a i * normalizedPartner r i - 1) *
        nodeLogQuotient (r.a i, normalizedPartner r i)).re + 2*κ*Complex.normSq (normalizedPartner r i))
      (U ∩ initialTorus S) :=
    fun r hr => normSq_drift_of_ne_zero S hdet hε hκ hδ p r hr.1 i hi (hr.2 i)
  exact he.of_subset_closure hD.continuousOn hR inter_subset_left
    (fun r hr => hU.inter_closure ⟨hr, dense_initialTorus S hdet r⟩) hq

/-- Exact squared-norm law at EVERY zero-coordinate point, including a zero partner. -/
theorem normSq_drift_zero {ε κ δ : ℝ} (hε : 0 < ε) (hκ : 2*ε+1 ≤ κ)
    (hδ : 0 < δ) (q : S.Point) (i : S.Mutable) (ha : q.a i = 0) :
    (SmoothAtlas.presentation S hdet).manifold.scalarDerivative
      (fun r => Complex.normSq (normalizedPartner r i)) q
      (GlobalLiouvilleField.Z S hdet ε κ hδ q) =
        2 * (1 + κ) * Complex.normSq (normalizedPartner q i) := by
  rw [normSq_drift S hdet hε hκ hδ q q (LocalPrimitive.mem_neighborhood S ε κ hδ q)
    i ((q.mem_zeroSet i).mpr ⟨i.property, ha⟩), ha]
  simp only [zero_mul, zero_sub, nodeLogQuotient_zero, mul_neg, neg_mul, neg_neg, mul_one,
    Complex.mul_re, Complex.conj_re, Complex.conj_im, Complex.normSq_apply]
  ring

/-- The native chain rule along a genuine integral curve on an arbitrary time set. -/
theorem hasDerivWithinAt_scalar_along_integralCurve
    {n : ℕ} (M : SmoothManifold n)
    {W : (q : M.Point) → M.Tangent q}
    {γ : ℝ → M.Point} {s : Set ℝ} {t : ℝ} {f : M.Point → ℝ}
    (hγ : IsMIntegralCurveOn γ W s) (ht : t ∈ s)
    (hf : MDifferentiableAt 𝓘(ℝ, Model n) 𝓘(ℝ, ℝ) f (γ t)) :
    HasDerivWithinAt (fun u => f (γ u))
      (M.scalarDerivative f (γ t) (W (γ t))) s t := by
  have hd := (hasMFDerivWithinAt_iff_hasFDerivWithinAt.mp
    (hf.hasMFDerivAt.comp_hasMFDerivWithinAt t (hγ t ht))).hasDerivWithinAt
  apply hd.congr_deriv
  change M.scalarDerivative f (γ t) ((1 : ℝ) • W (γ t)) = _
  rw [one_smul]

/-- Pointwise local membership suffices; the curve need not stay in the neighborhood. -/
theorem normSq_hasDerivWithinAt {ε κ δ : ℝ} (hε : 0 < ε) (hκ : 2*ε+1 ≤ κ)
    (hδ : 0 < δ) (p : S.Point) (i : S.Mutable) (hi : (i : Fin d) ∈ p.zeroSet)
    {γ : ℝ → S.Point} {s : Set ℝ} {t : ℝ} :
    letI := SmoothAtlas.charts S hdet
    IsMIntegralCurveOn γ (GlobalLiouvilleField.Z S hdet ε κ hδ) s → t ∈ s →
    γ t ∈ LocalPrimitive.neighborhood S ε κ δ p →
    HasDerivWithinAt (fun u => Complex.normSq (normalizedPartner (γ u) i))
      (2 * (conj (normalizedPartner (γ t) i) * ((γ t).a i * normalizedPartner (γ t) i - 1) *
        nodeLogQuotient ((γ t).a i, normalizedPartner (γ t) i)).re +
          2 * κ * Complex.normSq (normalizedPartner (γ t) i)) s t := by
  letI := SmoothAtlas.charts S hdet
  intro hγ ht hq
  have hd := hasDerivWithinAt_scalar_along_integralCurve
    (SmoothAtlas.presentation S hdet).manifold hγ ht
    ((partner_normSq_smooth S hdet p.zeroSet_independent i hi (γ t) hq.2.1).mdifferentiableAt
      (by simp))
  rwa [normSq_drift S hdet hε hκ hδ p (γ t) hq i hi] at hd

/-- The exact zero-coordinate squared-norm derivative along this field's genuine curve.
No invariance, angular coefficient, or complete flow is assumed or asserted. -/
theorem normSq_hasDerivWithinAt_zero {ε κ δ : ℝ} (hε : 0 < ε) (hκ : 2*ε+1 ≤ κ)
    (hδ : 0 < δ) (i : S.Mutable) {γ : ℝ → S.Point} {s : Set ℝ} {t : ℝ} :
    letI := SmoothAtlas.charts S hdet
    IsMIntegralCurveOn γ (GlobalLiouvilleField.Z S hdet ε κ hδ) s → t ∈ s →
    (γ t).a i = 0 →
    HasDerivWithinAt (fun u => Complex.normSq (normalizedPartner (γ u) i))
      (2 * (1 + κ) * Complex.normSq (normalizedPartner (γ t) i)) s t := by
  letI := SmoothAtlas.charts S hdet
  intro hγ ht ha
  have hi := ((γ t).mem_zeroSet i).mpr ⟨i.property, ha⟩
  have hd := hasDerivWithinAt_scalar_along_integralCurve
    (SmoothAtlas.presentation S hdet).manifold hγ ht
    ((partner_normSq_smooth S hdet (γ t).zeroSet_independent i hi (γ t)
      (PrimitiveLocalization.mem_zero_locus (γ t))).mdifferentiableAt (by simp))
  rwa [normSq_drift_zero S hdet hε hκ hδ (γ t) i ha] at hd

end ClusterSkeleton.NormalizedPartnerNormDrift
