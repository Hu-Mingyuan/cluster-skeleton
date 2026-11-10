import ClusterSkeleton.GlobalLiouvilleField

/-! Native local node calculus and boundary tangency for the accepted global field. -/
noncomputable section
set_option autoImplicit false
set_option linter.style.haveILetI false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology BigOperators
open Set Filter FsFltz.Geometry

namespace ClusterSkeleton.BoundaryTangency

variable {d : ℕ} (S : Seed d) (hdet : S.Unimodular)

/-- The actual product of the original coordinate and its normalized partner. -/
def nodeProduct (i : S.Mutable) (q : S.Point) : ℂ := q.a i * normalizedPartner q i

/-- Native differentiation of a complex-valued function along the accepted field. -/
def drift (ε κ : ℝ) {δ : ℝ} (hδ : 0 < δ) (f : S.Point → ℂ) (q : S.Point) : ℂ :=
  complexDifferential (SmoothAtlas.presentation S hdet).manifold f q
    (GlobalLiouvilleField.Z S hdet ε κ hδ q)

theorem contMDiffOn_complexDerivative {n : ℕ} (M : SmoothManifold n)
    {W : (q : M.Point) → M.Tangent q} (hW : M.IsSmoothVectorField W)
    {U : Set M.Point} (hU : IsOpen U) {f : M.Point → ℂ}
    (hf : ContMDiffOn 𝓘(ℝ, Model n) 𝓘(ℝ, ℂ) ∞ f U) :
    ContMDiffOn 𝓘(ℝ, Model n) 𝓘(ℝ, ℂ) ∞
      (fun q => complexDifferential M f q (W q)) U := by
  have ht := hf.contMDiffOn_tangentMapWithin (m := ∞) (by simp) hU.uniqueMDiffOn
  have hc := ht.comp hW.contMDiff_section.contMDiffOn (fun q hq => hq)
  have he := (contMDiff_tangentBundleModelSpaceHomeomorph
    (I := 𝓘(ℝ, ℂ)) (n := ∞)).comp_contMDiffOn hc
  have hs := (ContinuousLinearMap.snd ℝ ℂ ℂ).contDiff.contMDiff (n := ∞)
  rw [modelWithCornersSelf_prod] at hs
  apply (hs.comp_contMDiffOn he).congr
  intro q hq
  change mfderiv 𝓘(ℝ, Model n) 𝓘(ℝ, ℂ) f q (W q) =
    mfderivWithin 𝓘(ℝ, Model n) 𝓘(ℝ, ℂ) f U q (W q)
  rw [mfderivWithin_of_isOpen hU hq]

theorem nodeLog_smooth {ε κ δ : ℝ} (p : S.Point)
    (i : S.Mutable) (hi : (i : Fin d) ∈ p.zeroSet)
    (q : S.Point) (hq : q ∈ LocalPrimitive.neighborhood S ε κ δ p) :
    letI := SmoothAtlas.charts S hdet
    ContMDiffAt 𝓘(ℝ, Model (2*d)) 𝓘(ℝ, ℂ) ∞
      (fun r => PrimitiveLocalization.nodeLog r i) q := by
  letI := SmoothAtlas.charts S hdet
  exact (NodePrimitiveCancellation.contDiffAt_L (hq.2.2 i hi)).contMDiffAt.comp q
    (NativeNodePrimitive.nodeMap_smooth S hdet p.zeroSet_independent i hi q hq.2.1)

theorem nodeProduct_smooth {I : Finset (Fin d)} (hI : S.Independent I)
    (i : S.Mutable) (hi : (i : Fin d) ∈ I) (q : S.Point)
    (hq : q ∈ candidateChartLocus S I) :
    letI := SmoothAtlas.charts S hdet
    ContMDiffAt 𝓘(ℝ, Model (2*d)) 𝓘(ℝ, ℂ) ∞ (nodeProduct S i) q := by
  letI := SmoothAtlas.charts S hdet
  have hm : ContDiff ℝ ∞ (fun z : ℂ × ℂ => z.1 * z.2) := contDiff_fst.mul contDiff_snd
  exact hm.contDiffAt.contMDiffAt.comp q
    (NativeNodePrimitive.nodeMap_smooth S hdet hI i hi q hq)

/-- The product rule, including both coordinate derivatives at every zero partner. -/
theorem differential_nodeProduct {I : Finset (Fin d)} (hI : S.Independent I)
    (i : S.Mutable) (hi : (i : Fin d) ∈ I) (q : S.Point)
    (hq : q ∈ candidateChartLocus S I)
    (v : (SmoothAtlas.presentation S hdet).manifold.Tangent q) :
    complexDifferential (SmoothAtlas.presentation S hdet).manifold (nodeProduct S i) q v =
      normalizedPartner q i * (SmoothAtlas.presentation S hdet).coordinateDifferential i q v +
        q.a i * (NativeNodePrimitive.nodeDifferential S hdet i q v).2 := by
  letI := SmoothAtlas.charts S hdet
  have hn := (NativeNodePrimitive.nodeMap_smooth S hdet hI i hi q hq).mdifferentiableAt
    (by simp)
  have hp := ((hasFDerivAt_fst (𝕜 := ℝ) (p := NativeNodePrimitive.nodeMap S i q)).mul
    (hasFDerivAt_snd (𝕜 := ℝ))).hasMFDerivAt.comp q hn.hasMFDerivAt
  change mfderiv 𝓘(ℝ, Model (2*d)) 𝓘(ℝ, ℂ) (nodeProduct S i) q v = _
  erw [hp.mfderiv]
  change q.a i * (NativeNodePrimitive.nodeDifferential S hdet i q v).2 +
    normalizedPartner q i * (NativeNodePrimitive.nodeDifferential S hdet i q v).1 = _
  rw [NativeNodePrimitive.nodeDifferential_fst S hdet hI i hi q hq v, add_comm]

/-- The logarithm chain rule uses its actual slit-plane domain. -/
theorem differential_nodeLog {ε κ δ : ℝ} (p : S.Point)
    (i : S.Mutable) (hi : (i : Fin d) ∈ p.zeroSet)
    (q : S.Point) (hq : q ∈ LocalPrimitive.neighborhood S ε κ δ p)
    (v : (SmoothAtlas.presentation S hdet).manifold.Tangent q) :
    complexDifferential (SmoothAtlas.presentation S hdet).manifold
      (fun r => PrimitiveLocalization.nodeLog r i) q v =
      complexDifferential (SmoothAtlas.presentation S hdet).manifold (nodeProduct S i) q v /
        (nodeProduct S i q - 1) := by
  letI := SmoothAtlas.charts S hdet
  have hn := (NativeNodePrimitive.nodeMap_smooth S hdet p.zeroSet_independent
    i hi q hq.2.1).mdifferentiableAt (by simp)
  have hl := ((NodePrimitiveCancellation.contDiffAt_L (hq.2.2 i hi)).differentiableAt
    (by simp)).hasFDerivAt.hasMFDerivAt.comp q hn.hasMFDerivAt
  change mfderiv 𝓘(ℝ, Model (2*d)) 𝓘(ℝ, ℂ)
    (fun r => PrimitiveLocalization.nodeLog r i) q v = _
  erw [hl.mfderiv]
  change fderiv ℝ NodePrimitiveCancellation.L (NativeNodePrimitive.nodeMap S i q)
    (NativeNodePrimitive.nodeDifferential S hdet i q v) = _
  rw [NodePrimitiveCancellation.fderiv_L (hq.2.2 i hi),
    differential_nodeProduct S hdet p.zeroSet_independent i hi q hq.2.1 v,
    NativeNodePrimitive.nodeDifferential_fst S hdet p.zeroSet_independent i hi q hq.2.1 v]
  rfl

/-- A genuine family inside the same zero stratum: only one mutation partner moves. -/
def boundaryPerturb (p : S.Point) (i : S.Mutable) (ha : p.a i = 0) (t : ℂ) : S.Point :=
  ⟨(p.a, Function.update p.b i (p.b i + t * S.negativeMonomial p.a i)), by
    constructor
    · intro j
      by_cases hj : j = i
      · subst j
        simpa only [Function.update_self, ha, zero_mul] using p.exchange i
      · simpa only [Function.update_of_ne hj] using p.exchange j
    · exact p.frozen_ne_zero⟩

@[simp] theorem boundaryPerturb_a (p : S.Point) (i : S.Mutable) (ha : p.a i = 0)
    (t : ℂ) : (boundaryPerturb S p i ha t).a = p.a := rfl

@[simp] theorem boundaryPerturb_zeroSet (p : S.Point) (i : S.Mutable) (ha : p.a i = 0)
    (t : ℂ) : (boundaryPerturb S p i ha t).zeroSet = p.zeroSet := rfl

@[simp] theorem boundaryPerturb_zero (p : S.Point) (i : S.Mutable) (ha : p.a i = 0) :
    boundaryPerturb S p i ha 0 = p := by
  apply Subtype.ext
  change (p.a, Function.update p.b i (p.b i + 0 * _)) = (p.a, p.b)
  simp

theorem continuous_boundaryPerturb (p : S.Point) (i : S.Mutable) (ha : p.a i = 0) :
    Continuous (boundaryPerturb S p i ha) := by
  apply Continuous.subtype_mk
  apply continuous_const.prodMk
  apply continuous_pi
  intro j
  by_cases hj : j = i
  · subst j
    simp only [Function.update_self]
    fun_prop
  · simpa only [Function.update_of_ne hj] using (continuous_const : Continuous (fun _ : ℂ => p.b j))

theorem boundaryPerturb_partner (p : S.Point) (i : S.Mutable) (ha : p.a i = 0)
    (t : ℂ) : normalizedPartner (boundaryPerturb S p i ha t) i = normalizedPartner p i + t := by
  have hi : (i : Fin d) ∈ p.zeroSet := (p.mem_zeroSet i).mpr ⟨i.property, ha⟩
  have hQ := negativeMonomial_ne_zero_on_independent_locus p.zeroSet_independent
    (PrimitiveLocalization.mem_zero_locus p) hi
  change (Function.update p.b i (p.b i + t * S.negativeMonomial p.a i)) i /
    S.negativeMonomial p.a i = p.b i / S.negativeMonomial p.a i + t
  simp [add_div, hQ]

theorem vartheta_deriv_one {δ t : ℝ} (hδ : 0 < δ)
    (ht : |t| < PrimitiveCutoffs.angularRadius δ / 2) :
    deriv (PrimitiveCutoffs.vartheta δ) t = 1 := by
  have he : PrimitiveCutoffs.vartheta δ =ᶠ[𝓝 t] id := by
    filter_upwards [continuous_abs.continuousAt.eventually_lt_const ht] with s hs
    exact PrimitiveCutoffs.vartheta_eq_self hδ hs.le
  rw [he.deriv_eq]
  exact deriv_id t

theorem local_vartheta_deriv {ε κ δ : ℝ} (hδ : 0 < δ) {p q : S.Point}
    (hq : q ∈ LocalPrimitive.neighborhood S ε κ δ p)
    (i : S.Mutable) (hi : (i : Fin d) ∈ p.zeroSet) :
    deriv (PrimitiveCutoffs.vartheta δ) (Complex.arg (-exchangeCharacter q i)) = 1 := by
  apply vartheta_deriv_one hδ
  have hr := PrimitiveLocalization.neighborhood_subset_region ε κ δ p hq.1
  have hb := (PrimitiveLocalization.node_bridges hq.1 i hi).2.2.2.2.1
  change (Complex.log (-exchangeCharacter q i)).im = _ at hb
  rw [Complex.log_im] at hb
  rw [hb]
  exact (hr.2 i hi).2.2.1

theorem deep_radius_torus {ε κ δ : ℝ} (hε : 0 < ε)
    (hκ : 2 * ε + 1 ≤ κ) (hδ : 0 < δ) {p q : S.Point}
    (hq : q ∈ LocalPrimitive.neighborhood S ε κ δ p) (ht : q ∈ initialTorus S)
    (i : S.Mutable) (hi : (i : Fin d) ∈ p.zeroSet) :
    GlobalLiouvilleField.L S hdet ε κ hδ q i = -κ := by
  rw [GlobalLiouvilleField.mutable_radial_equation S hdet hε hκ hδ q ht i i.property,
    local_vartheta_deriv S hδ hq i hi]
  obtain ⟨hd, hr, _, hh⟩ := PrimitiveLocalization.plateaus hε hκ hδ hq.1 ht i hi
  change DominanceCutoff.dominance S ε i (GlobalLiouvilleField.A S q) = 1 at hd
  change PrimitiveCutoffs.rho (∑ j, (S.B i j : ℝ) * GlobalLiouvilleField.A S q j) = 1 at hr
  change PrimitiveCutoffs.radial ε κ (GlobalLiouvilleField.A S q i) =
    GlobalLiouvilleField.A S q i + κ at hh
  rw [hd, hr, hh]
  ring

/-- Only the selected coordinate must be nonzero; other mutable coordinates may vanish. -/
theorem deep_radius {ε κ δ : ℝ} (hε : 0 < ε)
    (hκ : 2 * ε + 1 ≤ κ) (hδ : 0 < δ) (p q : S.Point)
    (hq : q ∈ LocalPrimitive.neighborhood S ε κ δ p)
    (i : S.Mutable) (hi : (i : Fin d) ∈ p.zeroSet) (ha : q.a i ≠ 0) :
    GlobalLiouvilleField.L S hdet ε κ hδ q i = -κ := by
  let U := LocalPrimitive.neighborhood S ε κ δ p
  have hU : IsOpen U := LocalPrimitive.isOpen_neighborhood S ε κ δ p
  have hL := GlobalLiouvilleField.continuousAt_L S hdet hε hκ hδ q i ha
  have he (r : S.Point) (hr : r ∈ U ∩ initialTorus S) :=
    deep_radius_torus S hdet hε hκ hδ hr.1 hr.2 i hi
  exact le_antisymm
    (GlobalLiouvilleField.le_of_dense_open (dense_initialTorus S hdet) hU hq hL
      continuousAt_const (fun r hr => (he r hr).le))
    (GlobalLiouvilleField.le_of_dense_open (dense_initialTorus S hdet) hU hq
      continuousAt_const hL (fun r hr => (he r hr).ge))

theorem differential_nodeLog_torus {ε κ δ : ℝ} (p : S.Point)
    (i : S.Mutable) (hi : (i : Fin d) ∈ p.zeroSet) (q : S.Point)
    (hq : q ∈ LocalPrimitive.neighborhood S ε κ δ p) (ht : q ∈ initialTorus S)
    (v : (SmoothAtlas.presentation S hdet).manifold.Tangent q) :
    complexDifferential (SmoothAtlas.presentation S hdet).manifold
      (fun r => PrimitiveLocalization.nodeLog r i) q v =
      ∑ j : Fin d, (S.B i j : ℂ) *
        ((SmoothAtlas.presentation S hdet).coordinateDifferential j q v / q.a j) := by
  letI := SmoothAtlas.charts S hdet
  have hc := (TorusCorrection.contMDiffAt_exchangeCharacter S hdet q ht i).mdifferentiableAt
    (by simp)
  have he : (fun r : S.Point => PrimitiveLocalization.nodeLog r i) =ᶠ[𝓝 q]
      (fun r => Complex.log (-exchangeCharacter r i)) := by
    filter_upwards [(isOpen_candidateChartLocus S p.zeroSet).mem_nhds hq.2.1] with r hr
    rw [PrimitiveLocalization.neg_character_node p.zeroSet_independent hr i hi]
    rfl
  have hl := (Complex.hasStrictFDerivAt_log_real
    (LocalPrimitive.node_domains S hq i hi).2.2.2.1).hasFDerivAt.hasMFDerivAt.comp q
      hc.hasMFDerivAt.neg
  change mfderiv 𝓘(ℝ, Model (2*d)) 𝓘(ℝ, ℂ)
    (fun r => PrimitiveLocalization.nodeLog r i) q v = _
  rw [he.mfderiv_eq]
  erw [hl.mfderiv]
  change (-exchangeCharacter q i)⁻¹ *
    (-complexDifferential (SmoothAtlas.presentation S hdet).manifold
      (fun r => exchangeCharacter r i) q v) = _
  rw [TorusLiouvilleDynamics.differential_character S hdet q ht v i]
  simp [TorusCorrection.exchangeCharacter_ne_zero S q ht i]

theorem row_real_drift_torus {ε κ δ : ℝ} (hε : 0 < ε)
    (_hκ : 2 * ε + 1 ≤ κ) (hδ : 0 < δ) {p q : S.Point}
    (hq : q ∈ LocalPrimitive.neighborhood S ε κ δ p) (ht : q ∈ initialTorus S)
    (i : S.Mutable) (hi : (i : Fin d) ∈ p.zeroSet) :
    (∑ j : Fin d, (S.B i j : ℝ) *
      (TorusLiouvilleDynamics.logarithmicComponents S hdet ε κ δ q j).re) =
        (PrimitiveLocalization.nodeLog q i).re := by
  rw [← (PrimitiveLocalization.node_bridges hq.1 i hi).2.2.2.2.2 ht]
  unfold PrimitiveLocalization.rowLog
  apply Finset.sum_congr rfl
  intro j _
  rw [TorusLiouvilleDynamics.real_logarithmicComponents S hdet ε κ hδ q ht j]
  by_cases hij : S.B i j = 0
  · simp [show S.E j (i : Fin d) = 0 from hij]
  · have hc : TorusLiouvilleDynamics.radialCorrection S ε κ δ q j = 0 := by
      by_cases hj : j ∈ S.mutable
      · have hd := PrimitiveLocalization.adjacent_dominance_zero hε hq.1 ht ⟨j,hj⟩
          ⟨i, hi, hij⟩
        change DominanceCutoff.dominance S ε j (TorusCorrection.A S q) = 0 at hd
        simp [TorusLiouvilleDynamics.radialCorrection, hj, TorusLiouvilleDynamics.amplitude, hd]
      · simp [TorusLiouvilleDynamics.radialCorrection, hj]
    rw [hc, sub_zero]
    rfl


open TorusLiouvilleDynamics in
theorem amplitude_partial_nonadjacent (ε κ : ℝ) (a : Fin d → ℝ) (i j : Fin d)
    (hji : j ≠ i) (hB : S.B j i = 0) :
    fderiv ℝ (amplitude S ε κ j) a (Pi.single i 1) = 0 := by
  classical
  have hd : fderiv ℝ (DominanceCutoff.dominance S ε j) a (Pi.single i 1) = 0 := by
    rw [fderiv_dominance_apply S ε j a (Pi.single i 1)]
    apply Finset.sum_eq_zero
    intro k hk
    have hki : k ≠ i := by
      intro h
      exact ((DominanceCutoff.mem_mutableNeighbors S j k).mp hk).2 (by simpa only [h] using hB)
    simp [hji, hki]
  rw [fderiv_amplitude_apply S ε κ j a (Pi.single i 1), hd]
  simp [Pi.single_apply, hji, show S.E i j = 0 from hB]

open TorusLiouvilleDynamics in
theorem differential_amplitude_radial (ε κ : ℝ) (q : S.Point) (ht : q ∈ initialTorus S)
    (i j : Fin d) :
    differentialCovector (SmoothAtlas.presentation S hdet).manifold
      (fun r => amplitude S ε κ j (TorusCorrection.A S r)) q
      (radialTangent S hdet q ht i) =
    fderiv ℝ (amplitude S ε κ j) (TorusCorrection.A S q) (Pi.single i 1) := by
  classical
  rw [differential_radial_function S hdet _ q ht
    ((amplitude_smooth S ε κ j).differentiable (by simp) _)]
  congr 1
  funext k
  simp [logarithmic_radialTangent, Pi.single_apply, apply_ite]

open TorusLiouvilleDynamics in
include hdet in
theorem amplitude_partial_self {ε κ δ : ℝ} (hε : 0 < ε) (hκ : 2 * ε + 1 ≤ κ)
    (hδ : 0 < δ) {p q : S.Point}
    (hq : q ∈ LocalPrimitive.neighborhood S ε κ δ p) (ht : q ∈ initialTorus S)
    (i : S.Mutable) (hi : (i : Fin d) ∈ p.zeroSet) :
    fderiv ℝ (amplitude S ε κ i) (TorusCorrection.A S q) (Pi.single i.val 1) = 1 := by
  classical
  letI := SmoothAtlas.charts S hdet
  have hg : (fun r : S.Point => amplitude S ε κ i (TorusCorrection.A S r)) =ᶠ[𝓝 q]
      (fun r => TorusCorrection.A S r i + κ) := by
    filter_upwards [(PrimitiveLocalization.isOpen_neighborhood ε κ δ p).mem_nhds hq.1,
      (isOpen_initialTorus S).mem_nhds ht] with r hr hrt
    obtain ⟨hd, hρ, _, hrad⟩ := PrimitiveLocalization.plateaus hε hκ hδ hr hrt i hi
    change PrimitiveCutoffs.radial ε κ (DominanceCutoff.logNorms S r i) *
      DominanceCutoff.dominance S ε i (DominanceCutoff.logNorms S r) *
        PrimitiveCutoffs.rho (PrimitiveLocalization.rowLog r i) =
      DominanceCutoff.logNorms S r i + κ
    rw [hd, hρ, hrad]
    simp
  have he : differentialCovector (SmoothAtlas.presentation S hdet).manifold
      (fun r => amplitude S ε κ i (TorusCorrection.A S r)) q =
    differentialCovector (SmoothAtlas.presentation S hdet).manifold
      (fun r => TorusCorrection.A S r i + κ) q := hg.mfderiv_eq
  have hAi := (contMDiffAt_pi_space.mp
    (TorusCorrection.contMDiffAt_A S hdet q ht) i.val).mdifferentiableAt (by simp)
  have hplus : differentialCovector (SmoothAtlas.presentation S hdet).manifold
      (fun r => TorusCorrection.A S r i + κ) q =
    differentialCovector (SmoothAtlas.presentation S hdet).manifold
      (fun r => TorusCorrection.A S r i) q := by
    change mfderiv 𝓘(ℝ, Model (2*d)) 𝓘(ℝ, ℝ)
      ((fun r => TorusCorrection.A S r i) + fun _ => κ) q = _
    erw [mfderiv_add hAi (mdifferentiableAt_const (c := κ)), mfderiv_const]
    exact add_zero _
  rw [← differential_amplitude_radial S hdet ε κ q ht i.val i.val,
    he, hplus, differential_A S hdet q ht,
    logarithmic_radialTangent S hdet q ht i.val i.val]
  simp

open TorusLiouvilleDynamics in
include hdet in
theorem amplitude_partial_adjacent {ε κ δ : ℝ} (hε : 0 < ε) {p q : S.Point}
    (hq : q ∈ LocalPrimitive.neighborhood S ε κ δ p) (ht : q ∈ initialTorus S)
    (i : Fin d) (j : S.Mutable) (hj : ∃ k ∈ p.zeroSet, S.B k j ≠ 0) :
    fderiv ℝ (amplitude S ε κ j) (TorusCorrection.A S q) (Pi.single i 1) = 0 := by
  letI := SmoothAtlas.charts S hdet
  have hg : (fun r : S.Point => amplitude S ε κ j (TorusCorrection.A S r)) =ᶠ[𝓝 q]
      (fun _ => 0) := by
    filter_upwards [(PrimitiveLocalization.isOpen_neighborhood ε κ δ p).mem_nhds hq.1,
      (isOpen_initialTorus S).mem_nhds ht] with r hr hrt
    have hd := PrimitiveLocalization.adjacent_dominance_zero hε hr hrt j hj
    change PrimitiveCutoffs.radial ε κ (DominanceCutoff.logNorms S r j) *
      DominanceCutoff.dominance S ε j (DominanceCutoff.logNorms S r) *
        PrimitiveCutoffs.rho (PrimitiveLocalization.rowLog r j) = 0
    rw [hd]
    simp
  have he : differentialCovector (SmoothAtlas.presentation S hdet).manifold
      (fun r => amplitude S ε κ j (TorusCorrection.A S r)) q = 0 := by
    calc
      _ = mfderiv 𝓘(ℝ, Model (2*d)) 𝓘(ℝ, ℝ) (fun _ : S.Point => (0 : ℝ)) q :=
        hg.mfderiv_eq
      _ = 0 := mfderiv_const
  rw [← differential_amplitude_radial S hdet ε κ q ht i j.val, he]
  rfl

open TorusLiouvilleDynamics in
/-- The derivative of the literal Hamiltonian follows from neighborhood germs,
not merely values of cutoff functions at the point. -/
theorem local_H_radial {ε κ δ : ℝ} (hε : 0 < ε) (hκ : 2 * ε + 1 ≤ κ)
    (hδ : 0 < δ) {p q : S.Point}
    (hq : q ∈ LocalPrimitive.neighborhood S ε κ δ p) (ht : q ∈ initialTorus S)
    (i : S.Mutable) (hi : (i : Fin d) ∈ p.zeroSet) :
    differentialCovector (SmoothAtlas.presentation S hdet).manifold
      (TorusCorrection.H S ε κ δ) q (radialTangent S hdet q ht i) =
        (S.D (i : Fin d) : ℝ) * (PrimitiveLocalization.nodeLog q i).im := by
  classical
  rw [differential_H_radial S hdet ε κ hδ q ht i]
  have hangle : TorusCorrection.angular S δ q i = (PrimitiveLocalization.nodeLog q i).im := by
    simpa only [TorusCorrection.angular, PrimitiveLocalization.angle, Complex.log_im] using
      ((PrimitiveLocalization.plateaus hε hκ hδ hq.1 ht i hi).2.2.1.trans
        (PrimitiveLocalization.node_bridges hq.1 i hi).2.2.2.2.1)
  rw [Finset.sum_eq_single i.val]
  · rw [amplitude_partial_self S hdet hε hκ hδ hq ht i hi, mul_one, hangle]
  · intro j hj hji
    by_cases hij : S.B i j = 0
    · have hjiB : S.B j i = 0 := (S.B_eq_zero_iff i j).mp hij
      rw [amplitude_partial_nonadjacent S ε κ _ i.val j hji hjiB, mul_zero, mul_zero]
    · rw [amplitude_partial_adjacent S hdet hε hq ht i.val ⟨j, hj⟩ ⟨i.val, hi, hij⟩,
        mul_zero, mul_zero]
  · exact fun h => (h i.property).elim

/-- The native complex logarithmic drift on the torus part of the open node neighborhood. -/
theorem nodeLog_drift_torus {ε κ δ : ℝ} (hε : 0 < ε) (hκ : 2 * ε + 1 ≤ κ)
    (hδ : 0 < δ) (p q : S.Point)
    (hq : q ∈ LocalPrimitive.neighborhood S ε κ δ p) (ht : q ∈ initialTorus S)
    (i : S.Mutable) (hi : (i : Fin d) ∈ p.zeroSet) :
    drift S hdet ε κ hδ (fun r => PrimitiveLocalization.nodeLog r i) q =
      PrimitiveLocalization.nodeLog q i := by
  unfold drift
  rw [differential_nodeLog_torus S hdet p i hi q hq ht,
    GlobalLiouvilleField.Z_eq_torus S hdet hε hκ hδ q ht]
  change (∑ j : Fin d, (S.B i j : ℂ) *
    TorusLiouvilleDynamics.logarithmicComponents S hdet ε κ δ q j) = _
  apply Complex.ext
  · simpa only [Complex.re_sum, Complex.mul_re, Complex.intCast_re, Complex.intCast_im,
      zero_mul, sub_zero] using row_real_drift_torus S hdet hε hκ hδ hq ht i hi
  · have hrow := TorusLiouvilleDynamics.angular_equation_row S hdet ε κ hδ q ht i
    rw [local_H_radial S hdet hε hκ hδ hq ht i hi] at hrow
    have hD : ((S.D (i : Fin d) : ℚ) : ℝ) ≠ 0 := by
      have := S.D_pos (i : Fin d)
      exact_mod_cast this.ne'
    simpa only [Complex.im_sum, Complex.mul_im, Complex.intCast_re, Complex.intCast_im,
      zero_mul, add_zero] using mul_left_cancel₀ hD hrow


/-- The actual local logarithmic drift extends across all zeros on the OPEN neighborhood. -/
theorem nodeLog_drift {ε κ δ : ℝ} (hε : 0 < ε) (hκ : 2 * ε + 1 ≤ κ)
    (hδ : 0 < δ) (p q : S.Point)
    (hq : q ∈ LocalPrimitive.neighborhood S ε κ δ p)
    (i : S.Mutable) (hi : (i : Fin d) ∈ p.zeroSet) :
    drift S hdet ε κ hδ (fun r => PrimitiveLocalization.nodeLog r i) q =
      PrimitiveLocalization.nodeLog q i := by
  letI := SmoothAtlas.charts S hdet
  let U := LocalPrimitive.neighborhood S ε κ δ p
  have hU : IsOpen U := LocalPrimitive.isOpen_neighborhood S ε κ δ p
  have hf : ContMDiffOn 𝓘(ℝ, Model (2*d)) 𝓘(ℝ, ℂ) ∞
      (fun r => PrimitiveLocalization.nodeLog r i) U :=
    fun r hr => (nodeLog_smooth S hdet p i hi r hr).contMDiffWithinAt
  have hD := contMDiffOn_complexDerivative (SmoothAtlas.presentation S hdet).manifold
    (GlobalLiouvilleField.isSmoothVectorField_Z S hdet hε hκ hδ) hU hf
  have he : EqOn (drift S hdet ε κ hδ (fun r => PrimitiveLocalization.nodeLog r i))
      (fun r => PrimitiveLocalization.nodeLog r i) (U ∩ initialTorus S) :=
    fun r hr => nodeLog_drift_torus S hdet hε hκ hδ p r hr.1 hr.2 i hi
  exact he.of_subset_closure hD.continuousOn hf.continuousOn inter_subset_left
    (fun r hr => hU.inter_closure ⟨hr, dense_initialTorus S hdet r⟩) hq

/-- The native product drift; its denominator was proved nonzero in the log chain rule. -/
theorem nodeProduct_drift {ε κ δ : ℝ} (hε : 0 < ε) (hκ : 2 * ε + 1 ≤ κ)
    (hδ : 0 < δ) (p q : S.Point)
    (hq : q ∈ LocalPrimitive.neighborhood S ε κ δ p)
    (i : S.Mutable) (hi : (i : Fin d) ∈ p.zeroSet) :
    drift S hdet ε κ hδ (nodeProduct S i) q =
      (nodeProduct S i q - 1) * PrimitiveLocalization.nodeLog q i := by
  have h := nodeLog_drift S hdet hε hκ hδ p q hq i hi
  unfold drift at h
  rw [differential_nodeLog S hdet p i hi q hq] at h
  have hn : nodeProduct S i q - 1 ≠ 0 := by
    have hn := Complex.slitPlane_ne_zero (hq.2.2 i hi)
    change 1 - nodeProduct S i q ≠ 0 at hn
    intro he
    exact hn (by linear_combination -he)
  exact (div_eq_iff hn).mp h |>.trans (mul_comm _ _)

/-- Smooth evaluation of the native original-coordinate differential. -/
theorem continuous_coordinate_drift {ε κ δ : ℝ} (hε : 0 < ε)
    (hκ : 2 * ε + 1 ≤ κ) (hδ : 0 < δ) (i : Fin d) :
    Continuous (fun q : S.Point => (SmoothAtlas.presentation S hdet).coordinateDifferential i q
      (GlobalLiouvilleField.Z S hdet ε κ hδ q)) := by
  letI := SmoothAtlas.charts S hdet
  have hf := (ContinuousLinearMap.proj i : (Fin d → ℂ) →L[ℝ] ℂ).contMDiff.comp
    (TorusNondegeneracy.original_smooth S (SmoothAtlas.presentation S hdet))
  exact continuousOn_univ.mp (contMDiffOn_complexDerivative
    (SmoothAtlas.presentation S hdet).manifold
    (GlobalLiouvilleField.isSmoothVectorField_Z S hdet hε hκ hδ) isOpen_univ
    hf.contMDiffOn).continuousOn

/-- Product differentiation gives tangency wherever the normalized partner is nonzero. -/
theorem zero_coordinate_tangent_of_partner_ne_zero {ε κ δ : ℝ}
    (hε : 0 < ε) (hκ : 2 * ε + 1 ≤ κ) (hδ : 0 < δ)
    (p : S.Point) (i : S.Mutable) (ha : p.a i = 0) (hb : normalizedPartner p i ≠ 0) :
    (SmoothAtlas.presentation S hdet).coordinateDifferential i p
      (GlobalLiouvilleField.Z S hdet ε κ hδ p) = 0 := by
  have hi := (p.mem_zeroSet i).mpr ⟨i.property, ha⟩
  have h := nodeProduct_drift S hdet hε hκ hδ p p
    (LocalPrimitive.mem_neighborhood S ε κ hδ p) i hi
  unfold drift at h
  rw [differential_nodeProduct S hdet p.zeroSet_independent i hi p
    (PrimitiveLocalization.mem_zero_locus p)] at h
  simp only [nodeProduct, PrimitiveLocalization.nodeLog, ha, zero_mul, add_zero,
    sub_zero, Complex.log_one, mul_zero] at h
  exact (mul_eq_zero.mp h).resolve_left hb

/-- The perturbation converges inside every chosen open neighborhood of its center. -/
theorem boundaryPerturb_eventually_mem (ε κ : ℝ) {δ : ℝ} (hδ : 0 < δ)
    (p : S.Point) (i : S.Mutable) (ha : p.a i = 0) :
    ∀ᶠ t in 𝓝 (0 : ℂ), boundaryPerturb S p i ha t ∈
      LocalPrimitive.neighborhood S ε κ δ p := by
  have h := (continuous_boundaryPerturb S p i ha).continuousAt (x := (0 : ℂ))
  change Tendsto (boundaryPerturb S p i ha) (𝓝 0) (𝓝 (boundaryPerturb S p i ha 0)) at h
  rw [boundaryPerturb_zero] at h
  exact h.eventually ((LocalPrimitive.isOpen_neighborhood S ε κ δ p).mem_nhds
    (LocalPrimitive.mem_neighborhood S ε κ hδ p))

/-- Tangency at every zero original coordinate, including a zero normalized partner
and arbitrary simultaneous zeros. The final limit stays in the SAME zero stratum. -/
theorem zero_coordinate_tangent {ε κ δ : ℝ} (hε : 0 < ε)
    (hκ : 2 * ε + 1 ≤ κ) (hδ : 0 < δ) (p : S.Point) (i : S.Mutable)
    (ha : p.a i = 0) :
    (SmoothAtlas.presentation S hdet).coordinateDifferential i p
      (GlobalLiouvilleField.Z S hdet ε κ hδ p) = 0 := by
  by_cases hb : normalizedPartner p i ≠ 0
  · exact zero_coordinate_tangent_of_partner_ne_zero S hdet hε hκ hδ p i ha hb
  · have hb0 : normalizedPartner p i = 0 := not_ne_iff.mp hb
    let F : ℂ → ℂ := fun t => (SmoothAtlas.presentation S hdet).coordinateDifferential i
      (boundaryPerturb S p i ha t)
      (GlobalLiouvilleField.Z S hdet ε κ hδ (boundaryPerturb S p i ha t))
    have hc : Continuous F := (continuous_coordinate_drift S hdet hε hκ hδ i).comp
      (continuous_boundaryPerturb S p i ha)
    have he : F =ᶠ[𝓝[≠] (0 : ℂ)] fun _ => 0 := by
      filter_upwards [self_mem_nhdsWithin] with t ht
      apply zero_coordinate_tangent_of_partner_ne_zero S hdet hε hκ hδ
        (boundaryPerturb S p i ha t) i ha
      rw [boundaryPerturb_partner, hb0, zero_add]
      exact ht
    have hz : F 0 = 0 := tendsto_nhds_unique_of_eventuallyEq
      (hc.continuousAt.mono_left nhdsWithin_le_nhds) tendsto_const_nhds he
    have heq := congrArg (fun r : S.Point =>
      (SmoothAtlas.presentation S hdet).coordinateDifferential i r
        (GlobalLiouvilleField.Z S hdet ε κ hδ r)) (boundaryPerturb_zero S p i ha)
    exact heq.symm.trans hz

/-- Finite-index form with no supplied mutability or stratum witness. -/
theorem coordinate_tangent {ε κ δ : ℝ} (hε : 0 < ε)
    (hκ : 2 * ε + 1 ≤ κ) (hδ : 0 < δ) (p : S.Point) (i : Fin d) (ha : p.a i = 0) :
    (SmoothAtlas.presentation S hdet).coordinateDifferential i p
      (GlobalLiouvilleField.Z S hdet ε κ hδ p) = 0 := by
  have hi : i ∈ S.mutable := by
    by_contra hi
    exact p.frozen_ne_zero i hi ha
  exact zero_coordinate_tangent S hdet hε hκ hδ p ⟨i,hi⟩ ha

end ClusterSkeleton.BoundaryTangency
