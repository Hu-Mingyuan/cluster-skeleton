import ClusterSkeleton.GlobalPrimitive
import ClusterSkeleton.TorusLiouvilleDynamics
import FsFltz.Geometry.SmoothLiouville
import FsFltz.Geometry.VectorFieldBridge
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv

/-! The global native Liouville field and radial control on nonzero coordinate loci. -/
noncomputable section
set_option autoImplicit false
open scoped Manifold ContDiff Topology BigOperators
open Set Filter FsFltz.Geometry

namespace ClusterSkeleton.GlobalLiouvilleField

variable {d : ℕ} (S : Seed d) (hdet : S.Unimodular)

/-- The pinned intrinsic vector of the constructed global primitive. -/
def Z (ε κ : ℝ) {δ : ℝ} (hδ : 0 < δ) (p : S.Point) :
    (SmoothAtlas.presentation S hdet).manifold.Tangent p :=
  (SmoothAtlas.presentation S hdet).manifold.liouvilleVector
    (GlobalPrimitive.alpha S hdet ε κ hδ) p

theorem isSmoothVectorField_Z {ε κ δ : ℝ} (hε : 0 < ε)
    (hκ : 2 * ε + 1 ≤ κ) (hδ : 0 < δ) :
    (SmoothAtlas.presentation S hdet).manifold.IsSmoothVectorField (Z S hdet ε κ hδ) :=
  (SmoothAtlas.presentation S hdet).manifold.isSmoothVectorField_liouvilleVector _
    (GlobalPrimitive.isSmoothForm_alpha S hdet hε hκ hδ)
    (GlobalPrimitive.nondegenerate_exteriorDerivative_alpha S hdet hε hκ hδ)

/-- Contraction with the actual exterior derivative, against every native tangent. -/
theorem contraction_exteriorDerivative {ε κ δ : ℝ} (hε : 0 < ε)
    (hκ : 2 * ε + 1 ≤ κ) (hδ : 0 < δ) (p : S.Point)
    (v : (SmoothAtlas.presentation S hdet).manifold.Tangent p) :
    SmoothManifold.evalTwo
      ((SmoothAtlas.presentation S hdet).manifold.exteriorDerivative
        (GlobalPrimitive.alpha S hdet ε κ hδ)) p (Z S hdet ε κ hδ p) v =
      SmoothManifold.evalOne (GlobalPrimitive.alpha S hdet ε κ hδ) p v :=
  (SmoothAtlas.presentation S hdet).manifold.liouvilleVector_contraction _ p
    ((SmoothAtlas.presentation S hdet).manifold.liouvilleEquation_exists _ p
      (GlobalPrimitive.nondegenerate_exteriorDerivative_alpha S hdet hε hκ hδ p)) v

theorem contraction_omega {ε κ δ : ℝ} (hε : 0 < ε)
    (hκ : 2 * ε + 1 ≤ κ) (hδ : 0 < δ) (p : S.Point)
    (v : (SmoothAtlas.presentation S hdet).manifold.Tangent p) :
    SmoothManifold.evalTwo (GlobalTwoForm.omega S hdet) p (Z S hdet ε κ hδ p) v =
      SmoothManifold.evalOne (GlobalPrimitive.alpha S hdet ε κ hδ) p v := by
  rw [← GlobalPrimitive.exteriorDerivative_alpha S hdet hε hκ hδ]
  exact contraction_exteriorDerivative S hdet hε hκ hδ p v

/-- Nondegenerate contraction identifies the actual global vector on the torus. -/
theorem Z_eq_torus {ε κ δ : ℝ} (hε : 0 < ε)
    (hκ : 2 * ε + 1 ≤ κ) (hδ : 0 < δ) (p : S.Point) (hp : p ∈ initialTorus S) :
    Z S hdet ε κ hδ p = TorusLiouvilleDynamics.Z S hdet ε κ δ p := by
  apply (SmoothAtlas.presentation S hdet).manifold.liouvilleVector_eq
    (GlobalPrimitive.alpha S hdet ε κ hδ) p
    (GlobalPrimitive.nondegenerate_exteriorDerivative_alpha S hdet hε hκ hδ p)
  intro v
  rw [GlobalPrimitive.exteriorDerivative_alpha S hdet hε hκ hδ]
  change SmoothManifold.evalTwo (GlobalTwoForm.omega S hdet) p
    (TorusLiouvilleDynamics.Z S hdet ε κ δ p) v =
      GlobalPrimitive.alpha S hdet ε κ hδ p (fun _ => v)
  rw [GlobalPrimitive.alpha_eq_torus S hdet hε hκ hδ p hp]
  exact TorusLiouvilleDynamics.contraction S hdet ε κ hδ p hp v

/-- Literal logarithmic components of this global field, used on nonzero loci. -/
def logarithmicComponents (ε κ : ℝ) {δ : ℝ} (hδ : 0 < δ)
    (p : S.Point) (j : Fin d) : ℂ :=
  (SmoothAtlas.presentation S hdet).coordinateDifferential j p (Z S hdet ε κ hδ p) / p.a j

theorem logarithmicComponents_eq_torus {ε κ δ : ℝ} (hε : 0 < ε)
    (hκ : 2 * ε + 1 ≤ κ) (hδ : 0 < δ) (p : S.Point) (hp : p ∈ initialTorus S) :
    logarithmicComponents S hdet ε κ hδ p =
      TorusLiouvilleDynamics.logarithmicComponents S hdet ε κ δ p := by
  funext j
  simp only [logarithmicComponents, TorusLiouvilleDynamics.logarithmicComponents,
    Z_eq_torus S hdet hε hκ hδ p hp]

/-- The totalized value has smoothness assertions only on its nonzero locus. -/
def A (p : S.Point) (j : Fin d) : ℝ := Real.log ‖p.a j‖

/-- Native scalar derivative along the global field. -/
def L (ε κ : ℝ) {δ : ℝ} (hδ : 0 < δ) (p : S.Point) (j : Fin d) : ℝ :=
  (SmoothAtlas.presentation S hdet).manifold.scalarDerivative
    (fun q => A S q j) p (Z S hdet ε κ hδ p)

/-- Selected-coordinate nonvanishing suffices, with arbitrary other zero coordinates. -/
theorem differential_A (p : S.Point) (j : Fin d) (hj : p.a j ≠ 0)
    (v : (SmoothAtlas.presentation S hdet).manifold.Tangent p) :
    (SmoothAtlas.presentation S hdet).manifold.scalarDerivative (fun q => A S q j) p v =
      ((SmoothAtlas.presentation S hdet).coordinateDifferential j p v / p.a j).re := by
  letI := SmoothAtlas.charts S hdet
  have hc := (((ContinuousLinearMap.proj j : (Fin d → ℂ) →L[ℝ] ℂ).contMDiff.comp
    (TorusNondegeneracy.original_smooth S (SmoothAtlas.presentation S hdet))) p).mdifferentiableAt
      (by simp)
  have h := (TorusLiouvilleDynamics.hasFDerivAt_log_norm hj).hasMFDerivAt.comp p hc.hasMFDerivAt
  change mfderiv 𝓘(ℝ, Model (2*d)) 𝓘(ℝ, ℝ)
    (fun q : S.Point => Real.log ‖q.a j‖) p v = _
  erw [h.mfderiv]
  change ((p.a j)⁻¹ * (SmoothAtlas.presentation S hdet).coordinateDifferential j p v).re = _
  simp only [div_eq_mul_inv, mul_comm]

theorem L_eq_logarithmicComponents (ε κ : ℝ) {δ : ℝ} (hδ : 0 < δ)
    (p : S.Point) (j : Fin d) (hj : p.a j ≠ 0) :
    L S hdet ε κ hδ p j = (logarithmicComponents S hdet ε κ hδ p j).re :=
  differential_A S hdet p j hj _

/-- The literal mutable radial equation concerns the constructed global vector. -/
theorem mutable_radial_equation {ε κ δ : ℝ} (hε : 0 < ε)
    (hκ : 2 * ε + 1 ≤ κ) (hδ : 0 < δ) (p : S.Point) (hp : p ∈ initialTorus S)
    (i : Fin d) (hi : i ∈ S.mutable) :
    L S hdet ε κ hδ p i = A S p i -
      PrimitiveCutoffs.radial ε κ (A S p i) *
        DominanceCutoff.dominance S ε i (A S p) *
        PrimitiveCutoffs.rho (∑ j : Fin d, (S.B i j : ℝ) * A S p j) *
        deriv (PrimitiveCutoffs.vartheta δ) (Complex.arg (-exchangeCharacter p i)) := by
  rw [L_eq_logarithmicComponents S hdet ε κ hδ p i (hp i),
    logarithmicComponents_eq_torus S hdet hε hκ hδ p hp]
  exact TorusLiouvilleDynamics.mutable_radial_equation S hdet ε κ hδ p hp i hi

theorem frozen_radial_equation_torus {ε κ δ : ℝ} (hε : 0 < ε)
    (hκ : 2 * ε + 1 ≤ κ) (hδ : 0 < δ) (p : S.Point) (hp : p ∈ initialTorus S)
    (i : Fin d) (hi : i ∉ S.mutable) : L S hdet ε κ hδ p i = A S p i := by
  rw [L_eq_logarithmicComponents S hdet ε κ hδ p i (hp i),
    logarithmicComponents_eq_torus S hdet hε hκ hδ p hp]
  exact TorusLiouvilleDynamics.frozen_radial_equation S hdet ε κ hδ p hp i hi

/-- The angular equation uses the genuine local-log partial derivative. -/
theorem angular_equation_partial_deriv {ε κ δ : ℝ} (hε : 0 < ε)
    (hκ : 2 * ε + 1 ≤ κ) (hδ : 0 < δ) (p : S.Point) (hp : p ∈ initialTorus S)
    (i : Fin d) :
    (∑ j : Fin d, (S.B i j : ℝ) * (logarithmicComponents S hdet ε κ hδ p j).im) =
      deriv (fun t : ℝ => TorusLiouvilleDynamics.logarithmicHamiltonian S ε κ δ p
        (t • (Pi.single i 1 : Fin d → ℂ))) 0 := by
  rw [logarithmicComponents_eq_torus S hdet hε hκ hδ p hp]
  exact TorusLiouvilleDynamics.angular_equation_partial_deriv S hdet ε κ hδ p hp i

/-- One constant for all torus points; no zero-stratum growth assertion. -/
theorem logarithmic_linear_growth {ε κ δ : ℝ} (hε : 0 < ε)
    (hκ : 2 * ε + 1 ≤ κ) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (p : S.Point), p ∈ initialTorus S →
      (∑ j : Fin d, (|(logarithmicComponents S hdet ε κ hδ p j).re| +
        |(logarithmicComponents S hdet ε κ hδ p j).im|)) ≤
      C * (1 + ∑ j : Fin d, |A S p j|) := by
  obtain ⟨C, hC, h⟩ := TorusLiouvilleDynamics.logarithmic_linear_growth S hdet hε hκ hδ
  refine ⟨C, hC, fun p hp => ?_⟩
  rw [logarithmicComponents_eq_torus S hdet hε hκ hδ p hp]
  exact h p hp

/-- Native scalar differentiation of a smooth field is smooth on any open
set where the scalar function is smooth. -/
theorem contMDiffOn_scalarDerivative {n : ℕ} (M : SmoothManifold n)
    {W : (p : M.Point) → M.Tangent p} (hW : M.IsSmoothVectorField W)
    {U : Set M.Point} (hU : IsOpen U) {f : M.Point → ℝ}
    (hf : ContMDiffOn 𝓘(ℝ, Model n) 𝓘(ℝ, ℝ) ∞ f U) :
    ContMDiffOn 𝓘(ℝ, Model n) 𝓘(ℝ, ℝ) ∞
      (fun p => M.scalarDerivative f p (W p)) U := by
  have ht := hf.contMDiffOn_tangentMapWithin (m := ∞) (by simp) hU.uniqueMDiffOn
  have hc := ht.comp hW.contMDiff_section.contMDiffOn (fun p hp => hp)
  have he := (contMDiff_tangentBundleModelSpaceHomeomorph
    (I := 𝓘(ℝ, ℝ)) (n := ∞)).comp_contMDiffOn hc
  have hs := (ContinuousLinearMap.snd ℝ ℝ ℝ).contDiff.contMDiff (n := ∞)
  rw [modelWithCornersSelf_prod] at hs
  apply (hs.comp_contMDiffOn he).congr
  intro p hp
  change M.scalarDerivative f p (W p) =
    mfderivWithin 𝓘(ℝ, Model n) 𝓘(ℝ, ℝ) f U p (W p)
  rw [mfderivWithin_of_isOpen hU hp]
  rfl

def nonzeroLocus (j : Fin d) : Set S.Point := {p | p.a j ≠ 0}

theorem isOpen_nonzeroLocus (j : Fin d) : IsOpen (nonzeroLocus S j) :=
  isOpen_ne_fun (continuous_originalCoordinate S j) continuous_const

theorem contMDiffAt_A (p : S.Point) (j : Fin d) (hj : p.a j ≠ 0) :
    letI := SmoothAtlas.charts S hdet
    ContMDiffAt 𝓘(ℝ, Model (2*d)) 𝓘(ℝ, ℝ) ∞ (fun q => A S q j) p :=
  RegularCorrection.contMDiffAt_log_coordinate S hdet j hj

include hdet in
theorem continuousAt_A (p : S.Point) (j : Fin d) (hj : p.a j ≠ 0) :
    ContinuousAt (fun q => A S q j) p := by
  letI := SmoothAtlas.charts S hdet
  exact (contMDiffAt_A S hdet p j hj).continuousAt

theorem contMDiffOn_L {ε κ δ : ℝ} (hε : 0 < ε)
    (hκ : 2 * ε + 1 ≤ κ) (hδ : 0 < δ) (j : Fin d) :
    letI := SmoothAtlas.charts S hdet
    ContMDiffOn 𝓘(ℝ, Model (2*d)) 𝓘(ℝ, ℝ) ∞
      (fun q => L S hdet ε κ hδ q j) (nonzeroLocus S j) := by
  letI := SmoothAtlas.charts S hdet
  exact contMDiffOn_scalarDerivative (SmoothAtlas.presentation S hdet).manifold
    (isSmoothVectorField_Z S hdet hε hκ hδ) (isOpen_nonzeroLocus S j)
    (fun p hp => (contMDiffAt_A S hdet p j hp).contMDiffWithinAt)

theorem continuousAt_L {ε κ δ : ℝ} (hε : 0 < ε)
    (hκ : 2 * ε + 1 ≤ κ) (hδ : 0 < δ) (p : S.Point) (j : Fin d)
    (hj : p.a j ≠ 0) : ContinuousAt (fun q => L S hdet ε κ hδ q j) p := by
  letI := SmoothAtlas.charts S hdet
  exact ((contMDiffOn_L S hdet hε hκ hδ j).contMDiffAt
    ((isOpen_nonzeroLocus S j).mem_nhds hj)).continuousAt

/-- Density is restricted to an open neighborhood, never a closed sign locus. -/
theorem le_of_dense_open {X : Type*} [TopologicalSpace X]
    {T V : Set X} (hT : Dense T) (hV : IsOpen V) {p : X} (hp : p ∈ V)
    {f g : X → ℝ} (hf : ContinuousAt f p) (hg : ContinuousAt g p)
    (hle : ∀ q ∈ V ∩ T, f q ≤ g q) : f p ≤ g p := by
  have hclosure : p ∈ closure (V ∩ T) := hV.inter_closure ⟨hp, hT p⟩
  exact ContinuousWithinAt.closure_le hclosure hf.continuousWithinAt hg.continuousWithinAt hle

include hdet in
/-- Open inverse images of the locally smooth log coordinate. -/
theorem isOpen_log_preimage (j : Fin d) {U : Set ℝ} (hU : IsOpen U) :
    IsOpen {p : S.Point | p.a j ≠ 0 ∧ A S p j ∈ U} := by
  rw [isOpen_iff_mem_nhds]
  intro p hp
  exact Filter.inter_mem ((isOpen_nonzeroLocus S j).mem_nhds hp.1)
    ((continuousAt_A S hdet p j hp.1).preimage_mem_nhds (hU.mem_nhds hp.2))

/-- The entire open collar above the radial cutoff has exact radial drift. -/
theorem L_eq_A_of_collar {ε κ δ : ℝ} (hε : 0 < ε)
    (hκ : 2 * ε + 1 ≤ κ) (hδ : 0 < δ) (p : S.Point) (j : Fin d)
    (hj : p.a j ≠ 0) (ha : -2 * ε < A S p j) :
    L S hdet ε κ hδ p j = A S p j := by
  have hk : 2 * ε < κ := by linarith
  let V : Set S.Point := {q | q.a j ≠ 0 ∧ -2 * ε < A S q j}
  have hV : IsOpen V := isOpen_log_preimage S hdet j isOpen_Ioi
  have hpV : p ∈ V := ⟨hj, ha⟩
  have he (q : S.Point) (hq : q ∈ V ∩ initialTorus S) :
      L S hdet ε κ hδ q j = A S q j := by
    rw [L_eq_logarithmicComponents S hdet ε κ hδ q j hq.1.1,
      logarithmicComponents_eq_torus S hdet hε hκ hδ q hq.2,
      TorusLiouvilleDynamics.real_logarithmicComponents S hdet ε κ hδ q hq.2 j]
    have hr := PrimitiveCutoffs.radial_eq_zero hk hq.1.2.le
    change PrimitiveCutoffs.radial ε κ (TorusCorrection.A S q j) = 0 at hr
    simp only [TorusLiouvilleDynamics.radialCorrection, TorusLiouvilleDynamics.amplitude, hr,
      zero_mul, ite_self, sub_zero] <;> rfl
  have hl := continuousAt_L S hdet hε hκ hδ p j hj
  have hA := continuousAt_A S hdet p j hj
  exact le_antisymm
    (le_of_dense_open (dense_initialTorus S hdet) hV hpV hl hA (fun q hq => (he q hq).le))
    (le_of_dense_open (dense_initialTorus S hdet) hV hpV hA hl (fun q hq => (he q hq).ge))

theorem L_eq_A_of_nonneg {ε κ δ : ℝ} (hε : 0 < ε)
    (hκ : 2 * ε + 1 ≤ κ) (hδ : 0 < δ) (p : S.Point) (j : Fin d)
    (hj : p.a j ≠ 0) (ha : 0 ≤ A S p j) : L S hdet ε κ hδ p j = A S p j :=
  L_eq_A_of_collar S hdet hε hκ hδ p j hj (by linarith)

theorem L_negative_bound {ε κ δ : ℝ} (hε : 0 < ε)
    (hκ : 2 * ε + 1 ≤ κ) (hδ : 0 < δ) (p : S.Point) (j : Fin d)
    (hj : p.a j ≠ 0) (ha : A S p j < 0) :
    L S hdet ε κ hδ p j ≤ A S p j - PrimitiveCutoffs.radial ε κ (A S p j) ∧
      A S p j - PrimitiveCutoffs.radial ε κ (A S p j) < 0 := by
  have hk : 2 * ε < κ := by linarith
  refine ⟨?_, sub_neg.mpr (PrimitiveCutoffs.radial_gt hε hk ha)⟩
  let V : Set S.Point := {q | q.a j ≠ 0 ∧ A S q j < 0}
  have hV : IsOpen V := isOpen_log_preimage S hdet j isOpen_Iio
  have hA := continuousAt_A S hdet p j hj
  apply le_of_dense_open (dense_initialTorus S hdet) hV (show p ∈ V from ⟨hj, ha⟩)
    (continuousAt_L S hdet hε hκ hδ p j hj)
    (hA.sub ((PrimitiveCutoffs.radial_smooth ε κ).continuous.continuousAt.comp hA))
  intro q hq
  rw [L_eq_logarithmicComponents S hdet ε κ hδ q j hq.1.1,
    logarithmicComponents_eq_torus S hdet hε hκ hδ q hq.2]
  exact (TorusLiouvilleDynamics.radial_negative_bound S hdet hε hk hδ q hq.2 j hq.1.2).1

/-- Frozen coordinates are nonzero variables at every actual exchange point. -/
theorem frozen_radial_equation {ε κ δ : ℝ} (hε : 0 < ε)
    (hκ : 2 * ε + 1 ≤ κ) (hδ : 0 < δ) (p : S.Point) (j : Fin d)
    (hj : j ∉ S.mutable) : L S hdet ε κ hδ p j = A S p j := by
  have hn := p.frozen_ne_zero j hj
  have hl := continuousAt_L S hdet hε hκ hδ p j hn
  have hA := continuousAt_A S hdet p j hn
  have he (q : S.Point) (hq : q ∈ nonzeroLocus S j ∩ initialTorus S) :
      L S hdet ε κ hδ q j = A S q j :=
    frozen_radial_equation_torus S hdet hε hκ hδ q hq.2 j hj
  exact le_antisymm
    (le_of_dense_open (dense_initialTorus S hdet) (isOpen_nonzeroLocus S j) hn hl hA
      (fun q hq => (he q hq).le))
    (le_of_dense_open (dense_initialTorus S hdet) (isOpen_nonzeroLocus S j) hn hA hl
      (fun q hq => (he q hq).ge))

end ClusterSkeleton.GlobalLiouvilleField
