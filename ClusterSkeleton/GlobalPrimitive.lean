import ClusterSkeleton.LocalPrimitive
import ClusterSkeleton.GlobalSymplectic

/-!
# The global primitive on the actual exchange manifold

The local primitives are glued on their constructed open cover. Density proves
uniqueness of smooth forms and the whole-form derivative identity; nondegeneracy
comes separately from the accepted zero-set chart calculation.
-/

noncomputable section
set_option autoImplicit false
open scoped Manifold ContDiff Topology BigOperators
open Set Filter FsFltz.Geometry

namespace ClusterSkeleton.GlobalPrimitive

/-- Local equality of native forms implies equality of their actual exterior
derivatives. The inverse chart pulls the neighborhood equality into a fixed
coefficient space, and the chart differential transports the derivative back. -/
theorem exteriorDerivative_eq_of_eventuallyEq {n k : ℕ} (M : SmoothManifold n)
    {eta theta : M.Form k} (p : M.Point)
    (h : ∀ᶠ q in 𝓝 p, eta q = theta q) :
    M.exteriorDerivative eta p = M.exteriorDerivative theta p := by
  let c := chartAt (Model n) p
  have hp : p ∈ c.source := mem_chart_source _ _
  have hi : c.symm (c p) = p := c.left_inv hp
  have hc : ContinuousAt c.symm (c p) := c.continuousAt_symm (c.map_source hp)
  have hn : ∀ᶠ y in 𝓝 (c p), eta (c.symm y) = theta (c.symm y) := by
    apply hc.eventually (p := fun q => eta q = theta q)
    simpa only [hi] using h
  have he : M.formInChart p eta =ᶠ[𝓝 (c p)] M.formInChart p theta := by
    filter_upwards [hn] with y hy
    exact congrArg (fun f => f.compContinuousLinearMap (M.inverseChartTangentMap p y)) hy
  exact congrArg (fun f => f.compContinuousLinearMap (M.chartTangentMap p p))
    he.extDeriv_eq

variable {d : ℕ} (S : Seed d) (hdet : S.Unimodular)

/-- Pointwise gluing of the constructed local primitive family. Positivity of
delta supplies the cover; the other bounds enter the compatibility proofs. -/
def alpha (ε κ : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    (SmoothAtlas.presentation S hdet).manifold.Form 1 :=
  LocalFormGluing.glue (SmoothAtlas.presentation S hdet).manifold
    (LocalPrimitive.neighborhood S ε κ δ) (LocalPrimitive.eta S hdet ε κ δ)
    (LocalPrimitive.covers S ε κ hδ)

/-- Restriction to every local domain, independent of the index selected by glue. -/
theorem alpha_eq_eta {ε κ δ : ℝ} (hε : 0 < ε) (hκ : 2 * ε + 1 ≤ κ)
    (hδ : 0 < δ) (p q : S.Point) (hq : q ∈ LocalPrimitive.neighborhood S ε κ δ p) :
    alpha S hdet ε κ hδ q = LocalPrimitive.eta S hdet ε κ δ p q :=
  LocalFormGluing.glue_eq (SmoothAtlas.presentation S hdet).manifold
    (LocalPrimitive.neighborhood S ε κ δ) (LocalPrimitive.eta S hdet ε κ δ)
    (LocalPrimitive.isOpen_neighborhood S ε κ δ) (LocalPrimitive.covers S ε κ hδ)
    (dense_initialTorus S hdet) (LocalPrimitive.locallySmooth_eta S hdet ε κ hδ)
    (LocalPrimitive.agree_on_torus S hdet hε hκ hδ) p q hq

/-- The glued one-form is smooth in the native atlas. -/
theorem isSmoothForm_alpha {ε κ δ : ℝ} (hε : 0 < ε) (hκ : 2 * ε + 1 ≤ κ)
    (hδ : 0 < δ) :
    (SmoothAtlas.presentation S hdet).manifold.IsSmoothForm (alpha S hdet ε κ hδ) :=
  LocalFormGluing.isSmoothForm_glue (SmoothAtlas.presentation S hdet).manifold
    (LocalPrimitive.neighborhood S ε κ δ) (LocalPrimitive.eta S hdet ε κ δ)
    (LocalPrimitive.isOpen_neighborhood S ε κ δ) (LocalPrimitive.covers S ε κ hδ)
    (dense_initialTorus S hdet) (LocalPrimitive.locallySmooth_eta S hdet ε κ hδ)
    (LocalPrimitive.agree_on_torus S hdet hε hκ hδ)

/-- Literal equality with the accepted corrected primitive on the initial torus. -/
theorem alpha_eq_torus {ε κ δ : ℝ} (hε : 0 < ε) (hκ : 2 * ε + 1 ≤ κ)
    (hδ : 0 < δ) (p : S.Point) (hp : p ∈ initialTorus S) :
    alpha S hdet ε κ hδ p = TorusCorrection.alpha S hdet ε κ δ p := by
  rw [alpha_eq_eta S hdet hε hκ hδ p p (LocalPrimitive.mem_neighborhood S ε κ hδ p)]
  exact LocalPrimitive.eta_eq_torus S hdet hε hκ hδ p p
    (LocalPrimitive.mem_neighborhood S ε κ hδ p) hp

/-- Arbitrary native tangent evaluation uses both full matrix index sets,
including every frozen coordinate. -/
theorem evalOne_alpha {ε κ δ : ℝ} (hε : 0 < ε) (hκ : 2 * ε + 1 ≤ κ)
    (hδ : 0 < δ) (p : S.Point) (hp : p ∈ initialTorus S)
    (v : (SmoothAtlas.presentation S hdet).manifold.Tangent p) :
    SmoothManifold.evalOne (alpha S hdet ε κ hδ) p v =
      (∑ i : Fin d, ∑ j : Fin d, (S.K i j : ℝ) * Real.log ‖p.a i‖ *
        ((SmoothAtlas.presentation S hdet).coordinateDifferential j p v / p.a j).im) +
      differentialCovector (SmoothAtlas.presentation S hdet).manifold
        (TorusCorrection.H S ε κ δ) p v := by
  change alpha S hdet ε κ hδ p (fun _ => v) = _
  rw [alpha_eq_torus S hdet hε hκ hδ p hp]
  exact TorusCorrection.evalOne_alpha S hdet ε κ δ p v

/-- Uniqueness among native smooth extensions of the literal torus form. -/
theorem eq_alpha_of_torus {ε κ δ : ℝ} (hε : 0 < ε) (hκ : 2 * ε + 1 ≤ κ)
    (hδ : 0 < δ) {theta : (SmoothAtlas.presentation S hdet).manifold.Form 1}
    (hs : (SmoothAtlas.presentation S hdet).manifold.IsSmoothForm theta)
    (ht : ∀ p ∈ initialTorus S, theta p = TorusCorrection.alpha S hdet ε κ δ p) :
    theta = alpha S hdet ε κ hδ :=
  FormExtensionUniqueness.form_eq_of_dense (SmoothAtlas.presentation S hdet).manifold
    (dense_initialTorus S hdet) hs (isSmoothForm_alpha S hdet hε hκ hδ)
    (fun p hp => (ht p hp).trans (alpha_eq_torus S hdet hε hκ hδ p hp).symm)

/-- Every subordinate selection gives the same native one-form. -/
theorem alpha_eq_selection {ε κ δ : ℝ} (hε : 0 < ε) (hκ : 2 * ε + 1 ≤ κ)
    (hδ : 0 < δ) (select : S.Point → S.Point)
    (hselect : ∀ p, p ∈ LocalPrimitive.neighborhood S ε κ δ (select p)) :
    alpha S hdet ε κ hδ = fun p => LocalPrimitive.eta S hdet ε κ δ (select p) p := by
  funext p
  exact alpha_eq_eta S hdet hε hκ hδ (select p) p (hselect p)

/-- Openness makes torus agreement an equality of germs, so the actual native
derivative agrees there with the accepted derivative of the torus primitive. -/
theorem exteriorDerivative_alpha_torus {ε κ δ : ℝ} (hε : 0 < ε)
    (hκ : 2 * ε + 1 ≤ κ) (hδ : 0 < δ) (p : S.Point) (hp : p ∈ initialTorus S) :
    (SmoothAtlas.presentation S hdet).manifold.exteriorDerivative
      (alpha S hdet ε κ hδ) p = GlobalTwoForm.omega S hdet p := by
  have he : ∀ᶠ q in 𝓝 p,
      alpha S hdet ε κ hδ q = TorusCorrection.alpha S hdet ε κ δ q := by
    filter_upwards [(isOpen_initialTorus S).mem_nhds hp] with q hq
    exact alpha_eq_torus S hdet hε hκ hδ q hq
  exact (exteriorDerivative_eq_of_eventuallyEq (SmoothAtlas.presentation S hdet).manifold
    p he).trans (TorusCorrection.exteriorDerivative_alpha S hdet ε κ hδ p hp)

/-- Equality of the entire native two-forms, proved by smoothness and density. -/
theorem exteriorDerivative_alpha {ε κ δ : ℝ} (hε : 0 < ε)
    (hκ : 2 * ε + 1 ≤ κ) (hδ : 0 < δ) :
    (SmoothAtlas.presentation S hdet).manifold.exteriorDerivative
      (alpha S hdet ε κ hδ) = GlobalTwoForm.omega S hdet :=
  FormExtensionUniqueness.form_eq_of_dense (SmoothAtlas.presentation S hdet).manifold
    (dense_initialTorus S hdet)
    (SmoothManifold.isSmoothForm_exteriorDerivative _ _ (isSmoothForm_alpha S hdet hε hκ hδ))
    (GlobalTwoForm.isSmoothForm_omega S hdet)
    (exteriorDerivative_alpha_torus S hdet hε hκ hδ)

/-- Nondegeneracy uses the accepted chart-based theorem, never density. -/
theorem nondegenerate_exteriorDerivative_alpha {ε κ δ : ℝ} (hε : 0 < ε)
    (hκ : 2 * ε + 1 ≤ κ) (hδ : 0 < δ) (p : S.Point) :
    (SmoothAtlas.presentation S hdet).manifold.Nondegenerate
      ((SmoothAtlas.presentation S hdet).manifold.exteriorDerivative
        (alpha S hdet ε κ hδ)) p := by
  rw [exteriorDerivative_alpha S hdet hε hκ hδ]
  exact GlobalSymplectic.nondegenerate_omega S hdet p

/-- The derivative of the constructed primitive is the accepted symplectic form. -/
theorem isSymplecticOn_exteriorDerivative_alpha {ε κ δ : ℝ} (hε : 0 < ε)
    (hκ : 2 * ε + 1 ≤ κ) (hδ : 0 < δ) :
    (SmoothAtlas.presentation S hdet).manifold.IsSymplecticOn
      ((SmoothAtlas.presentation S hdet).manifold.exteriorDerivative
        (alpha S hdet ε κ hδ)) Set.univ := by
  rw [exteriorDerivative_alpha S hdet hε hκ hδ]
  exact GlobalSymplectic.isSymplecticOn_omega S hdet

/-- Constructed admissible parameters; no parameter witness is a premise. -/
theorem concrete_parameters :
    (0 : ℝ) < 1 ∧ 2 * (1 : ℝ) + 1 ≤ 3 ∧
      0 < Real.pi / 2 ∧ Real.pi / 2 < Real.pi := by
  have hp := Real.pi_pos
  constructor
  · norm_num
  constructor
  · norm_num
  constructor <;> linarith

/-- A global smooth exact symplectic primitive with admissible manuscript
parameters and literal initial-torus agreement, with no geometric witness premise. -/
theorem exists_global_primitive :
    ∃ (ε κ δ : ℝ) (theta : (SmoothAtlas.presentation S hdet).manifold.Form 1),
      0 < ε ∧ 2 * ε + 1 ≤ κ ∧ 0 < δ ∧ δ < Real.pi ∧
      (SmoothAtlas.presentation S hdet).manifold.IsSmoothForm theta ∧
      (∀ p ∈ initialTorus S, theta p = TorusCorrection.alpha S hdet ε κ δ p) ∧
      (SmoothAtlas.presentation S hdet).manifold.exteriorDerivative theta =
        GlobalTwoForm.omega S hdet ∧
      (∀ p, (SmoothAtlas.presentation S hdet).manifold.Nondegenerate
        ((SmoothAtlas.presentation S hdet).manifold.exteriorDerivative theta) p) := by
  obtain ⟨hε, hκ, hδ, hδπ⟩ := concrete_parameters
  exact ⟨1, 3, Real.pi / 2, alpha S hdet 1 3 hδ, hε, hκ, hδ, hδπ,
    isSmoothForm_alpha S hdet hε hκ hδ, alpha_eq_torus S hdet hε hκ hδ,
    exteriorDerivative_alpha S hdet hε hκ hδ,
    nondegenerate_exteriorDerivative_alpha S hdet hε hκ hδ⟩

end ClusterSkeleton.GlobalPrimitive
