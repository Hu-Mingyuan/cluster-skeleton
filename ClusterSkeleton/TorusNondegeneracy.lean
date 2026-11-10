import ClusterSkeleton.SmoothAtlas
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace

/-!
# Native logarithmic tangent coordinates on the initial torus

The exchange equations express the inclusion locally as a smooth graph over the
original coordinates. Its actual `mfderiv`, together with the accepted immersion
and equality of finite dimensions, gives tangent coordinates. Dividing by the
nonzero coordinates then gives the logarithmic equivalence.

Skewness of the weighted matrix `K = E * D` together with its nonvanishing
determinant `∏ d_i` prove nondegeneracy of the exact normalized imaginary
pairing; the coefficient is `K`, not `E`. The final consumers use the
constructed atlas.
These are torus-only results: no extension, closedness, primitive, flow, or
skeleton statement is asserted.
-/
noncomputable section
open scoped Manifold ContDiff BigOperators
open Set FsFltz.Geometry

namespace ClusterSkeleton.TorusNondegeneracy
variable {d : ℕ} (S : Seed d)

/-- The rational graph forced by the exchange equations on the initial torus. -/
def exchangeGraph (a : Fin d → ℂ) : (Fin d → ℂ) × (S.Mutable → ℂ) :=
  (a, fun i => (S.positiveMonomial a i + S.negativeMonomial a i) / a i)

theorem exchangeGraph_eq (p : S.Point) (hp : p ∈ initialTorus S) :
    exchangeGraph S p.a = p.val := by
  apply Prod.ext
  · rfl
  funext i
  change (S.positiveMonomial p.a i + S.negativeMonomial p.a i) / p.a i = p.b i
  rw [← p.exchange i, mul_div_cancel_left₀ _ (hp i)]

theorem exchangeGraph_smooth (a : Fin d → ℂ) (ha : ∀ j, a j ≠ 0) :
    ContDiffAt ℝ ∞ (exchangeGraph S) a := by
  suffices h : ContDiffAt ℂ ∞ (exchangeGraph S) a from h.restrict_scalars ℝ
  apply ContDiffAt.prodMk contDiffAt_id
  apply contDiffAt_pi.mpr
  intro i
  apply ContDiffAt.div _ (contDiff_apply ℂ ℂ (i : Fin d)).contDiffAt (ha i)
  apply ContDiffAt.add
  · unfold Seed.positiveMonomial
    apply ContDiff.contDiffAt
    apply contDiff_prod
    intro j _
    exact (contDiff_apply ℂ ℂ j).pow _
  · unfold Seed.negativeMonomial
    apply ContDiff.contDiffAt
    apply contDiff_prod
    intro j _
    exact (contDiff_apply ℂ ℂ j).pow _

variable (P : SmoothPresentation S)

/-- Native smoothness of the original-coordinate projection. -/
theorem original_smooth :
    letI := P.charts
    ContMDiff (𝓘(ℝ, Model (2 * d))) (𝓘(ℝ, Fin d → ℂ)) ∞ (fun p : S.Point => p.a) := by
  letI := P.charts
  exact (ContinuousLinearMap.fst ℝ (Fin d → ℂ) (S.Mutable → ℂ)).contMDiff.comp
    P.inclusion_smooth

/-- The differential of all original coordinates, in the actual tangent fiber. -/
def originalDifferential (p : S.Point) : P.manifold.Tangent p →L[ℝ] (Fin d → ℂ) :=
  letI := P.charts
  mfderiv (𝓘(ℝ, Model (2 * d))) (𝓘(ℝ, Fin d → ℂ)) (fun q : S.Point => q.a) p

theorem originalDifferential_apply (p : S.Point) (v : P.manifold.Tangent p) (j : Fin d) :
    originalDifferential S P p v j = P.coordinateDifferential j p v := by
  letI := P.charts
  let ev : (Fin d → ℂ) →L[ℝ] ℂ := ContinuousLinearMap.proj j
  have h := mfderiv_comp p (ev.mdifferentiable p.a)
    ((original_smooth S P p).mdifferentiableAt (by simp))
  rw [mfderiv_eq_fderiv, ev.hasFDerivAt.fderiv] at h
  exact (congrArg (fun f => f v) h).symm

/-- The exchange graph and the actual immersion force injectivity. -/
theorem originalDifferential_injective (p : S.Point) (hp : p ∈ initialTorus S) :
    Function.Injective (originalDifferential S P p) := by
  letI := P.charts
  have he : (fun q : S.Point => exchangeGraph S q.a) =ᶠ[nhds p] (fun q => q.val) := by
    filter_upwards [(isOpen_initialTorus S).mem_nhds hp] with q hq
    exact exchangeGraph_eq S q hq
  have hc := mfderiv_comp p ((exchangeGraph_smooth S p.a hp).contMDiffAt.mdifferentiableAt (by simp))
    ((original_smooth S P p).mdifferentiableAt (by simp))
  -- The native congruence theorem includes its tangent-space cast;
  -- equality of the ambient basepoints is supplied by `he` itself.
  have he' := he.mfderiv_eq (I := 𝓘(ℝ, Model (2 * d)))
    (I' := 𝓘(ℝ, (Fin d → ℂ) × (S.Mutable → ℂ)))
  intro v w hvw
  apply P.inclusion_immersion p
  have h := congrArg (mfderiv (𝓘(ℝ, Fin d → ℂ))
    (𝓘(ℝ, (Fin d → ℂ) × (S.Mutable → ℂ))) (exchangeGraph S) p.a) hvw
  change (_ ∘L originalDifferential S P p) v = (_ ∘L originalDifferential S P p) w at h
  unfold originalDifferential at h
  change (mfderiv (𝓘(ℝ, Fin d → ℂ)) _ (exchangeGraph S) p.a ∘L
    mfderiv (𝓘(ℝ, Model (2 * d))) (𝓘(ℝ, Fin d → ℂ)) (fun q : S.Point => q.a) p) v =
    (mfderiv (𝓘(ℝ, Fin d → ℂ)) _ (exchangeGraph S) p.a ∘L
    mfderiv (𝓘(ℝ, Model (2 * d))) (𝓘(ℝ, Fin d → ℂ)) (fun q : S.Point => q.a) p) w at h
  rw [← hc] at h
  have hv := congrArg (fun f => f v) he'
  have hw := congrArg (fun f => f w) he'
  exact hv.symm.trans (h.trans hw)

/-- The actual original-coordinate derivative promoted to a continuous equivalence. -/
def originalTangentEquiv (p : S.Point) (hp : p ∈ initialTorus S) :
    P.manifold.Tangent p ≃L[ℝ] (Fin d → ℂ) :=
  (LinearEquiv.ofInjectiveOfFinrankEq (originalDifferential S P p).toLinearMap
    (originalDifferential_injective S P p hp) (by
      change Module.finrank ℝ (Model (2 * d)) = Module.finrank ℝ (Fin d → ℂ)
      rw [finrank_euclideanSpace_fin, finrank_real_of_complex, Module.finrank_pi, Fintype.card_fin]
    )).toContinuousLinearEquiv

@[simp] theorem originalTangentEquiv_apply (p : S.Point) (hp : p ∈ initialTorus S)
    (v : P.manifold.Tangent p) (j : Fin d) :
    originalTangentEquiv S P p hp v j = P.coordinateDifferential j p v :=
  originalDifferential_apply S P p v j

/-- Coordinatewise division by a nonvanishing complex vector, as a real equivalence. -/
def divideEquiv (a : Fin d → ℂ) (ha : ∀ j, a j ≠ 0) :
    (Fin d → ℂ) ≃L[ℝ] (Fin d → ℂ) :=
  ({ toFun := fun u j => u j / a j
     invFun := fun u j => u j * a j
     left_inv := by intro u; funext j; exact div_mul_cancel₀ _ (ha j)
     right_inv := by intro u; funext j; exact mul_div_cancel_right₀ _ (ha j)
     map_add' := by intro u w; funext j; exact add_div _ _ _
     map_smul' := by intro c u; funext j; simp [smul_eq_mul, mul_div_assoc]
   } : (Fin d → ℂ) ≃ₗ[ℂ] (Fin d → ℂ)).toContinuousLinearEquiv.restrictScalars ℝ

/-- Logarithmic coordinates of the actual tangent vector. -/
def logarithmicTangentEquiv (p : S.Point) (hp : p ∈ initialTorus S) :
    P.manifold.Tangent p ≃L[ℝ] (Fin d → ℂ) :=
  (originalTangentEquiv S P p hp).trans (divideEquiv p.a hp)

@[simp] theorem logarithmicTangentEquiv_apply (p : S.Point) (hp : p ∈ initialTorus S)
    (v : P.manifold.Tangent p) (j : Fin d) :
    logarithmicTangentEquiv S P p hp v j = P.coordinateDifferential j p v / p.a j := by
  change originalTangentEquiv S P p hp v j / p.a j = _
  rw [originalTangentEquiv_apply]

/-- The weighted form matrix `K = E * D`, extended to the complex numbers.
This is the coefficient matrix of `SmoothPresentation.logarithmicImaginaryValue`;
with a nontrivial symmetrizer it is **not** the integral exchange matrix. -/
def complexMatrix : Matrix (Fin d) (Fin d) ℂ := fun i j => (S.K i j : ℂ)

theorem complexMatrix_map :
    complexMatrix S = (Rat.castHom ℂ).mapMatrix S.K := rfl

/-- The weighted determinant: unimodularity of `E` gives `det K = ∏ d_i`, which
is nonzero but no longer equal to one. -/
theorem complexMatrix_det (hdet : S.Unimodular) :
    (complexMatrix S).det = ∏ i, (S.D i : ℂ) := by
  rw [complexMatrix_map, ← RingHom.map_det, S.det_K_of_unimodular hdet]
  exact map_prod (Rat.castHom ℂ) _ _

theorem complexMatrix_det_ne_zero (hdet : S.Unimodular) :
    (complexMatrix S).det ≠ 0 := by
  rw [complexMatrix_det S hdet]
  exact Finset.prod_ne_zero_iff.mpr fun i _ => Rat.cast_ne_zero.mpr (S.D_ne_zero i)

theorem isUnit_complexMatrix_det (hdet : S.Unimodular) :
    IsUnit (complexMatrix S).det :=
  isUnit_iff_ne_zero.mpr (complexMatrix_det_ne_zero S hdet)

/-- Skewness of the weighted matrix `K` removes exactly the factor one half in
the antisymmetrization. Only `K_skew` is used; no integrality is needed. -/
theorem normalized_pairing (u w : Fin d → ℂ) :
    (1 / 2 : ℂ) * ∑ i, ∑ j, (S.K i j : ℂ) * (u i * w j - w i * u j) =
      ∑ j, (∑ i, (S.K i j : ℂ) * u i) * w j := by
  have hs : (∑ i, ∑ j, (S.K i j : ℂ) * (w i * u j)) =
      -(∑ i, ∑ j, (S.K i j : ℂ) * (u i * w j)) := by
    rw [Finset.sum_comm]
    simp only [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [S.K_skew j i, Rat.cast_neg]
    ring
  have ht : (∑ i, ∑ j, (S.K i j : ℂ) * (u i * w j)) =
      ∑ j, (∑ i, (S.K i j : ℂ) * u i) * w j := by
    rw [Finset.sum_comm]
    simp only [Finset.sum_mul, mul_assoc]
  simp only [mul_sub, Finset.sum_sub_distrib]
  rw [hs, ← ht]
  ring

/-- The imaginary part of the normalized complex pairing is real nondegenerate. -/
theorem normalized_pairing_nondegenerate (hdet : S.Unimodular) (u : Fin d → ℂ)
    (h : ∀ w : Fin d → ℂ,
      ((1 / 2 : ℂ) * ∑ i, ∑ j, (S.K i j : ℂ) * (u i * w j - w i * u j)).im = 0) :
    u = 0 := by
  classical
  have hz : ∀ j, (∑ i, (S.K i j : ℂ) * u i) = 0 := by
    intro j
    have hi := h (Pi.single j 1)
    have hr := h (Pi.single j Complex.I)
    rw [normalized_pairing] at hi hr
    simp only [Pi.single_apply] at hi hr
    simp at hi hr
    apply Complex.ext
    · simpa using hr
    · simpa using hi
  have hu : Matrix.vecMul u (complexMatrix S) = 0 := by
    funext j
    simpa [Matrix.vecMul, dotProduct, complexMatrix, mul_comm] using hz j
  apply Matrix.vecMul_injective_of_isUnit
    ((Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_complexMatrix_det S hdet))
  simpa using hu

/-- Torus-only nondegeneracy for any compatible smooth presentation. -/
theorem logarithmicImaginaryValue_nondegenerate (hdet : S.Unimodular)
    (p : S.Point) (hp : p ∈ initialTorus S) (v : P.manifold.Tangent p)
    (h : ∀ w, P.logarithmicImaginaryValue p v w = 0) : v = 0 := by
  let e := logarithmicTangentEquiv S P p hp
  have hz : e v = 0 := by
    apply normalized_pairing_nondegenerate S hdet
    intro z
    obtain ⟨w, rfl⟩ := e.surjective z
    simpa only [e, logarithmicTangentEquiv_apply, SmoothPresentation.logarithmicImaginaryValue]
      using h w
  apply e.injective
  simpa using hz

/-- The logarithmic tangent equivalence for the constructed atlas itself. -/
def smoothAtlas_logarithmicTangentEquiv (hdet : S.Unimodular)
    (p : S.Point) (hp : p ∈ initialTorus S) :
    (SmoothAtlas.presentation S hdet).manifold.Tangent p ≃L[ℝ] (Fin d → ℂ) :=
  logarithmicTangentEquiv S (SmoothAtlas.presentation S hdet) p hp

@[simp] theorem smoothAtlas_logarithmicTangentEquiv_apply (hdet : S.Unimodular)
    (p : S.Point) (hp : p ∈ initialTorus S)
    (v : (SmoothAtlas.presentation S hdet).manifold.Tangent p) (j : Fin d) :
    smoothAtlas_logarithmicTangentEquiv S hdet p hp v j =
      (SmoothAtlas.presentation S hdet).coordinateDifferential j p v / p.a j :=
  logarithmicTangentEquiv_apply S (SmoothAtlas.presentation S hdet) p hp v j

/-- Concrete consumer: the presentation is the constructed atlas. -/
theorem smoothAtlas_logarithmicImaginaryValue_nondegenerate (hdet : S.Unimodular)
    (p : S.Point) (hp : p ∈ initialTorus S)
    (v : (SmoothAtlas.presentation S hdet).manifold.Tangent p)
    (h : ∀ w, (SmoothAtlas.presentation S hdet).logarithmicImaginaryValue p v w = 0) :
    v = 0 :=
  logarithmicImaginaryValue_nondegenerate S (SmoothAtlas.presentation S hdet) hdet p hp v h

end ClusterSkeleton.TorusNondegeneracy

