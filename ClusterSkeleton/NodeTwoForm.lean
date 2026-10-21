import ClusterSkeleton.TorusNondegeneracy
import ClusterSkeleton.FormExtensionUniqueness
import Mathlib.Analysis.Calculus.Deriv.ZPow

/-!
# The complete node two-form

The exponent matrix is the accepted inverse matrix T, not its transpose.
The residual coefficient matrix is Tᵀ B[outside,outside] T. Node characters
are q = uv - 1. All formulas below use the full node domain, including u = 0.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open scoped Manifold ContDiff BigOperators
open Set FsFltz.Geometry

namespace ClusterSkeleton.NodeTwoForm

/-- The unnormalized wedge of two complex covectors. -/
def wedge {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (a b : E →L[ℂ] ℂ) : E [⋀^Fin 2]→L[ℂ] ℂ where
  toFun v := a (v 0) * b (v 1) - a (v 1) * b (v 0)
  map_update_add' v i x y := by fin_cases i <;> simp <;> ring
  map_update_smul' v i c x := by fin_cases i <;> simp [smul_eq_mul] <;> ring
  map_eq_zero_of_eq' v i j h hij := by
    fin_cases i <;> fin_cases j <;> simp_all
  cont := by fun_prop

@[simp] theorem wedge_apply {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (a b : E →L[ℂ] ℂ) (v : Fin 2 → E) :
    wedge a b v = a (v 0) * b (v 1) - a (v 1) * b (v 0) := rfl

/-- Wedge is a continuous bilinear operation in finite dimension. -/
def wedgeCLM {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [FiniteDimensional ℂ E] :
    (E →L[ℂ] ℂ) →L[ℂ] (E →L[ℂ] ℂ) →L[ℂ] (E [⋀^Fin 2]→L[ℂ] ℂ) :=
  LinearMap.toContinuousLinearMap
  { toFun := fun a => LinearMap.toContinuousLinearMap
      { toFun := wedge a
        map_add' := by intros; ext v; simp; ring
        map_smul' := by intros; ext v; simp [smul_eq_mul]; ring }
    map_add' := by intros; ext b v; simp; ring
    map_smul' := by intros; ext b v; simp [smul_eq_mul]; ring }

/-- Smooth dependence of the wedge in its two covectors. -/
theorem contDiffAt_wedge {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [FiniteDimensional ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F]
    {a b : F → E →L[ℂ] ℂ} {x : F}
    (ha : ContDiffAt ℂ ∞ a x) (hb : ContDiffAt ℂ ∞ b x) :
    ContDiffAt ℂ ∞ (fun y => wedge (a y) (b y)) x := by
  let W : (E →L[ℂ] ℂ) →L[ℂ] (E →L[ℂ] ℂ) →L[ℂ] (E [⋀^Fin 2]→L[ℂ] ℂ) := wedgeCLM
  have hw := ContinuousLinearMap.contDiff (𝕜 := ℂ) (E := E →L[ℂ] ℂ)
    (F := (E →L[ℂ] ℂ) →L[ℂ] (E [⋀^Fin 2]→L[ℂ] ℂ)) (n := ∞) W
  exact (hw.contDiffAt.comp x ha).clm_apply hb

variable {d : ℕ} (S : Seed d) (I : Finset (Fin d))
open IndependentNodeChart

/-- Native coordinate covectors on the accepted node vector space. -/
def du (i : {i : Fin d // i ∈ I}) : Vector S I →L[ℂ] ℂ :=
  (ContinuousLinearMap.fst ℂ ℂ ℂ).comp
    ((ContinuousLinearMap.proj i).comp (ContinuousLinearMap.fst ℂ _ _))
def dv (i : {i : Fin d // i ∈ I}) : Vector S I →L[ℂ] ℂ :=
  (ContinuousLinearMap.snd ℂ ℂ ℂ).comp
    ((ContinuousLinearMap.proj i).comp (ContinuousLinearMap.fst ℂ _ _))
def dw (k : Complement S I) : Vector S I →L[ℂ] ℂ :=
  (ContinuousLinearMap.proj k).comp (ContinuousLinearMap.snd ℂ _ _)

/-- The exact derivative of q = uv - 1, divided by q; or dw/w on a free factor. -/
def logParameter (x : Vector S I) : IndependentRowBasisIndex S I → (Vector S I →L[ℂ] ℂ) :=
  Sum.elim (fun i => ((x.1 i).2 / rawParameters S I x (Sum.inl i)) • du S I i +
    ((x.1 i).1 / rawParameters S I x (Sum.inl i)) • dv S I i)
    (fun k => (x.2 k)⁻¹ • dw S I k)

@[simp] theorem logParameter_inl (x v : Vector S I) (i : {i : Fin d // i ∈ I}) :
    logParameter S I x (Sum.inl i) v =
      ((x.1 i).2 * (v.1 i).1 + (x.1 i).1 * (v.1 i).2) /
        ((x.1 i).1 * (x.1 i).2 - 1) := by
  simp [logParameter, du, dv, rawParameters, smul_eq_mul]
  ring

@[simp] theorem logParameter_inr (x v : Vector S I) (k : Complement S I) :
    logParameter S I x (Sum.inr k) v = v.2 k / x.2 k := by
  simp [logParameter, dw, smul_eq_mul, div_eq_mul_inv, mul_comm]

variable (hdet : S.Unimodular) (hI : S.Independent I)

/-- All B-dependent residual coefficients, over the integers, in the accepted basis. -/
def residualMatrix : Matrix (IndependentRowBasisIndex S I) (IndependentRowBasisIndex S I) ℤ :=
  (independentRowInverseMatrix S I hdet hI).transpose *
    (S.B.submatrix (fun j : {j : Fin d // j ∉ I} => j.val) (fun k : {j : Fin d // j ∉ I} => k.val)) * independentRowInverseMatrix S I hdet hI

/-- The full complex form on the literal node vector space. Its geometric domain is `domain S I`. -/
def complexForm (x : Vector S I) : Vector S I [⋀^Fin 2]→L[ℂ] ℂ :=
  (∑ i, (rawParameters S I x (Sum.inl i))⁻¹ • wedge (du S I i) (dv S I i)) +
  (1 / 2 : ℂ) • ∑ k, ∑ l, (residualMatrix S I hdet hI k l : ℂ) •
    wedge (logParameter S I x k) (logParameter S I x l)

/-- Exact normalization: take the imaginary part after forming the complex two-form. -/
def realForm (x : Vector S I) : Vector S I [⋀^Fin 2]→L[ℝ] ℝ :=
  Complex.imCLM.compContinuousAlternatingMap ((complexForm S I hdet hI x).restrictScalars ℝ)

/-- Actual native tangent map into the accepted node coordinates, with the constructed atlas. -/
def tangentMap (p : S.Point) :
    (SmoothAtlas.presentation S hdet).manifold.Tangent p →L[ℝ] Vector S I :=
  letI := SmoothAtlas.charts S hdet
  mfderiv (𝓘(ℝ, FsFltz.Geometry.Model (2 * d))) (𝓘(ℝ, Vector S I))
    (SmoothAtlas.rawChart S hdet I hI) p

/-- A native real two-form on each independent locus, pulled back by the actual chart derivative.
Values outside `candidateChartLocus S I` have no asserted geometric meaning. -/
def localForm : (SmoothAtlas.presentation S hdet).manifold.Form 2 :=
  fun p => (realForm S I hdet hI (SmoothAtlas.rawChart S hdet I hI p)).compContinuousLinearMap
    (tangentMap S I hdet hI p)

/-- Cancellation at a nonzero u; q need only satisfy the accepted node-domain condition. -/
theorem node_cancellation (u v a b c e : ℂ) (hu : u ≠ 0) (hq : u * v - 1 ≠ 0) :
    a / u * ((v * c + u * e) / (u * v - 1)) -
      c / u * ((v * a + u * b) / (u * v - 1)) =
        (a * e - c * b) / (u * v - 1) := by
  field_simp
  <;> ring

/-- At every boundary center, q=-1 and dlog(q)=-v du, including v=0. -/
theorem logParameter_boundary (x t : Vector S I) (hz : ∀ i, (x.1 i).1 = 0)
    (i : {i : Fin d // i ∈ I}) :
    logParameter S I x (Sum.inl i) t = -(x.1 i).2 * (t.1 i).1 := by
  rw [logParameter_inl, hz i]
  simp [div_neg, div_one]

/-- The literal character differential, checked against native Fréchet derivatives. -/
theorem hasFDerivAt_parameter {x : Vector S I} (hx : x ∈ domain S I)
    (k : IndependentRowBasisIndex S I) :
    HasFDerivAt (fun y => rawParameters S I y k)
      (rawParameters S I x k • logParameter S I x k) x := by
  cases k with
  | inl i =>
    have h := (((du S I i).hasFDerivAt (x := x)).mul (dv S I i).hasFDerivAt).sub_const (1 : ℂ)
    apply h.congr_fderiv
    apply ContinuousLinearMap.ext
    intro t
    simp [logParameter, rawParameters, du, dv, smul_eq_mul]
    field_simp [sub_ne_zero.mpr (hx.1 i)]
    <;> ring
  | inr k =>
    apply (dw S I k).hasFDerivAt.congr_fderiv
    apply ContinuousLinearMap.ext
    intro t
    simp [logParameter, rawParameters, dw, smul_eq_mul, hx.2 k]

theorem contDiffAt_logParameter {x : Vector S I} (hx : x ∈ domain S I)
    (k : IndependentRowBasisIndex S I) :
    ContDiffAt ℂ ∞ (fun y => logParameter S I y k) x := by
  cases k with
  | inl i =>
    exact ((((dv S I i).contDiff.contDiffAt).div
      (contDiff_rawParameters S I (Sum.inl i)).contDiffAt
      (rawParameters_ne_zero S I hx _)).smul contDiffAt_const).add
      ((((du S I i).contDiff.contDiffAt).div
      (contDiff_rawParameters S I (Sum.inl i)).contDiffAt
      (rawParameters_ne_zero S I hx _)).smul contDiffAt_const)
  | inr k =>
    exact (((dw S I k).contDiff.contDiffAt).inv (hx.2 k)).smul contDiffAt_const

variable (hdet : S.Unimodular) (hI : S.Independent I)

theorem contDiffAt_complexForm {x : Vector S I} (hx : x ∈ domain S I) :
    ContDiffAt ℂ ∞ (complexForm S I hdet hI) x := by
  apply ContDiffAt.add
  · apply ContDiffAt.sum
    intro i _
    exact (((contDiff_rawParameters S I (Sum.inl i)).contDiffAt).inv
      (rawParameters_ne_zero S I hx _)).smul contDiffAt_const
  · apply ContDiffAt.const_smul
    apply ContDiffAt.sum
    intro k _
    apply ContDiffAt.sum
    intro l _
    exact (contDiffAt_wedge (contDiffAt_logParameter S I hx k)
      (contDiffAt_logParameter S I hx l)).const_smul _

/-- The accepted basis gives RT=[Id,0], with no sign or transpose change. -/
theorem row_inverse (i : {i : Fin d // i ∈ I}) (k : IndependentRowBasisIndex S I) :
    (∑ j : {j : Fin d // j ∉ I}, S.B i j * independentRowInverseMatrix S I hdet hI j k) =
      if Sum.inl i = k then 1 else 0 := by
  have h := congrFun (congrFun (independentRowForward_mul_inverse S I hdet hI) (Sum.inl i)) k
  simpa only [Matrix.mul_apply, independentRowForwardMatrix_inl, Matrix.one_apply] using h

/-- Inverse Laurent logarithmic differential, retaining every inverse exponent. -/
def outsideLog (x : Vector S I) (j : {j : Fin d // j ∉ I}) : Vector S I →L[ℂ] ℂ :=
  ∑ k, (independentRowInverseMatrix S I hdet hI j k : ℂ) • logParameter S I x k

theorem row_outsideLog (x t : Vector S I) (i : {i : Fin d // i ∈ I}) :
    (∑ j : {j : Fin d // j ∉ I}, (S.B i j : ℂ) * outsideLog S I hdet hI x j t) =
      logParameter S I x (Sum.inl i) t := by
  classical
  simp only [outsideLog, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
    smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  simp_rw [← mul_assoc, ← Finset.sum_mul]
  have h (k : IndependentRowBasisIndex S I) :
      (∑ j : {j : Fin d // j ∉ I}, (S.B i j : ℂ) *
        (independentRowInverseMatrix S I hdet hI j k : ℂ)) = if Sum.inl i = k then 1 else 0 := by
    exact_mod_cast row_inverse S I hdet hI i k
  simp_rw [h]
  simp

/-- A product rule in logarithmic form; the inputs are actual native derivatives. -/
theorem hasFDerivAt_product_log {E κ : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (s : Finset κ) {f : κ → E → ℂ} {l : κ → E →L[ℂ] ℂ} {x : E}
    (h : ∀ i ∈ s, HasFDerivAt (f i) (f i x • l i) x) :
    HasFDerivAt (fun y => ∏ i ∈ s, f i y)
      ((∏ i ∈ s, f i x) • ∑ i ∈ s, l i) x := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hasFDerivAt_const (𝕜 := ℂ) (1 : ℂ) x
  | @insert i s hi ih =>
    have hs := ih (fun j hj => h j (Finset.mem_insert_of_mem hj))
    have hp := (h i (Finset.mem_insert_self _ _)).mul hs
    simp only [Finset.prod_insert hi, Finset.sum_insert hi]
    apply hp.congr_fderiv
    ext t
    simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply, smul_eq_mul]
    ring

/-- The Laurent-power rule with the exact integer exponent. -/
theorem hasFDerivAt_zpow_log {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {f : E → ℂ} {l : E →L[ℂ] ℂ} {x : E} (hf : HasFDerivAt f (f x • l) x)
    (hx : f x ≠ 0) (n : ℤ) :
    HasFDerivAt (fun y => f y ^ n) ((f x ^ n) • ((n : ℂ) • l)) x := by
  have h := (hasDerivAt_zpow n (f x) (Or.inl hx)).comp_hasFDerivAt x hf
  apply h.congr_fderiv
  ext t
  simp [zpow_sub₀ hx, smul_eq_mul]
  field_simp
  <;> ring


/-- The inverse Laurent expression differentiates to the specified inverse-matrix covector. -/
theorem hasFDerivAt_rawOutside {x : Vector S I} (hx : x ∈ domain S I)
    (j : {j : Fin d // j ∉ I}) :
    HasFDerivAt (fun y => rawOutside S I hdet hI y j)
      (rawOutside S I hdet hI x j • outsideLog S I hdet hI x j) x := by
  apply hasFDerivAt_product_log
  intro k _
  exact hasFDerivAt_zpow_log (hasFDerivAt_parameter S I hx k)
    (rawParameters_ne_zero S I hx k) _

/-- The original logarithmic tangent vector recovered from the actual node chart. -/
def originalLog (x t : Vector S I) (j : Fin d) : ℂ :=
  if hj : j ∈ I then (t.1 ⟨j, hj⟩).1 / (x.1 ⟨j, hj⟩).1
  else outsideLog S I hdet hI x ⟨j, hj⟩ t

/-- The native derivative of each recovered original coordinate, divided by that coordinate. -/
theorem originalLog_eq_fderiv {x : Vector S I} (hx : x ∈ domain S I)
    (t : Vector S I) (j : Fin d) :
    originalLog S I hdet hI x t j =
      fderiv ℂ (fun y => rawOriginal S I hdet hI y j) x t / rawOriginal S I hdet hI x j := by
  classical
  by_cases hj : j ∈ I
  · simp only [originalLog, rawOriginal, dif_pos hj]
    change du S I ⟨j, hj⟩ t / _ = fderiv ℂ (du S I ⟨j, hj⟩) x t / _
    rw [(du S I ⟨j, hj⟩).hasFDerivAt.fderiv]
  · simp only [originalLog, rawOriginal, dif_neg hj]
    rw [(hasFDerivAt_rawOutside S I hdet hI hx ⟨j, hj⟩).fderiv]
    simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
    have hn := rawOriginal_ne_zero S I hdet hI hx j hj
    simp only [rawOriginal, dite_eq_right hj] at hn
    rw [mul_div_cancel_left₀ _ hn]

/-- A normalized alternating matrix expression, retaining the factor one half. -/
def matrixValue {κ : Type*} [Fintype κ] (B : Matrix κ κ ℂ) (a b : κ → ℂ) : ℂ :=
  (1 / 2 : ℂ) * ∑ i, ∑ j, B i j * (a i * b j - b i * a j)

/-- Equivalent dot-product notation, without a skew-symmetry premise. -/
theorem matrixValue_dot {κ : Type*} [Fintype κ] (B : Matrix κ κ ℂ) (a b : κ → ℂ) :
    matrixValue B a b = (1 / 2 : ℂ) * (dotProduct a (B.mulVec b) - dotProduct b (B.mulVec a)) := by
  simp only [matrixValue, Matrix.mulVec, dotProduct, Finset.mul_sum,
    mul_sub, Finset.sum_sub_distrib]
  congr 1 <;>
    apply Finset.sum_congr rfl <;> intro i _ <;>
    apply Finset.sum_congr rfl <;> intro j _ <;> ring

/-- The exact transpose convention under a change of logarithmic coordinates. -/
theorem matrixValue_congruence {κ ι : Type*} [Fintype κ] [Fintype ι]
    (B : Matrix κ κ ℂ) (T : Matrix κ ι ℂ) (a b : ι → ℂ) :
    matrixValue (T.transpose * B * T) a b = matrixValue B (T.mulVec a) (T.mulVec b) := by
  simp only [matrixValue_dot, ← Matrix.mulVec_mulVec]
  congr 2 <;> rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]

/-- For a skew matrix the normalization cancels the antisymmetrization, exactly once. -/
theorem matrixValue_skew {κ : Type*} [Fintype κ] (B : Matrix κ κ ℂ)
    (hB : ∀ i j, B i j = -B j i) (a b : κ → ℂ) :
    matrixValue B a b = ∑ i, ∑ j, B i j * (a i * b j) := by
  have hs : (∑ i, ∑ j, B i j * (b i * a j)) = -(∑ i, ∑ j, B i j * (a i * b j)) := by
    rw [Finset.sum_comm]
    simp only [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [hB j i]
    ring
  simp only [matrixValue, mul_sub, Finset.sum_sub_distrib]
  rw [hs]
  ring


include hI in
/-- Expansion into the independent incident rows and the entire outside block. -/
theorem matrixValue_split (a b : Fin d → ℂ) :
    matrixValue (TorusNondegeneracy.complexMatrix S) a b =
      (∑ i : {i : Fin d // i ∈ I},
        (a i * (∑ j : {j : Fin d // j ∉ I}, (S.B i j : ℂ) * b j) -
        b i * (∑ j : {j : Fin d // j ∉ I}, (S.B i j : ℂ) * a j))) +
      matrixValue (TorusNondegeneracy.complexMatrix S |>.submatrix
        (fun j : {j : Fin d // j ∉ I} => j.val) (fun j : {j : Fin d // j ∉ I} => j.val))
        (fun j => a j) (fun j => b j) := by
  classical
  have hsk (i j : Fin d) : (S.B i j : ℂ) = -(S.B j i : ℂ) := by
    rw [S.skew i j, Int.cast_neg]
  rw [matrixValue_skew (TorusNondegeneracy.complexMatrix S) hsk a b,
    matrixValue_skew ((TorusNondegeneracy.complexMatrix S).submatrix
      (fun j : {j : Fin d // j ∉ I} => j.val) (fun j : {j : Fin d // j ∉ I} => j.val))
      (fun i j => hsk i j) (fun j => a j) (fun j => b j)]
  have part (f : Fin d → ℂ) : (∑ i, f i) =
      (∑ i : {i : Fin d // i ∈ I}, f i) + ∑ j : {j : Fin d // j ∉ I}, f j :=
    by
      convert! (Fintype.sum_subtype_add_sum_subtype (fun i => i ∈ I) f).symm using 1
      apply congrArg₂ (· + ·)
      all_goals
        apply Finset.sum_congr
        · ext i; simp
        · intro i _; rfl
  simp only [TorusNondegeneracy.complexMatrix, Matrix.submatrix_apply]
  rw [part]
  simp_rw [part, Finset.sum_add_distrib]
  have hii : (∑ i : {i : Fin d // i ∈ I}, ∑ j : {j : Fin d // j ∈ I},
      (S.B i j : ℂ) * (a i * b j)) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    apply Finset.sum_eq_zero
    intro j _
    rw [hI.2 i i.property j j.property]
    simp
  rw [hii, zero_add]
  have hc : (∑ j : {j : Fin d // j ∉ I}, ∑ i : {i : Fin d // i ∈ I},
      (S.B j i : ℂ) * (a j * b i)) =
      -(∑ i : {i : Fin d // i ∈ I}, b i * ∑ j : {j : Fin d // j ∉ I}, (S.B i j : ℂ) * a j) := by
    rw [Finset.sum_comm]
    simp only [← Finset.sum_neg_distrib, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [hsk j i]
    ring
  rw [hc]
  simp only [Finset.sum_sub_distrib, Finset.mul_sum]
  have ha : (∑ i : {i : Fin d // i ∈ I}, ∑ j : {j : Fin d // j ∉ I},
      (S.B i j : ℂ) * (a i * b j)) =
      ∑ i : {i : Fin d // i ∈ I}, ∑ j : {j : Fin d // j ∉ I}, a i * ((S.B i j : ℂ) * b j) := by
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [ha]
  ring

/-- The integer congruence matrix casts to the same complex congruence matrix. -/
theorem residualMatrix_cast :
    (fun k l => (residualMatrix S I hdet hI k l : ℂ)) =
      (independentRowInverseMatrix S I hdet hI |>.map (Int.castRingHom ℂ)).transpose *
      (S.B.submatrix (fun j : {j : Fin d // j ∉ I} => j.val)
        (fun j : {j : Fin d // j ∉ I} => j.val) |>.map (Int.castRingHom ℂ)) *
      (independentRowInverseMatrix S I hdet hI |>.map (Int.castRingHom ℂ)) := by
  ext k l
  simp [residualMatrix, Matrix.mul_apply, Matrix.transpose_apply]

/-- The full expression in the original outside covectors. -/
theorem complexForm_apply (x : Vector S I) (t : Fin 2 → Vector S I) :
    complexForm S I hdet hI x t =
      (∑ i, (((t 0).1 i |>.1) * ((t 1).1 i |>.2) /
        rawParameters S I x (Sum.inl i) -
        ((t 1).1 i |>.1) * ((t 0).1 i |>.2) / rawParameters S I x (Sum.inl i))) +
      matrixValue (S.B.submatrix (fun j : {j : Fin d // j ∉ I} => j.val)
        (fun j : {j : Fin d // j ∉ I} => j.val) |>.map (Int.castRingHom ℂ))
        (fun j => outsideLog S I hdet hI x j (t 0))
        (fun j => outsideLog S I hdet hI x j (t 1)) := by
  have h := matrixValue_congruence
    (S.B.submatrix (fun j : {j : Fin d // j ∉ I} => j.val)
      (fun j : {j : Fin d // j ∉ I} => j.val) |>.map (Int.castRingHom ℂ))
    (independentRowInverseMatrix S I hdet hI |>.map (Int.castRingHom ℂ))
    (fun k => logParameter S I x k (t 0)) (fun k => logParameter S I x k (t 1))
  rw [← residualMatrix_cast S I hdet hI] at h
  simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, Int.coe_castRingHom] at h
  simp only [complexForm, ContinuousAlternatingMap.add_apply,
    ContinuousAlternatingMap.sum_apply, ContinuousAlternatingMap.smul_apply, smul_eq_mul, wedge_apply]
  rw [show (1 / 2 : ℂ) * _ = _ from h]
  apply congrArg₂ (· + ·)
  · apply Finset.sum_congr rfl
    intro i _
    simp [du, dv, div_eq_mul_inv]
    ring
  · congr 1 <;> funext j <;>
      simp [outsideLog, Matrix.mulVec, dotProduct, smul_eq_mul]

/-- The recovered original coordinates agree with the actual point on the full chart source. -/
theorem rawOriginal_chart (p : S.Point) (hp : p ∈ candidateChartLocus S I) :
    rawOriginal S I hdet hI (SmoothAtlas.rawChart S hdet I hI p) = p.a := by
  change rawOriginal S I hdet hI (ambientForward S I hdet hI p.val) = _
  rw [ambientForward_eq S I hdet hI ⟨p, hp⟩, rawOriginal_flatten]
  exact congrArg (fun q : Locus S I => q.val.a) (backward_forward S I hdet hI ⟨p, hp⟩)

/-- The native node chart is smooth at every point of its source in the accepted atlas. -/
theorem chart_smooth (p : S.Point) (hp : p ∈ candidateChartLocus S I) :
    letI := SmoothAtlas.charts S hdet
    ContMDiffAt (𝓘(ℝ, FsFltz.Geometry.Model (2 * d))) (𝓘(ℝ, Vector S I)) ∞
      (SmoothAtlas.rawChart S hdet I hI) p := by
  letI := SmoothAtlas.charts S hdet
  exact (contDiffAt_ambientForward_real S I hdet hI ⟨p, hp⟩).contMDiffAt.comp p
    (SmoothAtlas.inclusion_smooth S hdet p)

/-- Logarithmic differentiation of the inverse chart also holds for the native real derivative. -/
theorem originalLog_eq_real_fderiv {x : Vector S I} (hx : x ∈ domain S I)
    (t : Vector S I) (j : Fin d) :
    originalLog S I hdet hI x t j =
      fderiv ℝ (fun y => rawOriginal S I hdet hI y j) x t / rawOriginal S I hdet hI x j := by
  have hd := ((contDiff_apply ℂ ℂ j).contDiffAt.comp x
    (contDiffAt_rawOriginal S I hdet hI hx)).differentiableAt (by simp)
  have he := hd.fderiv_restrictScalars ℝ
  simp only [Function.comp_def] at he
  rw [he]
  exact originalLog_eq_fderiv S I hdet hI hx t j

/-- The original logarithmic tangent entries, proved from the actual native chain rule. -/
theorem originalLog_tangentMap (p : S.Point) (hp : p ∈ candidateChartLocus S I)
    (t : (SmoothAtlas.presentation S hdet).manifold.Tangent p) (j : Fin d) :
    originalLog S I hdet hI (SmoothAtlas.rawChart S hdet I hI p)
      (tangentMap S I hdet hI p t) j =
        (SmoothAtlas.presentation S hdet).coordinateDifferential j p t / p.a j := by
  letI := SmoothAtlas.charts S hdet
  let x := SmoothAtlas.rawChart S hdet I hI p
  have hx : x ∈ domain S I := (SmoothAtlas.rawChart S hdet I hI).map_source hp
  have hs := ((contDiff_apply ℂ ℂ j).contDiffAt.comp x
    (contDiffAt_rawOriginal S I hdet hI hx)).restrict_scalars ℝ
  have hc := mfderiv_comp p (hs.contMDiffAt.mdifferentiableAt (by simp))
    ((chart_smooth S I hdet hI p hp).mdifferentiableAt (by simp))
  have he : (fun q : S.Point => rawOriginal S I hdet hI
      (SmoothAtlas.rawChart S hdet I hI q) j) =ᶠ[nhds p] (fun q => q.a j) := by
    filter_upwards [(isOpen_candidateChartLocus S I).mem_nhds hp] with q hq
    exact congrFun (rawOriginal_chart S I hdet hI q hq) j
  have he' := he.mfderiv_eq (I := 𝓘(ℝ, FsFltz.Geometry.Model (2 * d))) (I' := 𝓘(ℝ, ℂ))
  rw [originalLog_eq_real_fderiv S I hdet hI hx, rawOriginal_chart S I hdet hI p hp]
  congr 1
  rw [mfderiv_eq_fderiv] at hc
  exact (congrArg (fun f => f t) hc).symm.trans (congrArg (fun f => f t) he')

/-- Full complex torus restriction in node tangent coordinates. -/
theorem complexForm_torus {x : Vector S I} (hx : x ∈ domain S I)
    (hu : ∀ i, (x.1 i).1 ≠ 0) (a b : Vector S I) :
    complexForm S I hdet hI x ![a,b] =
      matrixValue (TorusNondegeneracy.complexMatrix S)
        (originalLog S I hdet hI x a) (originalLog S I hdet hI x b) := by
  rw [complexForm_apply, matrixValue_split S I hI]
  have hin (i : {i : Fin d // i ∈ I}) (v : Vector S I) :
      originalLog S I hdet hI x v i = (v.1 i).1 / (x.1 i).1 := by
    simp only [originalLog, dite_eq_left i.property]
  have hout (j : {j : Fin d // j ∉ I}) (v : Vector S I) :
      originalLog S I hdet hI x v j = outsideLog S I hdet hI x j v := by
    simp only [originalLog, dite_eq_right j.property]
  simp_rw [hin, hout, row_outsideLog]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
    logParameter_inl, rawParameters, Sum.elim_inl]
  rw [← sub_div]
  exact (node_cancellation _ _ _ _ _ _ (hu i) (rawParameters_ne_zero S I hx (Sum.inl i))).symm

/-- The exact real torus form on the actual accepted manifold. -/
theorem localForm_torus (p : S.Point) (hp : p ∈ initialTorus S)
    (a b : (SmoothAtlas.presentation S hdet).manifold.Tangent p) :
    SmoothManifold.evalTwo (localForm S I hdet hI) p a b =
      (SmoothAtlas.presentation S hdet).logarithmicImaginaryValue p a b := by
  have hpI : p ∈ candidateChartLocus S I := fun j _ => hp j
  have hx := (SmoothAtlas.rawChart S hdet I hI).map_source hpI
  have hu : ∀ i, (((SmoothAtlas.rawChart S hdet I hI p).1) i).1 ≠ 0 := fun i => hp i
  change (complexForm S I hdet hI (SmoothAtlas.rawChart S hdet I hI p)
    (fun k => tangentMap S I hdet hI p (![a,b] k))).im = _
  have hv : (fun k => tangentMap S I hdet hI p (![a,b] k)) =
      ![tangentMap S I hdet hI p a, tangentMap S I hdet hI p b] := by
    funext k; fin_cases k <;> rfl
  rw [hv, complexForm_torus S I hdet hI hx hu]
  simp only [matrixValue, TorusNondegeneracy.complexMatrix, originalLog_tangentMap S I hdet hI p hpI]
  rfl

/-- Imaginary part and restriction of scalars, bundled as a bounded real linear map. -/
def imaginaryPartCLM : (Vector S I [⋀^Fin 2]→L[ℂ] ℂ) →L[ℝ]
    (Vector S I [⋀^Fin 2]→L[ℝ] ℝ) :=
  LinearMap.mkContinuous
    { toFun := fun f => Complex.imCLM.compContinuousAlternatingMap (f.restrictScalars ℝ)
      map_add' := by intros; ext t; simp [map_add]
      map_smul' := by intros; ext t; simp }
    ‖Complex.imCLM‖ (fun f => by
      simpa using ContinuousLinearMap.norm_compContinuousAlternatingMap_le
        Complex.imCLM (f.restrictScalars ℝ))

/-- Native real smoothness of the full local form coefficients on the entire node domain. -/
theorem contDiffOn_realForm : ContDiffOn ℝ ∞ (realForm S I hdet hI) (domain S I) := by
  intro x hx
  exact ((imaginaryPartCLM S I).contDiff.contDiffAt.comp x
    ((contDiffAt_complexForm S I hdet hI hx).restrict_scalars ℝ)).contDiffWithinAt

/-- Boundary logarithmic inputs in exactly the same completed row index as the residual matrix. -/
def boundaryLog (x t : Vector S I) : IndependentRowBasisIndex S I → ℂ :=
  Sum.elim (fun i => -(x.1 i).2 * (t.1 i).1) (fun k => t.2 k / x.2 k)

theorem logParameter_eq_boundaryLog (x t : Vector S I) (hz : ∀ i, (x.1 i).1 = 0)
    (k : IndependentRowBasisIndex S I) :
    logParameter S I x k t = boundaryLog S I x t k := by
  cases k with
  | inl i => exact logParameter_boundary S I x t hz i
  | inr k => exact logParameter_inr S I x t k

/-- Boundary specialization with all residual blocks retained; no nondegeneracy premise. -/
theorem complexForm_boundary (x a b : Vector S I) (hz : ∀ i, (x.1 i).1 = 0) :
    complexForm S I hdet hI x ![a,b] =
      -(∑ i, ((a.1 i).1 * (b.1 i).2 - (b.1 i).1 * (a.1 i).2)) +
      matrixValue (fun k l => (residualMatrix S I hdet hI k l : ℂ))
        (boundaryLog S I x a) (boundaryLog S I x b) := by
  simp only [complexForm, ContinuousAlternatingMap.add_apply,
    ContinuousAlternatingMap.sum_apply, ContinuousAlternatingMap.smul_apply, smul_eq_mul,
    wedge_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
    logParameter_eq_boundaryLog S I x _ hz]
  congr 1
  simp [rawParameters, hz, du, dv, ← Finset.sum_neg_distrib]

/-- Real boundary specialization in node coordinates. -/
theorem realForm_boundary (x a b : Vector S I) (hz : ∀ i, (x.1 i).1 = 0) :
    realForm S I hdet hI x ![a,b] =
      (-(∑ i, ((a.1 i).1 * (b.1 i).2 - (b.1 i).1 * (a.1 i).2)) +
        matrixValue (fun k l => (residualMatrix S I hdet hI k l : ℂ))
          (boundaryLog S I x a) (boundaryLog S I x b)).im :=
  congrArg Complex.im (complexForm_boundary S I hdet hI x a b hz)

/-- The accepted chart sends its actual zero stratum to u=0. -/
theorem chart_boundary (p : S.Point) (hz : ∀ i : {i : Fin d // i ∈ I}, p.a i = 0) :
    ∀ i, (((SmoothAtlas.rawChart S hdet I hI p).1) i).1 = 0 := hz

/-- Boundary interface in the actual manifold tangent fiber; the input map is native `mfderiv`. -/
theorem localForm_boundary (p : S.Point) (hz : ∀ i : {i : Fin d // i ∈ I}, p.a i = 0)
    (a b : (SmoothAtlas.presentation S hdet).manifold.Tangent p) :
    let x := SmoothAtlas.rawChart S hdet I hI p
    let A := tangentMap S I hdet hI p a
    let B := tangentMap S I hdet hI p b
    SmoothManifold.evalTwo (localForm S I hdet hI) p a b =
      (-(∑ i, ((A.1 i).1 * (B.1 i).2 - (B.1 i).1 * (A.1 i).2)) +
        matrixValue (fun k l => (residualMatrix S I hdet hI k l : ℂ))
          (boundaryLog S I x A) (boundaryLog S I x B)).im := by
  dsimp only
  change realForm S I hdet hI _ (fun k => tangentMap S I hdet hI p (![a,b] k)) = _
  have hv : (fun k => tangentMap S I hdet hI p (![a,b] k)) =
      ![tangentMap S I hdet hI p a, tangentMap S I hdet hI p b] := by
    funext k; fin_cases k <;> rfl
  rw [hv]
  exact realForm_boundary S I hdet hI _ _ _ (chart_boundary S I hdet hI p hz)

/-- Unresolved compatibility/gluing obligation. This is a proposition, not an assumption or proof. -/
def LocalCompatibility : Prop :=
  ∀ (J : Finset (Fin d)) (hJ : S.Independent J) (p : S.Point),
    p ∈ candidateChartLocus S I → p ∈ candidateChartLocus S J →
    localForm S I hdet hI p = localForm S J hdet hJ p

/-- Unresolved global smooth closed extension, stated using the pinned native form interface.
No nondegeneracy, primitive, flow, or skeleton conclusion is asserted here. -/
def GlobalClosedExtension : Prop :=
  ∃ omega : (SmoothAtlas.presentation S hdet).manifold.Form 2,
    (SmoothAtlas.presentation S hdet).manifold.IsSmoothForm omega ∧
    (∀ p, (SmoothAtlas.presentation S hdet).manifold.exteriorDerivative omega p = 0) ∧
    ∀ (J : Finset (Fin d)) (hJ : S.Independent J) (p : S.Point),
      p ∈ candidateChartLocus S J → omega p = localForm S J hdet hJ p

/-- The accepted inverse chart recovers the literal ambient inclusion. -/
theorem ambientBackward_chart (p : S.Point) (hp : p ∈ candidateChartLocus S I) :
    ambientBackward S I hdet hI (SmoothAtlas.rawChart S hdet I hI p) = p.val := by
  change ambientBackward S I hdet hI (ambientForward S I hdet hI p.val) = _
  rw [ambientForward_eq S I hdet hI ⟨p, hp⟩, ambientBackward_eq]
  exact congrArg (fun q : Locus S I => q.val.val) (backward_forward S I hdet hI ⟨p, hp⟩)

/-- Injectivity of the native node differential follows from the accepted immersion. -/
theorem tangentMap_injective (p : S.Point) (hp : p ∈ candidateChartLocus S I) :
    Function.Injective (tangentMap S I hdet hI p) := by
  letI := SmoothAtlas.charts S hdet
  have hx := (SmoothAtlas.rawChart S hdet I hI).map_source hp
  have hc := mfderiv_comp p
    ((contDiffAt_ambientBackward_real S I hdet hI hx).contMDiffAt.mdifferentiableAt (by simp))
    ((chart_smooth S I hdet hI p hp).mdifferentiableAt (by simp))
  have he : (fun q : S.Point => ambientBackward S I hdet hI
      (SmoothAtlas.rawChart S hdet I hI q)) =ᶠ[nhds p] (fun q => q.val) := by
    filter_upwards [(isOpen_candidateChartLocus S I).mem_nhds hp] with q hq
    exact ambientBackward_chart S I hdet hI q hq
  have he' := he.mfderiv_eq (I := 𝓘(ℝ, FsFltz.Geometry.Model (2 * d)))
    (I' := 𝓘(ℝ, Ambient S))
  intro a b hab
  apply SmoothAtlas.inclusion_immersion S hdet p
  have hv := congrArg (mfderiv (𝓘(ℝ, Vector S I)) (𝓘(ℝ, Ambient S))
    (ambientBackward S I hdet hI) (SmoothAtlas.rawChart S hdet I hI p)) hab
  change (_ ∘L tangentMap S I hdet hI p) a = (_ ∘L tangentMap S I hdet hI p) b at hv
  unfold tangentMap at hv
  rw [← hc] at hv
  exact (congrArg (fun f => f a) he').symm.trans (hv.trans (congrArg (fun f => f b) he'))

/-- Exact native tangent equivalence on the full independent locus, including every node axis. -/
def tangentEquiv (p : S.Point) (hp : p ∈ candidateChartLocus S I) :
    (SmoothAtlas.presentation S hdet).manifold.Tangent p ≃L[ℝ] Vector S I :=
  (LinearEquiv.ofInjectiveOfFinrankEq (tangentMap S I hdet hI p).toLinearMap
    (tangentMap_injective S I hdet hI p hp) (by
      change Module.finrank ℝ (FsFltz.Geometry.Model (2 * d)) = Module.finrank ℝ (Vector S I)
      rw [finrank_euclideanSpace_fin, vector_finrank_real S I hdet hI])).toContinuousLinearEquiv

@[simp] theorem tangentEquiv_apply (p : S.Point) (hp : p ∈ candidateChartLocus S I)
    (v : (SmoothAtlas.presentation S hdet).manifold.Tangent p) :
    tangentEquiv S I hdet hI p hp v = tangentMap S I hdet hI p v := rfl

end ClusterSkeleton.NodeTwoForm
