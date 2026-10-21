import ClusterSkeleton.NodeTwoForm
import Mathlib.Data.Matrix.Block

/-!
# Nondegeneracy at the centers of the actual node charts

The complement block is derived from the full unimodular matrix by the prescribed
integral basis change. No nondegeneracy assumption on a residual block is used.
-/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
open Matrix

namespace ClusterSkeleton.NodeNondegeneracy
open IndependentNodeChart NodeTwoForm

/-- The inclusion of the prescribed row coordinates: `[Id,0]`. -/
def rowProjection {A W : Type*} [DecidableEq A] : Matrix A (A ⊕ W) ℂ :=
  fun i => Sum.elim (fun j => if i = j then 1 else 0) (fun _ => 0)

/-- A kernel vector of the residual block lifts to a kernel vector of the full
normal block matrix. This statement includes empty index types. -/
theorem complement_kernel {A W : Type*} [Fintype A] [Fintype W] [DecidableEq A]
    (C : Matrix (A ⊕ W) (A ⊕ W) ℂ)
    (hinj : Function.Injective
      (Matrix.fromBlocks 0 (rowProjection : Matrix A (A ⊕ W) ℂ)
        (-rowProjection.transpose) C).mulVec)
    (w : W → ℂ) (hw : (C.submatrix Sum.inr Sum.inr).mulVec w = 0) : w = 0 := by
  let z : A ⊕ W → ℂ := Sum.elim 0 w
  let a : A → ℂ := fun i => C.mulVec z (Sum.inl i)
  have hk : (Matrix.fromBlocks 0 (rowProjection : Matrix A (A ⊕ W) ℂ)
      (-rowProjection.transpose) C).mulVec (Sum.elim a z) = 0 := by
    funext k
    cases k with
    | inl i => simp [rowProjection, z, Matrix.mulVec,
        dotProduct, Fintype.sum_sum_type]
    | inr k =>
      cases k with
      | inl i => simp [rowProjection, Matrix.mulVec,
          dotProduct, Fintype.sum_sum_type, a]
      | inr j =>
        have hj := congrFun hw j
        simpa [Matrix.fromBlocks_mulVec, rowProjection, z, Matrix.mulVec,
          dotProduct, Fintype.sum_sum_type] using hj
  have hz := hinj (hk.trans (Matrix.mulVec_zero _).symm)
  funext j
  exact congrFun hz (Sum.inr (Sum.inr j))

/-- Congruence by an actual two-sided rectangular basis change preserves
injectivity, without a cardinality or positive-dimension premise. -/
theorem congruence_injective {J K : Type*} [Fintype J] [Fintype K]
    [DecidableEq J] [DecidableEq K]
    (B : Matrix J J ℂ) (Q : Matrix J K ℂ) (P : Matrix K J ℂ)
    (hPQ : P * Q = 1) (hQP : Q * P = 1)
    (hB : Function.Injective B.mulVec) :
    Function.Injective (Q.transpose * B * Q).mulVec := by
  intro x y h
  have ht : P.transpose * Q.transpose = 1 := by
    rw [← Matrix.transpose_mul, hQP, Matrix.transpose_one]
  have h' := congrArg P.transpose.mulVec h
  simp only [← Matrix.mulVec_mulVec] at h'
  have h'' : B.mulVec (Q.mulVec x) = B.mulVec (Q.mulVec y) := by
    simpa only [Matrix.mulVec_mulVec, ← Matrix.mul_assoc, ht, Matrix.one_mul] using h'
  have hq := congrArg P.mulVec (hB h'')
  simpa only [Matrix.mulVec_mulVec, hPQ, Matrix.one_mulVec] using hq

variable {d : ℕ} (S : Seed d) (I : Finset (Fin d))
    (hdet : S.Unimodular) (hI : S.Independent I)

/-- The actual residual integer matrix extended to complex scalars. -/
def complexResidual : Matrix (IndependentRowBasisIndex S I) (IndependentRowBasisIndex S I) ℂ :=
  fun k l => (residualMatrix S I hdet hI k l : ℂ)

/-- The free-coordinate block, with precisely the accepted complement index. -/
def complementMatrix : Matrix (Complement S I) (Complement S I) ℂ :=
  (complexResidual S I hdet hI).submatrix Sum.inr Sum.inr

/-- The full block matrix after the prescribed basis change is injective. -/
theorem normalMatrix_injective : Function.Injective
    (Matrix.fromBlocks 0
      (rowProjection : Matrix {i : Fin d // i ∈ I} (IndependentRowBasisIndex S I) ℂ)
      (-rowProjection.transpose) (complexResidual S I hdet hI)).mulVec := by
  classical
  let A := {i : Fin d // i ∈ I}
  let J := {j : Fin d // j ∉ I}
  let K := IndependentRowBasisIndex S I
  let T : Matrix J K ℂ := (independentRowInverseMatrix S I hdet hI).map (Int.castRingHom ℂ)
  let F : Matrix K J ℂ := (independentRowForwardMatrix S I hdet hI).map (Int.castRingHom ℂ)
  have hFT : F * T = 1 := by
    change (independentRowForwardMatrix S I hdet hI).map (Int.castRingHom ℂ) *
      (independentRowInverseMatrix S I hdet hI).map (Int.castRingHom ℂ) = 1
    rw [← Matrix.map_mul, independentRowForward_mul_inverse]
    simp
  have hTF : T * F = 1 := by
    change (independentRowInverseMatrix S I hdet hI).map (Int.castRingHom ℂ) *
      (independentRowForwardMatrix S I hdet hI).map (Int.castRingHom ℂ) = 1
    rw [← Matrix.map_mul, independentRowInverse_mul_forward]
    simp
  let R : Matrix A J ℂ := fun i j => (S.B i j : ℂ)
  let D : Matrix J J ℂ := fun i j => (S.B i j : ℂ)
  have hRT : R * T = (rowProjection : Matrix A K ℂ) := by
    ext i k
    have h := row_inverse S I hdet hI i k
    have hc : (∑ j : J, (S.B i j : ℂ) *
        (independentRowInverseMatrix S I hdet hI j k : ℂ)) =
        if Sum.inl i = k then 1 else 0 := by exact_mod_cast h
    cases k <;> simpa [R, T, Matrix.mul_apply, rowProjection] using hc
  let e : A ⊕ J ≃ Fin d := Equiv.sumCompl (fun i => i ∈ I)
  let B := (TorusNondegeneracy.complexMatrix S).submatrix e e
  have hBunit : IsUnit B := by
    apply (Matrix.isUnit_iff_isUnit_det _).mpr
    have hd : B.det = 1 := (Matrix.det_submatrix_equiv_self e _).trans
      (TorusNondegeneracy.complexMatrix_det S hdet)
    rw [hd]
    exact isUnit_one
  have hB : B = Matrix.fromBlocks 0 R (-R.transpose) D := by
    ext i j
    cases i with
    | inl i =>
      cases j with
      | inl j =>
        change (S.B i j : ℂ) = 0
        rw [hI.2 i i.property j j.property, Int.cast_zero]
      | inr j => rfl
    | inr i =>
      cases j with
      | inl j =>
        change (S.B i j : ℂ) = -(S.B j i : ℂ)
        rw [S.skew i j, Int.cast_neg]
      | inr j => rfl
  let Q : Matrix (A ⊕ J) (A ⊕ K) ℂ := Matrix.fromBlocks 1 0 0 T
  let P : Matrix (A ⊕ K) (A ⊕ J) ℂ := Matrix.fromBlocks 1 0 0 F
  have hPQ : P * Q = 1 := by simp [P, Q, Matrix.fromBlocks_multiply, hFT, Matrix.fromBlocks_one]
  have hQP : Q * P = 1 := by simp [P, Q, Matrix.fromBlocks_multiply, hTF, Matrix.fromBlocks_one]
  have hn : Q.transpose * B * Q = Matrix.fromBlocks 0
      (rowProjection : Matrix A K ℂ) (-rowProjection.transpose)
      (complexResidual S I hdet hI) := by
    have hr : T.transpose * (-R.transpose) = -(rowProjection : Matrix A K ℂ).transpose := by
      rw [Matrix.mul_neg, ← Matrix.transpose_mul, hRT]
    have hc : T.transpose * D * T = complexResidual S I hdet hI :=
      (residualMatrix_cast S I hdet hI).symm
    rw [hB]
    simp only [Q, Matrix.fromBlocks_transpose, Matrix.transpose_one, Matrix.transpose_zero,
      Matrix.fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, Matrix.one_mul,
      Matrix.mul_one, add_zero, zero_add, hRT, hr, hc]
  rw [← hn]
  exact congruence_injective B Q P hPQ hQP (Matrix.mulVec_injective_iff_isUnit.mpr hBunit)

/-- Unimodularity of the seed forces trivial kernel of the actual complement block. -/
theorem complementMatrix_kernel (w : Complement S I → ℂ)
    (hw : (complementMatrix S I hdet hI).mulVec w = 0) : w = 0 :=
  complement_kernel (complexResidual S I hdet hI)
    (normalMatrix_injective S I hdet hI) w hw

/-- Invertibility of the residual complement is a conclusion, not input data. -/
theorem complementMatrix_isUnit : IsUnit (complementMatrix S I hdet hI) := by
  apply Matrix.mulVec_injective_iff_isUnit.mp
  intro x y h
  have hz := complementMatrix_kernel S I hdet hI (x - y)
    (by rw [Matrix.mulVec_sub, h, sub_self])
  exact sub_eq_zero.mp hz

/-- The actual congruence retains skew symmetry over the complex scalars. -/
theorem complexResidual_skew (k l : IndependentRowBasisIndex S I) :
    complexResidual S I hdet hI k l = -complexResidual S I hdet hI l k := by
  let T := (independentRowInverseMatrix S I hdet hI).map (Int.castRingHom ℂ)
  let D : Matrix {j : Fin d // j ∉ I} {j : Fin d // j ∉ I} ℂ := fun i j => (S.B i j : ℂ)
  have hs : D.transpose = -D := by
    ext i j
    change (S.B j i : ℂ) = -(S.B i j : ℂ)
    rw [S.skew j i, Int.cast_neg]
  have hc : complexResidual S I hdet hI = T.transpose * D * T :=
    residualMatrix_cast S I hdet hI
  have ht : (complexResidual S I hdet hI).transpose = -complexResidual S I hdet hI := by
    rw [hc, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, hs]
    simp only [Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc]
  exact congrFun (congrFun ht l) k

/-- The complex boundary form has trivial kernel. The v coordinates may vanish. -/
theorem complexForm_boundary_nondegenerate (x : Vector S I)
    (hx : x ∈ domain S I) (hz : ∀ i, (x.1 i).1 = 0)
    (a : Vector S I) (ha : ∀ b, complexForm S I hdet hI x ![a,b] = 0) : a = 0 := by
  classical
  have hu : ∀ i, (a.1 i).1 = 0 := by
    intro i
    let b : Vector S I := (fun j => (0, (Pi.single i (1 : ℂ) : _ → ℂ) j), 0)
    have hb : boundaryLog S I x b = 0 := by
      funext k
      cases k <;> simp [boundaryLog, b]
    have h := ha b
    rw [complexForm_boundary S I hdet hI x a b hz, hb] at h
    simpa [b, matrixValue, Pi.single_apply] using h
  have hw : a.2 = 0 := by
    have hv : Matrix.vecMul (fun k => a.2 k / x.2 k) (complementMatrix S I hdet hI) = 0 := by
      funext j
      let b : Vector S I := (0, fun k => x.2 k * (Pi.single j (1 : ℂ) : _ → ℂ) k)
      have hb : boundaryLog S I x b = Sum.elim (fun _ : {i : Fin d // i ∈ I} => (0 : ℂ))
          (Pi.single j (1 : ℂ) : Complement S I → ℂ) := by
        funext k
        cases k with
        | inl i => simp [boundaryLog, b]
        | inr k => simp [boundaryLog, b, hx.2 k]
      have h := ha b
      rw [complexForm_boundary S I hdet hI x a b hz] at h
      change -(∑ i, ((a.1 i).1 * (b.1 i).2 - (b.1 i).1 * (a.1 i).2)) +
        matrixValue (complexResidual S I hdet hI) (boundaryLog S I x a)
          (boundaryLog S I x b) = 0 at h
      rw [matrixValue_skew _ (complexResidual_skew S I hdet hI), hb] at h
      simpa [b, boundaryLog, hu, Fintype.sum_sum_type, Pi.single_apply,
        Matrix.vecMul, dotProduct, complementMatrix, mul_comm] using h
    have hn : (fun k => a.2 k / x.2 k) = 0 := by
      apply Matrix.vecMul_injective_of_isUnit (complementMatrix_isUnit S I hdet hI)
      simpa using hv
    funext k
    exact (div_eq_zero_iff).mp (congrFun hn k) |>.resolve_right (hx.2 k)
  have hl : boundaryLog S I x a = 0 := by
    funext k
    cases k <;> simp [boundaryLog, hu, hw]
  have hv : ∀ i, (a.1 i).2 = 0 := by
    intro i
    let b : Vector S I := (fun j => ((Pi.single i (1 : ℂ) : _ → ℂ) j, 0), 0)
    have h := ha b
    rw [complexForm_boundary S I hdet hI x a b hz, hl] at h
    simpa [b, matrixValue, hu, Pi.single_apply] using h
  apply Prod.ext _ hw
  funext i
  exact Prod.ext (hu i) (hv i)

/-- Multiplication by i in the second complex argument detects the real part.
Thus a zero imaginary contraction is a zero complex contraction. -/
theorem complex_kernel_of_imaginary_kernel {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] (ω : E [⋀^Fin 2]→L[ℂ] ℂ) (a : E)
    (ha : ∀ b, (ω ![a,b]).im = 0) : ∀ b, ω ![a,b] = 0 := by
  intro b
  have hs : ω ![a, Complex.I • b] = Complex.I * ω ![a,b] := by
    have h := ω.map_update_smul ![a,b] 1 Complex.I b
    have h₁ : Function.update ![a,b] 1 (Complex.I • b) = ![a, Complex.I • b] := by
      funext i
      fin_cases i <;> rfl
    have h₂ : Function.update ![a,b] 1 b = ![a,b] := by
      funext i
      fin_cases i <;> rfl
    simpa only [h₁, h₂, smul_eq_mul] using h
  apply Complex.ext
  · have hr := ha (Complex.I • b)
    rw [hs] at hr
    simpa using hr
  · exact ha b

/-- Real nondegeneracy of the imaginary part of the actual complex boundary form. -/
theorem realForm_boundary_nondegenerate (x : Vector S I)
    (hx : x ∈ domain S I) (hz : ∀ i, (x.1 i).1 = 0)
    (a : Vector S I) (ha : ∀ b, realForm S I hdet hI x ![a,b] = 0) : a = 0 := by
  apply complexForm_boundary_nondegenerate S I hdet hI x hx hz a
  exact complex_kernel_of_imaginary_kernel (complexForm S I hdet hI x) a ha

/-- Transfer through the constructed native derivative equivalence, on its actual chart source. -/
theorem localForm_boundary_nondegenerate (p : S.Point)
    (hp : p ∈ candidateChartLocus S I)
    (hz : ∀ i : {i : Fin d // i ∈ I}, p.a i = 0)
    (a : (SmoothAtlas.presentation S hdet).manifold.Tangent p)
    (ha : ∀ b, FsFltz.Geometry.SmoothManifold.evalTwo (localForm S I hdet hI) p a b = 0) :
    a = 0 := by
  let e := tangentEquiv S I hdet hI p hp
  have he : e a = 0 := by
    apply realForm_boundary_nondegenerate S I hdet hI
      (SmoothAtlas.rawChart S hdet I hI p)
      ((SmoothAtlas.rawChart S hdet I hI).map_source hp)
      (chart_boundary S I hdet hI p hz)
    intro t
    obtain ⟨b, rfl⟩ := e.surjective t
    have h := ha b
    change realForm S I hdet hI (SmoothAtlas.rawChart S hdet I hI p)
      (fun i => tangentMap S I hdet hI p (![a,b] i)) = 0 at h
    have hv : (fun i => tangentMap S I hdet hI p (![a,b] i)) = ![e a,e b] := by
      funext i
      fin_cases i <;> rfl
    rw [hv] at h
    exact h
  apply e.injective
  simpa using he

/-- Every actual point belongs to the chart indexed by its actual zero set. -/
theorem zeroSet_chart_mem (p : S.Point) : p ∈ candidateChartLocus S p.zeroSet := by
  intro j hj hz
  have hm : j ∈ S.mutable := by
    by_contra hf
    exact p.frozen_ne_zero j hf hz
  exact hj ((p.mem_zeroSet j).mpr ⟨hm, hz⟩)

/-- Unconditional pointwise boundary nondegeneracy in the actual zero-set chart.
This does not assert global gluing or closedness. -/
theorem zeroSet_localForm_nondegenerate (p : S.Point)
    (a : (SmoothAtlas.presentation S hdet).manifold.Tangent p)
    (ha : ∀ b, FsFltz.Geometry.SmoothManifold.evalTwo
      (localForm S p.zeroSet hdet p.zeroSet_independent) p a b = 0) : a = 0 := by
  apply localForm_boundary_nondegenerate S p.zeroSet hdet p.zeroSet_independent p
    (zeroSet_chart_mem S p) _ a ha
  intro i
  exact ((p.mem_zeroSet i).mp i.property).2

end ClusterSkeleton.NodeNondegeneracy
