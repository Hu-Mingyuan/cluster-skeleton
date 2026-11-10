import ClusterSkeleton.NodeTwoForm
import ClusterSkeleton.SymmetrizerAlgebra
import Mathlib.Data.Matrix.Block

/-!
# Nondegeneracy at the centers of the actual node charts, weighted case

The complement block is derived from the full unimodular matrix by the prescribed
integral basis change. No nondegeneracy assumption on a residual block is used.

With a nontrivial symmetrizer the form matrix is `K = E * D`, so the first block
row of the transformed matrix carries the weights: by `Seed.K_eq_neg_D_mul_B` the
`K`-rows at `I` against the integer inverse basis are `-D_I [Id, 0]`, giving the
blueprint matrix

```
[[0, -D_I, 0], [D_I, A, B₀], [0, -B₀ᵀ, C]] .
```

Nonsingularity of `K` is `det K = ∏ d_i ≠ 0`, not `det = 1`, and the elimination
of the first two block rows is
`SymmetrizerAlgebra.residualBlock_eq_zero_of_mulVec_eq_zero`.
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

/-- The actual residual matrix extended to complex scalars. Its entries are
rational, because the middle factor is the weighted matrix `K`. -/
def complexResidual : Matrix (IndependentRowBasisIndex S I) (IndependentRowBasisIndex S I) ℂ :=
  fun k l => (residualMatrix S I hdet hI k l : ℂ)

/-- The free-coordinate block, with precisely the accepted complement index. -/
def complementMatrix : Matrix (Complement S I) (Complement S I) ℂ :=
  (complexResidual S I hdet hI).submatrix Sum.inr Sum.inr

/-- The actual congruence retains skew symmetry over the complex scalars. -/
theorem complexResidual_skew (k l : IndependentRowBasisIndex S I) :
    complexResidual S I hdet hI k l = -complexResidual S I hdet hI l k := by
  let T := (independentRowInverseMatrix S I hdet hI).map (Int.castRingHom ℂ)
  have hs : (complexOutsideBlock S I).transpose = -(complexOutsideBlock S I) := by
    ext i j
    change ((S.K j i : ℚ) : ℂ) = -((S.K i j : ℚ) : ℂ)
    rw [S.K_skew j i, Rat.cast_neg]
  have hc : complexResidual S I hdet hI = T.transpose * (complexOutsideBlock S I) * T :=
    residualMatrix_cast S I hdet hI
  have ht : (complexResidual S I hdet hI).transpose = -complexResidual S I hdet hI := by
    rw [hc, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, hs]
    simp only [Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc]
  exact congrFun (congrFun ht l) k

/-- The weighted first block row `-D_I [Id, 0]`: the `K`-rows at `I` read in the
accepted integer basis. With `D = 1` it is `-rowProjection`. -/
def weightProjection : Matrix {i : Fin d // i ∈ I} (IndependentRowBasisIndex S I) ℂ :=
  fun i k => -(S.D i : ℂ) *
    (rowProjection : Matrix {i : Fin d // i ∈ I} (IndependentRowBasisIndex S I) ℂ) i k

@[simp] theorem weightProjection_inl (i i' : {i : Fin d // i ∈ I}) :
    weightProjection S I i (Sum.inl i') = if i = i' then -(S.D i : ℂ) else 0 := by
  by_cases h : i = i' <;> simp [weightProjection, rowProjection, h]

@[simp] theorem weightProjection_inr (i : {i : Fin d // i ∈ I}) (r : Complement S I) :
    weightProjection S I i (Sum.inr r) = 0 := by
  simp [weightProjection, rowProjection]

/-- The blueprint matrix `[[0, -D_I, 0], [D_I, A, B₀], [0, -B₀ᵀ, C]]`, i.e. the
weighted form matrix after the prescribed rectangular basis change. -/
def normalMatrix :
    Matrix ({i : Fin d // i ∈ I} ⊕ IndependentRowBasisIndex S I)
      ({i : Fin d // i ∈ I} ⊕ IndependentRowBasisIndex S I) ℂ :=
  Matrix.fromBlocks 0 (weightProjection S I) (-(weightProjection S I).transpose)
    (complexResidual S I hdet hI)

theorem normalMatrix_skew :
    (normalMatrix S I hdet hI).transpose = -normalMatrix S I hdet hI := by
  ext a b
  rcases a with i | k <;> rcases b with j | l
  · simp [normalMatrix]
  · simp [normalMatrix]
  · simp [normalMatrix]
  · simpa [normalMatrix] using (complexResidual_skew S I hdet hI l k)

/-- The residual block of the blueprint matrix is exactly the complement block. -/
theorem residualBlock_normalMatrix :
    SymmetrizerAlgebra.residualBlock (normalMatrix S I hdet hI) =
      complementMatrix S I hdet hI := rfl

/-- The full block matrix after the prescribed basis change is injective. -/
theorem normalMatrix_injective :
    Function.Injective (normalMatrix S I hdet hI).mulVec := by
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
  -- the weighted `I` rows and the weighted outside block of `K`
  let R : Matrix A J ℂ := fun i j => (S.K i j : ℂ)
  let Dblk : Matrix J J ℂ := fun i j => (S.K i j : ℂ)
  have hRT : R * T = weightProjection S I := by
    ext i k
    have h := row_inverse S I hdet hI i k
    have hc : (∑ j : J, (S.B i j : ℂ) *
        (independentRowInverseMatrix S I hdet hI j k : ℂ)) =
        if Sum.inl i = k then 1 else 0 := by exact_mod_cast h
    have hK : ∀ j : J, (S.K i j : ℂ) = -(S.D i : ℂ) * (S.B i j : ℂ) := by
      intro j
      have hq := S.K_eq_neg_D_mul_B i j
      rw [show ((S.K i j : ℚ) : ℂ) = ((-(S.D i) * (S.B i j : ℚ) : ℚ) : ℂ) from
        congrArg (fun r : ℚ => (r : ℂ)) hq]
      push_cast
      ring
    have hrow : (R * T) i k = -(S.D i : ℂ) * (if Sum.inl i = k then (1 : ℂ) else 0) := by
      simp only [Matrix.mul_apply, R, T, Matrix.map_apply, Int.coe_castRingHom]
      rw [← hc, Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by rw [hK j, mul_assoc]
    rw [hrow]
    cases k with
    | inl i' =>
      rw [weightProjection_inl]
      by_cases h : i = i' <;> simp [h, Sum.inl.injEq]
    | inr r => simp
  let e : A ⊕ J ≃ Fin d := Equiv.sumCompl (fun i => i ∈ I)
  let B := (TorusNondegeneracy.complexMatrix S).submatrix e e
  have hBunit : IsUnit B := by
    apply (Matrix.isUnit_iff_isUnit_det _).mpr
    rw [show B.det = (TorusNondegeneracy.complexMatrix S).det from
      Matrix.det_submatrix_equiv_self e _]
    exact TorusNondegeneracy.isUnit_complexMatrix_det S hdet
  have hB : B = Matrix.fromBlocks 0 R (-R.transpose) Dblk := by
    ext i j
    cases i with
    | inl i =>
      cases j with
      | inl j =>
        change ((S.K i j : ℚ) : ℂ) = 0
        rw [Seed.K_apply, hI.2 i i.property j j.property]
        simp
      | inr j => rfl
    | inr i =>
      cases j with
      | inl j =>
        change ((S.K i j : ℚ) : ℂ) = -((S.K j i : ℚ) : ℂ)
        rw [S.K_skew i j, Rat.cast_neg]
      | inr j => rfl
  let Q : Matrix (A ⊕ J) (A ⊕ K) ℂ := Matrix.fromBlocks 1 0 0 T
  let P : Matrix (A ⊕ K) (A ⊕ J) ℂ := Matrix.fromBlocks 1 0 0 F
  have hPQ : P * Q = 1 := by simp [P, Q, Matrix.fromBlocks_multiply, hFT, Matrix.fromBlocks_one]
  have hQP : Q * P = 1 := by simp [P, Q, Matrix.fromBlocks_multiply, hTF, Matrix.fromBlocks_one]
  have hn : Q.transpose * B * Q = normalMatrix S I hdet hI := by
    have hr : T.transpose * (-R.transpose) = -(weightProjection S I).transpose := by
      rw [Matrix.mul_neg, ← Matrix.transpose_mul, hRT]
    have hc : T.transpose * Dblk * T = complexResidual S I hdet hI :=
      (residualMatrix_cast S I hdet hI).symm
    rw [hB, normalMatrix]
    simp only [Q, Matrix.fromBlocks_transpose, Matrix.transpose_one, Matrix.transpose_zero,
      Matrix.fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, Matrix.one_mul,
      Matrix.mul_one, add_zero, zero_add, hRT, hr, hc]
  rw [← hn]
  exact congruence_injective B Q P hPQ hQP (Matrix.mulVec_injective_iff_isUnit.mpr hBunit)

theorem isUnit_det_normalMatrix : IsUnit (normalMatrix S I hdet hI).det :=
  (Matrix.isUnit_iff_isUnit_det _).mp
    (Matrix.mulVec_injective_iff_isUnit.mp (normalMatrix_injective S I hdet hI))

/-- Unimodularity of the seed forces trivial kernel of the actual complement
block. The first two block rows are eliminated by the weighted residual-block
lemma, with `δ i = -d_i`. -/
theorem complementMatrix_kernel (w : Complement S I → ℂ)
    (hw : (complementMatrix S I hdet hI).mulVec w = 0) : w = 0 := by
  refine SymmetrizerAlgebra.residualBlock_eq_zero_of_mulVec_eq_zero
    (normalMatrix_skew S I hdet hI) (isUnit_det_normalMatrix S I hdet hI)
    (δ := fun i : {i : Fin d // i ∈ I} => -(S.D i : ℂ))
    (fun i => neg_ne_zero.mpr (Rat.cast_ne_zero.mpr (S.D_ne_zero i)))
    (fun i i' => rfl) (fun i r => by simp [normalMatrix])
    (fun i i' => by simp [normalMatrix]) ?_
  rw [residualBlock_normalMatrix]
  exact hw

/-- Invertibility of the residual complement is a conclusion, not input data. -/
theorem complementMatrix_isUnit : IsUnit (complementMatrix S I hdet hI) := by
  apply Matrix.mulVec_injective_iff_isUnit.mp
  intro x y h
  have hz := complementMatrix_kernel S I hdet hI (x - y)
    (by rw [Matrix.mulVec_sub, h, sub_self])
  exact sub_eq_zero.mp hz

/-- The complex boundary form has trivial kernel. The v coordinates may vanish. -/
theorem complexForm_boundary_nondegenerate (x : Vector S I)
    (hx : x ∈ domain S I) (hz : ∀ i, (x.1 i).1 = 0)
    (a : Vector S I) (ha : ∀ b, complexForm S I hdet hI x ![a,b] = 0) : a = 0 := by
  classical
  -- the `y_i` directions: the node coefficient is now `d_i`, which is nonzero
  have hD : ∀ i : {i : Fin d // i ∈ I}, (S.D i : ℂ) ≠ 0 :=
    fun i => Rat.cast_ne_zero.mpr (S.D_ne_zero i)
  have hu : ∀ i, (a.1 i).1 = 0 := by
    intro i
    let b : Vector S I := (fun j => (0, (Pi.single i (1 : ℂ) : _ → ℂ) j), 0)
    have hb : boundaryLog S I x b = 0 := by
      funext k
      cases k <;> simp [boundaryLog, b]
    have h := ha b
    rw [complexForm_boundary S I hdet hI x a b hz, hb] at h
    have h' : (S.D i : ℂ) * (a.1 i).1 = 0 := by
      simpa [b, matrixValue, Pi.single_apply] using h
    exact (mul_eq_zero.mp h').resolve_left (hD i)
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
      change (∑ i : {i : Fin d // i ∈ I},
          (S.D i : ℂ) * ((a.1 i).1 * (b.1 i).2 - (b.1 i).1 * (a.1 i).2)) +
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
    have h' : (S.D i : ℂ) * (a.1 i).2 = 0 := by
      simpa [b, matrixValue, hu, Pi.single_apply] using h
    exact (mul_eq_zero.mp h').resolve_left (hD i)
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
