import ClusterSkeleton.GlobalTwoForm
import ClusterSkeleton.NodeNondegeneracy

/-! The accepted global form is symplectic on the actual exchange manifold. -/
noncomputable section
set_option autoImplicit false
open FsFltz.Geometry

namespace ClusterSkeleton.GlobalSymplectic

variable {d : ℕ} (S : Seed d) (hdet : S.Unimodular)

/-- At each point, use its full zero-set chart and the accepted boundary kernel
calculation. No nondegeneracy hypothesis is imposed on the global form. -/
theorem nondegenerate_omega (p : S.Point) :
    (SmoothAtlas.presentation S hdet).manifold.Nondegenerate
      (GlobalTwoForm.omega S hdet) p := by
  intro a ha
  apply NodeNondegeneracy.zeroSet_localForm_nondegenerate S hdet p a
  intro b
  have hf := GlobalTwoForm.omega_eq_localForm S hdet p.zeroSet
    p.zeroSet_independent p (NodeNondegeneracy.zeroSet_chart_mem S p)
  have hb := ha b
  change GlobalTwoForm.omega S hdet p ![a, b] = 0 at hb
  change NodeTwoForm.localForm S p.zeroSet hdet p.zeroSet_independent p ![a, b] = 0
  rw [← hf]
  exact hb

/-- Smoothness, the actual exterior derivative, and unconditional kernel
triviality packaged in the pinned native symplectic predicate. -/
theorem isSymplecticOn_omega :
    (SmoothAtlas.presentation S hdet).manifold.IsSymplecticOn
      (GlobalTwoForm.omega S hdet) Set.univ :=
  ⟨GlobalTwoForm.isSmoothForm_omega S hdet,
    fun p _ => GlobalTwoForm.exteriorDerivative_omega S hdet p,
    fun p _ => nondegenerate_omega S hdet p⟩

/-- The existence witness is exactly the accepted normalized global form. -/
theorem exists_symplectic_form :
    ∃ omega : (SmoothAtlas.presentation S hdet).manifold.Form 2,
      omega = GlobalTwoForm.omega S hdet ∧
      (SmoothAtlas.presentation S hdet).manifold.IsSymplecticOn omega Set.univ :=
  ⟨GlobalTwoForm.omega S hdet, rfl, isSymplecticOn_omega S hdet⟩

end ClusterSkeleton.GlobalSymplectic
