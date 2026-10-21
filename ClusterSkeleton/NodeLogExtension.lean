import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic

/-!
# The removable logarithmic quotient in a node chart

The extension of `log (1 - z * w) / z` at `z = 0` has value `-w`.
We use Mathlib's differentiated slope instead of asserting a removable
singularity or choosing an unspecified extension.

Smoothness holds on the explicit principal-log branch domain
`{(z,w) | 1 - z*w ∈ Complex.slitPlane}`. This open set contains every point
`(0,w)` and the neighborhood `‖z*w‖ < 1`, but is not the entire node surface
`{(z,w) | z*w ≠ 1}`.
-/

noncomputable section

open Set
open scoped Topology ContDiff

namespace ClusterSkeleton

/-- An explicit domain on which the principal logarithm is analytic. -/
def nodeLogDomain : Set (ℂ × ℂ) :=
  {p | 1 - p.1 * p.2 ∈ Complex.slitPlane}

/-- The actual removable extension, written using native `dslope`.
Its value at a zero first coordinate is forced by the derivative of `log`
at `1`; it is not a separately assumed extension. -/
def nodeLogQuotient (p : ℂ × ℂ) : ℂ :=
  -p.2 * dslope Complex.log 1 (1 - p.1 * p.2)

theorem isOpen_nodeLogDomain : IsOpen nodeLogDomain :=
  Complex.isOpen_slitPlane.preimage
    (continuous_const.sub (continuous_fst.mul continuous_snd))

@[simp]
theorem zero_mem_nodeLogDomain (w : ℂ) : (0, w) ∈ nodeLogDomain := by
  simp [nodeLogDomain]

/-- A convenient neighborhood of every point on the zero-coordinate divisor. -/
theorem mem_nodeLogDomain_of_norm_mul_lt_one {z w : ℂ}
    (h : ‖z * w‖ < 1) : (z, w) ∈ nodeLogDomain := by
  have hneg : ‖-(z * w)‖ < 1 := by simpa only [norm_neg] using h
  simpa only [nodeLogDomain, mem_ofPred_eq, sub_eq_add_neg] using
    Complex.mem_slitPlane_of_norm_lt_one hneg

@[simp]
theorem nodeLogQuotient_zero (w : ℂ) : nodeLogQuotient (0, w) = -w := by
  simp [nodeLogQuotient, Complex.deriv_log Complex.one_mem_slitPlane]

/-- Multiplication by the first coordinate recovers the original numerator,
including on the divisor. No branch-domain hypothesis is needed for this
algebraic identity. -/
theorem mul_nodeLogQuotient (p : ℂ × ℂ) :
    p.1 * nodeLogQuotient p = Complex.log (1 - p.1 * p.2) := by
  calc
    p.1 * nodeLogQuotient p =
        ((1 - p.1 * p.2) - 1) *
          dslope Complex.log 1 (1 - p.1 * p.2) := by
      dsimp only [nodeLogQuotient]
      ring
    _ = Complex.log (1 - p.1 * p.2) := by
      simpa only [smul_eq_mul, Complex.log_one, sub_zero] using
        sub_smul_dslope Complex.log 1 (1 - p.1 * p.2)

theorem nodeLogQuotient_eq_div {p : ℂ × ℂ} (hz : p.1 ≠ 0) :
    nodeLogQuotient p = Complex.log (1 - p.1 * p.2) / p.1 := by
  apply (eq_div_iff hz).2
  simpa only [mul_comm] using mul_nodeLogQuotient p

private theorem analyticOnNhd_dslope_log_one :
    AnalyticOnNhd ℂ (dslope Complex.log 1) Complex.slitPlane := by
  apply DifferentiableOn.analyticOnNhd _ Complex.isOpen_slitPlane
  apply (Complex.differentiableOn_dslope
    (Complex.isOpen_slitPlane.mem_nhds Complex.one_mem_slitPlane)).2
  intro z hz
  exact (Complex.differentiableAt_log hz).differentiableWithinAt

/-- Joint complex analyticity, including all points `(0,w)` of the divisor. -/
theorem analyticOnNhd_nodeLogQuotient :
    AnalyticOnNhd ℂ nodeLogQuotient nodeLogDomain := by
  intro p hp
  have harg : AnalyticAt ℂ (fun q : ℂ × ℂ => 1 - q.1 * q.2) p :=
    analyticAt_const.sub (analyticAt_fst.mul analyticAt_snd)
  exact analyticAt_snd.neg.mul
    ((analyticOnNhd_dslope_log_one _ hp).comp (f := fun q : ℂ × ℂ => 1 - q.1 * q.2) harg)

/-- The extension is smooth over the real scalars used by the symplectic
manifold target. -/
theorem contDiffOn_nodeLogQuotient :
    ContDiffOn ℝ ∞ nodeLogQuotient nodeLogDomain :=
  (analyticOnNhd_nodeLogQuotient.restrictScalars (𝕜 := ℝ)).contDiffOn_of_completeSpace

theorem contDiffAt_nodeLogQuotient_zero (w : ℂ) :
    ContDiffAt ℝ ∞ nodeLogQuotient (0, w) :=
  ((analyticOnNhd_nodeLogQuotient (0, w) (zero_mem_nodeLogDomain w)).restrictScalars (𝕜 := ℝ)).contDiffAt

end ClusterSkeleton
