import ClusterSkeleton.SkewSeed
import ClusterSkeleton.CoordinateLoci
import ClusterSkeleton.CapSet
import ClusterSkeleton.CapStrata
import ClusterSkeleton.TrappedSet
import ClusterSkeleton.GeometryTarget
import Mathlib

/-!
# Recovery scaffolding for the old `D = I` theorem

Stage A supplies `SkewSeed.toSeed` (`E := B`, `D := 1`), the carrier identity
`SkewSeed.carrier_set_eq` and the canonical homeomorphism
`SkewSeed.pointHomeomorph`. It does not yet *state* the recovery of the old
skew-symmetric theorem. This file prepares the stage-A-only part of that
statement, so that stage C has to add only the instantiation of the weighted
theorem.

Three things are delivered.

* **Convention and sign matching.** `torus_anchor_old_matrix` rewrites the
  coefficient of the weighted logarithmic two-form
  `SmoothPresentation.logarithmicImaginaryValue` as the **old integer matrix**
  `S.B`, with no transpose, no sign change and no extra factor. This is the
  clause that certifies that the recovered form is the old form and hence that
  the Liouville flow is not time-reversed; the forward-orbit trapped set is not
  invariant under a time reversal, so this is the pivotal clause of acceptance
  check 2 of `docs/roadmap.md`.
* **The old objects, on the old carrier.** `SkewSeed.initialTorus`,
  `SkewSeed.coordinateCap` and `SkewSeed.lambdaStratum` are the reference
  predicates `T = {z_1⋯z_n ≠ 0}`, `C_B` and `Λ_I` written on `S.Point`, i.e. on
  the carrier of the *old* exchange equations. They are identified with the
  weighted loci of `S.toSeed` along `pointHomeomorph`, in both the image and
  the preimage direction, and the stratification and per-stratum compactness
  are transported.
* **Flow conjugation.** Mathlib's `Flow` API has `Homeomorph.flow` (the discrete
  `ℤ`-flow of a self-homeomorphism) and `Flow.IsSemiconjugacy`, but no transport
  of a flow along a homeomorphism between two different spaces, so `conjFlow`
  is constructed here. `trappedSet_conjFlow` transports the skeleton set.

## Smooth structure

No transported smooth structure is claimed; `pointHomeomorph` is a
homeomorphism, not a diffeomorphism. Recovery is to be stated directly for
`S.toSeed` as (a) + (b) + (c) of `docs/reviews/stage-a-semantic-audit.md` §4;
see `docs/weighted-recovery-plan.md` for that decision and its reason.
-/

set_option autoImplicit false

open scoped BigOperators Manifold ContDiff
open Set
open FsFltz.Geometry
open FsFltz.Geometry.SmoothManifold

namespace ClusterSkeleton

namespace SkewSeed

variable {d : ℕ} (S : SkewSeed d)

/-! ### Ambient coordinates of an old point

`SkewSeed.Point` is a subtype of the same ambient space as `Seed.Point` but for
the old defining predicate, so `Seed.Point.a` and `Seed.Point.b` do not apply to
it. These are the same two projections for the old carrier; `SkewSeed.lean` is
owned by another mission and is not edited. -/

namespace Point

variable {S}

/-- Original coordinates of an old point, including the variable frozen ones. -/
def a (p : S.Point) : Fin d → ℂ := p.1.1

/-- Mutation partners of an old point; they exist only for mutable vertices. -/
def b (p : S.Point) : S.Mutable → ℂ := p.1.2

end Point

/-- The homeomorphism preserves every original coordinate. -/
@[simp] theorem pointHomeomorph_a (p : S.Point) (j : Fin d) :
    (pointHomeomorph S p).a j = p.a j := rfl

/-- The homeomorphism preserves every mutation partner. -/
@[simp] theorem pointHomeomorph_b (p : S.Point) (i : S.Mutable) :
    (pointHomeomorph S p).b i = p.b i := rfl

@[simp] theorem pointHomeomorph_symm_a (p : (S.toSeed).Point) (j : Fin d) :
    ((pointHomeomorph S).symm p).a j = p.a j := rfl

@[simp] theorem pointHomeomorph_symm_b (p : (S.toSeed).Point) (i : S.Mutable) :
    ((pointHomeomorph S).symm p).b i = p.b i := rfl

/-- Unimodularity transfers to the weighted reading; this is the hypothesis of
the weighted theorem that stage C instantiates. -/
theorem toSeed_unimodular (hdet : S.Unimodular) : (S.toSeed).Unimodular :=
  (S.toSeed_unimodular_iff).mpr hdet

/-! ### (b) Convention and sign matching: the torus anchor with the old matrix -/

/-- The complex-cast form coefficient of the image seed is the old integer
matrix entry: no transpose, no sign change, no extra factor. -/
@[simp] theorem toSeed_K_complex (i j : Fin d) :
    (((S.toSeed).K i j : ℚ) : ℂ) = (S.B i j : ℂ) := by
  rw [toSeed_K]
  push_cast
  ring

/-- Matrix form of `toSeed_K_complex`: the complex-cast weighted form matrix of
the image seed is the complex-cast old exchange matrix. -/
theorem toSeed_K_matrix :
    ((S.toSeed).K.map ((↑) : ℚ → ℂ)) = S.B.map ((↑) : ℤ → ℂ) := by
  ext i j
  simp

/-- **Convention and sign matching.** The weighted logarithmic two-form of the
image seed, evaluated at any smooth presentation, is literally the old form:
its coefficient is the old integer matrix `S.B` itself. In particular there is
no sign flip, hence no time reversal of the Liouville flow, hence the
forward-orbit skeleton transports. Immediate from `toSeed_K`. -/
theorem torus_anchor_old_matrix (P : SmoothPresentation S.toSeed)
    (p : (S.toSeed).Point) (v w : P.manifold.Tangent p) :
    P.logarithmicImaginaryValue p v w =
      ((1 / 2 : ℂ) * ∑ i : Fin d, ∑ j : Fin d, (S.B i j : ℂ) *
        ((P.coordinateDifferential i p v / p.a i) *
          (P.coordinateDifferential j p w / p.a j) -
         (P.coordinateDifferential i p w / p.a i) *
          (P.coordinateDifferential j p v / p.a j))).im := by
  unfold SmoothPresentation.logarithmicImaginaryValue
  simp only [toSeed_K_complex]

/-! ### (c) The old loci on the old carrier -/

/-- The reference's initial torus `T = {z_1 ⋯ z_n ≠ 0}` on the **old** carrier. -/
def initialTorus : Set S.Point := {p | ∀ j, p.a j ≠ 0}

/-- The reference's coordinate cap `C_B` on the **old** carrier:
`|z_f| = 1` for frozen `f`, `|z_i| ≤ 1` and `(1 - |z_i|²) z_i' = 0` for mutable
`i`. Purely ambient, hence convention free. -/
def coordinateCap : Set S.Point :=
  {p | (∀ f, f ∉ S.mutable → ‖p.a f‖ = 1) ∧
    ∀ i : S.Mutable, ‖p.a i‖ ≤ 1 ∧
      ((1 - ‖p.a i‖ ^ 2 : ℝ) : ℂ) * p.b i = 0}

/-- The reference's stratum `Λ_I` on the **old** carrier. -/
def lambdaStratum (I : Finset (Fin d)) : Set S.Point :=
  {p | (∀ i : S.Mutable, (i : Fin d) ∈ I → ‖p.a i‖ ≤ 1 ∧ p.b i = 0) ∧
       (∀ j : Fin d, j ∉ I → ‖p.a j‖ = 1)}

/-- Every locus above is phrased in ambient coordinates, which the
homeomorphism preserves on the nose. -/
theorem mem_initialTorus_iff (p : S.Point) :
    p ∈ initialTorus S ↔
      pointHomeomorph S p ∈ _root_.ClusterSkeleton.initialTorus S.toSeed :=
  Iff.rfl

theorem mem_coordinateCap_iff (p : S.Point) :
    p ∈ coordinateCap S ↔
      pointHomeomorph S p ∈ _root_.ClusterSkeleton.coordinateCap S.toSeed :=
  Iff.rfl

theorem mem_lambdaStratum_iff (I : Finset (Fin d)) (p : S.Point) :
    p ∈ lambdaStratum S I ↔
      pointHomeomorph S p ∈ _root_.ClusterSkeleton.lambdaStratum S.toSeed I :=
  Iff.rfl

theorem preimage_initialTorus :
    pointHomeomorph S ⁻¹' _root_.ClusterSkeleton.initialTorus S.toSeed =
      initialTorus S :=
  Set.ext fun p => (mem_initialTorus_iff S p).symm

theorem preimage_coordinateCap :
    pointHomeomorph S ⁻¹' _root_.ClusterSkeleton.coordinateCap S.toSeed =
      coordinateCap S :=
  Set.ext fun p => (mem_coordinateCap_iff S p).symm

theorem preimage_lambdaStratum (I : Finset (Fin d)) :
    pointHomeomorph S ⁻¹' _root_.ClusterSkeleton.lambdaStratum S.toSeed I =
      lambdaStratum S I :=
  Set.ext fun p => (mem_lambdaStratum_iff S I p).symm

private theorem image_of_preimage {t : Set ((S.toSeed).Point)} {s : Set S.Point}
    (h : pointHomeomorph S ⁻¹' t = s) : pointHomeomorph S '' s = t := by
  rw [← h, Set.image_preimage_eq _ (pointHomeomorph S).surjective]

theorem image_initialTorus :
    pointHomeomorph S '' initialTorus S =
      _root_.ClusterSkeleton.initialTorus S.toSeed :=
  image_of_preimage S (preimage_initialTorus S)

theorem image_coordinateCap :
    pointHomeomorph S '' coordinateCap S =
      _root_.ClusterSkeleton.coordinateCap S.toSeed :=
  image_of_preimage S (preimage_coordinateCap S)

theorem image_lambdaStratum (I : Finset (Fin d)) :
    pointHomeomorph S '' lambdaStratum S I =
      _root_.ClusterSkeleton.lambdaStratum S.toSeed I :=
  image_of_preimage S (preimage_lambdaStratum S I)

/-- The old cap is the union of the old strata over the **old** independent
subsets of the mutable vertices: the reference's stratified skeleton, on the old
carrier. The index set is unchanged, because `toSeed_independent_iff` is
`Iff.rfl`. -/
theorem coordinateCap_eq_iUnion_lambdaStratum :
    coordinateCap S =
      ⋃ I : {I : Finset (Fin d) // S.Independent I}, lambdaStratum S I.val := by
  ext p
  rw [mem_coordinateCap_iff,
    _root_.ClusterSkeleton.coordinateCap_eq_iUnion_lambdaStratum]
  simp only [Set.mem_iUnion]
  constructor
  · rintro ⟨I, hI⟩
    exact ⟨⟨I.val, I.property⟩, (mem_lambdaStratum_iff S I.val p).mpr hI⟩
  · rintro ⟨I, hI⟩
    exact ⟨⟨I.val, I.property⟩, (mem_lambdaStratum_iff S I.val p).mp hI⟩

/-- Each old stratum is compact in the inherited topology of the old carrier,
by transport of `CapStrata.isCompact_lambdaStratum` along the homeomorphism. -/
theorem isCompact_lambdaStratum (I : Finset (Fin d)) (hI : I ⊆ S.mutable) :
    IsCompact (lambdaStratum S I) := by
  rw [← preimage_lambdaStratum]
  exact (pointHomeomorph S).isCompact_preimage.mpr
    (_root_.ClusterSkeleton.isCompact_lambdaStratum S.toSeed I hI)

/-- The old cap is compact as well. -/
theorem isCompact_coordinateCap : IsCompact (coordinateCap S) := by
  rw [← preimage_coordinateCap]
  exact (pointHomeomorph S).isCompact_preimage.mpr
    (_root_.ClusterSkeleton.isCompact_coordinateCap S.toSeed)

/-! ### (c) Flow conjugation and the trapped set

Mathlib supplies no transport of a `Flow` along a homeomorphism between two
different carriers (`Mathlib/Dynamics/Flow.lean` has only `Homeomorph.flow`,
the discrete `ℤ`-flow of a self-homeomorphism, and `Flow.IsSemiconjugacy`),
so the conjugate flow is constructed here from `Homeomorph.continuous` and the
group laws of the given flow. -/

/-- The flow on the old carrier conjugate to a flow on the weighted carrier.
Continuity is `Homeomorph.continuous` on both sides; the two group laws come
from those of `Φ` and `Homeomorph.apply_symm_apply`. -/
noncomputable def conjFlow (Φ : Flow ℝ ((S.toSeed).Point)) : Flow ℝ S.Point where
  toFun t p := (pointHomeomorph S).symm (Φ t (pointHomeomorph S p))
  cont' := by
    have h : Continuous fun x : ℝ × S.Point => Φ x.1 (pointHomeomorph S x.2) :=
      Φ.continuous continuous_fst
        ((pointHomeomorph S).continuous.comp continuous_snd)
    exact (pointHomeomorph S).symm.continuous.comp h
  map_add' t₁ t₂ p := by
    simp only [Homeomorph.apply_symm_apply, Flow.map_add]
  map_zero' p := by
    simp only [Flow.map_zero_apply, Homeomorph.symm_apply_apply]

@[simp] theorem conjFlow_apply (Φ : Flow ℝ ((S.toSeed).Point)) (t : ℝ)
    (p : S.Point) :
    conjFlow S Φ t p = (pointHomeomorph S).symm (Φ t (pointHomeomorph S p)) :=
  rfl

/-- The conjugate flow is a conjugation on the nose: the homeomorphism is a
semiconjugacy from the old flow to the weighted one. -/
theorem pointHomeomorph_conjFlow (Φ : Flow ℝ ((S.toSeed).Point)) (t : ℝ)
    (p : S.Point) :
    pointHomeomorph S (conjFlow S Φ t p) = Φ t (pointHomeomorph S p) := by
  simp

/-- Forward orbits transport along the homeomorphism, in the image form. -/
theorem forwardOrbit_conjFlow (Φ : Flow ℝ ((S.toSeed).Point)) (p : S.Point) :
    (conjFlow S Φ).forwardOrbit p =
      (pointHomeomorph S).symm '' Φ.forwardOrbit (pointHomeomorph S p) := by
  ext q
  simp only [Flow.forwardOrbit_eq_range_nonneg, Set.mem_range, Set.mem_image,
    conjFlow_apply]
  constructor
  · rintro ⟨t, rfl⟩
    exact ⟨Φ t (pointHomeomorph S p), ⟨t, rfl⟩, rfl⟩
  · rintro ⟨y, ⟨t, rfl⟩, rfl⟩
    exact ⟨t, rfl⟩

/-- Forward orbits transport along the homeomorphism, in the preimage form. -/
theorem forwardOrbit_conjFlow_preimage (Φ : Flow ℝ ((S.toSeed).Point))
    (p : S.Point) :
    (conjFlow S Φ).forwardOrbit p =
      pointHomeomorph S ⁻¹' Φ.forwardOrbit (pointHomeomorph S p) := by
  rw [forwardOrbit_conjFlow, Homeomorph.image_eq_preimage_symm,
    Homeomorph.symm_symm]

/-- Forward orbits transport along the homeomorphism, in the forward image
form. -/
theorem image_forwardOrbit_conjFlow (Φ : Flow ℝ ((S.toSeed).Point))
    (p : S.Point) :
    pointHomeomorph S '' (conjFlow S Φ).forwardOrbit p =
      Φ.forwardOrbit (pointHomeomorph S p) := by
  rw [forwardOrbit_conjFlow_preimage]
  exact Set.image_preimage_eq _ (pointHomeomorph S).surjective

/-- **The skeleton set transports.** The trapped set of the conjugate flow on
the old carrier is the preimage of the trapped set of the given flow: closure
and compactness of forward orbits both transport along a homeomorphism. -/
theorem trappedSet_conjFlow (Φ : Flow ℝ ((S.toSeed).Point)) :
    trappedSet (conjFlow S Φ) = pointHomeomorph S ⁻¹' trappedSet Φ := by
  ext p
  simp only [Set.mem_preimage, mem_trappedSet, forwardOrbit_conjFlow]
  rw [← Homeomorph.image_closure]
  exact (pointHomeomorph S).symm.isCompact_image

/-- The same identity in the image direction. -/
theorem image_trappedSet_conjFlow (Φ : Flow ℝ ((S.toSeed).Point)) :
    pointHomeomorph S '' trappedSet (conjFlow S Φ) = trappedSet Φ := by
  rw [trappedSet_conjFlow]
  exact Set.image_preimage_eq _ (pointHomeomorph S).surjective

/-- The recovered skeleton identity on the old carrier: if the weighted
skeleton identity holds for a flow on `(S.toSeed).Point`, then the conjugate
flow on the old carrier has exactly the old coordinate cap as its trapped set.
This is the shape in which stage C reads off the old theorem. -/
theorem trappedSet_conjFlow_eq_coordinateCap (Φ : Flow ℝ ((S.toSeed).Point))
    (h : trappedSet Φ = _root_.ClusterSkeleton.coordinateCap S.toSeed) :
    trappedSet (conjFlow S Φ) = coordinateCap S := by
  rw [trappedSet_conjFlow, h, preimage_coordinateCap]

end SkewSeed

end ClusterSkeleton
