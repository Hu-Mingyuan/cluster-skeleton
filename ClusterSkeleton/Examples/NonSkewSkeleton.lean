import ClusterSkeleton.FullSkeleton
import ClusterSkeleton.Examples.NonSkew

/-!
# The first geometric target for a genuinely non-skew seed

`Examples/NonSkew` builds the concrete input of Section 4 of
`target-theorem.pdf`,
```
E = [[0,1,-1,0],[-2,0,0,-1],[1,0,0,0],[0,1,0,0]],  D = diag(1,2,1,2),  M = {0,1}
```
which is skew-*symmetrizable* but not skew-symmetric: `E 0 1 = 1` while
`E 1 0 = -2`, so no rescaling by a single constant turns `E` into a skew matrix
and the old `D = I` library does not apply to it.

Here the universal theorem is *instantiated* at that seed, which is acceptance
check 3 of `docs/roadmap.md`. Nothing is specialized: the witnesses are the ones
`FullSkeleton` constructs for an arbitrary unimodular weighted seed, and
`FullSkeleton.firstGeometricTarget` stays the quantified statement. The side
conditions of the roadmap are collected in explicit, literal form in
`nonSkewSeed_side_checks`.
-/

noncomputable section
set_option autoImplicit false
open scoped Manifold ContDiff Topology Matrix
open Set FsFltz.Geometry

namespace ClusterSkeleton.Examples

/-- All the roadmap's side conditions on the concrete seed, in literal form:
the three data, unimodularity, positivity of the weights, entrywise
skew-symmetry of `K = E · D`, acyclicity of the mutable block, and the failure
of skew-symmetry of `E` itself. All of them are the already proved facts of
`Examples/NonSkew` and the structure fields of `nonSkewSeed`. -/
theorem nonSkewSeed_side_checks :
    nonSkewSeed.E = !![0, 1, -1, 0;
                      -2, 0, 0, -1;
                       1, 0, 0, 0;
                       0, 1, 0, 0] ∧
    nonSkewSeed.D = ![1, 2, 1, 2] ∧
    nonSkewSeed.mutable = {0, 1} ∧
    nonSkewSeed.E.det = 1 ∧
    (∀ i, 0 < nonSkewSeed.D i) ∧
    (∀ i j, (nonSkewSeed.E i j : ℚ) * nonSkewSeed.D j =
      -((nonSkewSeed.E j i : ℚ) * nonSkewSeed.D i)) ∧
    WellFounded (fun i j : {i // i ∈ nonSkewSeed.mutable} => 0 < nonSkewSeed.E i j) ∧
    ¬ ∀ i j, nonSkewSeed.E i j = -nonSkewSeed.E j i :=
  ⟨nonSkewSeed_E, nonSkewSeed_D, nonSkewSeed_mutable, nonSkewSeed_unimodular,
    nonSkewSeed.D_pos, nonSkewSeed.skewSymmetrizable, nonSkewSeed.acyclic,
    nonSkewSeed_not_skew⟩

/-- **Acceptance check 3.** The concrete non-skew seed satisfies the first
geometric target, by instantiating the universal theorem at it. -/
theorem nonSkewSeed_liouvilleSkeletonTarget :
    LiouvilleSkeletonTarget nonSkewSeed :=
  FullSkeleton.liouvilleSkeletonTarget nonSkewSeed nonSkewSeed_unimodular

/-- The same statement read off the quantified theorem
`FullSkeleton.firstGeometricTarget` itself, at `d = 4` and this seed. -/
theorem nonSkewSeed_target_of_firstGeometricTarget :
    LiouvilleSkeletonTarget nonSkewSeed :=
  FullSkeleton.firstGeometricTarget 4 nonSkewSeed nonSkewSeed_unimodular

/-- The constructed complete flow of the non-skew seed has exactly the
coordinate cap as its dynamical skeleton. -/
theorem nonSkewSeed_trappedSet {ε κ δ : ℝ} (hε : 0 < ε) (hκ : 2 * ε + 1 ≤ κ)
    (hδ : 0 < δ) :
    trappedSet (FullSkeleton.liouvilleData nonSkewSeed nonSkewSeed_unimodular
        hε hκ hδ).completeFlow.flow =
      coordinateCap nonSkewSeed :=
  FullSkeleton.liouvilleData_trappedSet nonSkewSeed nonSkewSeed_unimodular hε hκ hδ

/-- Its stratified form: the skeleton is the union of the strata `Λ_I` over the
independent subsets of `{0, 1}`. -/
theorem nonSkewSeed_trappedSet_iUnion {ε κ δ : ℝ} (hε : 0 < ε)
    (hκ : 2 * ε + 1 ≤ κ) (hδ : 0 < δ) :
    trappedSet (FullSkeleton.liouvilleData nonSkewSeed nonSkewSeed_unimodular
        hε hκ hδ).completeFlow.flow =
      ⋃ I : {I : Finset (Fin 4) // nonSkewSeed.Independent I},
        lambdaStratum nonSkewSeed I.val :=
  FullSkeleton.trappedSet_eq_iUnion_lambdaStratum nonSkewSeed
    nonSkewSeed_unimodular hε hκ hδ

end ClusterSkeleton.Examples
