import ClusterSkeleton
import Lean.Util.CollectAxioms

/-! Reproducible publication audit. This checks the final theorem directly and
all declarations attributed to every project module, including private and
generated declarations. The native collector traverses transitive dependencies.
Only Lean's standard foundational axioms are allowed. -/

#print axioms ClusterSkeleton.FullSkeleton.trappedSet_eq_coordinateCap
#print axioms ClusterSkeleton.FullSkeleton.liouvilleData
#print axioms ClusterSkeleton.FullSkeleton.liouvilleData_flow
#print axioms ClusterSkeleton.FullSkeleton.torus_anchor
#print axioms ClusterSkeleton.FullSkeleton.liouvilleData_trappedSet
#print axioms ClusterSkeleton.FullSkeleton.liouvilleSkeletonTarget_of_parameters
#print axioms ClusterSkeleton.FullSkeleton.liouvilleSkeletonTarget
#print axioms ClusterSkeleton.FullSkeleton.firstGeometricTarget
#print axioms ClusterSkeleton.FullSkeleton.trappedSet_eq_iUnion_lambdaStratum
#print axioms ClusterSkeleton.coordinateCap_eq_iUnion_lambdaStratum
#print axioms ClusterSkeleton.IndependentNodeChart.complementRank_eq_sub_two_mul_card

-- The recovery of the old `D = I` theorem (acceptance check 2).
#print axioms ClusterSkeleton.SkewSeed.liouvilleSkeletonTarget
#print axioms ClusterSkeleton.SkewSeed.skeleton_recovery
#print axioms ClusterSkeleton.SkewSeed.skeleton_recovery_of_parameters
#print axioms ClusterSkeleton.SkewSeed.dense_initialTorus
#print axioms ClusterSkeleton.SkewSeed.torus_anchor_old_matrix
#print axioms ClusterSkeleton.SkewSeed.liouvilleData_torus_anchor_old_matrix
#print axioms ClusterSkeleton.SkewSeed.trappedSet_conjFlow_eq_coordinateCap
#print axioms ClusterSkeleton.SkewSeed.liouvilleData_trappedSet_conjFlow
#print axioms ClusterSkeleton.SkewSeed.liouvilleData_trappedSet_conjFlow_iUnion

-- The genuinely non-skew instance (acceptance check 3).
#print axioms ClusterSkeleton.Examples.nonSkewSeed_side_checks
#print axioms ClusterSkeleton.Examples.nonSkewSeed_liouvilleSkeletonTarget
#print axioms ClusterSkeleton.Examples.nonSkewSeed_target_of_firstGeometricTarget
#print axioms ClusterSkeleton.Examples.nonSkewSeed_trappedSet
#print axioms ClusterSkeleton.Examples.nonSkewSeed_trappedSet_iUnion

-- The PDF clauses that `LiouvilleSkeletonTarget` does not itself contain
-- (RISK R4): the stratified form of the cap, compactness of every stratum and
-- the node chart. Proposed by section 8 of `docs/reviews/final-statement-review.md`
-- and, for the two old-carrier compactness roots, by RISK R-N2 of
-- `docs/reviews/recovery-nonskew-review.md`.
#print axioms ClusterSkeleton.isCompact_coordinateCap
#print axioms ClusterSkeleton.isCompact_lambdaStratum
#print axioms ClusterSkeleton.isClosed_lambdaStratum
#print axioms ClusterSkeleton.lambdaStratum_subset_coordinateCap
#print axioms ClusterSkeleton.dense_initialTorus
#print axioms ClusterSkeleton.initialTorus_nonempty
#print axioms ClusterSkeleton.iUnion_independent_candidateChartLocus
#print axioms ClusterSkeleton.Seed.Point.exists_independent_nonvanishing_locus
#print axioms ClusterSkeleton.IndependentNodeChart.homeomorph
#print axioms ClusterSkeleton.IndependentNodeChart.two_mul_card_le
#print axioms ClusterSkeleton.IndependentNodeChart.vector_finrank_real
#print axioms ClusterSkeleton.SkewSeed.isCompact_coordinateCap
#print axioms ClusterSkeleton.SkewSeed.isCompact_lambdaStratum

-- The constructed witnesses of the existentially quantified target, and the
-- dynamics the blueprint's equations are checked against.
#print axioms ClusterSkeleton.NativeCompleteFlow.completeFlow
#print axioms ClusterSkeleton.NativeCompleteFlow.exists_completeLiouvilleFlow
#print axioms ClusterSkeleton.SmoothAtlas.presentation
#print axioms ClusterSkeleton.GlobalPrimitive.alpha
#print axioms ClusterSkeleton.GlobalPrimitive.isSymplecticOn_exteriorDerivative_alpha
#print axioms ClusterSkeleton.GlobalLiouvilleField.Z
#print axioms ClusterSkeleton.GlobalLiouvilleField.contraction_exteriorDerivative
#print axioms ClusterSkeleton.GlobalLiouvilleField.mutable_radial_equation
#print axioms ClusterSkeleton.TorusLiouvilleDynamics.angular_equation
#print axioms ClusterSkeleton.TorusLiouvilleDynamics.angular_equation_row
#print axioms ClusterSkeleton.TorusLiouvilleDynamics.radial_matrix_equation
#print axioms ClusterSkeleton.TorusLiouvilleDynamics.mutable_radial_equation
#print axioms ClusterSkeleton.TorusLiouvilleDynamics.frozen_radial_equation
#print axioms ClusterSkeleton.TorusLiouvilleDynamics.omega_real
#print axioms ClusterSkeleton.TorusLiouvilleDynamics.full_matrix_inverse_bound
#print axioms ClusterSkeleton.BoundaryTangency.local_H_radial
#print axioms ClusterSkeleton.BoundaryTangency.nodeLog_drift_torus
#print axioms ClusterSkeleton.LocalAngularDynamics.nu
#print axioms ClusterSkeleton.AllStrataGrowth.row_nu_equation

-- The weighted linear algebra that replaces the baseline's `det B = 1`
-- cancellations: `K = E D`, `K` skew, `det K = ∏ d_i` with `IsUnit` only.
#print axioms ClusterSkeleton.Seed.K_eq_neg_D_mul_B
#print axioms ClusterSkeleton.Seed.sum_K_row_eq
#print axioms ClusterSkeleton.Seed.K_transpose
#print axioms ClusterSkeleton.Seed.det_K_of_unimodular
#print axioms ClusterSkeleton.Seed.acyclic_exponent
#print axioms ClusterSkeleton.SeedAlgebra.Kreal
#print axioms ClusterSkeleton.SeedAlgebra.K_eq_neg_D_mul_B
#print axioms ClusterSkeleton.SeedAlgebra.sum_K_row
#print axioms ClusterSkeleton.SeedAlgebra.c_inv_K
#print axioms ClusterSkeleton.SeedAlgebra.isUnit_det_Kreal
#print axioms ClusterSkeleton.SeedAlgebra.det_Kreal_of_unimodular
#print axioms ClusterSkeleton.SeedAlgebra.exists_inverse_bound_Kreal
#print axioms ClusterSkeleton.SeedAlgebra.Kreal_vecMul_injective
#print axioms ClusterSkeleton.SymmetrizerAlgebra.K_transpose
#print axioms ClusterSkeleton.SymmetrizerAlgebra.isUnit_det_K

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let modules := #[`ClusterSkeleton.AllStrataGrowth,
    `ClusterSkeleton.BoundaryTangency,
    `ClusterSkeleton.CapAngularTangency,
    `ClusterSkeleton.CapForwardInvariance,
    `ClusterSkeleton.CapIndependence,
    `ClusterSkeleton.CapSet,
    `ClusterSkeleton.CapStrata,
    `ClusterSkeleton.CompactInteriorRigidity,
    `ClusterSkeleton.ConstructedFlowCapInclusion,
    `ClusterSkeleton.ConstructedFlowReverseInclusion,
    `ClusterSkeleton.CoordinateLoci,
    `ClusterSkeleton.DominanceCutoff,
    `ClusterSkeleton.Examples.A2,
    `ClusterSkeleton.Examples.NonSkew,
    `ClusterSkeleton.Examples.NonSkewSkeleton,
    `ClusterSkeleton.FiniteTimeConfinement,
    `ClusterSkeleton.FormExtensionUniqueness,
    `ClusterSkeleton.FullSkeleton,
    `ClusterSkeleton.GeometryNativeBridge,
    `ClusterSkeleton.GeometryTarget,
    `ClusterSkeleton.GlobalLiouvilleField,
    `ClusterSkeleton.GlobalPrimitive,
    `ClusterSkeleton.GlobalSymplectic,
    `ClusterSkeleton.GlobalTwoForm,
    `ClusterSkeleton.IndependentLaurentCoordinates,
    `ClusterSkeleton.IndependentNodeChart,
    `ClusterSkeleton.IndependentNodeSmooth,
    `ClusterSkeleton.InitialTorusDensity,
    `ClusterSkeleton.IntegralBasisCompletion,
    `ClusterSkeleton.InteriorPartnerPropagation,
    `ClusterSkeleton.LaurentCoordinates,
    `ClusterSkeleton.LocalAngularDynamics,
    `ClusterSkeleton.LocalFormGluing,
    `ClusterSkeleton.LocalPrimitive,
    `ClusterSkeleton.NativeCompleteFlow,
    `ClusterSkeleton.NativeNodePrimitive,
    `ClusterSkeleton.NativeRadialOrbit,
    `ClusterSkeleton.NodeCoordinates,
    `ClusterSkeleton.NodeLogExtension,
    `ClusterSkeleton.NodeNondegeneracy,
    `ClusterSkeleton.NodePrimitiveCancellation,
    `ClusterSkeleton.NodeTwoForm,
    `ClusterSkeleton.NormalizedPartnerNormDrift,
    `ClusterSkeleton.PrimitiveCutoffs,
    `ClusterSkeleton.PrimitiveLocalization,
    `ClusterSkeleton.PrimitiveResidual,
    `ClusterSkeleton.RegularCorrection,
    `ClusterSkeleton.ScalarOrbitDynamics,
    `ClusterSkeleton.Seed,
    `ClusterSkeleton.SeedAlgebra,
    `ClusterSkeleton.SkewSeed,
    `ClusterSkeleton.SkewSeedRecovery,
    `ClusterSkeleton.SkewSeedSkeleton,
    `ClusterSkeleton.SmoothAtlas,
    `ClusterSkeleton.SymmetrizerAlgebra,
    `ClusterSkeleton.TorusChart,
    `ClusterSkeleton.TorusCorrection,
    `ClusterSkeleton.TorusLiouvilleDynamics,
    `ClusterSkeleton.TorusNondegeneracy,
    `ClusterSkeleton.TorusPrimitive,
    `ClusterSkeleton.TrappedSet,
    `ClusterSkeleton.ZeroSet,
    `ClusterSkeleton.ZeroStratumEscape,
    `ClusterSkeleton.ZeroStratumInvariance,
    `ClusterSkeleton.ZeroStratumPartnerDynamics]
  let mut counts : Array Nat := Array.replicate modules.size 0
  let mut total : Nat := 0
  for (name, _) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? name then
      if let some i := modules.toList.idxOf? env.header.moduleNames[idx]! then
        let axioms ← collectAxioms name
        for axiomName in axioms do
          unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
            throwError "Forbidden axiom {axiomName} in {name}"
        logInfo m!"AUDIT {name}: {axioms}"
        counts := counts.modify i (· + 1)
        total := total + 1
  for i in [:modules.size] do
    if counts[i]! == 0 then
      throwError "No declarations audited in {modules[i]!}"
    logInfo m!"AUDITED {modules[i]!}: {counts[i]!} declarations"
  logInfo m!"TOTAL_AUDITED: {total}"

-- These generated equations have had import-dependent module attribution.
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for name in #[`FsFltz.Geometry.SmoothManifold.evalTwo.eq_1,
      `ClusterSkeleton.SmoothPresentation.logarithmicImaginaryValue.eq_1] do
    unless env.contains name do
      throwError "Missing generated declaration {name}"
    let axioms ← collectAxioms name
    for axiomName in axioms do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
        throwError "Forbidden axiom {axiomName} in {name}"
    logInfo m!"GENERATED AUDIT {name}: {axioms}"
