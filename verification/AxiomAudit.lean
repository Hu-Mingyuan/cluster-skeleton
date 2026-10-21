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

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let modules := #[`ClusterSkeleton.AllStrataGrowth,
    `ClusterSkeleton.BoundaryTangency,
    `ClusterSkeleton.CapAngularTangency,
    `ClusterSkeleton.CapForwardInvariance,
    `ClusterSkeleton.CapIndependence,
    `ClusterSkeleton.CapSet,
    `ClusterSkeleton.CompactInteriorRigidity,
    `ClusterSkeleton.ConstructedFlowCapInclusion,
    `ClusterSkeleton.ConstructedFlowReverseInclusion,
    `ClusterSkeleton.CoordinateLoci,
    `ClusterSkeleton.DominanceCutoff,
    `ClusterSkeleton.Examples.A2,
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
    `ClusterSkeleton.SmoothAtlas,
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
