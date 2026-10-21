# Global smooth closed two-form

This lane uses the entire accepted integration tree `baccb6706466be36e25697dd884ede77007182b6` (tree `3efec59ff91e88eed064a03e972dc85b7ea6e5b8`) and exactly the three NodeTwoForm additions from `dcbeaca46ef3acaa9090e4ae43b189e3c9958222`. The 44-file source/mode/blob manifest is artifact `304c97a9-99b0-4eeb-9989-b1f3c4c38ccb`. The root imports, AxiomAudit, both accepted mathematical sources, PDF, and dependency pins are preserved exactly. This file does not establish publication or independent acceptance; those require accompanying immutable receipts.

All declarations below belong to `ClusterSkeleton.GlobalTwoForm`. For any `S : Seed d` and `hdet : S.Unimodular`, the carrier and topology are literally those of `S.Point` and `(SmoothAtlas.presentation S hdet).manifold`. There is no positive dimension assumption. Frozen coordinates remain nonzero variables; full skew symmetry/determinant one and mutable-only acyclicity are inherited from the unchanged seed.

## Native local compatibility and gluing

`localForm_inChart` identifies the actual native inverse-chart tangent pullback with the Euclidean pullback by the raw node-chart transition. `contDiffAt_localForm_inChart` and `continuousOn_localForm_coefficients` establish smoothness and continuity on the entire relevant source, including the node axes. The two-argument currying calculation is adapted, with attribution, from the pinned FsFltz theorem in `IntrinsicNativeCompletionFamilyExteriorGerms.lean`; upstream files are unchanged.

`localForm_eq_on_torus` compares the actual dependent tangent fibers. `localCompatibility S hdet I hI` inhabits the unchanged `NodeTwoForm.LocalCompatibility S I hdet hI`, for every independent `I`. Its proof compares continuous coefficients on each open overlap with any independent `J`, uses the accepted density of the initial torus, then cancels the actual inverse-chart differential. Compatibility is proved, never supplied as a premise.

`omega S hdet` selects the accepted local form in the atlas-selected independent chart at each point. `omega_eq_localForm` proves equality to **every** accepted node-local form on its full `candidateChartLocus`. `isSmoothForm_omega` proves the pinned native `IsSmoothForm` by local equality of native chart coefficients. The construction takes no extension witness, tangent identification, or boundary-nondegeneracy premise.

`omega_torus` gives exactly `logarithmicImaginaryValue`, namely

`Im ((1/2) Σ i,j B_ij (da_i(v)/a_i * da_j(w)/a_j - da_i(w)/a_i * da_j(v)/a_j))`.

## Actual closedness

`matrixForm` is the constant normalized imaginary alternating form on `Fin d → ℂ`. `normalizedLog b x` is the coordinatewise principal logarithm of `x_i/b_i`. At every torus center `b`, these ratios are near one, so the slit-plane logarithm supplies a smooth germ. `fderiv_normalizedLog` proves its actual real Fréchet derivative is `v_i/x_i`.

`exteriorDerivative_omega_torus` expresses the native chart coefficients near each torus point as the pullback of `matrixForm` by those logarithms. Mathlib exterior-derivative naturality and the derivative of the constant form prove vanishing there. `isSmoothForm_exteriorDerivative_omega` reuses the pinned theorem that the **actual** native exterior derivative of a smooth form is smooth. `exteriorDerivative_omega` applies accepted dense-set uniqueness to degree-three forms and the zero form. Density is used for equality, never for nondegeneracy.

`globalClosedExtension S hdet` inhabits the unchanged `NodeTwoForm.GlobalClosedExtension S hdet`, using `omega`, native smoothness, actual closedness, and all local restrictions. No compatibility, closedness, or desired-existence hypothesis is added.

## Verification and remaining work

The consumer imports the integrated root and the new module. It checks arbitrary independent overlaps, the actual zero-set chart, all local restrictions, the exact normalized imaginary formula, the unchanged extension proposition, and an explicitly inhabited determinant-one seed with `d=0`.

The consumer uses native `Lean.collectAxioms` on every defining-module declaration in GlobalTwoForm and NodeTwoForm and every current consumer declaration, including private/generated declarations. It explicitly preserves the attribution-sensitive roots `ClusterSkeleton.IndependentNodeChart.rawParameters.eq_1`, `ClusterSkeleton.SmoothAtlas.rawChart.congr_simp`, and `ContinuousAlternatingMap.restrictScalars.congr_simp`. Only `propext`, `Classical.choice`, and `Quot.sound` are allowed. The accompanying evidence must contain full per-root results and carry the unchanged accepted inherited manifests; namespace coverage alone is insufficient.

Boundary nondegeneracy belongs to lane B. Global symplectic existence, a primitive, a complete native flow, and the full same-flow skeleton equality remain open. The existing coordinator owns integration and recovery. This lane neither changes the cap/trapped definitions nor advances the default branch, objective phase, or any other lane.
