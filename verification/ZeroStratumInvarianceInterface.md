# Native zero-stratum invariance

The field is exactly GlobalLiouvilleField.Z S hdet ε κ hδ on
SmoothAtlas.presentation S hdet. The carrier is the actual complex solution
subtype of the exchange equations, with its induced topology. Frozen coordinates
remain arbitrary nonzero variables. The full skew-symmetric integer matrix has
determinant one; only its mutable quiver is acyclic.

For ε>0, κ≥2ε+1 and δ>0, normSq_drift proves
D_Z(normSq(a_i)) = -2κ normSq(a_i) on exactly
LocalPrimitive.neighborhood S ε κ δ p, for any mutable i in p.zeroSet.
The stronger positive-δ scope includes the requested 0<δ<π regime.
coordinate_smooth proves native coordinate smoothness, and differential_normSq
composes its actual manifold derivative with the real Fréchet derivative of
the squared norm. At a zero coordinate this derivative is zero directly.
Away from zero, inner_eq_normSq_mul_re_div converts it to the accepted
BoundaryTangency.deep_radius identity. Division is used only under a proved
nonzero hypothesis. No normalized-partner condition is present. The accepted
boundary tangency result remains unchanged; angular divisibility is not a premise.

coordinate_hasDerivWithinAt explicitly composes HasMFDerivAt with the
HasMFDerivWithinAt supplied by native IsMIntegralCurveOn, passes through
hasMFDerivWithinAt_iff_hasFDerivWithinAt, and evaluates the derivative on one.
normSq_hasDerivWithinAt uses HasDerivWithinAt.norm_sq to give the genuine
scalar ODE within the time domain.

For any preconnected J⊆ℝ and any genuine integral curve γ of this same field,
coordinate_zero_iff proves (γ s).a i=0 iff (γ t).a i=0 for all s,t∈J and
all indices i. zeroSet_eq proves equality of the full zero sets.
coordinate_ne_zero_iff gives nonvanishing persistence in both directions.

The argument takes a relative real ball around each zero time whose image lies
in the accepted local neighborhood. Preconnected subsets of ℝ are convex.
On their intersection with the ball, exp(2κt)normSq(a_i(γ t)) has derivative
zero. The native convex mean-value estimate with bound zero proves constancy,
including relative endpoints and singleton sets. The zero fiber is closed by
continuity and open by local persistence in the subtype J; its clopen property
propagates the zero to all of J. Every derivative hypothesis of the generic
scalar helper is discharged from the actual native curve. There is no flow,
completeness, invariant-stratum, or desired-zero-equivalence hypothesis.

The consumer exercises literal mfderiv, scalarDerivative and
HasDerivWithinAt; generic full zeroSet constancy and both time directions;
closed-interval endpoints and singleton domains; actual A₂ boundary centers
with arbitrary or zero complex partner and every point in their local
neighborhood; simultaneous-zero strata with arbitrary or zero partners; a
nonzero selected coordinate while another stays zero, with nonvacuous
punctured-neighborhood examples; variable frozen data; empty mutable sets;
and an inhabited dimension-zero carrier with an actual constant native
integral curve on all real time.

## Compiled theorem inventory

The module namespace is ClusterSkeleton.ZeroStratumInvariance (11 theorems):

local_zero_propagation, zero_iff_of_local_linear_ode, coordinate_smooth, differential_normSq, inner_eq_normSq_mul_re_div, normSq_drift, coordinate_hasDerivWithinAt, normSq_hasDerivWithinAt, coordinate_zero_iff, zeroSet_eq, coordinate_ne_zero_iff.

The consumer namespace is ZeroStratumInvarianceConsumer (23 theorems):

literal_native_normSq, native_chain_bridge, preconnected_curve_both_directions, closed_interval_endpoints, singleton_domain, boundary_coordinates, pair_unimodular, frozen_unimodular, empty_unimodular, a2_boundary_local, a2_zero_partner_local, a2_center, simultaneous_local, simultaneous_zero_partners_local, selected_with_other_zero, continuous_selectedBoundary, selected_neighborhood_nonvacuous, variable_frozen_boundary, empty_mutable_variable, empty_mutable_curve, inhabited_dimension_zero, simultaneous_curve, dimension_zero_native_curve.

The consumer's eight concrete fixture definitions are boundaryPoint,
pairSeed, frozenSeed, frozenPoint, emptySeed, doubleBoundary,
selectedBoundary, and variableFrozenBoundary. They are actual exchange
points/seeds, not dynamical assumptions.

## Verification and remaining ownership

The source base is accepted97 commit
28cd68ae9627f1826a99b9feae5a55b9520d72d1, tree
12276581f1fb3a0416aa5491170cfd39682b238c; full raw input artifact
2bdbd49e-9b3b-4c1e-bbc4-1054abf54ba7 has SHA256
bc1054ac17e5df6c6a6ee4fd6c884dccde2b3ef0c9839fd147ad3340ad1b7a05.
All97 old file modes, blobs and hashes, plus unrelated extras, are preserved.
Only this interface, the new module, and its consumer are published: exact100.

The source-bound delivery carries managed exact-source module and consumer
receipts, isolated new-import composition checks, all2639 inherited per-root
axiom records, every fresh combined project/FsFltz/private/generated/consumer
root, all9 mandatory supplements, and inherited/new lazy equations. Exact
full-name overlap equality, ordered imports, native outputs and checker
identities are checked. Only propext, Classical.choice and Quot.sound are
permitted. The optimized audit remains UNADOPTED. Mathematical/manuscript/native
review, actual terminal reviewer collection, private publication, bounded
maintainer acceptance and actual durable collection remain separate evidence;
a successful build alone does not establish mission acceptance.

The source argument is manuscript Lemma2.5, page11. This mission supplies its
zero-stratum invariance step without assuming the displayed smooth angular
coefficient or normalized-partner equation.

OPEN, with root mission df1a0cdf-af80-4485-9c04-b045ff0f3ffb and its existing
successor96 68949252-bca3-474a-bf13-6e417f9d50d3 as integration owner:
smooth angular coefficient, normalized-partner equations, all-strata growth
bounds, construction of two-sided complete trajectories/flow, and the same-flow
skeleton equality. Shared imports, final integration/packaging, audit adoption
and provenance recovery also remain root-owned. GeometryTarget definitions
are unchanged and unresolved. No global target or phase acceptance is claimed.
