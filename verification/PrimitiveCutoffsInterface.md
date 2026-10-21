# Manuscript scalar cutoffs

Source: manuscript page 10, equations (2.6)–(2.7), in the unchanged
`references/acyclic_cluster_HMS.pdf` (SHA256
`4426e18f96290d63d0650817dc07834e58217516248e7dd10c45470d0a10b666`).
Only scalar data are constructed. No H, global primitive, flow, or skeleton result
is inferred. Native Mathlib `ContDiff`, `deriv`, and `iteratedDeriv` are used.

## Concrete functions

Write `s = Real.smoothTransition` and `F(x) = ∫ t in 0..x, s(t)`.
The proof establishes `F(1)=1/2` by the reflection symmetry of `s`.

- `rho(x) = s(2-x²)`. Its values lie in [0,1], it equals one for |x|≤1,
  and equals zero for |x|≥2. Its support is compact, and every native iterated
  derivative has a finite uniform bound.
- `radial ε κ A = -L * F((-A-2ε)/L)`, where `L=2*(κ-2ε)`.
  For ε>0 take κ₀=2ε+1>0. Every κ≥κ₀ satisfies L>0. The function is
  smooth, nonpositive, has derivative in [0,1], and is strictly greater than A
  when A<0. It vanishes for A≥-2ε and equals A+κ on the entire half-line
  A≤-L-2ε, whose endpoint is negative. Positive-order derivatives are bounded;
  the stronger estimate |radial ε κ A|≤|A| gives the required growth with C=1.
- Let `r=min(δ/2,π/4)` and
  `w(T)=s((cos T-cos r)/(cos(r/2)-cos r))`.
  Set `vartheta δ T = arcsin(sin T)*w(T)`. For every δ>0 (hence every
  prescribed 0<δ<π), this is smooth and 2π-periodic, and equals T for |T|≤r/2.
  On the principal interval |T|≤π its **closed** support is contained in |T|<δ.
  Its derivative is at most one globally. The sign T*vartheta(T)≥0 is proved
  only on |T|≤π. Integer-period shifts preserve its value. Every native iterated
  derivative is uniformly bounded by continuity and periodicity.

The angular smoothness proof uses local vanishing where cosine is below the
support threshold, avoiding the singular values of arcsine. On the remaining
region cosine is positive. The derivative correction has nonpositive sign by
monotonicity of smoothTransition and arcsin(sin T)*sin T≥0.

## Consumers and verification

`verification/PrimitiveCutoffsConsumer.lean` directly imports the construction.
It quantifies arbitrary positive ε, every κ≥2ε+1, and every 0<δ<π; proves the
existence of the positive intercept threshold; exercises the closed zero plateau,
the entire affine negative half-line, arbitrarily deep tail points, and a nonzero
point of each angular identity germ. It also checks all derivative bounds and
periodic representative independence.

The consumer's audit uses unmodified native `Lean.collectAxioms` separately for
all declarations attributed to the new module, all matching public/private names,
all local consumer declarations, and all nine required generated supplements.
It fails on absent supplements and on axioms outside `propext`, `Classical.choice`,
and `Quot.sound`. The complete source-matched inherited 671-root evidence is
carried in the delivery artifact, with equal duplicate results checked. The
unadopted optimized audit is neither modified nor used.

Exact-source managed module and consumer receipts, full per-root results, source
hashes, and verified private publication are recorded together in the delivery
artifact. Compilation is separate from independent mathematical acceptance.

## Declaration inventory

Module namespace: `ClusterSkeleton.PrimitiveCutoffs`.

`ClusterSkeleton/PrimitiveCutoffs.lean`: 54 theorem declarations.

- `rho_smooth`
- `rho_nonneg`
- `rho_le_one`
- `rho_eq_one`
- `rho_eq_zero`
- `rho_compactSupport`
- `bounded_iteratedDeriv_of_compactSupport`
- `rho_iteratedDeriv_bound`
- `transitionPrimitive_hasDerivAt`
- `transitionPrimitive_deriv`
- `transitionPrimitive_smooth`
- `transitionPrimitive_zero`
- `transitionPrimitive_nonneg`
- `transitionPrimitive_le`
- `smoothTransition_reflect`
- `transitionPrimitive_one`
- `transitionPrimitive_tail`
- `radial_smooth`
- `radial_length_pos`
- `radial_hasDerivAt`
- `radial_deriv`
- `radial_deriv_nonneg`
- `radial_deriv_le_one`
- `radial_nonpos`
- `radial_eq_zero`
- `radial_tail`
- `radial_gt`
- `angularRadius_pos`
- `angularRadius_le_quarter`
- `angularRadius_lt`
- `angular_den_pos`
- `angular_cos_pos`
- `angularWindow_smooth`
- `angularWindow_nonneg`
- `angularWindow_le_one`
- `angularWindow_zero`
- `angularWindow_one`
- `vartheta_periodic`
- `vartheta_representative_independent`
- `vartheta_eq_self`
- `vartheta_zero_of_radius_le`
- `vartheta_support_principal`
- `vartheta_local_sign`
- `vartheta_eventually_zero`
- `vartheta_tsupport_principal`
- `vartheta_smooth`
- `vartheta_deriv_le_one`
- `periodic_iteratedDeriv`
- `bounded_iteratedDeriv_of_periodic`
- `vartheta_iteratedDeriv_bound`
- `radial_abs_le`
- `radial_linear_growth`
- `radial_secondDeriv_compactSupport`
- `radial_iteratedDeriv_bound`

`verification/PrimitiveCutoffsConsumer.lean`: 9 theorem declarations.

- `rho_contract`
- `radial_parameters`
- `radial_plateau`
- `radial_bounds`
- `angular_parameters`
- `angular_representatives`
- `angular_nonzero_germ`
- `angular_closed_support`
- `radial_tail_halfline`

The accepted 52-file baseline is `6b99d39f5a9102c9749100054a66a7475769eb4b`.
Only the three owned scalar-cutoff files belong to this delivery. Root/successor56
retains shared-import integration, audit adoption, and provenance recovery. Source
reconstruction does not repair stale registered or physical Git metadata.
