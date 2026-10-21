# Global native primitive and exterior derivative

`GlobalPrimitive.alpha S hdet ε κ hδ` is the pointwise glue of the accepted
`LocalPrimitive.eta` family on its constructed common open cover. Its carrier
is the actual complex exchange subtype, with inherited topology and the native
`(SmoothAtlas.presentation S hdet).manifold` tangent and alternating-form types.
The full integer matrix remains skew-symmetric and determinant one, only the
mutable quiver is acyclic, and frozen coordinates remain nonzero variables.

`alpha_eq_eta` proves restriction to every cover member, using accepted native
local smoothness and dense-torus overlap agreement. `isSmoothForm_alpha` proves
global native smoothness. `alpha_eq_torus` is equality to the literal accepted
`TorusCorrection.alpha = beta - dH`. `evalOne_alpha` evaluates that expression
on an arbitrary native tangent using both full matrix index sets, including
frozen columns. `eq_alpha_of_torus` proves uniqueness among smooth forms with
that torus expression; `alpha_eq_selection` proves subordinate-choice independence.

`exteriorDerivative_eq_of_eventuallyEq` pulls neighborhood equality through the
continuous inverse chart into its fixed coefficient space, applies actual
Mathlib `EventuallyEq.extDeriv_eq`, and transports back with the native chart
differential. `exteriorDerivative_alpha_torus` uses openness of the initial
torus and the accepted `TorusCorrection.exteriorDerivative_alpha`.
`exteriorDerivative_alpha` proves equality of whole native forms on all exchange
points using smoothness of both forms and `form_eq_of_dense`.
`nondegenerate_exteriorDerivative_alpha` uses equality to the accepted
`GlobalSymplectic.nondegenerate_omega`, whose proof uses zero-set charts.
Nondegeneracy is not inferred from density. The derivative is also packaged
with the native `IsSymplecticOn` predicate.

The parameter regime is ε > 0, κ ≥ 2ε+1, and 0 < δ < π. Constituent results
hold for every positive δ; `concrete_parameters` and `exists_global_primitive`
retain the full regime and supply ε=1, κ=3, δ=π/2, and the constructed form.
No parameter, primitive, overlap, smoothness, or derivative witness is assumed.
This completes the primitive assertion of manuscript Lemma 2.4, page 10,
using its accepted local cancellation and smooth extension constructions.

The consumer exercises arbitrary restrictions and torus tangents, uniqueness,
selection independence, concrete existence, the whole-form derivative, and
kernel triviality at arbitrary exchange points. Its accepted six-coordinate
fixture has simultaneous zero set {0,2}, zero normalized partners, a surviving
nonconstant regular correction, and a varying frozen coordinate. The global
value retains the surviving differential; derivative equality and nondegeneracy
are exercised on that boundary. Empty mutable and zero-index cases and an
inhabited dimension-zero seed are included.

The consumer uses unmodified native `Lean.collectAxioms` on every project
module in its actual import header, all current consumer declarations, private
and generated project declarations, nine mandatory supplements, and explicitly
realized lazy equations including `GlobalPrimitive.alpha.eq_1`. Accepted
inherited per-root evidence is retained only under exact source, native-output,
checker and declaration identities; overlapping results are compared by full
name and axiom set. Only `propext`, `Classical.choice`, and `Quot.sound` are allowed.
The immutable 85-file input and unrelated extras are preserved. Private
publication adds only this module, its consumer and this interface (88 entries).
Source-bound delivery artifacts record exact compiled declarations and checks.
The optimized audit remains unadopted.

Outstanding root-owned obligations: the actual vector field, complete flow on
all strata, same-flow dynamical skeleton equality, final umbrella imports and
global theorem packaging. This bounded primitive result does not establish
them or global-objective acceptance. Independent mathematical/native-calculus/
manuscript acceptance and actual terminal reviewer collection remain required
before this mission can close.
