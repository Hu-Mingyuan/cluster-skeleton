# Native primitive residual and angular bridge

Manuscript: `references/acyclic_cluster_HMS.pdf`, pp. 9–11, Lemma 2.4 and
(2.7)–(2.8). Exact accepted parent: `a4362fb3aa4e8162c59574190adc82955520d85a`,
tree `3f8f3fa3c542f6dbcfa11dae23c07e601bee640b` (55 files unchanged).
Only `PrimitiveResidual.lean`, this interface, and its consumer are added.

For every seed and unimodularity proof, `tau` sums the entire integer matrix
row against the accepted native angular covectors. `logRow` sums the entire
row against log norms. Frozen coordinates remain nonzero variables in both
sums. `residual I` restricts BOTH indices to the complement of I.

`split_sum` proves the finite matrix identity from skew symmetry and the zero
independent block. `beta_decomposition` lifts it to equality of the actual
native one-forms at every actual exchange point, including zero coordinates
with the existing totalized definitions. Its singular term is precisely
`Σ i∈I, log ‖a_i‖ • tau_i - logRow_i • angleCovector_i`. There is no half,
inverse matrix, or sign change.

`contDiffAt_residual_inChart` proves coefficient smoothness in EVERY native
chart, assuming target membership and that the inverse-chart point lies in
`candidateChartLocus S I`. Independence is unnecessary for this smoothness
statement: all coordinates used in the residual are nonzero. No global
smoothness of the totalized residual at other points is asserted.

`node_argument` uses the actual exchange equation and accepted Laurent
character equality to identify `1-a_i*normalizedPartner_i` with the NEGATIVE
row character on the initial torus. `hasFDerivAt_log_neg_character` applies
native complex Laurent differentiation and the principal-log derivative.
`tau_eq_nodeAngle_differential` restricts scalars, takes the imaginary part,
and uses the native manifold chain rule and locality to identify `tau_i`
with `differentialCovector` of the actual normalized-node logarithm. Its
hypotheses retain initial-torus membership and the actual complex slit-plane
condition. No new node chart, scalar cutoff, or correction H is defined.

The consumer exercises arbitrary actual points and tangent directions, empty
I, and a full determinant-one four-dimensional seed with independent mutable
indices `{0,2}` and frozen indices `{1,3}`. It constructs an actual simultaneous
zero-stratum point and proves residual smoothness there. A separate family
allows both frozen coordinates to vary over arbitrary nonzero complex values;
the full angular row visibly contains a frozen coordinate differential. The
complementary frozen block is nonzero, and its exact residual expression is
checked separately.

The consumer uses unmodified native `Lean.collectAxioms` per root, including
all new defining-module/private/generated/local declarations and all nine
inherited attribution-sensitive supplements. The source-bound delivery
carries every inherited 740-root result, compares every overlapping result,
and records exact source/import/cache identities. Only `propext`,
`Classical.choice`, and `Quot.sound` are allowed. The optimized audit is not
adopted or edited here.

OPEN under the existing root/stage owners: corrected local primitive assembly,
simultaneous cancellation and gluing to global alpha, complete Liouville flow,
and full same-flow skeleton equality. Publication and compilation are separate
from independent mathematical acceptance. Root through successor67 retains
sole shared integration and final composition.
