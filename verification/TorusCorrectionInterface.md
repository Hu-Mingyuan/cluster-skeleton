# The manuscript torus correction

Source: `acyclic_cluster_HMS.pdf`, pages 9–11, particularly (2.5)–(2.7).
This delivery constructs H on the initial torus of the actual exchange points
with their inherited topology and the accepted `SmoothAtlas.presentation`.

`A S p j = log ‖p.a j‖`. `rowLog S p i` sums `(B i j : ℝ) * A S p j`
over **all** original coordinates. The H sum is over mutable i; its dominance
factor is the exact accepted product over mutable neighbors only. The angular
factor uses `vartheta δ (arg (-exchangeCharacter p i))`. Frozen coordinates
remain variable, as the consumer demonstrates through a varying full row.
The totalized expression off the torus is a definition, not an extension claim.

## The argument cut

`localAngle b z = Im(log(z/b)) + arg b`. At every nonzero b, the quotient
is 1, so the principal logarithm is smooth on a neighborhood of that base point.
The proof uses native complex `ContDiffAt`, restriction of scalars to ℝ,
and the continuous linear imaginary-part map. The lift has the same `Real.Angle`
class as `arg z` whenever both b and z are nonzero. Equality of sine and cosine
then proves equality of the accepted vartheta values. An eventual equality
transfers smoothness from this local representative to the angular factor.
Thus no globally smooth argument or unsupported periodic descent is assumed.
The consumer centers the lift at -1, where its value is π, and checks smoothness
at that principal cut point.

## Native result

`contMDiffOn_H` proves native smoothness on `initialTorus S`; in fact the proof
needs only δ>0 and allows arbitrary ε and κ. This includes every required
ε>0, κ≥2ε+1 and 0<δ<π. `alpha` is exactly `TorusPrimitive.alpha` applied to
this constructed H. `contDiffAt_alpha_inChart` proves coefficient smoothness
in every native chart at torus points. `exteriorDerivative_alpha` identifies
the actual pinned exterior derivative with `GlobalTwoForm.omega`, discharging
the H smoothness premise. `evalOne_alpha` preserves the full matrix convention
and the actual native differential of H.

The consumer quantifies all allowed parameters and checks the empty mutable
sum and d=0. A seed with B=[[0,1],[-1,0]] and only vertex 0 mutable supplies
an actual point with a₀=exp(-5), a₁=-exp(iπ/8). For ε=1, κ=3 and δ=π/2,
it proves H=-2(π/8)≠0 and the native derivative identity there. It also proves
that the frozen row varies between actual torus points.

## Verification and ownership

The complete scalar 55-entry parent and the exact three dominance and three
torus primitive additions retain their bytes and modes. Root imports, the live
audit, upstream dependencies, manuscript and all retained audit extras are
unchanged. Publication adds only the six borrowed files and these three owned
files. The native consumer audit checks each declaration attributed to all four
combined scalar/dominance/torus/correction modules, matching public/private
names, every consumer declaration, and all nine mandatory generated supplements.
The delivery records complete inherited source/checker/declaration identities,
per-root results, exact-source managed module/consumer receipts and verified
private publication. Independent mathematical acceptance is separate.

The author retains concrete repairs and terminal review collection.
Root/successor62 retains shared integration. Global smooth primitive extension,
complete flow and skeleton equality remain open; none follows here.
