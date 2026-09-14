# Verification map

## Status

`lake build GaussianDepthSeparation` checks the development and runs a mandatory axiom gate over
all declarations in its imported proof modules, including private helpers.
Only `propext`, `Classical.choice`, and `Quot.sound` are allowed; `sorryAx`,
project-defined axioms, and native-evaluation axioms fail the build.
The default `lake build` also runs the standalone `GaussianDepthSeparationAuditTests` regression
tests, whose deliberately untrusted fixtures are outside the mathematical
library. `GaussianDepthSeparationAudit.lean` retains the optional detailed axiom listing.
The main theorems and the numbered results in
Sections 2--5 are formally verified, including the radial polynomial distance
(Lemma 5.1), the local normalized chi-square density bound (Lemma 5.2), and the
paper's sign-change proof of the high-chaos energy bound (Lemma 5.3).
All fourteen numbered results have direct Lean counterparts. Corollary 1.3
is formalized by `depth_separation_comparison`, which combines the two depth
bounds with a common parameter budget and error tolerance. Its positive
asymptotic constants are quantified before dimension and accuracy, and its
dimension threshold is explicitly `16`. As reported in the companion manuscript,
the Lean statements corresponding to all numbered results have been reviewed
by a human to confirm that they express the intended mathematical claims.

This audit covers the standalone `GaussianDepthSeparation` library. Module paths
in the table below are relative to `GaussianDepthSeparation/`.

## Paper-to-Lean map

| Paper result | Lean declaration(s) | Module |
| --- | --- | --- |
| Theorem 1.1 (ridge lower bound) | `ridge_lower_bound` | `LowerBound.lean` |
| Theorem 1.2(i) (depth-2 lower bound) | `depth_separation_lower` | `DepthSeparation.lean` |
| Theorem 1.2(ii) (global depth-3 upper bound) | `depth_separation_upper_L2` | `GlobalUpper.lean` |
| Corollary 1.3 (matched parameter and accuracy budgets) | `depth_separation_comparison` | `DepthComparison.lean` |
| Lemma 2.1 (Hermite ridge identity) | `hermite_ridge_identity`, `ridgeHermite_eq_sum` | `Hermite.lean`, `Chaos.lean` |
| Lemma 2.2 (rotations commute with chaos projections) | `Pn_comp_rotation` | `Chaos.lean` |
| Proposition 3.1 (radialization commutes with chaos projections) | `radAvg_eq_starProjection`, `radAvg_comm_Pn` | `RadialAverage.lean` |
| Proposition 3.2 (radialized ridge expansion) | `radAvg_ridge_expansion` | `Radialization.lean` |
| Lemma 3.3 (spherical moments) | `sphereMoment_eq_zero_of_odd`, `sphereMoment_of_even` | `MomentsCore.lean`, `Moments.lean` |
| Proposition 3.4 (maximal spherical moment and product formula) | `abs_sphereMoment_le_Kmom`, `Kmom_eq` | `Moments.lean` |
| Proposition 4.1 (chaos correlation) | `correlation_eq_zero_of_odd`, `correlation_bound_of_even` | `Correlation.lean` |
| Corollary 4.2 (tail estimate) | `tail_estimate` | `LowerBound.lean` |
| Lemma 5.1 (radial polynomial distance) | `radial_polynomial_distance` | `RadialPolynomial.lean`, `RadialRepresentation.lean`, `RadialMeasure.lean`, `RadialDistance.lean` |
| Lemma 5.2 (local chi-square density) | `chi_square_local_density` (explicit constants `c₁ = exp (-2) / 8`, `d₀ = 16`) | `ChiSquare.lean` |
| Lemma 5.3 (high-chaos energy) | `radialError_weighted_lower`, `energy_lower_bound` (explicit constants `c = cEnergy`, `d₀ = 16`) | `Oscillation.lean`, `EnergyBound.lean` |

Supporting claims used as notation or prose in the paper are also checked:
one- and multivariate Hermite totality (`hermite_hasSum`, `chaos_hasSum_Pn`,
`Pge_hasSum`), the ReLU profile estimate (`norm_reluProfile_le`), the concrete
depth-2 network corollary (`depth_separation_lower_net2`), and the Gaussian tail
bound (`gaussian_norm_tail`).

In Corollary 1.3, `cLower` and `cUpper` witness the paper's Ω and O bounds.
Both are positive universal constants, independent of `d` and `ε`. The local
abbreviations are `L = d + log (1/ε)` and `B = A * L`, with the same `B` in
the `Net2` and `Net3` parameter hypotheses. Lean bounds the maximum of the
two depth-3 hidden widths, exactly as defined in the paper. The proof absorbs
the upper theorem's extra `+1` using `L ≥ 1`; the corollary statement has no
extra `+1`. The mathematical statement of the corollary is unchanged, and
no proof is added to the manuscript after it.

## Proof fidelity

All formal proofs follow the paper's mathematical decomposition, with the
analytic and measure-theoretic details made explicit.  Five local arguments
use equivalent formalization-friendly variants:

1. Lemma 2.1 is proved in Lean from the three-term Hermite recurrence and
   finite multi-index reindexing, rather than by comparing coefficients in the
   generating function.
2. In Lemma 3.3, Lean proves the radius-direction moment factorization by a
   Haar/Fubini argument, avoiding a separate formal independence theorem for
   Gaussian radius and direction.
3. In Proposition 3.4, the manuscript invokes generalized Hölder.  Lean uses
   its pointwise weighted-AM--GM consequence and then integrates, giving the
   same maximal-moment inequality.
4. In Lemma 5.2, the manuscript invokes Stirling to lower-bound `ρ(1)`.  Lean
   obtains the same `ρ(1) ≳ √d` estimate from normalization, the exact first two
   gamma moments, and Chebyshev; the subsequent logarithmic density comparison
   is the manuscript's argument.
5. Lemma 5.3 uses root-free full periods rather than arranging surviving
   half-periods into maximal runs.  Each root-free period contains a half-period
   on which the sine and polynomial have opposite signs, so this is the same
   sign-change/root-counting argument with slightly simpler bookkeeping.

In Lemma 5.3, the local-density and oscillation estimates give the squared-norm
bound `c₁/8`. Both the manuscript and Lean retain this factor and take
`c = √(c₁/8)`, proving the stated existential lemma.

In particular, the proofs of Lemmas 5.1--5.3 retain the manuscript's chain:
radial low-chaos elements are identified with polynomials in `‖x‖²/d`, the
Gaussian radial law is changed to the normalized chi-square density, the
density is bounded on its central window, and root counting supplies the
sign-change lower bound.

The upper-bound formalization follows the paper's interpolation-and-Gaussian-
tail strategy.  `CenteredReLU.lean` centers the squaring interpolants to obtain
the stated parameter scale.  Its constant hinge-interpolant term is represented
by one constant second-layer unit, so `Net3` itself has exactly the paper's
displayed architecture, with no separate affine output bias.

## Organization and dead-code audit

The foundation is split by responsibility: `Euclidean`, `GaussianSpace`,
`GaussianHermite`, `Symmetry`, `Spectral`, and `Target`. Modules import these
directly; the empty `Basic` compatibility module has been removed.
The finite ReLU definitions import `Euclidean`;
the chi-square-density and Gaussian-tail modules import `GaussianSpace`.
Neither analytic leaf depends on the Hermite, Haar, or radial-polynomial proofs.
The global upper bound imports `Target` directly, independently of the lower
bound. Mathlib imports specify the required subjects instead of importing all
of Mathlib.

The centered network's indexing implementation lives in `CenteredNetwork`,
with named coordinate, sign, cell, endpoint, and knot accessors. Grid selection
and total-width arithmetic are private lemmas; the final approximation theorem
assembles their estimates with the existing error and parameter bounds.

The cleanup audit removed an obsolete Hermite-polynomial filtration branch,
two unused density-positivity lemmas, a duplicate coordinate-bound lemma, and
two unused action/continuous-linear-map plumbing lemmas.
The remaining declarations with no later textual consumer are deliberate API
endpoints: numbered paper results (and their exact-architecture
forms), `Pge_hasSum`, the concrete `Net2` evaluation/corollary, and the
`continuous_relu` rule registered for `fun_prop`.  Typeclass instances are used
implicitly and are not classified as dead declarations.
