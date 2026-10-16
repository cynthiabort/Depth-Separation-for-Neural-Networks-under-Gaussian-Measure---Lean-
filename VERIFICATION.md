# Verification map

## Status

`lake build GaussianDepthSeparation` checks the development and runs a mandatory axiom gate over
all declarations in its imported proof modules, including private helpers.
Only `propext`, `Classical.choice`, and `Quot.sound` are allowed; `sorryAx`,
project-defined axioms, and native-evaluation axioms fail the build.
The default `lake build` also runs the standalone `GaussianDepthSeparationAuditTests` regression
tests, whose deliberately untrusted fixtures are outside the mathematical
library. `GaussianDepthSeparationAudit.lean` retains the optional detailed axiom listing.
All fifteen numbered results of `main.tex` (Theorems 1.1 and 1.3,
Corollaries 1.2, 1.4 and 4.2, Lemmas 2.1, 2.2, 3.3, 5.1, 5.2, 5.3, and
Propositions 3.1, 3.2, 3.4, 4.1) have direct Lean counterparts whose statements
match the manuscript. Where the paper says "there exist universal constants",
Lean either quantifies them existentially in the same order (Theorem 1.3:
`depth_separation`; Corollary 1.4: `depth_separation_comparison`) or provides
explicit witnesses (Lemma 5.2: `c₁ = exp(-2)/8`, `d₀ = 16`; Lemma 5.3 and
Theorem 1.3(1): `c = cEnergy`, `d₀ = 16`).

Review status: the manuscript reports human review of an earlier version.
That report does not cover the generalized Lemma 5.1
(`radial_polynomial_distance`, with `radial_polynomial_distance_nonneg` for
profiles on `[0, ∞)`), Corollary 1.2 (`polynomial_criterion`), the combined
Theorem 1.3 (`depth_separation`), the revised upper-bound statement
(`depth_separation_upper_L2`), or the revised Corollary 1.4
(`depth_separation_comparison`). These statements have been checked against
the manuscript with automated assistance and checked by Lean; this is not a
claim of a new human review.

Source references in the manuscript identify modules and declarations in the
companion source version. The former reference to commit `aff4b42` does not
identify the revised statements and must not be used as their source. Use the
Git revision containing this verification map to identify the revised source.

This audit covers the standalone `GaussianDepthSeparation` library. Module paths
in the table below are relative to `GaussianDepthSeparation/`.

## Paper-to-Lean map

| Paper result | Lean declaration(s) | Module |
| --- | --- | --- |
| Theorem 1.1 (ridge lower bound) | `ridge_lower_bound` | `LowerBound.lean` |
| Corollary 1.2 (polynomial criterion) | `polynomial_criterion` | `PolynomialCriterion.lean` |
| Theorem 1.3 (depth separation, both parts, existential constants) | `depth_separation` | `DepthSeparationTheorem.lean` |
| Theorem 1.3(1) with explicit constants | `depth_separation_lower` | `DepthSeparation.lean` |
| Theorem 1.3(2) (global depth-3 upper bound) | `depth_separation_upper_L2`, `depth_separation_upper_L2_explicit` | `GlobalUpper.lean` |
| Corollary 1.4 (matched depth comparison) | `depth_separation_comparison` | `DepthComparison.lean` |
| Lemma 2.1 (Hermite ridge identity) | `hermite_ridge_identity`, `ridgeHermite_eq_sum` | `Hermite.lean`, `Chaos.lean` |
| Lemma 2.2 (rotations commute with chaos projections) | `Pn_comp_rotation` | `Chaos.lean` |
| Proposition 3.1 (radialization commutes with chaos projections) | `radAvg_eq_starProjection`, `radAvg_comm_Pn` | `RadialAverage.lean` |
| Proposition 3.2 (radialized ridge expansion) | `radAvg_ridge_expansion` | `Radialization.lean` |
| Lemma 3.3 (spherical moments) | `sphereMoment_eq_zero_of_odd`, `sphereMoment_of_even` | `MomentsCore.lean`, `Moments.lean` |
| Proposition 3.4 (maximal spherical moment and product formula, `d ≥ 1`, even `n ≥ 0`) | `abs_sphereMoment_le_Kmom`, `Kmom_eq` | `Moments.lean` |
| Remark after Proposition 3.4 | `Kmom_le_pow`, `Kmom_le_two_pow` | `Moments.lean` |
| Proposition 4.1 (chaos correlation) | `correlation_eq_zero_of_odd`, `correlation_bound_of_even` | `Correlation.lean` |
| Corollary 4.2 (tail estimate) | `tail_estimate` | `LowerBound.lean` |
| Lemma 5.1 (general radial polynomial distance) | `radial_polynomial_distance`, `radial_polynomial_distance_nonneg` | `RadialPolynomial.lean`, `RadialRepresentation.lean`, `RadialMeasure.lean`, `RadialDistance.lean` |
| Lemma 5.2 (local chi-square density) | `chi_square_local_density` (explicit constants `c₁ = exp (-2) / 8`, `d₀ = 16`) | `ChiSquare.lean` |
| Lemma 5.3 (high-chaos energy) | `radialError_weighted_lower`, `energy_lower_bound` (explicit constants `c = cEnergy`, `d₀ = 16`) | `Oscillation.lean`, `EnergyBound.lean` |

Supporting claims used as notation or prose in the paper are also checked:
one- and multivariate Hermite totality (`hermite_hasSum`, `chaos_hasSum_Pn`,
`Pge_hasSum`), the ReLU profile estimate (`norm_reluProfile_le`), the concrete
depth-2 network corollary (`depth_separation_lower_net2`), and the Gaussian tail
bound `P(‖X‖ > R) ≤ 2^{d/2} e^{-R²/4}` (`gaussian_norm_tail`), the
interpolant bound `|𝒩_sin| ≤ 1` (`abs_hinge_le`), and the identification of
the normalized chi-square law with the law of `‖X‖²/d`
(`chiSqMeasure_eq_map`).

Lemma 5.1 is formalized for every `F ∈ L²(γ^d)` with
`F(x) = φ(‖x‖²/d)` almost everywhere, every measurable `φ`, every `d ≥ 1`,
and every even `n₀ ≥ 2`. The conclusion is the exact equality between
`‖P_{≥n₀}F‖²` and the infimum of the weighted polynomial errors.
`radial_polynomial_distance` uses a profile on `ℝ`;
`radial_polynomial_distance_nonneg` accepts a profile on `ℝ≥0`, exactly the
paper's `[0, ∞)` domain, by a measurable extension. No continuity, boundedness,
or sine-family restriction is imposed. The sine case is now the derived
corollary `radialSine_polynomial_distance`, used in Lemma 5.3.

In Corollary 1.2, the Lean hypotheses are: `d ≥ 2`; `n₀ ≥ 2` even;
`F ∈ L²(γ^d)` with `F(x) = φ(‖x‖²/d)` for `γ^d`-a.e. `x`, where `φ` is
measurable (needed for the integral to make sense); and
`a² ≤ ⨅_{deg q < n₀/2} ∫_0^∞ (φ - q)² ρ_d` with `a > 0`. The conclusion is
`r ≥ a/(4M√K_{n₀})`. The proof is exactly the paper's reduction: the
hypothesis gives `‖P_{≥n₀}F‖ ≥ a` by applying the general Lemma 5.1 directly,
and Theorem 1.1 applies.

In Theorem 1.3(2) and Corollary 1.4, the width of a depth-3 network is
`max(w₁, w₂)`, as defined in the paper, and parameters are bounded by
`C(d + log(1/ε))` with no extra additive constant. In Corollary 1.4,
`cLower` and `cUpper` witness the paper's Ω and O bounds, and `ε₀`, `A`, `d₁`
are existential, exactly as in the statement; the proof uses `d₁ = 16`. The
abbreviations are `L = d + log (1/ε)` and `B = A * L`, with the same `B` in
the `Net2` and `Net3` parameter hypotheses.

## Proof fidelity

All formal proofs follow the paper's mathematical decomposition, with the
analytic and measure-theoretic details made explicit.  The proof of Theorem 1.3(2) follows the manuscript step by step: the grids
`K = ⌈4dR²/η'⌉`, `K' = ⌈2κ(R²+2)/η''⌉` with `η' = η/(8π√d)`, `η'' = η/2`; the
interpolation errors `4R²/K` and `2κ(R²+2)/K'`; the global bound
`|𝒩_{R,η}| ≤ 1`; the parameter bound `2(R²+1) + 4π√d`; the radius
`R² = 2d log 2 + 8 log(4/ε)`; the tail `P(‖X‖ > R) ≤ ε²/16`; and
`‖F - 𝒩‖² ≤ η² + 4P(‖X‖ > R) ≤ ε²/2 ≤ ε²` with `η = ε/2`.
Five local arguments elsewhere use equivalent formalization-friendly
variants:

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

The upper-bound formalization realizes the constant term of `𝒩_sin` by one
constant second-layer unit, exactly as described in the manuscript, so `Net3`
itself has the paper's displayed architecture, with no separate affine output
bias.

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
