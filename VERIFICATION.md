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

The proof compatibility review on 2026-10-16 compared the mathematical source
at commit `1c71f14fd96637069f1271f41a2bc08d15c71161` with the compiled
`main.pdf` and its `main.tex` source. The reviewed PDF has SHA-256
`fa0ce413e829e6945cbdd67f38e668a4d14e7e678c5183dc13e58d84c183ada3`;
the TeX source has SHA-256
`e1aff3c8a5f15301caa92e4fd8fabe207de12ff53a94694f20e9a9ef3cea63cf`.
This was a source-level review with automated assistance, not a new human
review or a formal proof of equivalence between prose and Lean.

No mathematical incompatibility was found. The principal lower- and
upper-bound arguments agree, and the intermediate estimates have the
hypotheses and strength needed by the manuscript. Several supporting
arguments use alternative proofs, and Lean supplies details for claims the
paper cites or leaves implicit. The correspondence is as follows; source
paths refer to the modules in the statement map above.

| Paper result | Comparison of the actual arguments |
| --- | --- |
| Theorem 1.1 | Both apply the tail estimate, bound the sum of profile norms by `rM`, and rearrange. Lean explicitly separates `A = 0` and proves positivity of the denominator. |
| Corollary 1.2 | Both use the general Lemma 5.1 to obtain `A ≥ a`, then apply Theorem 1.1 with the smaller error threshold. |
| Theorem 1.3(1) | Both take `n₀ = d`, `m = 4d√d`, apply Lemma 5.3, use `K_d ≤ 2^(-d/2)`, and invoke Theorem 1.1. |
| Theorem 1.3(2) | The same clipped-ramp network, interpolation grids, parameter estimates, Gaussian tail bound, and error split are used. The quantitative correspondence is detailed below. |
| Corollary 1.4 | The manuscript states the corollary without a separate proof. Lean supplies the implied combination: `‖g_i‖₂ ≤ 2B²`, the depth-2 lower bound, and the upper theorem with a common `B = A(d + log(1/ε))`. All constants are chosen before `d` and `ε`. |
| Lemma 2.1 | The paper compares coefficients in the Hermite generating function. `hermite_ridge_identity` instead uses the three-term recurrence and finite multi-index reindexing. This is an alternative proof of the same identity. |
| Lemma 2.2 | Both prove that ridge Hermites span a chaos, use homogeneity to extract coefficients, show rotations preserve the span, and use orthogonality to commute with projection. |
| Proposition 3.1 | The paper uses preservation of the radial subspace and its orthogonal complement. `radAvg_comm_Pn` instead integrates the commutation identity from Lemma 2.2 over Haar measure. The identification of Haar averaging with radial orthogonal projection is proved separately. |
| Proposition 3.2 | Both average the finite ridge-Hermite expansion and extend by continuity in `L²`. Lean expresses the limit step by applying a continuous linear map to `hermite_hasSum`. |
| Lemma 3.3 | The current manuscript cites the spherical-moment formula without an in-text proof. Lean supplies coordinate-reflection symmetry for odd moments and Gaussian moment calculations plus a Haar/Fubini radius-direction factorization for even moments. This supplements the cited result. |
| Proposition 3.4 | For maximality, the paper uses generalized Hölder; Lean integrates a weighted AM-GM inequality and uses coordinate symmetry. For the product formula, the paper uses Funk-Hecke and beta/gamma integrals; `Kmom_eq` instead divides the Gaussian coordinate moment by the radial moment, both computed explicitly. Both parts have alternative proofs. |
| Proposition 4.1 | Both use radial averaging, vanishing odd moments, the exact radialized-ridge norm identity, and Cauchy-Schwarz. Lean packages the norm calculation as `norm_rho_sq`. |
| Corollary 4.2 | Both project the error to the tail, expand the square, bound correlations using Proposition 4.1 and monotonicity of `K_n`, and apply Cauchy-Schwarz. Lean first proves finite Bessel and finite-sum estimates, then passes to the limit through the ridge Hermite series. The full tail-series interpretation for arbitrary `F` is also proved in `MultivariateTotality`. |
| Lemma 5.1 | Both use the minimizing low-chaos projection, characterize radial low-chaos elements as polynomials in `‖x‖²/d`, and change to the normalized chi-square law. Lean makes the characterization explicit using an even axis polynomial; its converse uses injectivity and equality of finite dimensions. `RadialMeasure` proves the radial change of measure using polar integration and normalization. |
| Lemma 5.2 | The paper uses Stirling for `ρ_d(1) ≳ √d`. Lean obtains that estimate from normalization, the first two gamma moments, and Chebyshev. Both then compare the logarithmic density ratio near `1`; Lean uses `1 - 1/t ≤ log t ≤ t - 1`, with `d ≥ 16`, to obtain the same factor `exp(-1)`. |
| Lemma 5.3 | Both reduce to polynomial approximation, restrict to the central density window, and count roots to find opposite-sign sine half-periods. Lean selects root-free full periods in the variable `s = mt`, while the paper groups surviving half-periods into maximal runs after `u = πm(t - 1)`. The resulting local lower bound and the factor `c₁/8` agree. |

For Theorem 1.3(2), both proofs use the grids
`K = ⌈4dR²/η'⌉`, `K' = ⌈2κ(R²+2)/η''⌉` with `η' = η/(8π√d)`, `η'' = η/2`; the
interpolation errors `4R²/K` and `2κ(R²+2)/K'`; the global bound
`|𝒩_{R,η}| ≤ 1`; the parameter bound `2(R²+1) + 4π√d`; the radius
`R² = 2d log 2 + 8 log(4/ε)`; the tail `P(‖X‖ > R) ≤ ε²/16`; and
`‖F - 𝒩‖² ≤ η² + 4P(‖X‖ > R) ≤ ε²/2 ≤ ε²` with `η = ε/2`.
The hidden widths are `4dK` and `2K'+1`; the formal intermediate bound on
their sum implies the paper's bound on their maximum. Lean's squaring
coefficients are written as secant slopes, which equal `t_j + t_{j+1}`.

In Lemma 5.3 the two rescalings are related by `u = π(s - m)`, so Lean's
window `[m - m/√d, m + m/√d]` is exactly the paper's rescaled central
window. Each root-free full period contributes at least `1/2` in the `s`
coordinate, and the counting argument supplies at least `m/(4√d)` usable
periods. The zero polynomial is handled separately. After changing variables
back, both proofs obtain an unweighted local error at least `1/(8√d)` and
a weighted squared error at least `c₁/8`. Both take `c = √(c₁/8)`.
Lean's explicit witnesses are `c₁ = exp(-2)/8` and `d₀ = 16`; the
manuscript only requires positive universal constants.

In particular, the proofs of Lemmas 5.1--5.3 retain the manuscript's chain:
radial low-chaos elements are identified with polynomials in `‖x‖²/d`, the
Gaussian radial law is changed to the normalized chi-square density, the
density is bounded on its central window, and root counting supplies the
sign-change lower bound.

The upper-bound formalization realizes the constant term of `𝒩_sin` by one
constant second-layer unit, exactly as described in the manuscript, so `Net3`
itself has the paper's displayed architecture, with no separate affine output
bias.

The review required no changes to mathematical declarations or proof terms.
It expands the previous proof-fidelity notes, in particular recording the
alternative product-formula proof and the different proof of Proposition 3.1.
The local build and axiom audit covered 927 declarations and admitted only
`propext`, `Classical.choice`, and `Quot.sound`; the standalone audit
regression tests also passed. These checks used existing local dependencies,
with a `batteries` checkout warning, rather than a fresh dependency rebuild.

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
