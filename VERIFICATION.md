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
specific witnesses (Lemma 5.2: `c₁ = exp(-2)/8`,
`d₀ = chiSquareThreshold`; Lemma 5.3 and Theorem 1.3(i): `c = cEnergy`,
`d₀ = chiSquareThreshold`). The dimension threshold is chosen from the
Stirling asymptotic, as in the paper, and is at least 16. It is not asserted
to equal 16.

Review status: the manuscript reports human review of an earlier version.
That report does not cover the generalized Lemma 5.1
(`radial_polynomial_distance`, with `radial_polynomial_distance_nonneg` for
profiles on `[0, ∞)`), Corollary 1.2 (`polynomial_criterion`), the combined
Theorem 1.3 (`depth_separation`), the revised upper-bound statement
(`depth_separation_upper_L2`), or the revised Corollary 1.4
(`depth_separation_comparison`), or the proof rewrites described below. These
statements and arguments have been checked against
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
| Theorem 1.3(i) with explicit constants | `depth_separation_lower` | `DepthSeparation.lean` |
| Theorem 1.3(ii) (global depth-3 upper bound) | `depth_separation_upper_L2`, `depth_separation_upper_L2_explicit` | `GlobalUpper.lean` |
| Corollary 1.4 (matched depth comparison) | `depth_separation_comparison` | `DepthComparison.lean` |
| Lemma 2.1 (Hermite ridge identity) | `hermite_ridge_identity`, `ridgeHermite_eq_sum` | `Hermite.lean`, `Chaos.lean` |
| Lemma 2.2 (rotations commute with chaos projections) | `Pn_comp_rotation` | `Chaos.lean` |
| Proposition 3.1 (radialization commutes with chaos projections) | `radAvg_eq_starProjection`, `radAvg_comm_Pn` | `RadialAverage.lean` |
| Proposition 3.2 (radialized ridge expansion) | `radAvg_ridge_expansion` | `Radialization.lean` |
| Lemma 3.3 (spherical moments) | `sphereMoment_eq_zero_of_odd`, `sphereMoment_of_even` | `MomentsCore.lean`, `Moments.lean` |
| Proposition 3.4 (maximal spherical moment and product formula, also extended to `n = 0`) | `abs_sphereMoment_le_Kmom`, `Kmom_eq` | `Moments.lean` |
| Remark 3.5 | `Kmom_le_pow`, `Kmom_le_two_pow` | `Moments.lean` |
| Proposition 4.1 (chaos correlation) | `correlation_eq_zero_of_odd`, `correlation_bound_of_even` | `Correlation.lean` |
| Corollary 4.2 (tail estimate) | `tail_estimate` | `LowerBound.lean` |
| Lemma 5.1 (general radial polynomial distance) | `radial_polynomial_distance`, `radial_polynomial_distance_nonneg` | `RadialPolynomial.lean`, `RadialRepresentation.lean`, `RadialMeasure.lean`, `RadialDistance.lean` |
| Lemma 5.2 (local chi-square density) | `chi_square_local_density` (`c₁ = exp (-2) / 8`, `d₀ = chiSquareThreshold`) | `ChiSquare.lean` |
| Lemma 5.3 (high-chaos energy) | `radialError_weighted_lower`, `energy_lower_bound` (`c = cEnergy`, `d₀ = chiSquareThreshold`) | `Oscillation.lean`, `EnergyBound.lean` |

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

In Theorem 1.3(ii) and Corollary 1.4, the width of a depth-3 network is
`max(w₁, w₂)`, as defined in the paper, and parameters are bounded by
`C(d + log(1/ε))` with no extra additive constant. In Corollary 1.4,
`cLower` and `cUpper` witness the paper's Ω and O bounds, and `ε₀`, `A`, `d₁`
are existential, exactly as in the statement; the proof uses
`d₁ = chiSquareThreshold`. The
abbreviations are `L = d + log (1/ε)` and `B = A * L`, with the same `B` in
the `Net2` and `Net3` parameter hypotheses.

## Proof fidelity

The proof rewrite on 2026-10-16 follows the current `main.tex`, including the
maximal constant-sign blocks in Lemma 5.3 and its accompanying figure, and
the explicit quadratic interpolation error in Theorem 1.3(ii).
The companion `main.pdf` has SHA-256
`36705dad6e07623a8c8e160df47f8abbbf0e7322cb8487ee5a5a500e2bb111e1`;
the TeX source has SHA-256
`49306b4408f94f2d5e7b2b5fa42879f7582fd8b4afcd0427418c2923e582267e`.
The Git revision containing this map identifies the rewritten Lean source.
This is a source-level comparison with automated assistance and kernel-checked
proofs, not a new human review or a formal equivalence relation between prose
and proof terms.

The main proof routes now follow the paper. In particular, the former
recurrence proof of Lemma 2.1, Haar-integration proof of Proposition 3.1,
AM-GM proof and Gaussian-moment calculation in Proposition 3.4,
Chebyshev proof of Lemma 5.2, and full-period selection in Lemma 5.3 have
been replaced at their paper-facing declarations. Supporting theorems that
the paper cites or leaves implicit still require independent proofs; their
construction is recorded explicitly below.

| Paper result | Comparison of the actual arguments |
| --- | --- |
| Theorem 1.1 | Both apply the tail estimate, bound the sum of profile norms by `rM`, and rearrange. Lean explicitly separates `A = 0` and proves positivity of the denominator. |
| Corollary 1.2 | Both use the general Lemma 5.1 to obtain `A ≥ a`, then apply Theorem 1.1 with the smaller error threshold. |
| Theorem 1.3(i) | Both take `n₀ = d`, `m = 4d√d`, apply Lemma 5.3, use `K_d ≤ 2^(-d/2)`, and invoke Theorem 1.1. |
| Theorem 1.3(ii) | The same clipped-ramp network, interpolation grids, parameter estimates, Gaussian tail bound, and error split are used. The quantitative correspondence is detailed below. |
| Corollary 1.4 | The manuscript states the corollary without a separate proof. Lean supplies the implied combination: `‖g_i‖₂ ≤ 2B²`, the depth-2 lower bound, and the upper theorem with a common `B = A(d + log(1/ε))`. All constants are chosen before `d` and `ε`. |
| Lemma 2.1 | `hermite_ridge_identity` factors the exponential generating function using `∑ vᵢ² = 1`, expands the coordinatewise product, and compares coefficients of degree `n`, as in the displayed proof. `HermiteGenerating` supplies the formal-power-series identities. |
| Lemma 2.2 | Both prove that ridge Hermites span a chaos, use homogeneity to extract coefficients, show rotations preserve the span, and use orthogonality to commute with projection. |
| Proposition 3.1 | `isRadial_Pn` uses rotation commutation to preserve the radial subspace. `Pn_mem_radial_orthogonal` uses self-adjointness to preserve its orthogonal complement. `radAvg_comm_Pn` applies the orthogonal decomposition, exactly the paper's argument. Haar averaging is separately identified with radial orthogonal projection. |
| Proposition 3.2 | Both average the finite ridge-Hermite expansion and extend by continuity in `L²`. Lean expresses the limit step by applying a continuous linear map to `hermite_hasSum`. |
| Lemma 3.3 | The current manuscript cites the spherical-moment formula without an in-text proof. Lean supplies coordinate-reflection symmetry for odd moments and Gaussian moment calculations plus a Haar/Fubini radius-direction factorization for even moments. This supplements the cited result. |
| Proposition 3.4 | `abs_sphereMoment_le_Kmom` applies generalized Hölder with weights `αᵢ/n` and coordinate symmetry; zero weights contribute factors equal to one. `Kmom_eq` treats `d = 1` separately, then applies degree-zero Funk–Hecke, evenness, the substitution `u = t²`, Euler's beta integral, and the Gamma recurrence. The extension to `n = 0` is also checked. |
| Proposition 4.1 | Both use radial averaging, vanishing odd moments, the exact radialized-ridge norm identity, and Cauchy-Schwarz. Lean packages the norm calculation as `norm_rho_sq`. |
| Corollary 4.2 | Both project the error to the tail, expand the square, bound correlations using Proposition 4.1 and monotonicity of `K_n`, and apply Cauchy-Schwarz. Lean first proves finite Bessel and finite-sum estimates, then passes to the limit through the ridge Hermite series. The full tail-series interpretation for arbitrary `F` is also proved in `MultivariateTotality`. |
| Lemma 5.1 | Both use the minimizing low-chaos projection, characterize radial low-chaos elements as polynomials in `‖x‖²/d`, and change to the normalized chi-square law. Lean makes the characterization explicit using an even axis polynomial; its converse uses injectivity and equality of finite dimensions. `RadialMeasure` proves the radial change of measure using polar integration and normalization. |
| Lemma 5.2 | `chiSqDensity_one_stirling` proves `ρ_d(1)/√d → 1/(2√π)`. The proof chooses a sufficiently large threshold, uses the paper's exact bounds `(t−1)−(t−1)² ≤ log t ≤ t−1`, and derives the density-ratio factor `exp(-1)`. |
| Lemma 5.3 | Both restrict to the central density window, use `u = πm(t−1)`, discard half-period interiors containing roots, and count maximal consecutive blocks of constant polynomial sign. The checked estimates are `N′ ≥ N−deg q`, `G ≤ deg q+1`, and `2M_opp ≥ N′−G`. Roots at shared endpoints are included. Each opposing half-period contributes `π/2`, giving the paper's `c₁/8` bound. |

For Theorem 1.3(ii), both proofs use the grids
`K = ⌈4dR²/η'⌉`, `K' = ⌈2κ(R²+2)/η''⌉` with `η' = η/(8π√d)`, `η'' = η/2`; the
interpolation errors `4R²/K` and `2κ(R²+2)/K'`; the global bound
`|𝒩_{R,η}| ≤ 1`; the parameter bound `2(R²+1) + 4π√d`; the radius
`R² = 2d log 2 + 8 log(4/ε)`; the tail `P(‖X‖ > R) ≤ ε²/16`; and
`‖F - 𝒩‖² ≤ η² + 4P(‖X‖ > R) ≤ ε²/2 ≤ ε²` with `η = ε/2`.
The hidden widths are `4dK` and `2K'+1`; the formal intermediate bound on
their sum implies the paper's bound on their maximum. Lean's squaring
coefficients are written as secant slopes; `gslope_sq_eq` proves that they
are `t_j + t_{j+1}` and supplies their bound directly from the grid endpoints.
`hinge_sq_error_on_cell` proves the displayed identity
`p(t)−t² = (t−t_j)(t_{j+1}−t)`. `hinge_sq_error_sharp` bounds it between zero
and one quarter of the squared mesh size, `R²/(4K²)`, and
`hinge_sq_error_le` derives the coarser `4R²/K` used to choose the grid.
Thus the squaring error no longer uses the general Lipschitz interpolation
bound; that bound remains appropriate for the sine interpolant.

In Lemma 5.3, `SignBlocks` represents each maximal block by its first
retained half-period. Pairing every matching, noninitial interval with its
opposing predecessor proves the paper's summed bound `2M_opp ≥ N′−G`.
The count is implemented in `s = mt`, where half-periods have integer
endpoints. `phaseRadialError_window_lower` transports it through
`u = π(s−m)`, and `radialError_local_lower` checks the paper's substitution
`u = πm(t−1)` with Jacobian `πm`. The zero polynomial is handled separately.
After changing variables back, the unweighted local error is at least
`1/(8√d)` and the weighted squared error is at least `c₁/8`.
Both proofs take `c = √(c₁/8)`.

The background facts are formalized as follows:

- `HermiteGenerating` establishes the one-variable generating function from
  the Hermite recurrence and uniqueness of a formal differential equation.
  The ridge identity itself uses generating functions, rather than induction
  on ridge degree. Formal power series implement coefficient comparison
  without an additional analytic convergence argument.
- `sphere_coordinate_funkHecke` in `SphereFunkHecke` proves the degree-zero slice
  formula for every continuous real function, the background theorem cited
  in Proposition 3.4. Its independent proof identifies polynomial moments
  by Gaussian radius-direction factorization and beta integrals, then uses
  Weierstrass approximation. The private `coordinateMoment_product` retains
  the earlier Gaussian calculation for this supporting theorem. Thus the
  final product-formula proof follows the paper, while the full dependency
  tree still contains a Gaussian-moment proof of the cited slice theorem.
- `SphereBeta` checks the square substitution, reflection across zero,
  integrability at the endpoints, and conversion of Euler's beta integral
  to a real Gamma quotient.
- `GammaStirling` derives Stirling along the integer and half-integer
  arguments `d/2` from Mathlib's factorial Stirling theorem and Gamma
  log-convexity. `ChiSquare` then uses exactly the asymptotic and logarithmic
  estimates displayed in Lemma 5.2.

The supporting constructions above are additional mathematical details, not
arguments written out in the paper. Lemma 3.3, the radial-polynomial converse
in Lemma 5.1, and the limit passage in Corollary 4.2 likewise supply the
details described in the table. The intended correspondence is the paper's
mathematical argument at each numbered result, not literal equality of all
supporting proof steps.

To follow the asymptotic proof, the earlier concrete helper hypothesis
`16 ≤ d` has been replaced by `chiSquareThreshold ≤ d` throughout the lower
bound and matched comparison. The threshold is a fixed natural number
chosen from the Stirling limit and satisfies `16 ≤ chiSquareThreshold`.
The existential statements of Theorem 1.3 and Corollary 1.4 are unchanged.
The constant `c₁ = exp(-2)/8` is a convenient smaller universal constant
deduced from the paper's estimate.

In particular, the proofs of Lemmas 5.1--5.3 retain the manuscript's chain:
radial low-chaos elements are identified with polynomials in `‖x‖²/d`, the
Gaussian radial law is changed to the normalized chi-square density, the
density is bounded on its central window, and root counting supplies the
sign-change lower bound.

The upper-bound formalization realizes the constant term of `𝒩_sin` by one
constant second-layer unit, exactly as described in the manuscript, so `Net3`
itself has the paper's displayed architecture, with no separate affine output
bias.

Validation: `lake build` passed (3,785 jobs), including the mandatory axiom
audit of 1,013 declarations and the standalone regression tests. A direct
`lake env lean GaussianDepthSeparationAuditTests.lean` run also passed.
The audit permits only `propext`, `Classical.choice`, and `Quot.sound`, and
covers the new supporting modules and their private helpers. These checks
used Lean `v4.34.0-rc2`, Mathlib commit
`0cd048027c8b0239cdfe206691bbf2c0a0970078`, and existing local dependencies,
with a `batteries` checkout warning, rather than a fresh dependency download.

## Organization

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

The proof rewrite adds `HermiteGenerating`, `SphereBeta`, `SphereFunkHecke`,
`GammaStirling`, `SineIntervals`, and `SignBlocks`. All are imported transitively
by the main library and included in its axiom audit. Obsolete ridge-recurrence,
Chebyshev-density, and full-period-selection helpers have been removed.
