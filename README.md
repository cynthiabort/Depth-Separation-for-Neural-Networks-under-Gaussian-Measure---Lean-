# Depth Separation for Neural Networks under Gaussian Measure — Lean

Lean 4 formalization of *Depth Separation for Neural Networks under Gaussian
Measure* by Cynthia Bortolotto, Francisco Ganacim, and Roberto I. Oliveira.

The library is named `GaussianDepthSeparation`. It contains the proofs of all
fifteen numbered results of the paper, including the polynomial criterion in
Corollary 1.2, the matched-parameter comparison in Corollary 1.4, and Lemma 5.1
for arbitrary measurable radial profiles (including profiles defined only on
`[0, ∞)`). It also contains the supporting analytic results. See
[VERIFICATION.md](VERIFICATION.md) for the paper-to-Lean map, the statement
review status for this source version, and the correspondence of the proofs.

The paper-facing arguments use the manuscript's generating functions,
orthogonal radial decomposition, generalized Hölder inequality,
Funk–Hecke/beta-integral calculation, Stirling estimate, half-period
sign-block count, and exact quadratic interpolation error. The verification
map separately describes the supporting
proofs of background facts that the paper cites or leaves implicit.
The lower-bound dimension threshold `chiSquareThreshold` is chosen from
Stirling's asymptotic, as in the paper; the existential main statements
retain the manuscript's quantifier order.

## Build

Install [Lean via elan](https://github.com/leanprover/elan), then run:

```sh
git clone https://github.com/cynthiabort/Depth-Separation-for-Neural-Networks-under-Gaussian-Measure---Lean-.git
cd Depth-Separation-for-Neural-Networks-under-Gaussian-Measure---Lean-
lake exe cache get
lake build
```

The Lean version is pinned in `lean-toolchain`, and Mathlib and its dependencies
are pinned in `lake-manifest.json`. The first build requires internet access to
download the toolchain, dependencies, and compiled Mathlib cache.

Both `lake build` and `lake build GaussianDepthSeparation` run an axiom audit over
every declaration in the imported proof modules, including private helpers.
The only allowed axioms are `propext`, `Classical.choice`, and `Quot.sound`.
Admitted proofs, project-defined axioms, and native-evaluation axioms cause the
audit to fail.

The default build also checks the standalone negative regression tests in
`GaussianDepthSeparationAuditTests.lean`. Their deliberately forbidden axioms
and admitted-proof fixtures are never imported by the mathematical library.

To print the axiom dependencies of the paper-facing declarations:

```sh
lake env lean GaussianDepthSeparationAudit.lean
```

## Main results

All declarations below are in the `GaussianDepthSeparation` namespace.

| Paper result | Lean declaration | Source |
| --- | --- | --- |
| Theorem 1.1 | `ridge_lower_bound` | [LowerBound.lean](GaussianDepthSeparation/LowerBound.lean) |
| Corollary 1.2 | `polynomial_criterion` | [PolynomialCriterion.lean](GaussianDepthSeparation/PolynomialCriterion.lean) |
| Theorem 1.3 | `depth_separation` | [DepthSeparationTheorem.lean](GaussianDepthSeparation/DepthSeparationTheorem.lean) |
| Theorem 1.3(i) | `depth_separation_lower` | [DepthSeparation.lean](GaussianDepthSeparation/DepthSeparation.lean) |
| Theorem 1.3(ii) | `depth_separation_upper_L2` | [GlobalUpper.lean](GaussianDepthSeparation/GlobalUpper.lean) |
| Corollary 1.4 | `depth_separation_comparison` | [DepthComparison.lean](GaussianDepthSeparation/DepthComparison.lean) |
| Lemma 5.1 | `radial_polynomial_distance`, `radial_polynomial_distance_nonneg` | [RadialDistance.lean](GaussianDepthSeparation/RadialDistance.lean) |

## Organization

- `GaussianDepthSeparation.lean` imports the complete mathematical library and
  runs the audit.
- `GaussianDepthSeparation/` contains the foundations, Hermite analysis,
  radialization, lower bound, oscillation argument, and ReLU construction.
- `GaussianDepthSeparationAudit.lean` prints the detailed axiom report.
- `GaussianDepthSeparationAuditTests.lean` tests that the audit rejects forbidden
  dependencies.

The repository contains the standalone formalization, without the dependency
visualization, generated web assets, or historical working notes. Source
comments referring to `main.tex` quote statements of the companion
manuscript, with its numbering; the manuscript itself is not bundled here.
