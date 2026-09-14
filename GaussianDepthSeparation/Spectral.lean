/-
Finite Hermite chaos spaces, orthogonal projections, and spherical moments.
-/
import GaussianDepthSeparation.GaussianHermite
import GaussianDepthSeparation.Symmetry
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

namespace GaussianDepthSeparation

open MeasureTheory ProbabilityTheory Polynomial Real
open scoped RealInnerProductSpace ENNReal Nat

noncomputable section

/-! ## Chaos spaces and projections

LaTeX — `paper.tex` introduction: "Let $P_n$ denote the orthogonal projection onto the
$n$-th Gaussian chaos $\mathcal{H}_n = \operatorname{span}\{H_\alpha : |\alpha| = n\}$."
The spans are finite-dimensional, hence closed; the projections are genuine
Mathlib `Submodule.starProjection`s, so their laws come from Mathlib.
-/

/-- The `n`-th Gaussian chaos `ℋ_n = span{H_α : |α| = n}`. -/
def chaos (d n : ℕ) : Submodule ℝ (L2 d) :=
  Submodule.span ℝ (HL2 '' ↑(idxOf d n))

/-- `span{H_α : |α| < n₀}` — the low-degree space. -/
def chaosLt (d n₀ : ℕ) : Submodule ℝ (L2 d) :=
  Submodule.span ℝ (HL2 '' ↑(idxLt d n₀))

instance (d n : ℕ) : FiniteDimensional ℝ (chaos d n) :=
  FiniteDimensional.span_of_finite ℝ ((idxOf d n).finite_toSet.image _)

instance (d n₀ : ℕ) : FiniteDimensional ℝ (chaosLt d n₀) :=
  FiniteDimensional.span_of_finite ℝ ((idxLt d n₀).finite_toSet.image _)

/-- `P_n`, the orthogonal projection onto the `n`-th chaos. -/
def Pn (d n : ℕ) : L2 d →L[ℝ] L2 d := (chaos d n).starProjection

/-- `P_{<n₀}`, the orthogonal projection onto `span{H_α : |α| < n₀}`. -/
def Plt (d n₀ : ℕ) : L2 d →L[ℝ] L2 d := (chaosLt d n₀).starProjection

/-- LaTeX — `paper.tex` introduction: "For $n_0 \in \mathbb{N}$, write
$P_{\ge n_0}F = \sum_{n\ge n_0}P_n F$."
Formalized as the complementary projection `I − P_{<n₀}` (= the orthogonal
projection onto `(span{H_α : |α| < n₀})ᗮ`); the tail-sum description is recovered
once the Hermite system is proved total. -/
def Pge (d n₀ : ℕ) : L2 d →L[ℝ] L2 d :=
  ContinuousLinearMap.id ℝ (L2 d) - Plt d n₀

/-! ## Sphere moments

LaTeX — `paper.tex` §3 (proof of Lemma 3.3): "Let $G \sim \gamma^d$.  Then
$V = G/\|G\|_2$ is uniform on $S^{d-1}$."  We take this as the *definition* of
the uniform direction: `sphereUnif d` is the law of `X/‖X‖` under `γ^d`
(a measure on `ℝ^d` carried by the unit sphere).
-/

/-- The uniform distribution on `S^{d-1}`: the law of `X/‖X‖`, `X ∼ γ^d`. -/
def sphereUnif (d : ℕ) : Measure (Vec d) := (γ d).map (fun x => ‖x‖⁻¹ • x)

instance (d : ℕ) : IsProbabilityMeasure (sphereUnif d) := by
  unfold sphereUnif
  exact Measure.isProbabilityMeasure_map
    (Measurable.aemeasurable (by fun_prop))

/-- `𝔼[V^α]`, the moments of a uniform spherical vector `V ∼ Unif(S^{d-1})`. -/
def sphereMoment (d : ℕ) (α : MIdx d) : ℝ := ∫ v, mpow v α ∂(sphereUnif d)

/-- LaTeX — `paper.tex` §3 (Proposition 3.4): "$K_n := \mathbb{E}[V_1^n]$" — the maximal
even moment. -/
def Kmom (d n : ℕ) : ℝ := sphereMoment d (fun i => if (i : ℕ) = 0 then n else 0)

end

end GaussianDepthSeparation
