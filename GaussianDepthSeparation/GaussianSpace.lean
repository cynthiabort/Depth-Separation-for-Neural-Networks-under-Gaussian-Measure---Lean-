/-
Gaussian measures, L² carriers, and density/product-measure bridges.
-/
import GaussianDepthSeparation.Euclidean
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Tactic.FunProp

namespace GaussianDepthSeparation

open MeasureTheory ProbabilityTheory Real
open scoped RealInnerProductSpace ENNReal

noncomputable section

/-- `γ₁` — the one-dimensional standard Gaussian measure `γ`. -/
def γ₁ : Measure ℝ := gaussianReal 0 1

instance : IsProbabilityMeasure γ₁ := by unfold γ₁; infer_instance

/-- `γ d` — the standard Gaussian measure `γ^d` on `ℝ^d`, grounded as
`ProbabilityTheory.stdGaussian`. -/
def γ (d : ℕ) : Measure (Vec d) := stdGaussian (Vec d)

instance (d : ℕ) : IsProbabilityMeasure (γ d) := by unfold γ; infer_instance

/-- `L²(γ^d)`. -/
abbrev L2 (d : ℕ) := Lp ℝ 2 (γ d)

/-- `L²(γ)` (one dimension). -/
abbrev L2R := Lp ℝ 2 γ₁

/-- The squared `L²(γᵈ)` norm as a Gaussian integral. -/
lemma norm_sq_eq_integral {d : ℕ} (h : L2 d) :
    ‖h‖ ^ 2 = ∫ x, (h x) ^ 2 ∂(γ d) := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  simp [pow_two]

/-- Normal form of the standard Gaussian density. -/
lemma gaussianPDFReal_zero_one (t : ℝ) :
    gaussianPDFReal 0 1 t = (Real.sqrt (2 * π))⁻¹ * Real.exp (-t ^ 2 / 2) := by
  simp [gaussianPDFReal]

/-- Bridge: `γ`-integrals as Lebesgue integrals against the density. -/
lemma integral_gaussian_eq (f : ℝ → ℝ) :
    ∫ t, f t ∂γ₁ = ∫ t, f t * gaussianPDFReal 0 1 t := by
  rw [γ₁, integral_gaussianReal_eq_integral_smul one_ne_zero]
  simp only [smul_eq_mul]
  exact integral_congr_ae (ae_of_all _ fun t => mul_comm _ _)

/-- Transfer of `γ^d`-integrals to the coordinate product measure. -/
lemma integral_gaussD_eq_pi {d : ℕ} (f : Vec d → ℝ) (hf : AEStronglyMeasurable f (γ d)) :
    ∫ x, f x ∂(γ d) = ∫ y, f (WithLp.toLp 2 y)
      ∂(Measure.pi fun _ : Fin d => gaussianReal 0 1) := by
  rw [γ, ← ProbabilityTheory.map_pi_eq_stdGaussian] at hf ⊢
  exact integral_map (Measurable.aemeasurable (by fun_prop)) hf

/-- Transfer of `γ^d`-integrability to the coordinate product measure. -/
lemma integrable_gaussD_iff_pi {d : ℕ} (f : Vec d → ℝ) (hf : AEStronglyMeasurable f (γ d)) :
    Integrable f (γ d) ↔ Integrable (fun y => f (WithLp.toLp 2 y))
      (Measure.pi fun _ : Fin d => gaussianReal 0 1) := by
  rw [γ, ← ProbabilityTheory.map_pi_eq_stdGaussian] at hf ⊢
  exact integrable_map_measure hf (Measurable.aemeasurable (by fun_prop))

end

end GaussianDepthSeparation
