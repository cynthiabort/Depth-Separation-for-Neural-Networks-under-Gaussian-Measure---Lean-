/-
GaussianDepthSeparation — an explicit Gaussian norm tail used to pass from approximation on a
ball to approximation in `L²(γ^d)`.
-/
import GaussianDepthSeparation.GaussianSpace
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Ring

namespace GaussianDepthSeparation

open MeasureTheory ProbabilityTheory Real
open scoped RealInnerProductSpace

noncomputable section

/-- The quadratic exponential needed for the Gaussian Chernoff bound is
integrable in one dimension. -/
lemma integrable_exp_quarter_sq_gaussian :
    Integrable (fun t : ℝ => Real.exp (t ^ 2 / 4)) γ₁ := by
  rw [γ₁, gaussianReal_of_var_ne_zero _ one_ne_zero,
    integrable_withDensity_iff (measurable_gaussianPDF 0 1)
      (ae_of_all _ fun _ => gaussianPDF_lt_top)]
  have hrw :
      (fun t : ℝ => Real.exp (t ^ 2 / 4) * (gaussianPDF 0 1 t).toReal) =
        fun t => (Real.sqrt (2 * π))⁻¹ * Real.exp (-(1 / 4 : ℝ) * t ^ 2) := by
    funext t
    rw [toReal_gaussianPDF, gaussianPDFReal_zero_one]
    calc
      Real.exp (t ^ 2 / 4) * ((Real.sqrt (2 * π))⁻¹ * Real.exp (-t ^ 2 / 2)) =
          (Real.sqrt (2 * π))⁻¹ *
            (Real.exp (t ^ 2 / 4) * Real.exp (-t ^ 2 / 2)) := by ring
      _ = (Real.sqrt (2 * π))⁻¹ * Real.exp (-(1 / 4 : ℝ) * t ^ 2) := by
        rw [← Real.exp_add]
        congr 1
        ring_nf
  rw [hrw]
  exact (integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1 / 4)).const_mul _

/-- `E exp(X²/4) = √2` for a one-dimensional standard Gaussian. -/
lemma integral_exp_quarter_sq_gaussian :
    ∫ t : ℝ, Real.exp (t ^ 2 / 4) ∂γ₁ = Real.sqrt 2 := by
  rw [integral_gaussian_eq]
  have hrw :
      (fun t : ℝ => Real.exp (t ^ 2 / 4) * gaussianPDFReal 0 1 t) =
        fun t => (Real.sqrt (2 * π))⁻¹ * Real.exp (-(1 / 4 : ℝ) * t ^ 2) := by
    funext t
    rw [gaussianPDFReal_zero_one]
    calc
      Real.exp (t ^ 2 / 4) * ((Real.sqrt (2 * π))⁻¹ * Real.exp (-t ^ 2 / 2)) =
          (Real.sqrt (2 * π))⁻¹ *
            (Real.exp (t ^ 2 / 4) * Real.exp (-t ^ 2 / 2)) := by ring
      _ = (Real.sqrt (2 * π))⁻¹ * Real.exp (-(1 / 4 : ℝ) * t ^ 2) := by
        rw [← Real.exp_add]
        congr 1
        ring_nf
  rw [hrw, integral_const_mul, integral_gaussian]
  rw [show π / (1 / 4 : ℝ) = 4 * π by ring,
    Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4),
    Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
  have hπ : Real.sqrt π ≠ 0 := ne_of_gt (Real.sqrt_pos.2 Real.pi_pos)
  norm_num
  field_simp
  exact (Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)).symm

/-- The multivariate quadratic exponential is integrable under `γ^d`. -/
lemma integrable_exp_quarter_norm_sq_gaussD (d : ℕ) :
    Integrable (fun x : Vec d => Real.exp (‖x‖ ^ 2 / 4)) (γ d) := by
  have hcont : Continuous (fun x : Vec d => Real.exp (‖x‖ ^ 2 / 4)) := by fun_prop
  rw [integrable_gaussD_iff_pi _ hcont.aestronglyMeasurable]
  have hrw :
      (fun y : Fin d → ℝ => Real.exp (‖WithLp.toLp 2 y‖ ^ 2 / 4)) =
        fun y => ∏ i, Real.exp ((y i) ^ 2 / 4) := by
    funext y
    rw [norm_sq_eq_sum, Finset.sum_div, ← Real.exp_sum]
  rw [hrw]
  exact Integrable.fintype_prod fun _ => integrable_exp_quarter_sq_gaussian

/-- `E exp(‖X‖²/4) = (√2)^d` for the standard Gaussian on `ℝ^d`. -/
lemma integral_exp_quarter_norm_sq_gaussD (d : ℕ) :
    ∫ x : Vec d, Real.exp (‖x‖ ^ 2 / 4) ∂(γ d) = (Real.sqrt 2) ^ d := by
  have hcont : Continuous (fun x : Vec d => Real.exp (‖x‖ ^ 2 / 4)) := by fun_prop
  rw [integral_gaussD_eq_pi _ hcont.aestronglyMeasurable]
  have hrw :
      (fun y : Fin d → ℝ => Real.exp (‖WithLp.toLp 2 y‖ ^ 2 / 4)) =
        fun y => ∏ i, Real.exp ((y i) ^ 2 / 4) := by
    funext y
    rw [norm_sq_eq_sum, Finset.sum_div, ← Real.exp_sum]
  rw [hrw, integral_fintype_prod_eq_prod
    (f := fun _i : Fin d => fun t : ℝ => Real.exp (t ^ 2 / 4))]
  rw [Finset.prod_const, show gaussianReal 0 1 = γ₁ from rfl]
  rw [integral_exp_quarter_sq_gaussian, Finset.card_univ, Fintype.card_fin]

/-- Chernoff bound for the norm of a standard Gaussian vector.  The slightly
loose factor `2^d` keeps the downstream radius algebra elementary. -/
theorem gaussian_norm_tail (d : ℕ) {R : ℝ} (hR : 0 ≤ R) :
    (γ d).real {x : Vec d | R < ‖x‖} ≤
      (2 : ℝ) ^ d * Real.exp (-(R ^ 2) / 4) := by
  let f : Vec d → ℝ := fun x => Real.exp (‖x‖ ^ 2 / 4)
  let a : ℝ := Real.exp (R ^ 2 / 4)
  have ha : 0 < a := Real.exp_pos _
  have hmark := mul_meas_ge_le_integral_of_nonneg
    (μ := γ d) (f := f) (ae_of_all _ fun x => (Real.exp_pos _).le)
    (integrable_exp_quarter_norm_sq_gaussD d) a
  have hsub : {x : Vec d | R < ‖x‖} ⊆ {x | a ≤ f x} := by
    intro x hx
    dsimp [a, f]
    apply Real.exp_le_exp.mpr
    have hsquare : R ^ 2 ≤ ‖x‖ ^ 2 := pow_le_pow_left₀ hR (le_of_lt hx) 2
    linarith
  have hmeasure : (γ d).real {x : Vec d | R < ‖x‖} ≤
      (γ d).real {x | a ≤ f x} := measureReal_mono hsub
  have hint : ∫ x, f x ∂(γ d) = (Real.sqrt 2) ^ d :=
    integral_exp_quarter_norm_sq_gaussD d
  have hsqrt_sq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hsqrt_nonneg : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have hsqrt : Real.sqrt 2 ≤ 2 := by nlinarith
  have hpow : (Real.sqrt 2) ^ d ≤ (2 : ℝ) ^ d := pow_le_pow_left₀ (Real.sqrt_nonneg _) hsqrt d
  have hmul : a * (γ d).real {x : Vec d | R < ‖x‖} ≤ (2 : ℝ) ^ d := by
    calc a * (γ d).real {x : Vec d | R < ‖x‖}
        ≤ a * (γ d).real {x | a ≤ f x} := mul_le_mul_of_nonneg_left hmeasure ha.le
      _ ≤ ∫ x, f x ∂(γ d) := hmark
      _ = (Real.sqrt 2) ^ d := hint
      _ ≤ (2 : ℝ) ^ d := hpow
  have hdiv : (γ d).real {x : Vec d | R < ‖x‖} ≤ (2 : ℝ) ^ d / a :=
    (le_div_iff₀ ha).2 (by simpa [mul_comm] using hmul)
  calc (γ d).real {x : Vec d | R < ‖x‖}
      ≤ (2 : ℝ) ^ d / a := hdiv
    _ = (2 : ℝ) ^ d * Real.exp (-(R ^ 2) / 4) := by
      dsimp [a]
      rw [div_eq_mul_inv, ← Real.exp_neg]
      congr 2
      ring

end

end GaussianDepthSeparation
