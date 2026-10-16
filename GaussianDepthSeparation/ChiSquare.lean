/-
GaussianDepthSeparation §5 — the normalized chi-square density (Lemma 5.2).

As in the paper, Stirling's asymptotic controls the density at one, and
the quadratic logarithm bound transfers this to the central interval.
-/
import GaussianDepthSeparation.GaussianSpace
import Mathlib.Probability.Distributions.Gamma
import GaussianDepthSeparation.GammaStirling
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace GaussianDepthSeparation

open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal NNReal Nat

noncomputable section

/-- The density `ρ_d` of the normalized chi-square variable `‖X‖² / d`. -/
def chiSqDensity (d : ℕ) : ℝ → ℝ :=
  gammaPDFReal ((d : ℝ) / 2) ((d : ℝ) / 2)

/-- The normalized chi-square law, viewed as a gamma distribution with equal
shape and rate `d / 2`. -/
def chiSqMeasure (d : ℕ) : Measure ℝ :=
  gammaMeasure ((d : ℝ) / 2) ((d : ℝ) / 2)

lemma chiSqDensity_nonneg {d : ℕ} (hd : 0 < d) (t : ℝ) :
    0 ≤ chiSqDensity d t := by
  exact gammaPDFReal_nonneg (by positivity) (by positivity) t

instance chiSqMeasure_isProbabilityMeasure (d : ℕ) [NeZero d] :
    IsProbabilityMeasure (chiSqMeasure d) :=
  have hd : 0 < d := Nat.pos_of_ne_zero (NeZero.ne d)
  isProbabilityMeasure_gammaMeasure (by positivity) (by positivity)

/-- Gamma moments, used for polynomial integrability. -/
lemma integral_pow_gammaMeasure (a r : ℝ) (ha : 0 < a) (hr : 0 < r)
    (k : ℕ) :
    ∫ x : ℝ, x ^ k ∂(gammaMeasure a r) =
      r ^ a / Gamma a * ((1 / r) ^ (a + k) * Gamma (a + k)) := by
  rw [gammaMeasure]
  change (∫ x : ℝ, x ^ k ∂volume.withDensity
    (fun x => ENNReal.ofReal (gammaPDFReal a r x))) = _
  rw [integral_withDensity_eq_integral_toReal_smul
    (measurable_gammaPDFReal a r).ennreal_ofReal (by simp)]
  simp only [smul_eq_mul]
  simp_rw [ENNReal.toReal_ofReal (gammaPDFReal_nonneg ha hr _)]
  let g : ℝ → ℝ := fun x => gammaPDFReal a r x * x ^ k
  change (∫ x, g x) = _
  have hIoi : ∫ x in Ioi (0 : ℝ), g x =
      r ^ a / Gamma a * ((1 / r) ^ (a + k) * Gamma (a + k)) := by
    calc
      ∫ x in Ioi (0 : ℝ), g x = ∫ x in Ioi (0 : ℝ),
          (r ^ a / Gamma a) * (x ^ (a + k - 1) * exp (-(r * x))) := by
        refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
        have hx0 : 0 ≤ x := le_of_lt hx
        have hp : x ^ (a - 1) * x ^ (k : ℝ) = x ^ (a + k - 1) := by
          rw [← Real.rpow_add hx]
          congr 1
          ring
        simp only [g, gammaPDFReal, ite_eq_left hx0]
        rw [← Real.rpow_natCast x k]
        rw [← hp]
        ring
      _ = (r ^ a / Gamma a) * ∫ x in Ioi (0 : ℝ),
          x ^ (a + k - 1) * exp (-(r * x)) := by rw [integral_const_mul]
      _ = _ := by
        rw [Real.integral_rpow_mul_exp_neg_mul_Ioi (by positivity) hr]
  have hgIoi : IntegrableOn g (Ioi (0 : ℝ)) := by
    apply Integrable.of_integral_ne_zero
    rw [hIoi]
    positivity
  have hgIic : IntegrableOn g (Iic (0 : ℝ)) := by
    refine (integrable_zero ℝ ℝ volume).integrableOn.congr_fun_ae ?_
    filter_upwards [ae_restrict_of_ae (volume.ae_ne (0 : ℝ)),
      ae_restrict_mem measurableSet_Iic] with x hx0 hx
    have hxneg : x < 0 := lt_of_le_of_ne hx hx0
    simp [g, gammaPDFReal, not_le.mpr hxneg]
  have hg : Integrable g := by
    rw [← integrableOn_univ, ← Iic_union_Ioi, integrableOn_union]
    exact ⟨hgIic, hgIoi⟩
  rw [← integral_add_compl measurableSet_Ioi hg, compl_Ioi, hIoi]
  have hz : ∫ x in Iic (0 : ℝ), g x = 0 := by
    exact integral_eq_zero_of_ae (by
      filter_upwards [ae_restrict_of_ae (volume.ae_ne (0 : ℝ)),
        ae_restrict_mem measurableSet_Iic] with x hx0 hx
      have hxneg : x < 0 := lt_of_le_of_ne hx hx0
      simp [g, gammaPDFReal, not_le.mpr hxneg])
  rw [hz, add_zero]

lemma integrable_pow_gammaMeasure (a r : ℝ) (ha : 0 < a) (hr : 0 < r)
    (k : ℕ) : Integrable (fun x : ℝ => x ^ k) (gammaMeasure a r) := by
  apply Integrable.of_integral_ne_zero
  rw [integral_pow_gammaMeasure a r ha hr k]
  positivity

lemma integrable_polynomial_chiSqMeasure {d : ℕ} (hd : 0 < d)
    (q : Polynomial ℝ) : Integrable (fun t => q.eval t) (chiSqMeasure d) := by
  rw [chiSqMeasure]
  rw [show (fun t : ℝ => q.eval t) = fun t =>
      ∑ k ∈ Finset.range (q.natDegree + 1), q.coeff k * t ^ k from by
        funext t
        exact q.eval_eq_sum_range t]
  exact integrable_finsetSum _ fun k _ =>
    (integrable_pow_gammaMeasure _ _ (by positivity) (by positivity) k).const_mul _

lemma integrable_radialError_chiSqMeasure {d : ℕ} (hd : 0 < d)
    (m : ℝ) (q : Polynomial ℝ) :
    Integrable (fun t => (sin (π * m * t) - q.eval t) ^ 2) (chiSqMeasure d) := by
  let : NeZero d := ⟨Nat.ne_of_gt hd⟩
  have hq2 : Integrable (fun t => (q.eval t) ^ 2) (chiSqMeasure d) := by
    have h := integrable_polynomial_chiSqMeasure hd (q ^ 2)
    simpa using h
  refine Integrable.mono'
    ((integrable_const (2 : ℝ)).add (hq2.const_mul 2))
    (Continuous.aestronglyMeasurable (by fun_prop))
    (ae_of_all _ fun t => ?_)
  simp only [Pi.add_apply]
  change |(sin (π * m * t) - q.eval t) ^ 2| ≤ 2 + 2 * (q.eval t) ^ 2
  rw [abs_of_nonneg (sq_nonneg _)]
  nlinarith [Real.sin_sq_le_one (π * m * t), sq_nonneg (q.eval t),
    sq_nonneg (sin (π * m * t) + q.eval t)]

/-- Exact logarithmic comparison with the value of the density at one. -/
lemma chiSqDensity_eq_one_mul_exp {d : ℕ} (hd : 0 < d) {t : ℝ} (ht : 0 < t) :
    chiSqDensity d t = chiSqDensity d 1 *
      exp (((d : ℝ) / 2 - 1) * log t - (d : ℝ) / 2 * (t - 1)) := by
  have ha : 0 < (d : ℝ) / 2 := by positivity
  simp only [chiSqDensity, gammaPDFReal, ite_eq_left ht.le, ite_eq_left zero_le_one,
    Real.one_rpow, mul_one]
  rw [Real.rpow_def_of_pos ht]
  simp only [mul_assoc]
  congr 1
  rw [← Real.exp_add, ← Real.exp_add]
  congr 1
  ring

/-- The elementary logarithmic lower bound used in the manuscript. -/
lemma log_lower_quadratic {t : ℝ} (ht : 1 / 2 ≤ t) :
    (t - 1) - (t - 1) ^ 2 ≤ log t := by
  let f : ℝ → ℝ := fun x => log x - (x - 1) + (x - 1) ^ 2
  have hd (x : ℝ) (hx : 0 < x) :
      HasDerivAt f ((2 * x - 1) * (x - 1) / x) x := by
    convert! ((Real.hasDerivAt_log hx.ne').sub ((hasDerivAt_id x).sub_const 1)).add
      (((hasDerivAt_id x).sub_const 1).pow 2) using 1
    dsimp [f]
    field_simp
    ring
  have hf (s : Set ℝ) (hs : ∀ x ∈ s, 0 < x) : ContinuousOn f s := by
    intro x hx
    exact (hd x (hs x hx)).continuousAt.continuousWithinAt
  have hmin : f 1 ≤ f t := by
    rcases le_total t 1 with ht1 | h1t
    · have hanti : AntitoneOn f (Icc (1 / 2) 1) :=
        antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc _ _)
          (hf _ fun x hx => by linarith [hx.1])
          (fun x hx => (hd x (by
            have := interior_subset hx; change x ∈ Icc (1 / 2) 1 at this
            linarith [this.1])).hasDerivWithinAt)
          (fun x hx => by
            have hx' : x ∈ Icc (1 / 2 : ℝ) 1 := interior_subset hx
            exact div_nonpos_of_nonpos_of_nonneg
              (mul_nonpos_of_nonneg_of_nonpos (by linarith [hx'.1]) (by linarith [hx'.2]))
              (by linarith [hx'.1]))
      exact hanti ⟨ht, ht1⟩ (by constructor <;> norm_num) ht1
    · have hmono : MonotoneOn f (Ici 1) :=
        monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici _)
          (hf _ fun x hx => by change 1 ≤ x at hx; linarith)
          (fun x hx => (hd x (by
            have hx' : 1 ≤ x := interior_subset hx; linarith)).hasDerivWithinAt)
          (fun x hx => by
            have hx' : 1 ≤ x := interior_subset hx
            exact div_nonneg (mul_nonneg (by linarith) (by linarith)) (by linarith))
      exact hmono (by simp) h1t h1t
  dsimp [f] at hmin
  rw [Real.log_one] at hmin
  linarith

/-- The manuscript's logarithmic comparison: the density loses at most a
factor `e` on its central interval. The proof already works for `d ≥ 4`. -/
lemma chiSqDensity_one_mul_exp_neg_one_le {d : ℕ} (hd : 4 ≤ d) {t : ℝ}
    (ht : |t - 1| ≤ 1 / Real.sqrt d) :
    chiSqDensity d 1 * exp (-1) ≤ chiSqDensity d t := by
  have hd0 : (0 : ℝ) < d := by positivity
  have hsqrt : 0 < Real.sqrt d := Real.sqrt_pos.2 hd0
  have hsqrt2 : 2 ≤ Real.sqrt d := by
    rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]
    exact Real.sqrt_le_sqrt (by norm_num at hd ⊢; exact_mod_cast hd)
  have hinv : 1 / Real.sqrt d ≤ 1 / 2 :=
    one_div_le_one_div_of_le (by norm_num) hsqrt2
  have hδlo : -(1 / Real.sqrt d) ≤ t - 1 := neg_le_of_abs_le ht
  have hδhi : t - 1 ≤ 1 / Real.sqrt d := le_of_abs_le ht
  have ht12 : (1 : ℝ) / 2 ≤ t := by linarith
  have ht0 : 0 < t := by linarith
  have hloglo := log_lower_quadratic ht12
  have hloghi := Real.log_le_sub_one_of_pos ht0
  have hsq : (t - 1) ^ 2 ≤ 1 / d := by
    have h := (sq_le_sq₀ (abs_nonneg (t - 1)) (by positivity)).mpr ht
    rwa [sq_abs, div_pow, one_pow, Real.sq_sqrt hd0.le] at h
  have hquad : (d : ℝ) / 2 * (t - 1) ^ 2 ≤ 1 / 2 := by
    calc
      (d : ℝ) / 2 * (t - 1) ^ 2 ≤ (d : ℝ) / 2 * (1 / d) := by gcongr
      _ = 1 / 2 := by field_simp
  have hexp : -1 ≤ ((d : ℝ) / 2 - 1) * log t - (d : ℝ) / 2 * (t - 1) := by
    have hmain := mul_le_mul_of_nonneg_left hloglo
      (by positivity : (0 : ℝ) ≤ (d : ℝ) / 2)
    nlinarith
  rw [chiSqDensity_eq_one_mul_exp (by omega) ht0]
  exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp)
    (chiSqDensity_nonneg (by omega) 1)

lemma chiSqMeasure_real_eq_integral {d : ℕ} (hd : 0 < d) {s : Set ℝ}
    (hs : MeasurableSet s) :
    (chiSqMeasure d).real s = ∫ t in s, chiSqDensity d t := by
  rw [chiSqMeasure, gammaMeasure, measureReal_def, withDensity_apply _ hs]
  exact (integral_eq_lintegral_of_nonneg_ae
    (ae_of_all _ (chiSqDensity_nonneg hd))
    (by exact (measurable_gammaPDFReal _ _).aestronglyMeasurable)).symm

lemma integrable_chiSqDensity {d : ℕ} (hd : 0 < d) :
    Integrable (chiSqDensity d) := by
  apply Integrable.of_integral_ne_zero
  rw [integral_eq_lintegral_of_nonneg_ae
    (ae_of_all _ (chiSqDensity_nonneg hd))
    (by exact (measurable_gammaPDFReal _ _).aestronglyMeasurable)]
  change ENNReal.toReal (∫⁻ x, gammaPDF ((d : ℝ) / 2) ((d : ℝ) / 2) x) ≠ 0
  rw [lintegral_gammaPDF_eq_one (by positivity) (by positivity)]
  norm_num

/-- The Stirling asymptotic displayed in the proof of Lemma 5.2:
`ρ_d(1)/√d → 1/(2√π)`. -/
theorem chiSqDensity_one_stirling :
    Filter.Tendsto (fun d : ℕ => chiSqDensity d 1 / sqrt d) Filter.atTop
      (nhds (1 / (2 * sqrt π))) := by
  have heq (d : ℕ) : chiSqDensity d 1 = gammaPeak ((d : ℝ) / 2) := by
    simp only [chiSqDensity, gammaPDFReal, gammaPeak, ite_eq_left zero_le_one,
      Real.one_rpow, mul_one]
    ring
  simpa only [heq] using tendsto_gammaPeak_dimension

lemma chiSqDensity_one_half_stirling_eventually :
    ∀ᶠ d : ℕ in Filter.atTop, sqrt d / (4 * sqrt π) ≤ chiSqDensity d 1 := by
  have hc : 1 / (4 * sqrt π) < 1 / (2 * sqrt π) := by
    apply one_div_lt_one_div_of_lt (by positivity)
    nlinarith [sqrt_pos.2 pi_pos]
  filter_upwards [chiSqDensity_one_stirling.eventually_const_le hc,
    Filter.eventually_gt_atTop 0] with d hd hdpos
  have hs : 0 < sqrt (d : ℝ) := by positivity
  rw [le_div_iff₀ hs] at hd
  simpa [div_eq_mul_inv, mul_comm] using hd

/-- The paper's universal sufficiently-large-dimension threshold. -/
def chiSquareThreshold : ℕ := max 16
  (Classical.choose (Filter.eventually_atTop.mp chiSqDensity_one_half_stirling_eventually))

lemma chiSquareThreshold_ge_sixteen : 16 ≤ chiSquareThreshold := le_max_left _ _

lemma chiSqDensity_one_half_stirling {d : ℕ} (hd : chiSquareThreshold ≤ d) :
    sqrt d / (4 * sqrt π) ≤ chiSqDensity d 1 :=
  Classical.choose_spec (Filter.eventually_atTop.mp chiSqDensity_one_half_stirling_eventually)
    d ((le_max_right _ _).trans hd)

/-- A convenient smaller constant, chosen after the paper's Stirling estimate. -/
lemma chiSqDensity_one_lower {d : ℕ} (hd : chiSquareThreshold ≤ d) :
    sqrt d / (8 * exp 1) ≤ chiSqDensity d 1 := by
  have hpi : sqrt π ≤ 2 := by
    nlinarith [sq_sqrt pi_pos.le, sqrt_nonneg π, pi_le_four]
  have he : 1 ≤ exp (1 : ℝ) := Real.one_le_exp (by norm_num)
  exact (div_le_div_of_nonneg_left (sqrt_nonneg _) (by positivity)
    (by nlinarith : 4 * sqrt π ≤ 8 * exp 1)).trans (chiSqDensity_one_half_stirling hd)

/- LaTeX — `main.tex`, Lemma 5.2: "There exist universal constants
$c_1,d_0>0$ such that, for every $d\ge d_0$, the density $\rho_d$ satisfies
$\rho_d(t)\ge c_1\sqrt d$ for every $t\in[1-1/\sqrt d,\,1+1/\sqrt d]$."
We choose `c₁ = exp(-2)/8`; `d₀ = chiSquareThreshold` comes from Stirling,
as in the manuscript. -/
/-- **Lemma 5.2 (local normalized chi-square density bound).** -/
theorem chi_square_local_density (d : ℕ) (hd : chiSquareThreshold ≤ d) (t : ℝ)
    (ht : t ∈ Set.Icc (1 - 1 / Real.sqrt d) (1 + 1 / Real.sqrt d)) :
    (exp (-2) / 8) * Real.sqrt d ≤ chiSqDensity d t := by
  have hd16 : 16 ≤ d := chiSquareThreshold_ge_sixteen.trans hd
  have habs : |t - 1| ≤ 1 / Real.sqrt d := by
    rw [abs_le]
    constructor <;> linarith [ht.1, ht.2]
  have hlocal := chiSqDensity_one_mul_exp_neg_one_le (by omega) habs
  have hone := chiSqDensity_one_lower hd
  have he : 0 < exp 1 := Real.exp_pos _
  have hsqrt : 0 ≤ Real.sqrt d := Real.sqrt_nonneg _
  have hcombine : Real.sqrt d / (8 * exp 1) * exp (-1) ≤ chiSqDensity d t :=
    (mul_le_mul_of_nonneg_right hone (Real.exp_pos _).le).trans hlocal
  calc
    (exp (-2) / 8) * Real.sqrt d = Real.sqrt d / (8 * exp 1) * exp (-1) := by
      rw [show (-2 : ℝ) = -1 + -1 by ring, Real.exp_add]
      field_simp [Real.exp_ne_zero]
      rw [← Real.exp_add]
      norm_num
    _ ≤ chiSqDensity d t := hcombine

end

end GaussianDepthSeparation
