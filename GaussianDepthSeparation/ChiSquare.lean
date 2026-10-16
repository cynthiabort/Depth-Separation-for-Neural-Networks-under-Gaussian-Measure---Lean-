/-
GaussianDepthSeparation §5 — the normalized chi-square density (Lemma 5.2).

The paper invokes Stirling's formula to control the density at its mode.  We
use the equivalent probabilistic normalization argument: the gamma law below
has mean one and variance `2 / d`, so Chebyshev supplies mass near one; the
same logarithmic comparison as in the paper then makes that mass pointwise.
-/
import GaussianDepthSeparation.GaussianSpace
import Mathlib.Probability.Distributions.Gamma
import Mathlib.Probability.Moments.Variance
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

/-- The first two gamma moments.  Keeping the statement generic makes clear
that no asymptotic estimate is hidden in Lemma 5.2. -/
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

lemma integral_id_gammaMeasure (a r : ℝ) (ha : 0 < a) (hr : 0 < r) :
    ∫ x : ℝ, x ∂(gammaMeasure a r) = a / r := by
  have h := integral_pow_gammaMeasure a r ha hr 1
  simp only [pow_one, Nat.cast_one] at h
  rw [h, Real.Gamma_add_one ha.ne', one_div, Real.inv_rpow hr.le,
    ← Real.rpow_neg hr.le]
  have hp : r ^ a * r ^ (-(a + 1)) = r ^ (-1 : ℝ) := by
    rw [← Real.rpow_add hr]
    congr 1
    ring
  calc
    r ^ a / Gamma a * (r ^ (-(a + 1)) * (a * Gamma a))
        = (r ^ a * r ^ (-(a + 1))) * a := by
          field_simp [(Real.Gamma_pos_of_pos ha).ne']
    _ = r ^ (-1 : ℝ) * a := by rw [hp]
    _ = a / r := by rw [Real.rpow_neg_one]; ring

lemma integral_sq_gammaMeasure (a r : ℝ) (ha : 0 < a) (hr : 0 < r) :
    ∫ x : ℝ, x ^ 2 ∂(gammaMeasure a r) = a * (a + 1) / r ^ 2 := by
  have h := integral_pow_gammaMeasure a r ha hr 2
  norm_num only [Nat.cast_ofNat] at h
  rw [h, show a + 2 = (a + 1) + 1 by ring,
    Real.Gamma_add_one (by linarith : a + 1 ≠ 0), Real.Gamma_add_one ha.ne',
    one_div, Real.inv_rpow hr.le, ← Real.rpow_neg hr.le]
  have hp : r ^ a * r ^ (-(a + 1 + 1)) = r ^ (-2 : ℝ) := by
    rw [← Real.rpow_add hr]
    congr 1
    ring
  calc
    r ^ a / Gamma a * (r ^ (-(a + 1 + 1)) * ((a + 1) * (a * Gamma a)))
        = (r ^ a * r ^ (-(a + 1 + 1))) * (a * (a + 1)) := by
          field_simp [(Real.Gamma_pos_of_pos ha).ne']
    _ = r ^ (-2 : ℝ) * (a * (a + 1)) := by rw [hp]
    _ = a * (a + 1) / r ^ 2 := by
      rw [show (-2 : ℝ) = -(2 : ℝ) by norm_num, Real.rpow_neg hr.le,
        Real.rpow_two]
      field_simp [hr.ne']

lemma integrable_sq_gammaMeasure (a r : ℝ) (ha : 0 < a) (hr : 0 < r) :
    Integrable (fun x : ℝ => x ^ 2) (gammaMeasure a r) := by
  apply Integrable.of_integral_ne_zero
  rw [integral_sq_gammaMeasure a r ha hr]
  positivity

lemma memLp_id_gammaMeasure (a r : ℝ) (ha : 0 < a) (hr : 0 < r) :
    MemLp (fun x : ℝ => x) 2 (gammaMeasure a r) := by
  rw [memLp_two_iff_integrable_sq (by fun_prop)]
  exact integrable_sq_gammaMeasure a r ha hr

lemma variance_id_gammaMeasure (a r : ℝ) (ha : 0 < a) (hr : 0 < r) :
    Var[fun x : ℝ => x; gammaMeasure a r] = a / r ^ 2 := by
  let : IsProbabilityMeasure (gammaMeasure a r) :=
    isProbabilityMeasure_gammaMeasure ha hr
  rw [variance_eq_sub (memLp_id_gammaMeasure a r ha hr)]
  change (∫ x : ℝ, x ^ 2 ∂gammaMeasure a r) -
      (∫ x : ℝ, x ∂gammaMeasure a r) ^ 2 = _
  rw [integral_sq_gammaMeasure a r ha hr,
    integral_id_gammaMeasure a r ha hr]
  field_simp
  ring

lemma integral_id_chiSqMeasure {d : ℕ} (hd : 0 < d) :
    ∫ x : ℝ, x ∂(chiSqMeasure d) = 1 := by
  rw [chiSqMeasure, integral_id_gammaMeasure _ _ (by positivity) (by positivity)]
  field_simp

lemma variance_id_chiSqMeasure {d : ℕ} (hd : 0 < d) :
    Var[fun x : ℝ => x; chiSqMeasure d] = 2 / d := by
  rw [chiSqMeasure, variance_id_gammaMeasure _ _ (by positivity) (by positivity)]
  field_simp

lemma memLp_id_chiSqMeasure {d : ℕ} (hd : 0 < d) :
    MemLp (fun x : ℝ => x) 2 (chiSqMeasure d) :=
  memLp_id_gammaMeasure _ _ (by positivity) (by positivity)

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

/-- On the interval used by the paper, the chi-square density loses at most a
factor `e`. -/
lemma chiSqDensity_one_mul_exp_neg_one_le {d : ℕ} (hd : 16 ≤ d) {t : ℝ}
    (ht : |t - 1| ≤ 1 / Real.sqrt d) :
    chiSqDensity d 1 * exp (-1) ≤ chiSqDensity d t := by
  have hd0 : (0 : ℝ) < d := by positivity
  have hsqrt : 0 < Real.sqrt d := Real.sqrt_pos.2 hd0
  have hsqrt4 : 4 ≤ Real.sqrt d := by
    rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 4)]
    exact Real.sqrt_le_sqrt (by norm_num at hd ⊢; exact_mod_cast hd)
  have hinv : 1 / Real.sqrt d ≤ 1 / 4 := by
    exact (one_div_le_one_div_of_le (by norm_num) hsqrt4)
  have hδlo : -(1 / Real.sqrt d) ≤ t - 1 :=
    (neg_le_of_abs_le ht)
  have hδhi : t - 1 ≤ 1 / Real.sqrt d := le_of_abs_le ht
  have ht34 : (3 : ℝ) / 4 ≤ t := by linarith
  have ht0 : 0 < t := lt_of_lt_of_le (by norm_num) ht34
  have hloglo := Real.one_sub_inv_le_log_of_pos ht0
  have hloghi := Real.log_le_sub_one_of_pos ht0
  have hsq : (t - 1) ^ 2 ≤ 1 / d := by
    have := (sq_le_sq₀ (abs_nonneg (t - 1)) (by positivity)).mpr ht
    rw [sq_abs, div_pow, one_pow, Real.sq_sqrt hd0.le] at this
    exact this
  have hquad : (d : ℝ) / 2 * ((t - 1) ^ 2 / t) ≤ 2 / 3 := by
    have htpos : 0 < t := ht0
    rw [show (d : ℝ) / 2 * ((t - 1) ^ 2 / t) =
      ((d : ℝ) / 2 * (t - 1) ^ 2) / t by ring]
    rw [div_le_iff₀ htpos]
    have hmul := mul_le_mul_of_nonneg_left hsq (show 0 ≤ (d : ℝ) / 2 by positivity)
    have hnum : (d : ℝ) / 2 * (t - 1) ^ 2 ≤ 1 / 2 := by
      calc
        (d : ℝ) / 2 * (t - 1) ^ 2 ≤ (d : ℝ) / 2 * (1 / d) := hmul
        _ = 1 / 2 := by field_simp
    nlinarith [hnum, ht34]
  have hlogdiff : -((t - 1) ^ 2 / t) ≤ log t - (t - 1) := by
    have hid : 1 - t⁻¹ = (t - 1) - (t - 1) ^ 2 / t := by
      field_simp
      ring
    rw [hid] at hloglo
    linarith
  have hexp : -1 ≤ ((d : ℝ) / 2 - 1) * log t - (d : ℝ) / 2 * (t - 1) := by
    have hmain : -((d : ℝ) / 2 * ((t - 1) ^ 2 / t)) ≤
        (d : ℝ) / 2 * (log t - (t - 1)) := by
      convert mul_le_mul_of_nonneg_left hlogdiff
        (by positivity : (0 : ℝ) ≤ (d : ℝ) / 2) using 1
      all_goals first | ring | rfl
    nlinarith [hquad, hloghi, hδhi, hinv]
  rw [chiSqDensity_eq_one_mul_exp (by omega) ht0]
  exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp)
    (chiSqDensity_nonneg (by omega) 1)

/-- On the slightly wider Chebyshev interval, the density is at most `e`
times its value at one. -/
lemma chiSqDensity_le_one_mul_exp_one {d : ℕ} (hd : 16 ≤ d) {t : ℝ}
    (ht : |t - 1| < 2 / Real.sqrt d) :
    chiSqDensity d t ≤ chiSqDensity d 1 * exp 1 := by
  have hd0 : (0 : ℝ) < d := by positivity
  have hsqrt : 0 < Real.sqrt d := Real.sqrt_pos.2 hd0
  have hsqrt4 : 4 ≤ Real.sqrt d := by
    rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 4)]
    exact Real.sqrt_le_sqrt (by norm_num at hd ⊢; exact_mod_cast hd)
  have hinv : 2 / Real.sqrt d ≤ 1 / 2 := by
    rw [div_le_iff₀ hsqrt]
    nlinarith
  have hδlo : -(2 / Real.sqrt d) < t - 1 := neg_lt_of_abs_lt ht
  have ht12 : (1 : ℝ) / 2 < t := by linarith
  have ht0 : 0 < t := by linarith
  have hloghi := Real.log_le_sub_one_of_pos ht0
  have hloglo := Real.one_sub_inv_le_log_of_pos ht0
  have hinvt : t⁻¹ < 2 := by
    rw [inv_lt_iff_one_lt_mul₀ ht0]
    nlinarith
  have hlogneg : -1 < log t := by linarith
  have hexp : ((d : ℝ) / 2 - 1) * log t - (d : ℝ) / 2 * (t - 1) ≤ 1 := by
    have hdiff : log t - (t - 1) ≤ 0 := by linarith
    have hmain : (d : ℝ) / 2 * (log t - (t - 1)) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by positivity) hdiff
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

/-- Chebyshev supplies at least half the mass in the interval of radius
`2 / √d` about one. -/
lemma chiSqMeasure_two_sqrt_interval_ge_half {d : ℕ} (hd : 16 ≤ d) :
    (1 : ℝ) / 2 ≤ (chiSqMeasure d).real
      (Ioo (1 - 2 / Real.sqrt d) (1 + 2 / Real.sqrt d)) := by
  let : NeZero d := ⟨by omega⟩
  let μ := chiSqMeasure d
  let c : ℝ := 2 / Real.sqrt d
  have hc : 0 < c := by dsimp [c]; positivity
  have hcheb := meas_ge_le_variance_div_sq
    (μ := μ) (memLp_id_chiSqMeasure (by omega)) hc
  have hmean : ∫ x : ℝ, x ∂μ = 1 := by
    simpa [μ] using integral_id_chiSqMeasure (d := d) (by omega)
  have hvar : Var[fun x : ℝ => x; μ] = 2 / d := by
    simpa [μ] using variance_id_chiSqMeasure (d := d) (by omega)
  rw [hmean, hvar] at hcheb
  have hc_sq : c ^ 2 = 4 / d := by
    dsimp [c]
    rw [div_pow, Real.sq_sqrt (by positivity)]
    ring
  rw [hc_sq] at hcheb
  have hratio : (2 / (d : ℝ)) / (4 / d) = (1 : ℝ) / 2 := by
    field_simp
    norm_num
  rw [hratio] at hcheb
  let A : Set ℝ := {x | c ≤ |x - 1|}
  have hAmeas : MeasurableSet A := by
    exact measurableSet_le measurable_const (Continuous.measurable (by fun_prop))
  have hrealA : μ.real A ≤ 1 / 2 := by
    rw [measureReal_def]
    have htop : ENNReal.ofReal ((1 : ℝ) / 2) ≠ ∞ := by simp
    have := ENNReal.toReal_mono htop hcheb
    simpa [A, c] using this
  have hcomp : μ.real A + μ.real Aᶜ = 1 := by
    simpa [μ] using measureReal_add_measureReal_compl (μ := μ) hAmeas
  have hset : Aᶜ = Ioo (1 - 2 / Real.sqrt d) (1 + 2 / Real.sqrt d) := by
    ext x
    simp only [A, c, mem_compl_iff, mem_ofPred_eq, not_le, mem_Ioo, abs_lt]
    constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]
  rw [hset] at hcomp
  linarith

lemma chiSqDensity_one_lower {d : ℕ} (hd : 16 ≤ d) :
    Real.sqrt d / (8 * exp 1) ≤ chiSqDensity d 1 := by
  let a : ℝ := 1 - 2 / Real.sqrt d
  let b : ℝ := 1 + 2 / Real.sqrt d
  let C : ℝ := chiSqDensity d 1 * exp 1
  have hmass : (1 : ℝ) / 2 ≤ ∫ t in Ioo a b, chiSqDensity d t := by
    rw [← chiSqMeasure_real_eq_integral (by omega) measurableSet_Ioo]
    exact chiSqMeasure_two_sqrt_interval_ge_half hd
  have hmono : ∫ t in Ioo a b, chiSqDensity d t ≤ ∫ _t in Ioo a b, C := by
    refine setIntegral_mono_on (integrable_chiSqDensity (by omega)).integrableOn
      (integrableOn_const (μ := volume) (s := Ioo a b) (C := C)
        (by simp [Real.volume_Ioo])) measurableSet_Ioo ?_
    intro t ht
    exact chiSqDensity_le_one_mul_exp_one hd (by
      rw [abs_lt]
      constructor <;> dsimp [a, b] at ht ⊢ <;> linarith [ht.1, ht.2])
  have hconst : ∫ _t in Ioo a b, C = C * (4 / Real.sqrt d) := by
    rw [setIntegral_const]
    simp only [measureReal_def, smul_eq_mul]
    rw [Real.volume_Ioo]
    have hsqrt : 0 < Real.sqrt d := by positivity
    have hba : 0 ≤ b - a := by
      dsimp [a, b]
      have : 0 < 2 / Real.sqrt d := div_pos (by norm_num) hsqrt
      linarith
    rw [ENNReal.toReal_ofReal hba]
    dsimp [a, b]
    ring
  rw [hconst] at hmono
  have hsqrt : 0 < Real.sqrt d := by positivity
  dsimp [C] at hmono
  have : (1 : ℝ) / 2 ≤ chiSqDensity d 1 * exp 1 * (4 / Real.sqrt d) :=
    hmass.trans hmono
  have he : 0 < exp 1 := Real.exp_pos _
  have hmul := mul_le_mul_of_nonneg_right this hsqrt.le
  rw [mul_assoc, div_mul_cancel₀ 4 hsqrt.ne'] at hmul
  apply (div_le_iff₀ (mul_pos (by norm_num) he)).2
  nlinarith [hmul]

/- LaTeX — `main.tex`, Lemma 5.2: "There exist universal constants
$c_1,d_0>0$ such that, for every $d\ge d_0$, the density $\rho_d$ satisfies
$\rho_d(t)\ge c_1\sqrt d$ for every $t\in[1-1/\sqrt d,\,1+1/\sqrt d]$."
Here the constants are explicit: `c₁ = exp(-2)/8` and `d₀ = 16`. -/
/-- **Lemma 5.2 (local normalized chi-square density bound).** -/
theorem chi_square_local_density (d : ℕ) (hd : 16 ≤ d) (t : ℝ)
    (ht : t ∈ Set.Icc (1 - 1 / Real.sqrt d) (1 + 1 / Real.sqrt d)) :
    (exp (-2) / 8) * Real.sqrt d ≤ chiSqDensity d t := by
  have habs : |t - 1| ≤ 1 / Real.sqrt d := by
    rw [abs_le]
    constructor <;> linarith [ht.1, ht.2]
  have hlocal := chiSqDensity_one_mul_exp_neg_one_le hd habs
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
