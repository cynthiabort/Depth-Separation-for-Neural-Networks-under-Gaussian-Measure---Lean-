/- The beta integral and the substitution u = t² used in Proposition 3.4. -/
import Mathlib.Probability.Distributions.Beta
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic

namespace GaussianDepthSeparation

open MeasureTheory Real Set
open scoped Nat

noncomputable section

def betaKernel (a b u : ℝ) : ℝ := u ^ (a - 1) * (1 - u) ^ (b - 1)

lemma betaKernel_complex (a b : ℝ) {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) :
    ((u : ℂ) ^ ((a : ℂ) - 1) * (1 - (u : ℂ)) ^ ((b : ℂ) - 1)).re =
      betaKernel a b u := by
  have h1 : (u : ℂ) ^ ((a : ℂ) - 1) = (u ^ (a - 1) : ℝ) := by
    rw [← Complex.ofReal_one, ← Complex.ofReal_sub, ← Complex.ofReal_cpow hu.1.le]
  have h2 : (1 - (u : ℂ)) ^ ((b : ℂ) - 1) = ((1 - u) ^ (b - 1) : ℝ) := by
    rw [← Complex.ofReal_one, ← Complex.ofReal_sub, ← Complex.ofReal_sub,
      ← Complex.ofReal_cpow (by linarith [hu.2] : 0 ≤ 1 - u)]
  rw [h1, h2]
  simp [betaKernel]

lemma integrableOn_betaKernel {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    IntegrableOn (betaKernel a b) (Ioo 0 1) := by
  have hc := Complex.betaIntegral_convergent (u := (a : ℂ)) (v := (b : ℂ))
    (by simpa) (by simpa)
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)] at hc
  exact (hc.mono_set Ioo_subset_Ioc_self).re.congr_fun
    (fun u hu => betaKernel_complex a b hu) measurableSet_Ioo

/-- Euler's beta integral over the reals. -/
theorem integral_betaKernel {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    ∫ u in Ioo (0 : ℝ) 1, betaKernel a b u = Gamma a * Gamma b / Gamma (a + b) := by
  have hc := Complex.betaIntegral_convergent (u := (a : ℂ)) (v := (b : ℂ))
    (by simpa) (by simpa)
  have hci : IntegrableOn (fun u : ℝ =>
      (u : ℂ) ^ ((a : ℂ) - 1) * (1 - (u : ℂ)) ^ ((b : ℂ) - 1)) (Ioo 0 1) := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)] at hc
    exact hc.mono_set Ioo_subset_Ioc_self
  calc
    _ = (∫ u in Ioo (0 : ℝ) 1,
        (u : ℂ) ^ ((a : ℂ) - 1) * (1 - (u : ℂ)) ^ ((b : ℂ) - 1)).re := by
      rw [← RCLike.re_to_complex, ← integral_re hci]
      exact setIntegral_congr_fun measurableSet_Ioo fun u hu => (betaKernel_complex a b hu).symm
    _ = (Complex.betaIntegral a b).re := by
      rw [Complex.betaIntegral, intervalIntegral.integral_of_le (by norm_num),
        integral_Ioc_eq_integral_Ioo]
    _ = _ := by
      rw [Complex.betaIntegral_eq_Gamma_mul_div _ _ (by simpa) (by simpa)]
      simp only [← Complex.ofReal_add, Complex.Gamma_ofReal, ← Complex.ofReal_mul,
        ← Complex.ofReal_div, Complex.ofReal_re]

lemma square_image_unitInterval : (fun t : ℝ => t ^ 2) '' Ioo 0 1 = Ioo 0 1 := by
  ext u
  constructor
  · rintro ⟨t, ht, rfl⟩
    exact ⟨sq_pos_of_pos ht.1, by dsimp; nlinarith [ht.1, ht.2]⟩
  · intro hu
    refine ⟨sqrt u, ⟨sqrt_pos.2 hu.1, ?_⟩, sq_sqrt hu.1.le⟩
    nlinarith [sq_sqrt hu.1.le, sqrt_nonneg u, hu.2]

lemma square_injOn_unitInterval : Set.InjOn (fun t : ℝ => t ^ 2) (Ioo 0 1) := by
  intro x hx y hy h
  dsimp at h
  nlinarith [sq_nonneg (x - y), hx.1, hy.1]

/-- The exact Jacobian and exponent identity in the substitution `u=t²`. -/
lemma betaKernel_square (n : ℕ) (b : ℝ) {t : ℝ} (ht : 0 < t) :
    |2 * t| * betaKernel (((n : ℝ) + 1) / 2) b (t ^ 2) =
      2 * (t ^ n * (1 - t ^ 2) ^ (b - 1)) := by
  rw [betaKernel, abs_of_pos (by positivity)]
  have he : t * (t ^ 2) ^ (((n : ℝ) + 1) / 2 - 1) = t ^ n := by
    rw [← Real.rpow_natCast t 2, ← Real.rpow_mul ht.le]
    norm_num only [Nat.cast_ofNat]
    rw [show t * t ^ ((2 : ℝ) * (((n : ℝ) + 1) / 2 - 1)) =
      t ^ (1 + 2 * (((n : ℝ) + 1) / 2 - 1)) by rw [Real.rpow_add ht, Real.rpow_one]]
    have hexp : 1 + 2 * (((n : ℝ) + 1) / 2 - 1) = n := by ring
    rw [hexp, Real.rpow_natCast]
  calc
    _ = 2 * (t * (t ^ 2) ^ (((n : ℝ) + 1) / 2 - 1)) * (1 - t ^ 2) ^ (b - 1) := by ring
    _ = _ := by rw [he]; ring

/-- The square substitution, before evaluating the beta integral. -/
theorem sphereHalfIntegral_eq_beta (n : ℕ) (b : ℝ) :
    2 * (∫ t in Ioo (0 : ℝ) 1, t ^ n * (1 - t ^ 2) ^ (b - 1)) =
      ∫ u in Ioo (0 : ℝ) 1, betaKernel (((n : ℝ) + 1) / 2) b u := by
  have h := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioo
    (fun t _ => (hasDerivAt_pow 2 t).hasDerivWithinAt)
    square_injOn_unitInterval (betaKernel (((n : ℝ) + 1) / 2) b)
  rw [square_image_unitInterval] at h
  rw [← integral_const_mul]
  rw [h]
  refine setIntegral_congr_fun measurableSet_Ioo fun t ht => ?_
  simpa [smul_eq_mul] using (betaKernel_square n b ht.1).symm

lemma integrableOn_sphereHalf (n : ℕ) {b : ℝ} (hb : 0 < b) :
    IntegrableOn (fun t : ℝ => t ^ n * (1 - t ^ 2) ^ (b - 1)) (Ioo 0 1) := by
  have h := integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioo
    (fun t _ => (hasDerivAt_pow 2 t).hasDerivWithinAt)
    square_injOn_unitInterval (betaKernel (((n : ℝ) + 1) / 2) b)
  rw [square_image_unitInterval] at h
  have hi := h.mp (integrableOn_betaKernel (by positivity) hb)
  have hi' : IntegrableOn (fun t : ℝ => 2 * (t ^ n * (1 - t ^ 2) ^ (b - 1))) (Ioo 0 1) :=
    hi.congr_fun (fun t ht => by simpa [smul_eq_mul] using betaKernel_square n b ht.1)
      measurableSet_Ioo
  exact (hi'.const_mul (1 / 2 : ℝ)).congr (ae_of_all _ fun t => by ring)

lemma integrableOn_sphereSlice_monomial (n : ℕ) {b : ℝ} (hb : 0 < b) :
    IntegrableOn (fun t : ℝ => t ^ n * (1 - t ^ 2) ^ (b - 1)) (Ioo (-1) 1) := by
  let f : ℝ → ℝ := fun t => t ^ n * (1 - t ^ 2) ^ (b - 1)
  have hi : IntervalIntegrable f volume 0 1 :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num)).mpr
      (integrableOn_sphereHalf n hb)
  have hn : IntervalIntegrable (fun t => f (-t)) volume 0 1 := by
    convert hi.const_mul ((-1 : ℝ) ^ n) using 1
    ext t
    dsimp [f]
    rw [neg_sq, neg_pow]
    ring
  have hl : IntervalIntegrable f volume (-1) 0 := by
    have h := ((IntervalIntegrable.iff_comp_neg (f := fun t => f (-t)) (a := 0) (b := 1)).mp hn).symm
    simpa using h
  exact (intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num)).mp (hl.trans hi)

lemma sphereSlice_monomial_split (n : ℕ) {b : ℝ} (hb : 0 < b) :
    (∫ t in Ioo (-1 : ℝ) 1, t ^ n * (1 - t ^ 2) ^ (b - 1)) =
      ((-1 : ℝ) ^ n + 1) * (∫ t in Ioo (0 : ℝ) 1, t ^ n * (1 - t ^ 2) ^ (b - 1)) := by
  let f : ℝ → ℝ := fun t => t ^ n * (1 - t ^ 2) ^ (b - 1)
  have hi : IntervalIntegrable f volume (-1) 1 :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num)).mpr
      (integrableOn_sphereSlice_monomial n hb)
  have hl : IntervalIntegrable f volume (-1) 0 := hi.mono_set (by norm_num; intro x hx; constructor <;> linarith [hx.1, hx.2])
  have hr : IntervalIntegrable f volume 0 1 := hi.mono_set (by norm_num; intro x hx; constructor <;> linarith [hx.1, hx.2])
  change (∫ t in Ioo (-1 : ℝ) 1, f t) = _ * (∫ t in Ioo (0 : ℝ) 1, f t)
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le (by norm_num),
    ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le (by norm_num),
    ← intervalIntegral.integral_add_adjacent_intervals hl hr]
  have hneg : (∫ t in (-1 : ℝ)..0, f t) = (-1 : ℝ) ^ n * ∫ t in (0 : ℝ)..1, f t := by
    rw [← show (∫ t in (0 : ℝ)..1, f (-t)) = ∫ t in (-1 : ℝ)..0, f t by
      simp only [intervalIntegral.integral_comp_neg, neg_zero]]
    rw [← intervalIntegral.integral_const_mul]
    congr 1
    ext t
    dsimp [f]
    rw [neg_sq, neg_pow]
    ring
  rw [hneg]
  ring

/-- Even spherical slice moments: symmetry, `u=t²`, and Euler's beta integral. -/
theorem sphereSlice_even_moment (n : ℕ) (hn : Even n) {b : ℝ} (hb : 0 < b) :
    (∫ t in Ioo (-1 : ℝ) 1, t ^ n * (1 - t ^ 2) ^ (b - 1)) =
      Gamma (((n : ℝ) + 1) / 2) * Gamma b / Gamma (((n : ℝ) + 1) / 2 + b) := by
  rw [sphereSlice_monomial_split n hb, hn.neg_one_pow]
  norm_num only [one_add_one_eq_two]
  rw [sphereHalfIntegral_eq_beta, integral_betaKernel (by positivity) hb]

theorem sphereSlice_odd_moment (n : ℕ) (hn : Odd n) {b : ℝ} (hb : 0 < b) :
    (∫ t in Ioo (-1 : ℝ) 1, t ^ n * (1 - t ^ 2) ^ (b - 1)) = 0 := by
  rw [sphereSlice_monomial_split n hb, hn.neg_one_pow]
  ring

end

end GaussianDepthSeparation
