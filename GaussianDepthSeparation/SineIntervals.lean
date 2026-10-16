/-
GaussianDepthSeparation §5 — the sign-change estimate used in Lemma 5.3.
-/
import GaussianDepthSeparation.RadialDistance
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Algebra.Order.Floor.Ring

namespace GaussianDepthSeparation

open MeasureTheory Real Set Polynomial
open intervalIntegral
open scoped Interval NNReal ENNReal Nat

noncomputable section

def scaledRadialError (m : ℝ) (q : Polynomial ℝ) (s : ℝ) : ℝ :=
  (sin (π * s) - q.eval (s / m)) ^ 2

lemma continuous_scaledRadialError (m : ℝ) (q : Polynomial ℝ) :
    Continuous (scaledRadialError m q) := by
  unfold scaledRadialError
  fun_prop

lemma continuous_pos_on_Ioo_of_no_zero {f : ℝ → ℝ} {a b x₀ : ℝ}
    (hf : Continuous f) (hx₀ : x₀ ∈ Ioo a b) (hpos : 0 < f x₀)
    (hzero : ∀ x ∈ Ioo a b, f x ≠ 0) {x : ℝ} (hx : x ∈ Ioo a b) :
    0 < f x := by
  by_contra hnot
  have hxnonpos : f x ≤ 0 := le_of_not_gt hnot
  rcases le_total x x₀ with hxx₀ | hx₀x
  · have hmem : (0 : ℝ) ∈ Icc (f x) (f x₀) := ⟨hxnonpos, hpos.le⟩
    obtain ⟨z, hz, hzf⟩ :=
      (intermediate_value_Icc hxx₀ hf.continuousOn hmem)
    exact hzero z ⟨lt_of_lt_of_le hx.1 hz.1, lt_of_le_of_lt hz.2 hx₀.2⟩ hzf
  · have hmem : (0 : ℝ) ∈ Icc (f x) (f x₀) := ⟨hxnonpos, hpos.le⟩
    obtain ⟨z, hz, hzf⟩ :=
      (intermediate_value_Icc' hx₀x hf.continuousOn hmem)
    exact hzero z ⟨lt_of_lt_of_le hx₀.1 hz.1, lt_of_le_of_lt hz.2 hx.2⟩ hzf

lemma continuous_neg_on_Ioo_of_no_zero {f : ℝ → ℝ} {a b x₀ : ℝ}
    (hf : Continuous f) (hx₀ : x₀ ∈ Ioo a b) (hneg : f x₀ < 0)
    (hzero : ∀ x ∈ Ioo a b, f x ≠ 0) {x : ℝ} (hx : x ∈ Ioo a b) :
    f x < 0 := by
  have hp := continuous_pos_on_Ioo_of_no_zero hf.neg hx₀ (by simpa) (fun y hy h =>
    hzero y hy (neg_eq_zero.mp h)) hx
  simpa using hp

lemma sin_pi_mul_nonneg_first_half (z : ℤ) {s : ℝ}
    (hs : s ∈ Ioo (2 * (z : ℝ)) (2 * (z : ℝ) + 1)) :
    0 ≤ sin (π * s) := by
  let u := π * (s - 2 * (z : ℝ))
  have hu0 : 0 ≤ u := by
    dsimp [u]
    exact mul_nonneg Real.pi_pos.le (by linarith [hs.1])
  have hupi : u ≤ π := by
    dsimp [u]
    have h := mul_le_mul_of_nonneg_left (show s - 2 * (z : ℝ) ≤ 1 by linarith [hs.2])
      Real.pi_pos.le
    simpa using h
  have harg : π * s = u + z * (2 * π) := by
    dsimp [u]
    ring
  rw [harg, Real.sin_add_int_mul_two_pi]
  exact sin_nonneg_of_nonneg_of_le_pi hu0 hupi

lemma sin_pi_mul_nonpos_second_half (z : ℤ) {s : ℝ}
    (hs : s ∈ Ioo (2 * (z : ℝ) + 1) (2 * (z : ℝ) + 2)) :
    sin (π * s) ≤ 0 := by
  let u := π * (s - (2 * (z : ℝ) + 2))
  have hu0 : u ≤ 0 := by
    dsimp [u]
    exact mul_nonpos_of_nonneg_of_nonpos Real.pi_pos.le (by linarith [hs.2])
  have hupi : -π ≤ u := by
    dsimp [u]
    have h := mul_le_mul_of_nonneg_left
      (show (-1 : ℝ) ≤ s - (2 * (z : ℝ) + 2) by linarith [hs.1]) Real.pi_pos.le
    nlinarith
  have harg : π * s = u + ((z + 1 : ℤ) : ℝ) * (2 * π) := by
    dsimp [u]
    push_cast
    ring
  rw [harg, Real.sin_add_int_mul_two_pi]
  exact sin_nonpos_of_nonpos_of_neg_pi_le hu0 hupi

lemma integral_sin_sq_first_half (z : ℤ) :
    ∫ s in Ioo (2 * (z : ℝ)) (2 * (z : ℝ) + 1), sin (π * s) ^ 2 = 1 / 2 := by
  rw [← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le (by linarith)]
  have h := intervalIntegral.mul_integral_comp_mul_left
    (a := 2 * (z : ℝ)) (b := 2 * (z : ℝ) + 1)
    (f := fun u : ℝ => sin u ^ 2) π
  rw [integral_sin_sq] at h
  have hsin0 : sin (π * (2 * (z : ℝ))) = 0 := by
    rw [show π * (2 * (z : ℝ)) = (2 * z : ℤ) * π by push_cast; ring,
      Real.sin_int_mul_pi]
  have hsin1 : sin (π * (2 * (z : ℝ) + 1)) = 0 := by
    rw [show π * (2 * (z : ℝ) + 1) = (2 * z + 1 : ℤ) * π by push_cast; ring,
      Real.sin_int_mul_pi]
  simp only [hsin0, hsin1, zero_mul, sub_zero, zero_add] at h
  have hpi : π ≠ 0 := ne_of_gt Real.pi_pos
  apply (mul_left_cancel₀ hpi)
  calc
    π * (∫ (x : ℝ) in 2 * (z : ℝ)..2 * (z : ℝ) + 1, sin (π * x) ^ 2) =
        (π * (2 * (z : ℝ) + 1) - π * (2 * (z : ℝ))) / 2 := h
    _ = π * (1 / 2) := by ring

lemma integral_sin_sq_second_half (z : ℤ) :
    ∫ s in Ioo (2 * (z : ℝ) + 1) (2 * (z : ℝ) + 2), sin (π * s) ^ 2 = 1 / 2 := by
  rw [← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le (by linarith)]
  have h := intervalIntegral.mul_integral_comp_mul_left
    (a := 2 * (z : ℝ) + 1) (b := 2 * (z : ℝ) + 2)
    (f := fun u : ℝ => sin u ^ 2) π
  rw [integral_sin_sq] at h
  have hsin1 : sin (π * (2 * (z : ℝ) + 1)) = 0 := by
    rw [show π * (2 * (z : ℝ) + 1) = (2 * z + 1 : ℤ) * π by push_cast; ring,
      Real.sin_int_mul_pi]
  have hsin2 : sin (π * (2 * (z : ℝ) + 2)) = 0 := by
    rw [show π * (2 * (z : ℝ) + 2) = (2 * z + 2 : ℤ) * π by push_cast; ring,
      Real.sin_int_mul_pi]
  simp only [hsin1, hsin2, zero_mul, sub_zero, zero_add] at h
  have hpi : π ≠ 0 := ne_of_gt Real.pi_pos
  apply (mul_left_cancel₀ hpi)
  calc
    π * (∫ (x : ℝ) in 2 * (z : ℝ) + 1..2 * (z : ℝ) + 2,
        sin (π * x) ^ 2) =
        (π * (2 * (z : ℝ) + 2) - π * (2 * (z : ℝ) + 1)) / 2 := h
    _ = π * (1 / 2) := by ring

end

end GaussianDepthSeparation
