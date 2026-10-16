/-
Gamma-function estimates at integers and half-integers, obtained from
factorial Stirling and log-convexity. These are the arguments `d/2` needed
in the manuscript's chi-square density proof.
-/
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Tactic

namespace GaussianDepthSeparation

open Real Filter Set
open scoped Topology Nat

noncomputable section

lemma gamma_midpoint_sq_le {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    Gamma ((a + b) / 2) ^ 2 ≤ Gamma a * Gamma b := by
  have h := Gamma_mul_add_mul_le_rpow_Gamma_mul_rpow_Gamma ha hb
    (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num)
  rw [show (1 / 2 : ℝ) * a + 1 / 2 * b = (a + b) / 2 by ring,
    ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow] at h
  calc
    Gamma ((a + b) / 2) ^ 2 ≤ (sqrt (Gamma a) * sqrt (Gamma b)) ^ 2 :=
      pow_le_pow_left₀ (Gamma_pos_of_pos (by positivity)).le h 2
    _ = _ := by rw [mul_pow, sq_sqrt (Gamma_pos_of_pos ha).le,
      sq_sqrt (Gamma_pos_of_pos hb).le]

/-- The half-integer Gamma value lies between the two neighboring
factorial expressions. -/
lemma gamma_half_factorial_bounds (n : ℕ) (hn : 0 < n) :
    (n ! : ℝ) / sqrt ((n : ℝ) + 1 / 2) ≤ Gamma ((n : ℝ) + 1 / 2) ∧
    Gamma ((n : ℝ) + 1 / 2) ≤ (n ! : ℝ) / sqrt n := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hg : 0 < Gamma ((n : ℝ) + 1 / 2) := Gamma_pos_of_pos (by positivity)
  have hgn : Gamma (n : ℝ) * n = n ! := by
    rw [mul_comm, ← Gamma_add_one hnR.ne', Gamma_nat_eq_factorial]
  have hlo := gamma_midpoint_sq_le
    (by positivity : (0 : ℝ) < n + 1 / 2)
    (by positivity : (0 : ℝ) < (n + 1 / 2) + 1)
  rw [show (((n : ℝ) + 1 / 2) + ((n + 1 / 2) + 1)) / 2 = n + 1 by ring,
    Gamma_nat_eq_factorial, Gamma_add_one (by positivity)] at hlo
  have hhi := gamma_midpoint_sq_le hnR (by positivity : (0 : ℝ) < n + 1)
  rw [show ((n : ℝ) + (n + 1)) / 2 = n + 1 / 2 by ring,
    Gamma_nat_eq_factorial] at hhi
  constructor
  · apply (div_le_iff₀ (sqrt_pos.2 (by positivity))).2
    nlinarith [sq_sqrt (show (0 : ℝ) ≤ n + 1 / 2 by positivity),
      mul_nonneg hg.le (sqrt_nonneg ((n : ℝ) + 1 / 2)), (show (0 : ℝ) ≤ (n ! : ℝ) by positivity)]
  · apply (le_div_iff₀ (sqrt_pos.2 hnR)).2
    have hsq := mul_le_mul_of_nonneg_right hhi hnR.le
    have heq : Gamma (n : ℝ) * (n ! : ℝ) * n = (n ! : ℝ) ^ 2 := by
      calc
        _ = (Gamma (n : ℝ) * n) * (n ! : ℝ) := by ring
        _ = _ := by rw [hgn]; ring
    rw [heq] at hsq
    nlinarith [sq_sqrt hnR.le, mul_nonneg hg.le (sqrt_nonneg (n : ℝ)),
      (show (0 : ℝ) ≤ (n ! : ℝ) by positivity)]

def gammaPeak (a : ℝ) : ℝ := a ^ a * exp (-a) / Gamma a

lemma gammaPeak_nat (n : ℕ) (hn : 0 < n) :
    gammaPeak n / sqrt (2 * (n : ℝ)) = 1 / (2 * Stirling.stirlingSeq n) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hgn : Gamma (n : ℝ) = (n ! : ℝ) / n := by
    rw [eq_div_iff hnR.ne', mul_comm, ← Gamma_add_one hnR.ne', Gamma_nat_eq_factorial]
  have hs := sq_sqrt (show (0 : ℝ) ≤ 2 * n by positivity)
  have he : exp (-(n : ℝ)) = (exp 1)⁻¹ ^ n := by
    rw [← Real.exp_neg, ← Real.exp_nat_mul]
    congr 1
    ring
  simp only [gammaPeak, Real.rpow_natCast, he, hgn, Stirling.stirlingSeq, div_pow, inv_pow]
  field_simp
  nlinarith [sq_sqrt (show (0 : ℝ) ≤ (n : ℝ) * 2 by positivity)]

def gammaHalfCorrection (n : ℕ) : ℝ :=
  (n ! : ℝ) / (sqrt n * Gamma ((n : ℝ) + 1 / 2))

lemma gammaHalfCorrection_bounds (n : ℕ) (hn : 0 < n) :
    1 ≤ gammaHalfCorrection n ∧
      gammaHalfCorrection n ≤ sqrt (1 + (1 / 2 : ℝ) / n) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hg : 0 < Gamma ((n : ℝ) + 1 / 2) := Gamma_pos_of_pos (by positivity)
  obtain ⟨hlo, hhi⟩ := gamma_half_factorial_bounds n hn
  rw [div_le_iff₀ (sqrt_pos.2 (by positivity))] at hlo
  rw [le_div_iff₀ (sqrt_pos.2 hnR)] at hhi
  constructor
  · rw [gammaHalfCorrection, le_div_iff₀ (by positivity)]
    simpa [mul_comm] using hhi
  · calc
      gammaHalfCorrection n ≤
          (Gamma ((n : ℝ) + 1 / 2) * sqrt ((n : ℝ) + 1 / 2)) /
            (sqrt n * Gamma ((n : ℝ) + 1 / 2)) :=
        div_le_div_of_nonneg_right hlo (by positivity)
      _ = sqrt ((n : ℝ) + 1 / 2) / sqrt n := by field_simp
      _ = sqrt (1 + (1 / 2 : ℝ) / n) := by
        rw [← sqrt_div (by positivity)]
        congr 1
        field_simp

lemma tendsto_gammaHalfCorrection :
    Tendsto gammaHalfCorrection atTop (𝓝 1) := by
  have hu : Tendsto (fun n : ℕ => sqrt (1 + (1 / 2 : ℝ) / n)) atTop (𝓝 1) := by
    simpa using ((tendsto_const_nhds (x := (1 : ℝ))).add
      (tendsto_const_div_atTop_nhds_zero_nat (1 / 2 : ℝ))).sqrt
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hu
    ((eventually_gt_atTop 0).mono fun n hn => (gammaHalfCorrection_bounds n hn).1)
    ((eventually_gt_atTop 0).mono fun n hn => (gammaHalfCorrection_bounds n hn).2)

lemma gammaPeak_half (n : ℕ) (hn : 0 < n) :
    gammaPeak ((n : ℝ) + 1 / 2) / sqrt (2 * ((n : ℝ) + 1 / 2)) =
      ((1 + (1 / 2 : ℝ) / n) ^ n * exp (-(1 / 2 : ℝ)) /
        (2 * Stirling.stirlingSeq n)) * gammaHalfCorrection n := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have ha : (0 : ℝ) < (n : ℝ) + 1 / 2 := by positivity
  have he : exp (-((n : ℝ) + 1 / 2)) = (exp 1)⁻¹ ^ n * exp (-(1 / 2 : ℝ)) := by
    rw [neg_add, exp_add]
    congr 1
    rw [← Real.exp_neg, ← Real.exp_nat_mul]
    congr 1
    ring
  have hb : 1 + (1 / 2 : ℝ) / n = ((n : ℝ) + 1 / 2) / n := by field_simp
  rw [gammaPeak, Real.rpow_add ha, Real.rpow_natCast, ← sqrt_eq_rpow, he, hb,
    Stirling.stirlingSeq, gammaHalfCorrection, sqrt_mul (by norm_num : (0 : ℝ) ≤ 2),
    sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
  simp only [div_pow, inv_pow]
  field_simp
  ring_nf
  norm_num [Real.sq_sqrt]

/-- Stirling's asymptotic for the peak, at integer arguments. -/
lemma tendsto_gammaPeak_nat :
    Tendsto (fun n : ℕ => gammaPeak n / sqrt (2 * (n : ℝ))) atTop
      (𝓝 (1 / (2 * sqrt π))) := by
  apply Tendsto.congr' ((eventually_gt_atTop 0).mono fun n hn => (gammaPeak_nat n hn).symm)
  exact tendsto_const_nhds.div
    (tendsto_const_nhds.mul Stirling.tendsto_stirlingSeq_sqrt_pi) (by positivity)

/-- The same asymptotic at half-integers follows by the log-convexity squeeze. -/
lemma tendsto_gammaPeak_half :
    Tendsto (fun n : ℕ => gammaPeak ((n : ℝ) + 1 / 2) /
      sqrt (2 * ((n : ℝ) + 1 / 2))) atTop (𝓝 (1 / (2 * sqrt π))) := by
  have h := (((Real.tendsto_one_add_div_pow_exp (1 / 2 : ℝ)).mul_const
    (exp (-(1 / 2 : ℝ)))).div
      (tendsto_const_nhds.mul Stirling.tendsto_stirlingSeq_sqrt_pi)
      (by positivity : 2 * sqrt π ≠ 0)).mul tendsto_gammaHalfCorrection
  have he : exp (1 / 2 : ℝ) * exp (-(1 / 2 : ℝ)) = 1 := by rw [← exp_add]; norm_num
  rw [he, mul_one] at h
  exact h.congr' ((eventually_gt_atTop 0).mono fun n hn => (gammaPeak_half n hn).symm)

/-- Combine the integer and half-integer cases: this is precisely the
Gamma-Stirling asymptotic needed for dimensions `d ∈ ℕ`. -/
theorem tendsto_gammaPeak_dimension :
    Tendsto (fun d : ℕ => gammaPeak ((d : ℝ) / 2) / sqrt d) atTop
      (𝓝 (1 / (2 * sqrt π))) := by
  rw [Filter.tendsto_def]
  intro s hs
  obtain ⟨N, hN⟩ := eventually_atTop.mp (tendsto_gammaPeak_nat.eventually hs)
  obtain ⟨M, hM⟩ := eventually_atTop.mp (tendsto_gammaPeak_half.eventually hs)
  refine eventually_atTop.mpr ⟨2 * max N M + 2, fun d hd => ?_⟩
  have hdivN : N ≤ d / 2 := by omega
  have hdivM : M ≤ d / 2 := by omega
  rcases Nat.mod_two_eq_zero_or_one d with he | ho
  · have hdim : d = 2 * (d / 2) := by omega
    have hdimR : (d : ℝ) = 2 * ((d / 2 : ℕ) : ℝ) := by exact_mod_cast hdim
    have hhalf : (d : ℝ) / 2 = ((d / 2 : ℕ) : ℝ) := by rw [hdimR]; ring
    change gammaPeak ((d : ℝ) / 2) / sqrt d ∈ s
    rw [hhalf, hdimR]
    exact hN _ hdivN
  · have hdim : d = 2 * (d / 2) + 1 := by omega
    have hdimR : (d : ℝ) = 2 * ((d / 2 : ℕ) : ℝ) + 1 := by exact_mod_cast hdim
    have hhalf : (d : ℝ) / 2 = ((d / 2 : ℕ) : ℝ) + 1 / 2 := by rw [hdimR]; ring
    change gammaPeak ((d : ℝ) / 2) / sqrt d ∈ s
    rw [hhalf, show (d : ℝ) = 2 * (((d / 2 : ℕ) : ℝ) + 1 / 2) by rw [hdimR]; ring]
    exact hM _ hdivM

end

end GaussianDepthSeparation
