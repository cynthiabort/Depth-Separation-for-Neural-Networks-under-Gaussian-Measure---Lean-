/-
GaussianDepthSeparation — Theorem 1.3(ii): the global Gaussian `L²` upper bound in the
depth-separation theorem, following the proof in `main.tex`.
-/
import GaussianDepthSeparation.CenteredReLU
import GaussianDepthSeparation.GaussianTail
import GaussianDepthSeparation.Target
import Mathlib.Analysis.Complex.ExponentialBounds

namespace GaussianDepthSeparation

open MeasureTheory Real
open scoped RealInnerProductSpace

noncomputable section

/-- The Gaussian radius chosen in the proof of Theorem 1.3(ii):
`R² = 2d log 2 + 8 log(4/ε)`. -/
def upperRadius (d : ℕ) (ε : ℝ) : ℝ :=
  Real.sqrt (2 * (d : ℝ) * Real.log 2 + 8 * Real.log (4 / ε))

lemma upperRadius_arg_pos {d : ℕ} {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    0 < 2 * (d : ℝ) * Real.log 2 + 8 * Real.log (4 / ε) := by
  have hquot : 1 < 4 / ε := by rw [lt_div_iff₀ hε]; linarith
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have := Real.log_pos hquot
  positivity

lemma upperRadius_sq {d : ℕ} {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    upperRadius d ε ^ 2 = 2 * (d : ℝ) * Real.log 2 + 8 * Real.log (4 / ε) := by
  rw [upperRadius, Real.sq_sqrt (upperRadius_arg_pos hε hε1).le]

lemma upperRadius_pos {d : ℕ} {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    0 < upperRadius d ε :=
  Real.sqrt_pos.mpr (upperRadius_arg_pos hε hε1)

/-- With this radius, `P(‖X‖ > R) ≤ 2^{d/2} e^{-R²/4} = ε²/16`. -/
lemma upperRadius_tail {d : ℕ} {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    (γ d).real {x : Vec d | upperRadius d ε < ‖x‖} ≤ ε ^ 2 / 16 := by
  have htail := gaussian_norm_tail d (upperRadius_pos (d := d) hε hε1).le
  rw [upperRadius_sq hε hε1] at htail
  apply htail.trans_eq
  have h4 : 0 < 4 / ε := by positivity
  rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2), ← Real.exp_add,
    show Real.log 2 * ((d : ℝ) / 2) +
        -(2 * (d : ℝ) * Real.log 2 + 8 * Real.log (4 / ε)) / 4 =
        -(((2 : ℕ) : ℝ) * Real.log (4 / ε)) by push_cast; ring,
    Real.exp_neg, Real.exp_nat_mul, Real.exp_log h4]
  field_simp
  ring

/-- **Theorem 1.3(ii), with the explicit constants of the paper's proof.**
With `R² = 2d log 2 + 8 log(4/ε)` and `η = ε/2`, the network `𝒩_{R,η}`
satisfies `‖F - 𝒩_{R,η}‖² ≤ η² + 4·P(‖X‖ > R) ≤ ε²/2 ≤ ε²`, has width
`O(d^{5/2}(R²+1)/η)`, and has parameters bounded by `2(R²+1) + 4π√d`. -/
theorem depth_separation_upper_L2_explicit {d : ℕ} (hd : 0 < d) {ε : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ N : Net3 d, ∃ hN : MemLp N.eval 2 (γ d),
      ‖sepTarget d - hN.toLp N.eval‖ ≤ ε ∧
      ((N.n1 : ℝ) + N.n2 ≤
        200 * π * ((d : ℝ) ^ 2 * Real.sqrt d) *
          (2 * (d : ℝ) * Real.log 2 + 8 * Real.log (4 / ε) + 1) / (ε / 2)) ∧
      N.WeightsLe (2 * (2 * (d : ℝ) * Real.log 2 + 8 * Real.log (4 / ε) + 1) +
        4 * π * Real.sqrt d) := by
  set R := upperRadius d ε with hRdef
  have hR : 0 < R := by rw [hRdef]; exact upperRadius_pos hε hε1
  obtain ⟨N, hwidth, hweights, hlocal, hglobal⟩ :=
    exists_net3c_approx hd (show 0 < ε / 2 by positivity) (by linarith) hR
  have hN : MemLp N.eval 2 (γ d) :=
    MemLp.of_bound N.continuous_eval.aestronglyMeasurable 1
      (ae_of_all _ fun x => by rw [Real.norm_eq_abs]; exact hglobal x)
  refine ⟨N, hN, ?_, ?_, ?_⟩
  · have htarget : MemLp
        (fun x : Vec d => Real.sin (4 * π * Real.sqrt d * ‖x‖ ^ 2)) 2 (γ d) :=
      MemLp.of_bound (by fun_prop) 1 (ae_of_all _ fun x => by
        rw [Real.norm_eq_abs]
        exact Real.abs_sin_le_one _)
    have hdiffInt : Integrable (fun x : Vec d =>
        (Real.sin (4 * π * Real.sqrt d * ‖x‖ ^ 2) - N.eval x) ^ 2) (γ d) :=
      (htarget.sub hN).integrable_sq
    let S : Set (Vec d) := {x | R < ‖x‖}
    have hS : MeasurableSet S := by
      dsimp [S]
      exact measurableSet_lt measurable_const (by fun_prop)
    -- inside the ball the error is at most `η = ε/2`; outside, `|F - 𝒩| ≤ 2`
    have hpoint : ∀ x : Vec d,
        (Real.sin (4 * π * Real.sqrt d * ‖x‖ ^ 2) - N.eval x) ^ 2 ≤
          (ε / 2) ^ 2 + S.indicator (fun _ => (4 : ℝ)) x := by
      intro x
      by_cases hx : ‖x‖ ≤ R
      · have he := hlocal x hx
        have hnot : x ∉ S := not_lt.mpr hx
        rw [Set.indicator_of_notMem hnot, add_zero, abs_sub_comm] at *
        rw [← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) he 2
      · have hmem : x ∈ S := lt_of_not_ge hx
        rw [Set.indicator_of_mem hmem]
        have hsin := Real.abs_sin_le_one (4 * π * Real.sqrt d * ‖x‖ ^ 2)
        have hnet := hglobal x
        have habs : |Real.sin (4 * π * Real.sqrt d * ‖x‖ ^ 2) - N.eval x| ≤ 2 :=
          (abs_sub _ _).trans (by linarith)
        rw [← sq_abs]
        nlinarith [abs_nonneg (Real.sin (4 * π * Real.sqrt d * ‖x‖ ^ 2) - N.eval x)]
    have hconstInt : Integrable (fun _x : Vec d => (ε / 2) ^ 2) (γ d) :=
      integrable_const _
    have hindInt : Integrable (S.indicator (fun _x : Vec d => (4 : ℝ))) (γ d) :=
      (integrable_const _).indicator hS
    have hintLe : (∫ x : Vec d,
        (Real.sin (4 * π * Real.sqrt d * ‖x‖ ^ 2) - N.eval x) ^ 2 ∂(γ d)) ≤
        (ε / 2) ^ 2 + 4 * (γ d).real S := by
      calc
        (∫ x : Vec d,
            (Real.sin (4 * π * Real.sqrt d * ‖x‖ ^ 2) - N.eval x) ^ 2 ∂(γ d))
            ≤ ∫ x : Vec d, (ε / 2) ^ 2 +
                S.indicator (fun _ => (4 : ℝ)) x ∂(γ d) :=
              integral_mono hdiffInt (hconstInt.add hindInt) hpoint
        _ = (ε / 2) ^ 2 + 4 * (γ d).real S := by
              rw [integral_add hconstInt hindInt, integral_const,
                integral_indicator_const 4 hS]
              simp [smul_eq_mul, mul_comm]
    have htail : (γ d).real S ≤ ε ^ 2 / 16 := by
      simpa [S, R, hRdef] using upperRadius_tail (d := d) hε hε1
    have hnormSq : ‖sepTarget d - hN.toLp N.eval‖ ^ 2 =
        ∫ x : Vec d,
          (Real.sin (4 * π * Real.sqrt d * ‖x‖ ^ 2) - N.eval x) ^ 2 ∂(γ d) := by
      rw [norm_sq_eq_integral]
      apply integral_congr_ae
      filter_upwards [Lp.coeFn_sub (sepTarget d) (hN.toLp N.eval),
        sepTarget_coeFn d hd, MemLp.coeFn_toLp hN] with x hsub htargetx hNx
      rw [hsub]
      change (((sepTarget d : Vec d → ℝ) x -
        (hN.toLp N.eval : Vec d → ℝ) x) ^ 2) = _
      rw [htargetx, hNx]
    -- `‖F - 𝒩‖² ≤ η² + 4·P(‖X‖ > R) ≤ ε²/4 + ε²/4 = ε²/2 ≤ ε²`
    have hsq : ‖sepTarget d - hN.toLp N.eval‖ ^ 2 ≤ ε ^ 2 := by
      rw [hnormSq]
      nlinarith [hintLe, htail, sq_nonneg ε]
    nlinarith [norm_nonneg (sepTarget d - hN.toLp N.eval)]
  · rw [upperRadius_sq hε hε1] at hwidth
    exact hwidth
  · rw [upperRadius_sq hε hε1] at hweights
    exact hweights

/-- **Theorem 1.3(ii) (global depth-3 upper bound).**  For every `d ≥ 1` and
`0 < ε ≤ 1` there is a depth-3 ReLU network `𝒩` (two hidden ReLU layers, no
output bias) with `‖F - 𝒩‖_{L²(γ^d)} ≤ ε`, width
`max(w₁, w₂) = O(d^{5/2}(d + log(1/ε))/ε)`, and all parameters bounded by
`O(d + log(1/ε))`.  The constant `C` is universal. -/
theorem depth_separation_upper_L2 :
    ∃ C : ℝ, 0 < C ∧ ∀ d : ℕ, 0 < d → ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      ∃ N : Net3 d, ∃ hN : MemLp N.eval 2 (γ d),
        ‖sepTarget d - hN.toLp N.eval‖ ≤ ε ∧
        max (N.n1 : ℝ) (N.n2 : ℝ) ≤
          C * ((d : ℝ) ^ 2 * Real.sqrt d) * ((d : ℝ) + Real.log (1 / ε)) / ε ∧
        N.WeightsLe (C * ((d : ℝ) + Real.log (1 / ε))) := by
  refine ⟨6000 * π, by positivity, fun d hd ε hε hε1 => ?_⟩
  obtain ⟨N, hN, herr, hwidth, hweights⟩ :=
    depth_separation_upper_L2_explicit hd hε hε1
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hsqrtd : Real.sqrt d ≤ (d : ℝ) := by
    have hs := Real.sq_sqrt (show (0 : ℝ) ≤ d by positivity)
    nlinarith [Real.sqrt_nonneg (d : ℝ), Real.one_le_sqrt.mpr hd1]
  have hinv : 1 ≤ 1 / ε := by rw [le_div_iff₀ hε]; simpa using hε1
  have hL0 : 0 ≤ Real.log (1 / ε) := Real.log_nonneg hinv
  have hlog4 : Real.log (4 / ε) = 2 * Real.log 2 + Real.log (1 / ε) := by
    rw [show (4 : ℝ) / ε = 2 ^ 2 * (1 / ε) by ring,
      Real.log_mul (by norm_num) (by positivity), Real.log_pow]
    push_cast
    ring
  have hlog2 : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  have hlog2' : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set L := (d : ℝ) + Real.log (1 / ε) with hLdef
  set Q := 2 * (d : ℝ) * Real.log 2 + 8 * Real.log (4 / ε) + 1 with hQdef
  have hL1 : 1 ≤ L := by rw [hLdef]; linarith
  -- `R² + 1 = 2d log 2 + 8 log(4/ε) + 1 ≤ 15 (d + log(1/ε))`
  have hQL : Q ≤ 15 * L := by
    rw [hQdef, hlog4, hLdef]
    nlinarith [mul_le_mul_of_nonneg_left hlog2.le (Nat.cast_nonneg d)]
  have hQ0 : 0 ≤ Q := by rw [hQdef, hlog4]; positivity
  have hA0 : 0 ≤ (d : ℝ) ^ 2 * Real.sqrt d := by positivity
  refine ⟨N, hN, herr, ?_, ?_⟩
  · have hmax : max (N.n1 : ℝ) (N.n2 : ℝ) ≤ (N.n1 : ℝ) + N.n2 :=
      max_le (le_add_of_nonneg_right (Nat.cast_nonneg _))
        (le_add_of_nonneg_left (Nat.cast_nonneg _))
    refine hmax.trans (hwidth.trans ?_)
    rw [show ∀ x : ℝ, x / (ε / 2) = 2 * x / ε from fun x => by field_simp]
    apply div_le_div_of_nonneg_right _ hε.le
    calc 2 * (200 * π * ((d : ℝ) ^ 2 * Real.sqrt d) * Q)
        = 400 * π * ((d : ℝ) ^ 2 * Real.sqrt d) * Q := by ring
      _ ≤ 400 * π * ((d : ℝ) ^ 2 * Real.sqrt d) * (15 * L) := by gcongr
      _ = 6000 * π * ((d : ℝ) ^ 2 * Real.sqrt d) * L := by ring
  · refine hweights.mono ?_
    have hπ := Real.pi_gt_three
    nlinarith [hQL, hsqrtd, show (d : ℝ) ≤ L by rw [hLdef]; linarith]

end

end GaussianDepthSeparation
