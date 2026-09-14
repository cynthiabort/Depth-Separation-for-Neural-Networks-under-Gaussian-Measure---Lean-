/-
GaussianDepthSeparation — the global Gaussian `L²` upper bound in the depth-separation theorem.
-/
import GaussianDepthSeparation.CenteredReLU
import GaussianDepthSeparation.GaussianTail
import GaussianDepthSeparation.Target
import Mathlib.Analysis.Complex.ExponentialBounds

namespace GaussianDepthSeparation

open MeasureTheory Real
open scoped RealInnerProductSpace

noncomputable section

/-- The explicit Gaussian radius used in the global approximation theorem. -/
def upperRadius (d : ℕ) (ε : ℝ) : ℝ :=
  2 * Real.sqrt ((d : ℝ) * Real.log 2 + Real.log (64 / ε ^ 2))

lemma upperRadius_sq {d : ℕ} {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    upperRadius d ε ^ 2 =
      4 * ((d : ℝ) * Real.log 2 + Real.log (64 / ε ^ 2)) := by
  have hquot : 1 < 64 / ε ^ 2 := by
    have he2 : ε ^ 2 ≤ 1 := by nlinarith
    rw [lt_div_iff₀ (sq_pos_of_pos hε)]
    nlinarith
  have hQ : 0 ≤ (d : ℝ) * Real.log 2 + Real.log (64 / ε ^ 2) := by
    exact add_nonneg (mul_nonneg (Nat.cast_nonneg d) (Real.log_nonneg (by norm_num)))
      (Real.log_nonneg hquot.le)
  rw [upperRadius, mul_pow, Real.sq_sqrt hQ]
  ring

lemma upperRadius_pos {d : ℕ} (hd : 0 < d) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    0 < upperRadius d ε := by
  rw [upperRadius]
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hdR : 0 < (d : ℝ) := by exact_mod_cast hd
  have hQ : 0 < (d : ℝ) * Real.log 2 + Real.log (64 / ε ^ 2) := by
    have hquot : 1 ≤ 64 / ε ^ 2 := by
      have he2 : ε ^ 2 ≤ 1 := by nlinarith
      rw [le_div_iff₀ (sq_pos_of_pos hε)]
      nlinarith
    exact add_pos_of_pos_of_nonneg (mul_pos hdR hlog2) (Real.log_nonneg hquot)
  positivity

/-- The chosen radius leaves at most `ε²/64` Gaussian mass outside. -/
lemma upperRadius_tail {d : ℕ} {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    (γ d).real {x : Vec d | upperRadius d ε < ‖x‖} ≤ ε ^ 2 / 64 := by
  by_cases hd : d = 0
  · subst d
    have hR0 : 0 ≤ upperRadius 0 ε := by
      rw [upperRadius]
      positivity
    have hempty : {x : Vec 0 | upperRadius 0 ε < ‖x‖} = ∅ := by
      ext x
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      have hx : x = 0 := Subsingleton.elim _ _
      rw [hx, norm_zero]
      exact not_lt.mpr hR0
    rw [hempty, measureReal_empty]
    positivity
  · have hdpos : 0 < d := Nat.pos_of_ne_zero hd
    have hRpos := upperRadius_pos hdpos hε hε1
    have htail := gaussian_norm_tail d hRpos.le
    rw [upperRadius_sq hε hε1] at htail
    apply htail.trans_eq
    have hA : 0 < 64 / ε ^ 2 := div_pos (by norm_num) (sq_pos_of_pos hε)
    calc
      (2 : ℝ) ^ d * Real.exp (-(4 *
          ((d : ℝ) * Real.log 2 + Real.log (64 / ε ^ 2))) / 4)
          = Real.exp ((d : ℝ) * Real.log 2) *
              Real.exp (-((d : ℝ) * Real.log 2 + Real.log (64 / ε ^ 2))) := by
            rw [Real.exp_nat_mul]
            rw [Real.exp_log (by norm_num : (0 : ℝ) < 2)]
            congr 1
            ring_nf
      _ = Real.exp (-Real.log (64 / ε ^ 2)) := by
            rw [← Real.exp_add]
            congr 1
            ring
      _ = ε ^ 2 / 64 := by
            rw [Real.exp_neg, Real.exp_log hA]
            field_simp

/-- Exact quantitative form of the paper's global depth-3 upper bound. -/
theorem depth_separation_upper_L2_explicit {d : ℕ} (hd : 0 < d) {ε : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ N : Net3 d, ∃ hN : MemLp N.eval 2 (γ d),
      ‖sepTarget d - hN.toLp N.eval‖ ≤ ε ∧
      ((N.n1 : ℝ) + N.n2 ≤
        400 * π * ((d : ℝ) ^ 2 * Real.sqrt d) *
          (4 * ((d : ℝ) * Real.log 2 + Real.log (64 / ε ^ 2)) + 2) *
          (2 / ε + 1)) ∧
      N.WeightsLe (20 * π * (Real.sqrt d +
        4 * ((d : ℝ) * Real.log 2 + Real.log (64 / ε ^ 2)) + 1)) := by
  set R := upperRadius d ε with hRdef
  have hR : 0 < R := by rw [hRdef]; exact upperRadius_pos hd hε hε1
  obtain ⟨N, hwidth, hweights, hlocal, hglobal⟩ :=
    exists_net3c_approx hd (show 0 < ε / 2 by positivity) hR
  have hN : MemLp N.eval 2 (γ d) :=
    MemLp.of_bound N.continuous_eval.aestronglyMeasurable 2
      (ae_of_all _ fun x => by
        rw [Real.norm_eq_abs]
        have := hglobal x
        nlinarith)
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
    have hpoint : ∀ x : Vec d,
        (Real.sin (4 * π * Real.sqrt d * ‖x‖ ^ 2) - N.eval x) ^ 2 ≤
          ε ^ 2 / 4 + S.indicator (fun _ => (9 : ℝ)) x := by
      intro x
      by_cases hx : ‖x‖ ≤ R
      · have he := hlocal x hx
        have hnot : x ∉ S := not_lt.mpr hx
        rw [Set.indicator_of_notMem hnot]
        rw [abs_sub_comm] at he
        rw [← sq_abs]
        have hs := (sq_le_sq₀
          (abs_nonneg (Real.sin (4 * π * Real.sqrt d * ‖x‖ ^ 2) - N.eval x))
          (by positivity : 0 ≤ ε / 2)).2 he
        nlinarith
      · have hmem : x ∈ S := lt_of_not_ge hx
        rw [Set.indicator_of_mem hmem]
        have hsin := Real.abs_sin_le_one (4 * π * Real.sqrt d * ‖x‖ ^ 2)
        have hnet := hglobal x
        have habs : |Real.sin (4 * π * Real.sqrt d * ‖x‖ ^ 2) - N.eval x| ≤ 3 := by
          calc
            |Real.sin (4 * π * Real.sqrt d * ‖x‖ ^ 2) - N.eval x|
                ≤ |Real.sin (4 * π * Real.sqrt d * ‖x‖ ^ 2)| + |N.eval x| :=
                  abs_sub _ _
            _ ≤ 3 := by nlinarith
        rw [← sq_abs]
        have hs := (sq_le_sq₀
          (abs_nonneg (Real.sin (4 * π * Real.sqrt d * ‖x‖ ^ 2) - N.eval x))
          (by norm_num : (0 : ℝ) ≤ 3)).2 habs
        nlinarith
    have hconstInt : Integrable (fun _x : Vec d => ε ^ 2 / 4) (γ d) :=
      integrable_const _
    have hindInt : Integrable (S.indicator (fun _x : Vec d => (9 : ℝ))) (γ d) :=
      (integrable_const _).indicator hS
    have hrhsInt : Integrable (fun x : Vec d =>
        ε ^ 2 / 4 + S.indicator (fun _ => (9 : ℝ)) x) (γ d) :=
      hconstInt.add hindInt
    have hintLe : (∫ x : Vec d,
        (Real.sin (4 * π * Real.sqrt d * ‖x‖ ^ 2) - N.eval x) ^ 2 ∂(γ d)) ≤
        ε ^ 2 / 4 + 9 * (γ d).real S := by
      calc
        (∫ x : Vec d,
            (Real.sin (4 * π * Real.sqrt d * ‖x‖ ^ 2) - N.eval x) ^ 2 ∂(γ d))
            ≤ ∫ x : Vec d, ε ^ 2 / 4 +
                S.indicator (fun _ => (9 : ℝ)) x ∂(γ d) :=
              integral_mono hdiffInt hrhsInt hpoint
        _ = ε ^ 2 / 4 + 9 * (γ d).real S := by
              rw [integral_add hconstInt hindInt, integral_const,
                integral_indicator_const 9 hS]
              simp [smul_eq_mul, mul_comm]
    have htail : (γ d).real S ≤ ε ^ 2 / 64 := by
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
    have hsqInt : (∫ x : Vec d,
          (Real.sin (4 * π * Real.sqrt d * ‖x‖ ^ 2) - N.eval x) ^ 2 ∂(γ d)) ≤
        ε ^ 2 := by nlinarith [hintLe, htail, sq_nonneg ε]
    have hsq : ‖sepTarget d - hN.toLp N.eval‖ ^ 2 ≤ ε ^ 2 := by
      rw [hnormSq]
      exact hsqInt
    nlinarith [norm_nonneg (sepTarget d - hN.toLp N.eval)]
  · rw [upperRadius_sq hε hε1] at hwidth
    convert hwidth using 1
    all_goals ring
  · rw [upperRadius_sq hε hε1] at hweights
    simpa using hweights

/-- **Theorem 1.2(ii), in the paper's exact architecture and asymptotic scale.**
The network has two hidden ReLU layers and no output bias.  A single universal
constant controls the global `L²(γ^d)` error, width
`d^(5/2)(d + log(1/ε))/ε`, and parameter size `d + log(1/ε)`. -/
theorem depth_separation_upper_L2 :
    ∃ C : ℝ, 0 < C ∧ ∀ d : ℕ, 0 < d → ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      ∃ N : Net3 d, ∃ hN : MemLp N.eval 2 (γ d),
        ‖sepTarget d - hN.toLp N.eval‖ ≤ ε ∧
        ((N.n1 : ℝ) + N.n2 ≤ C * ((d : ℝ) ^ 2 * Real.sqrt d) *
          ((d : ℝ) + Real.log (1 / ε) + 1) / ε) ∧
        N.WeightsLe (C * ((d : ℝ) + Real.log (1 / ε) + 1)) := by
  refine ⟨40000 * π, by positivity, fun d hd ε hε hε1 => ?_⟩
  obtain ⟨N, hN, herr, hwidth, hweights⟩ :=
    depth_separation_upper_L2_explicit hd hε hε1
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hsqrtd : Real.sqrt d ≤ (d : ℝ) := by
    have hs := Real.sq_sqrt (show (0 : ℝ) ≤ d by positivity)
    nlinarith [Real.sqrt_nonneg (d : ℝ), hd1]
  have hinv : 1 ≤ 1 / ε := by
    rw [le_div_iff₀ hε]
    simpa using hε1
  have hL0 : 0 ≤ Real.log (1 / ε) := Real.log_nonneg hinv
  have hlogeps : Real.log (1 / ε) = -Real.log ε := by
    rw [Real.log_div one_ne_zero hε.ne', Real.log_one]
    ring
  have hlog64 : Real.log 64 = 6 * Real.log 2 := by
    rw [show (64 : ℝ) = 2 ^ 6 by norm_num, Real.log_pow]
    norm_num
  have hlogquot : Real.log (64 / ε ^ 2) =
      6 * Real.log 2 + 2 * Real.log (1 / ε) := by
    rw [Real.log_div (by norm_num) (pow_ne_zero 2 hε.ne'), hlog64,
      Real.log_pow, hlogeps]
    push_cast
    ring
  have hlog2 : Real.log 2 ≤ 1 := by linarith [Real.log_two_lt_d9]
  set D := (d : ℝ) + Real.log (1 / ε) + 1 with hDdef
  set Q := (d : ℝ) * Real.log 2 + Real.log (64 / ε ^ 2) with hQdef
  have hD1 : 1 ≤ D := by rw [hDdef]; nlinarith
  have hD0 : 0 ≤ D := by linarith
  have hQ0 : 0 ≤ Q := by
    rw [hQdef]
    exact add_nonneg (mul_nonneg (Nat.cast_nonneg d)
      (Real.log_nonneg (by norm_num))) (Real.log_nonneg (by
        rw [le_div_iff₀ (sq_pos_of_pos hε)]
        nlinarith [sq_nonneg ε]))
  have hQD : Q ≤ 6 * D := by
    rw [hQdef, hlogquot, hDdef]
    nlinarith [mul_le_mul_of_nonneg_left hlog2 (Nat.cast_nonneg d)]
  have hrad : 4 * Q + 2 ≤ 26 * D := by nlinarith
  have heta : 2 / ε + 1 ≤ 3 / ε := by
    rw [div_eq_mul_inv, div_eq_mul_inv]
    have hinv' : 1 ≤ ε⁻¹ := by simpa [one_div] using hinv
    nlinarith
  have hA0 : 0 ≤ (d : ℝ) ^ 2 * Real.sqrt d := by positivity
  refine ⟨N, hN, herr, ?_, ?_⟩
  · calc
      (N.n1 : ℝ) + N.n2 ≤
          400 * π * ((d : ℝ) ^ 2 * Real.sqrt d) * (4 * Q + 2) *
            (2 / ε + 1) := by simpa [Q, hQdef] using hwidth
      _ ≤ 400 * π * ((d : ℝ) ^ 2 * Real.sqrt d) * (26 * D) * (3 / ε) := by
        gcongr
      _ ≤ (40000 * π) * ((d : ℝ) ^ 2 * Real.sqrt d) * D / ε := by
        rw [div_eq_mul_inv, div_eq_mul_inv]
        have hz : 0 ≤ π * (((d : ℝ) ^ 2 * Real.sqrt d) * D * ε⁻¹) := by
          positivity
        ring_nf
        nlinarith
      _ = (40000 * π) * ((d : ℝ) ^ 2 * Real.sqrt d) *
          ((d : ℝ) + Real.log (1 / ε) + 1) / ε := by rw [hDdef]
  · refine hweights.mono ?_
    have hinner : Real.sqrt d + 4 * Q + 1 ≤ 26 * D := by
      nlinarith [hsqrtd, show (d : ℝ) ≤ D by rw [hDdef]; nlinarith]
    have hπ := Real.pi_pos
    calc
      20 * π * (Real.sqrt d + 4 * Q + 1)
          ≤ 20 * π * (26 * D) := mul_le_mul_of_nonneg_left hinner (by positivity)
      _ ≤ 40000 * π * D := by nlinarith [hD0]
      _ = (40000 * π) * ((d : ℝ) + Real.log (1 / ε) + 1) := by rw [hDdef]

end

end GaussianDepthSeparation
