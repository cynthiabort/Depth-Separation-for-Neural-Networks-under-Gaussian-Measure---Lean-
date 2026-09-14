/-
GaussianDepthSeparation — Corollary 1.3: common parameter and accuracy budgets at both depths.
-/
import GaussianDepthSeparation.DepthTwo
import GaussianDepthSeparation.GlobalUpper

namespace GaussianDepthSeparation

open MeasureTheory Real

noncomputable section

/- LaTeX — `paper.tex`, Corollary 1.3 (Matched depth comparison):
For universal constants and all even $d \ge d_1$, $0<\epsilon\le\epsilon_0$,
both depths have parameter budget $A(d+\log(1/\epsilon))$ and error tolerance
$\epsilon$. Depth 2 requires width
$\Omega(2^{d/4}/(d+\log(1/\epsilon))^2)$, while depth 3 has width
$O(d^{5/2}(d+\log(1/\epsilon))/\epsilon)$.
-/
/-- **Corollary 1.3.** The constants witnessing both asymptotic bounds are
quantified before dimension and accuracy. The dimension threshold is `16`;
depth-3 width is the maximum of its two hidden widths, as in the paper. -/
theorem depth_separation_comparison :
    ∃ ε₀ A cLower cUpper : ℝ,
      0 < ε₀ ∧ ε₀ < 1 ∧ 1 ≤ A ∧ 0 < cLower ∧ 0 < cUpper ∧
      ∀ d : ℕ, Even d → ∀ hd : 16 ≤ d, ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ →
        let L := (d : ℝ) + Real.log (1 / ε)
        let B := A * L
        (∀ N : Net2 d, N.WeightsLe B →
          ‖sepTarget d - N.asL2 (by omega)‖ ≤ ε →
          cLower * 2 ^ ((d : ℝ) / 4) / L ^ 2 ≤ (N.width : ℝ)) ∧
        ∃ N : Net3 d, ∃ hN : MemLp N.eval 2 (γ d),
          ‖sepTarget d - hN.toLp N.eval‖ ≤ ε ∧
          max (N.n1 : ℝ) (N.n2 : ℝ) ≤
            cUpper * ((d : ℝ) ^ 2 * Real.sqrt d) * L / ε ∧
          N.WeightsLe B := by
  obtain ⟨C, hC, hupper⟩ := depth_separation_upper_L2
  let A : ℝ := max 1 (2 * C)
  have hA1 : 1 ≤ A := le_max_left _ _
  have hApos : 0 < A := lt_of_lt_of_le zero_lt_one hA1
  have hcEnergy : 0 < cEnergy := cEnergy_pos
  refine ⟨min (cEnergy / 2) (1 / 2), A, cEnergy / (8 * A ^ 2), 2 * C,
    by positivity, lt_of_le_of_lt (min_le_right _ _) (by norm_num),
    hA1, by positivity, by positivity, ?_⟩
  intro d hde hd ε hε hε₀
  dsimp only
  set L : ℝ := (d : ℝ) + Real.log (1 / ε)
  have hdpos : 0 < d := by omega
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hdpos
  have hε1 : ε ≤ 1 := le_trans (hε₀.trans (min_le_right _ _)) (by norm_num)
  have hεc : ε ≤ cEnergy / 2 := hε₀.trans (min_le_left _ _)
  have hinv : 1 ≤ 1 / ε := by
    rw [le_div_iff₀ hε]
    simpa using hε1
  have hL1 : 1 ≤ L := by
    have hlog := Real.log_nonneg hinv
    dsimp [L]
    linarith
  have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one hL1
  have hB1 : 1 ≤ A * L := by
    simpa using mul_le_mul hA1 hL1 (by norm_num : (0 : ℝ) ≤ 1) hApos.le
  constructor
  · intro N hweights herr
    have herrc : ‖sepTarget d - N.asL2 hdpos‖ ≤ cEnergy / 2 := herr.trans hεc
    have herrsq : ‖sepTarget d - N.asL2 hdpos‖ ^ 2 ≤ cEnergy ^ 2 / 2 := by
      calc
        ‖sepTarget d - N.asL2 hdpos‖ ^ 2 ≤ (cEnergy / 2) ^ 2 := by gcongr
        _ ≤ cEnergy ^ 2 / 2 := by nlinarith [sq_nonneg cEnergy]
    have hlower := depth_separation_lower_net2 d hde hd N hB1 hweights herrsq
    calc
      cEnergy / (8 * A ^ 2) * 2 ^ ((d : ℝ) / 4) / L ^ 2
          = cEnergy * 2 ^ ((d : ℝ) / 4) / (8 * (A * L) ^ 2) := by
            field_simp
      _ ≤ (N.width : ℝ) := hlower
  · obtain ⟨N, hN, herr, hwidth, hweights⟩ := hupper d hdpos ε hε hε1
    have hparam : C * (L + 1) ≤ A * L := by
      calc
        C * (L + 1) ≤ C * (2 * L) :=
          mul_le_mul_of_nonneg_left (by linarith) hC.le
        _ = (2 * C) * L := by ring
        _ ≤ A * L := mul_le_mul_of_nonneg_right (le_max_right _ _) hLpos.le
    have hwidth' : (N.n1 : ℝ) + N.n2 ≤
        (2 * C) * ((d : ℝ) ^ 2 * Real.sqrt d) * L / ε := by
      calc
        (N.n1 : ℝ) + N.n2 ≤
            C * ((d : ℝ) ^ 2 * Real.sqrt d) * (L + 1) / ε := hwidth
        _ ≤ C * ((d : ℝ) ^ 2 * Real.sqrt d) * (2 * L) / ε := by
          gcongr
          linarith
        _ = (2 * C) * ((d : ℝ) ^ 2 * Real.sqrt d) * L / ε := by ring
    have hmax : max (N.n1 : ℝ) (N.n2 : ℝ) ≤ (N.n1 : ℝ) + N.n2 :=
      max_le (le_add_of_nonneg_right (Nat.cast_nonneg _))
        (le_add_of_nonneg_left (Nat.cast_nonneg _))
    exact ⟨N, hN, herr, hmax.trans hwidth', hweights.mono hparam⟩

end

end GaussianDepthSeparation
