/-
GaussianDepthSeparation — Corollary 1.4 of `main.tex`: common parameter and accuracy budgets at
both depths.
-/
import GaussianDepthSeparation.DepthTwo
import GaussianDepthSeparation.GlobalUpper

namespace GaussianDepthSeparation

open MeasureTheory Real

noncomputable section

/- LaTeX — `main.tex`, Corollary 1.4 (Matched depth comparison):
"There exist constants $\epsilon_0\in(0,1)$, $A\ge1$, and $d_1\ge1$ such that
for every even $d\ge d_1$ and every $0<\epsilon\le\epsilon_0$, setting
$B_{d,\epsilon}:=A(d+\log(1/\epsilon))$ the function
$F_d(x)=\sin(4\pi\sqrt d\,\|x\|^2)$ has the following properties:
(i) Every depth-2 ReLU network $\mathcal N$ whose parameters are bounded by
$B_{d,\epsilon}$ and which satisfies $\|F_d-\mathcal N\|\le\epsilon$ has width
$\Omega(2^{d/4}/(d+\log(1/\epsilon))^2)$.
(ii) There exists a depth-3 ReLU network $\mathcal N$ whose parameters are
bounded by $B_{d,\epsilon}$, whose error satisfies $\|F_d-\mathcal N\|\le\epsilon$,
and whose width is $O(d^{5/2}(d+\log(1/\epsilon))/\epsilon)$."

The `Ω` and `O` constants are `cLower` and `cUpper`; like `ε₀`, `A`, `d₁` they
are universal, i.e. quantified before `d` and `ε`.  The depth-3 width is
`max(w₁, w₂)`, as defined in the paper.
-/
/-- **Corollary 1.4 (Matched depth comparison).** -/
theorem depth_separation_comparison :
    ∃ ε₀ A : ℝ, ∃ d₁ : ℕ, ∃ _ : 1 ≤ d₁, ∃ cLower cUpper : ℝ,
      0 < ε₀ ∧ ε₀ < 1 ∧ 1 ≤ A ∧ 0 < cLower ∧ 0 < cUpper ∧
      ∀ d : ℕ, Even d → ∀ hd : d₁ ≤ d, ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ →
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
  let A : ℝ := max 1 C
  have hA1 : 1 ≤ A := le_max_left _ _
  have hApos : 0 < A := lt_of_lt_of_le zero_lt_one hA1
  have hcEnergy : 0 < cEnergy := cEnergy_pos
  refine ⟨min (cEnergy / 2) (1 / 2), A, chiSquareThreshold, by have := chiSquareThreshold_ge_sixteen; omega, cEnergy / (8 * A ^ 2), C,
    by positivity, lt_of_le_of_lt (min_le_right _ _) (by norm_num),
    hA1, by positivity, hC, ?_⟩
  intro d hde hd ε hε hε₀
  have hd16 : 16 ≤ d := chiSquareThreshold_ge_sixteen.trans hd
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
    exact ⟨N, hN, herr, hwidth,
      hweights.mono (mul_le_mul_of_nonneg_right (le_max_right _ _) hLpos.le)⟩

end

end GaussianDepthSeparation
