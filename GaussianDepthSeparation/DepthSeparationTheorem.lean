/-
GaussianDepthSeparation — Theorem 1.3 of `main.tex`, stated as in the paper (both parts, with
existential universal constants).
-/
import GaussianDepthSeparation.DepthSeparation
import GaussianDepthSeparation.GlobalUpper

namespace GaussianDepthSeparation

open MeasureTheory Real

noncomputable section

/- LaTeX — `main.tex`, Theorem 1.3:
"Let $F(x)=\sin(4\pi d^{1/2}\|x\|^2)$. Then, there are universal constants
$c>0$ and $d_0$ such that for every even $d\ge d_0$ the following holds
(1) Let $M>0$. For all $g_1,\ldots,g_r\in L^2(\gamma)$ with
$\|g_j\|_{L^2(\gamma)}\le M$ and all $v_1,\ldots,v_r\in S^{d-1}$, if
$\|F-\sum_j g_j(\langle v_j,\cdot\rangle)\|^2\le c^2/2$, then
$r\ge\frac{c}{4M}2^{d/4}$.
(2) For every $0<\epsilon\le1$, there is a depth-3 ReLU network $\mathcal N$
such that $\|F-\mathcal N\|\le\epsilon$, with width
$O(d^{5/2}(d+\log(1/\epsilon))/\epsilon)$, and with parameters bounded by
$O(d+\log(1/\epsilon))$."

The constant `C` makes the `O`-bounds explicit; it is universal, so it is
quantified before `d`.  The width of a depth-3 network is `max(w₁, w₂)`.
-/
/-- **Theorem 1.3 (Depth separation).** -/
theorem depth_separation :
    ∃ c : ℝ, 0 < c ∧ ∃ d₀ : ℕ, ∃ C : ℝ, 0 < C ∧
      ∀ d : ℕ, Even d → d₀ ≤ d →
        (∀ (M : ℝ), 0 < M → ∀ (r : ℕ) (g : Fin r → L2R) (v : Fin r → Vec d)
            (hv : ∀ j, ‖v j‖ = 1), (∀ j, ‖g j‖ ≤ M) →
            ‖sepTarget d - ∑ j, ridge (v j) (hv j) (g j)‖ ^ 2 ≤ c ^ 2 / 2 →
            c / (4 * M) * 2 ^ ((d : ℝ) / 4) ≤ (r : ℝ)) ∧
        (∀ ε : ℝ, 0 < ε → ε ≤ 1 →
          ∃ N : Net3 d, ∃ hN : MemLp N.eval 2 (γ d),
            ‖sepTarget d - hN.toLp N.eval‖ ≤ ε ∧
            max (N.n1 : ℝ) (N.n2 : ℝ) ≤
              C * ((d : ℝ) ^ 2 * Real.sqrt d) * ((d : ℝ) + Real.log (1 / ε)) / ε ∧
            N.WeightsLe (C * ((d : ℝ) + Real.log (1 / ε)))) := by
  obtain ⟨C, hC, hupper⟩ := depth_separation_upper_L2
  refine ⟨cEnergy, cEnergy_pos, 16, C, hC, fun d hde hd => ⟨?_, ?_⟩⟩
  · intro M hM r g v hv hgM happrox
    have h := depth_separation_lower d hde hd g v hv hM hgM happrox
    calc cEnergy / (4 * M) * 2 ^ ((d : ℝ) / 4)
        = cEnergy * 2 ^ ((d : ℝ) / 4) / (4 * M) := by ring
      _ ≤ (r : ℝ) := h
  · exact hupper d (by omega)

end

end GaussianDepthSeparation
