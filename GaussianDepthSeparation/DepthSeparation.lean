/-
GaussianDepthSeparation — Theorem 1.3(i), the depth-2 lower bound.
-/
import GaussianDepthSeparation.EnergyBound

namespace GaussianDepthSeparation

open MeasureTheory Real
open scoped RealInnerProductSpace

noncomputable section

/- LaTeX — `main.tex`, Theorem 1.3(1): "Let $F(x)=\sin(4\pi d^{1/2}\|x\|^2)$.
Then, there are universal constants $c>0$ and $d_0$ such that for every even
$d\ge d_0$ the following holds: Let $M>0$. For all
$g_1,\ldots,g_r\in L^2(\gamma)$ with $\|g_j\|_{L^2(\gamma)}\le M$ and all
$v_1,\ldots,v_r\in S^{d-1}$, if
$\|F-\sum_{j=1}^r g_j(\langle v_j,\cdot\rangle)\|_{L^2(\gamma^d)}^2\le c^2/2$, then
$r\ge\frac{c}{4M}\,2^{d/4}$."
The constants are `c = cEnergy` and `d₀ = chiSquareThreshold`, obtained
from Stirling’s formula as in the paper.  The statement
with existential constants, together with part (2), is `depth_separation`.
-/
/-- **Theorem 1.3(i) (Depth separation, lower bound).** -/
theorem depth_separation_lower (d : ℕ) (hde : Even d) (hd : chiSquareThreshold ≤ d)
    {r : ℕ} (g : Fin r → L2R) (v : Fin r → Vec d) (hv : ∀ j, ‖v j‖ = 1)
    {M : ℝ} (hM : 0 < M) (hgM : ∀ j, ‖g j‖ ≤ M)
    (happrox : ‖sepTarget d - ∑ j, ridge (v j) (hv j) (g j)‖ ^ 2 ≤
      cEnergy ^ 2 / 2) :
    cEnergy * 2 ^ ((d : ℝ) / 4) / (4 * M) ≤ (r : ℝ) := by
  have hd16 : 16 ≤ d := chiSquareThreshold_ge_sixteen.trans hd
  have hdpos : 0 < d := by omega
  have h2d : 2 ≤ d := by omega
  set P := ‖Pge d d (sepTarget d)‖ with hP
  set S := Real.sqrt (Kmom d d) with hS
  -- energy lower bound (n₀ = d, m = 4d√d)
  have hEnergy : cEnergy ≤ P := by
    have h := energy_lower_bound d hd d hde h2d (4 * d * Real.sqrt d) (le_refl _)
    exact h
  -- radiality
  have hrad : IsRadial (sepTarget d) := isRadial_radialSine d _
  -- approximation hypothesis in the ‖Pge‖² form
  have happrox' : ‖sepTarget d - ∑ j, ridge (v j) (hv j) (g j)‖ ^ 2 ≤ P ^ 2 / 2 := by
    refine happrox.trans ?_
    gcongr
    · exact cEnergy_pos.le
  -- Theorem 1.1
  have hlb := ridge_lower_bound hdpos hde (sepTarget d) hrad g v hv hM hgM happrox'
  -- S·2^{d/4} ≤ 1  (via (S·2^{d/4})² = K_d·2^{d/2} ≤ 1)
  have hQpos : (0 : ℝ) < 2 ^ ((d : ℝ) / 4) := by positivity
  have hSpos : 0 < S := Real.sqrt_pos.mpr (Kmom_pos hdpos hde)
  have hSQ : S * 2 ^ ((d : ℝ) / 4) ≤ 1 := by
    have hsq : (S * 2 ^ ((d : ℝ) / 4)) ^ 2 ≤ 1 := by
      have hS2 : S ^ 2 = Kmom d d := Real.sq_sqrt (Kmom_nonneg hdpos hde)
      have hQ2 : (2 ^ ((d : ℝ) / 4)) ^ 2 = (2 : ℝ) ^ ((d : ℝ) / 2) := by
        rw [← Real.rpow_natCast (2 ^ ((d : ℝ) / 4)) 2, ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
        congr 1; ring
      rw [mul_pow, hS2, hQ2]
      calc Kmom d d * 2 ^ ((d : ℝ) / 2)
          ≤ (2 : ℝ) ^ (-(d : ℝ) / 2) * 2 ^ ((d : ℝ) / 2) := by
            gcongr
            exact Kmom_le_two_pow hdpos hde
        _ = 1 := by
            rw [← Real.rpow_add (by norm_num : (0:ℝ) < 2),
              show (-(d : ℝ) / 2 + (d : ℝ) / 2) = 0 from by ring, Real.rpow_zero]
    nlinarith [hsq, mul_nonneg hSpos.le hQpos.le]
  -- final chain
  have hkey : cEnergy * 2 ^ ((d : ℝ) / 4) * S ≤ P := by
    calc cEnergy * 2 ^ ((d : ℝ) / 4) * S
        = cEnergy * (S * 2 ^ ((d : ℝ) / 4)) := by ring
      _ ≤ cEnergy * 1 := mul_le_mul_of_nonneg_left hSQ cEnergy_pos.le
      _ = cEnergy := mul_one _
      _ ≤ P := hEnergy
  have h4M : (0 : ℝ) < 4 * M := by positivity
  have h4MS : (0 : ℝ) < 4 * M * S := by positivity
  have hP_le : P ≤ (r : ℝ) * (4 * M * S) := (div_le_iff₀ h4MS).mp hlb
  have hX : cEnergy * 2 ^ ((d : ℝ) / 4) ≤ (r : ℝ) * (4 * M) := by
    have hmul : cEnergy * 2 ^ ((d : ℝ) / 4) * S ≤ (r : ℝ) * (4 * M) * S := by
      nlinarith [hkey, hP_le]
    exact le_of_mul_le_mul_right hmul hSpos
  rw [div_le_iff₀ h4M]
  exact hX

end

end GaussianDepthSeparation
