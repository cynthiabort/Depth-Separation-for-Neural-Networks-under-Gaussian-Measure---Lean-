/-
GaussianDepthSeparation §5 — Energy lower bound (Lemma 5.3), following the paper's
radial-polynomial and sign-change proof.
-/
import GaussianDepthSeparation.Oscillation

namespace GaussianDepthSeparation

open MeasureTheory Real Set

noncomputable section

/-- The universal constant in Lemma 5.3 supplied by Lemmas 5.1 and 5.2. -/
def cEnergy : ℝ := sqrt ((exp (-2) / 8) / 8)

theorem cEnergy_pos : 0 < cEnergy :=
  sqrt_pos.2 (div_pos (by positivity) (by norm_num))

/- LaTeX — `main.tex`, Lemma 5.3 (Energy lower bound): "There exist universal
constants $c, d_0 > 0$ such that for all $d \ge d_0$, all even integers
$n_0 \ge 2$, and all $m \ge 4n_0\sqrt{d}$,
$$\|P_{\ge n_0}F\|_{L^2(\gamma^d)} \ge c$$"
where $F(x) = \sin(\pi m \|x\|^2/d)$.
-/
/-- **Lemma 5.3 (Energy lower bound).**  The proof follows the paper:
Lemma 5.1 reduces the high-chaos energy to radial polynomial approximation,
Lemma 5.2 controls the chi-square density on its central window, and a
root-counting sign argument controls every low-degree polynomial. -/
theorem energy_lower_bound (d : ℕ) (hd : chiSquareThreshold ≤ d) (n₀ : ℕ)
    (hn₀e : Even n₀) (hn₀ : 2 ≤ n₀) (m : ℝ) (hm : 4 * n₀ * sqrt d ≤ m) :
    cEnergy ≤ ‖Pge d n₀ (radialSine d m)‖ := by
  have hd16 : 16 ≤ d := chiSquareThreshold_ge_sixteen.trans hd
  have hdpos : 0 < d := by omega
  have hsq : (exp (-2) / 8) / 8 ≤ ‖Pge d n₀ (radialSine d m)‖ ^ 2 := by
    rw [radialSine_polynomial_distance d hdpos n₀ hn₀e hn₀ m]
    exact le_ciInf fun q => radialError_weighted_lower d n₀ hd hn₀ m hm q
  calc
    cEnergy = sqrt ((exp (-2) / 8) / 8) := rfl
    _ ≤ sqrt (‖Pge d n₀ (radialSine d m)‖ ^ 2) := sqrt_le_sqrt hsq
    _ = ‖Pge d n₀ (radialSine d m)‖ := by simp

end

end GaussianDepthSeparation
