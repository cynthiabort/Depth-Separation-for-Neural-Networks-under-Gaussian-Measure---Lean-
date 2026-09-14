/-
Shared analytic and indexing helpers for the centered depth-3 ReLU
construction in `CenteredReLU.lean`.
-/
import GaussianDepthSeparation.Approx
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

namespace GaussianDepthSeparation

open scoped RealInnerProductSpace
open Real

noncomputable section

/-- The squaring function is `2R`-Lipschitz on `[-R,R]`. -/
lemma sq_lipschitz {R : ℝ} :
    ∀ s ∈ Set.Icc (-R) R, ∀ t ∈ Set.Icc (-R) R,
      |s ^ 2 - t ^ 2| ≤ (2 * R) * |s - t| := by
  intro s hs t ht
  obtain ⟨hs1, hs2⟩ := hs
  obtain ⟨ht1, ht2⟩ := ht
  have hfac : s ^ 2 - t ^ 2 = (s - t) * (s + t) := by ring
  rw [hfac, abs_mul]
  have hst : |s + t| ≤ 2 * R := by
    calc |s + t| ≤ |s| + |t| := abs_add_le _ _
      _ ≤ R + R := add_le_add (abs_le.mpr ⟨hs1, hs2⟩) (abs_le.mpr ⟨ht1, ht2⟩)
      _ = 2 * R := by ring
  calc |s - t| * |s + t| ≤ |s - t| * (2 * R) := by
        apply mul_le_mul_of_nonneg_left hst (abs_nonneg _)
    _ = 2 * R * |s - t| := by ring

/-- Product-to-flat indexing for paired second-layer ramps. -/
def e2 (M : ℕ) : Fin M × Fin 2 ≃ Fin (M * 2) := finProdFinEquiv

/-- Output coefficient of a paired hinge ramp. -/
def a2sq (a b : ℝ) (M : ℕ) (g : ℝ → ℝ) (k : Fin (M * 2)) : ℝ :=
  if ((e2 M).symm k).2 = 0 then gslope a b M g (((e2 M).symm k).1 : ℕ)
  else -gslope a b M g (((e2 M).symm k).1 : ℕ)

/-- The function `s ↦ sin(κs)` is `κ`-Lipschitz when `κ ≥ 0`. -/
lemma sinκ_lipschitz {κ : ℝ} (hκ : 0 ≤ κ) (a b : ℝ) :
    ∀ s ∈ Set.Icc a b, ∀ t ∈ Set.Icc a b,
      |Real.sin (κ * s) - Real.sin (κ * t)| ≤ κ * |s - t| := by
  intro s _ t _
  calc
    |Real.sin (κ * s) - Real.sin (κ * t)| ≤ |κ * s - κ * t| :=
      Real.abs_sin_sub_sin_le _ _
    _ = κ * |s - t| := by rw [← mul_sub, abs_mul, abs_of_nonneg hκ]

/-- Bound a uniform-grid point by the right endpoint. -/
lemma abs_gpt_le {a b : ℝ} {N : ℕ} (hab : a < b) (hN : 0 < N) {k : ℕ}
    (hk : k ≤ N) (hB : |a| ≤ b ∨ 0 ≤ a) : |gpt a b N k| ≤ b := by
  obtain ⟨h1, h2⟩ := gpt_mem hab hN hk
  rw [abs_le]
  refine ⟨?_, h2⟩
  rcases hB with hB | hB
  · rw [abs_le] at hB
    linarith [hB.2, h1]
  · linarith [h1, hB]

end

end GaussianDepthSeparation
