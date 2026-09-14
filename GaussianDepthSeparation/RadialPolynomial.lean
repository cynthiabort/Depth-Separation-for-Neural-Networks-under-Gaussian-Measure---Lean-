/-
GaussianDepthSeparation §5 — radial low-chaos polynomial approximation (Lemma 5.1).

This module separates the Hilbert-space part of the lemma from the radial
coordinate and polynomial-identification parts.  The latter are developed
below and then combined in `radial_polynomial_distance`.
-/
import GaussianDepthSeparation.Energy

namespace GaussianDepthSeparation

open MeasureTheory Real Polynomial
open scoped RealInnerProductSpace ENNReal Nat

noncomputable section

/-- The radial part of the low-chaos space. -/
def radialChaosLt (d n₀ : ℕ) : Submodule ℝ (L2 d) :=
  radialSub d ⊓ chaosLt d n₀

/-- The low-chaos projection of a radial function is radial. -/
lemma isRadial_Plt {d n₀ : ℕ} {F : L2 d} (hF : IsRadial F) :
    IsRadial (Plt d n₀ F) := by
  rw [Plt_eq_sum]
  intro U
  rw [map_sum]
  exact Finset.sum_congr rfl fun n _ => isRadial_Pn hF n U

/-- The orthogonal low-chaos projection is an admissible radial low-chaos
approximant whenever the target is radial. -/
lemma Plt_mem_radialChaosLt {d n₀ : ℕ} {F : L2 d} (hF : IsRadial F) :
    Plt d n₀ F ∈ radialChaosLt d n₀ :=
  ⟨isRadial_Plt hF, Submodule.starProjection_apply_mem _ _⟩

/-- Hilbert-space core of Lemma 5.1: for a radial target, the squared norm of
the complementary projection is the best squared distance to the radial
low-chaos space. -/
theorem normSq_Pge_eq_iInf_radialChaosLt {d n₀ : ℕ} (F : L2 d)
    (hF : IsRadial F) :
    ‖Pge d n₀ F‖ ^ 2 = ⨅ G : radialChaosLt d n₀, ‖F - (G : L2 d)‖ ^ 2 := by
  have hPge : Pge d n₀ F = F - Plt d n₀ F := rfl
  rw [hPge]
  apply le_antisymm
  · refine le_ciInf fun G => ?_
    have hmin : ‖F - Plt d n₀ F‖ ≤ ‖F - (G : L2 d)‖ := by
      change ‖F - (chaosLt d n₀).starProjection F‖ ≤ ‖F - (G : L2 d)‖
      rw [Submodule.starProjection_minimal]
      exact ciInf_le ⟨0, Set.forall_mem_range.mpr fun _ => norm_nonneg _⟩
        (⟨G, G.2.2⟩ : chaosLt d n₀)
    exact pow_le_pow_left₀ (norm_nonneg _) hmin 2
  · refine ciInf_le_of_le
      ⟨0, Set.forall_mem_range.mpr fun _ => sq_nonneg _⟩
      (⟨Plt d n₀ F, Plt_mem_radialChaosLt hF⟩ : radialChaosLt d n₀) ?_
    simp

end

end GaussianDepthSeparation
