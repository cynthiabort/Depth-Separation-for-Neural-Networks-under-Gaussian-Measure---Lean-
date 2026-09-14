/-
GaussianDepthSeparation §5 — finite low-chaos projection decomposition.

This small module supplies `Plt = ∑_{n<n₀} Pn`, used both by the radial
polynomial characterization and by multivariate Hermite totality.
-/
import GaussianDepthSeparation.LowerBound
import GaussianDepthSeparation.Target

namespace GaussianDepthSeparation

open MeasureTheory ProbabilityTheory Filter
open scoped RealInnerProductSpace ENNReal Nat Topology

noncomputable section

/-- `P_n` applied to an `H_β` generator: identity if `|β| = n`, else `0`. -/
private lemma Pn_HL2 {d : ℕ} (n : ℕ) {β : MIdx d} :
    Pn d n (HL2 β) = if mdeg β = n then HL2 β else 0 := by
  by_cases h : mdeg β = n
  · rw [ite_eq_left h]
    refine Pn_of_mem ?_
    rw [chaos]
    exact Submodule.subset_span ⟨β, by rw [Finset.mem_coe, mem_idxOf]; exact h, rfl⟩
  · rw [ite_eq_right h]
    refine Pn_of_mem_ne (k := mdeg β) (fun hcon => h hcon) ?_
    rw [chaos]
    exact Submodule.subset_span ⟨β, by rw [Finset.mem_coe, mem_idxOf], rfl⟩

/-- `Plt d n₀ F = ∑_{n<n₀} P_n F` (the low-chaos projection splits by degree). -/
theorem Plt_eq_sum {d : ℕ} (n₀ : ℕ) (F : L2 d) :
    Plt d n₀ F = ∑ n ∈ Finset.range n₀, Pn d n F := by
  refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero (K := chaosLt d n₀) ?_ ?_
  · refine Submodule.sum_mem _ fun n hn => ?_
    rw [Finset.mem_range] at hn
    exact chaos_le_chaosLt hn (Submodule.starProjection_apply_mem _ _)
  · intro w hw
    rw [inner_sub_left, sub_eq_zero]
    revert hw
    refine Submodule.span_induction
      (p := fun w _ => ⟪F, w⟫ = ⟪∑ n ∈ Finset.range n₀, Pn d n F, w⟫) ?_ ?_ ?_ ?_
    · rintro x ⟨β, hβ, rfl⟩
      rw [Finset.mem_coe, mem_idxLt] at hβ
      rw [sum_inner]
      have hterm : ∀ n ∈ Finset.range n₀, ⟪Pn d n F, HL2 β⟫ =
          if mdeg β = n then ⟪F, HL2 β⟫ else 0 := by
        intro n _
        rw [Pn_self_adjoint, Pn_HL2]
        by_cases h : mdeg β = n
        · rw [ite_eq_left h, ite_eq_left h]
        · rw [ite_eq_right h, ite_eq_right h, inner_zero_right]
      rw [Finset.sum_congr rfl hterm,
        Finset.sum_ite_eq (Finset.range n₀) (mdeg β) (fun _ => ⟪F, HL2 β⟫),
        ite_eq_left (by rw [Finset.mem_range]; exact hβ)]
    · simp
    · intro x y _ _ hx hy; simp only [inner_add_right, hx, hy]
    · intro c x _ hx; simp only [inner_smul_right, hx]

end

end GaussianDepthSeparation
