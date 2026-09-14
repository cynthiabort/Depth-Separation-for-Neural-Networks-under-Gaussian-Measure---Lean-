/-
Euclidean vectors and coordinate estimates, shared by the analytic and network modules.
-/
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace GaussianDepthSeparation

open scoped RealInnerProductSpace

noncomputable section

/-- Euclidean `ℝ^d`, carrying the ℓ² inner product. -/
abbrev Vec (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-- The squared Euclidean norm in coordinates. -/
lemma norm_sq_eq_sum {d : ℕ} (x : Vec d) : ‖x‖ ^ 2 = ∑ i, x i ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, PiLp.inner_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [RCLike.inner_apply, conj_trivial, pow_two]

/-- Every Euclidean coordinate is bounded by the norm. -/
lemma abs_coord_le_norm {d : ℕ} (x : Vec d) (i : Fin d) : |x i| ≤ ‖x‖ := by
  have hcoord : (x i) ^ 2 ≤ ∑ j, (x j) ^ 2 :=
    Finset.single_le_sum (f := fun j => (x j) ^ 2) (fun j _ => sq_nonneg _)
      (Finset.mem_univ i)
  rw [← norm_sq_eq_sum] at hcoord
  calc
    |x i| = Real.sqrt ((x i) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
    _ ≤ Real.sqrt (‖x‖ ^ 2) := Real.sqrt_le_sqrt hcoord
    _ = ‖x‖ := by rw [Real.sqrt_sq (norm_nonneg _)]

end

end GaussianDepthSeparation
