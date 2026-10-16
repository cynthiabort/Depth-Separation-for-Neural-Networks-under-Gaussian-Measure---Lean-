/-
GaussianDepthSeparation §2 — Hermite ridge identity (Lemma 2.1).

As in the manuscript, factor the exponential generating function over the
coordinates, expand the product, and compare the degree-`n` coefficients.
The one-variable generating-function infrastructure is in `HermiteGenerating`.
-/
import GaussianDepthSeparation.Spectral
import GaussianDepthSeparation.HermiteGenerating

namespace GaussianDepthSeparation

open MeasureTheory Polynomial
open scoped RealInnerProductSpace Nat

noncomputable section

/-! ### Index-shift vocabulary -/

/-- `α + eᵢ`. -/
def addE {d : ℕ} (i : Fin d) (α : MIdx d) : MIdx d := Function.update α i (α i + 1)

/-- `α − eᵢ` (`ℕ`-truncated). -/
def subE {d : ℕ} (i : Fin d) (α : MIdx d) : MIdx d := Function.update α i (α i - 1)

@[simp] lemma addE_apply_self {d : ℕ} (i : Fin d) (α : MIdx d) :
    addE i α i = α i + 1 := by simp [addE]

lemma addE_apply_ne {d : ℕ} {i j : Fin d} (h : j ≠ i) (α : MIdx d) :
    addE i α j = α j := by simp [addE, h]

@[simp] lemma subE_apply_self {d : ℕ} (i : Fin d) (α : MIdx d) :
    subE i α i = α i - 1 := by simp [subE]

lemma subE_apply_ne {d : ℕ} {i j : Fin d} (h : j ≠ i) (α : MIdx d) :
    subE i α j = α j := by simp [subE, h]

lemma subE_addE {d : ℕ} (i : Fin d) (α : MIdx d) : subE i (addE i α) = α := by
  funext j
  by_cases h : j = i
  · subst h; simp
  · rw [subE_apply_ne h, addE_apply_ne h]

lemma addE_subE {d : ℕ} {i : Fin d} {β : MIdx d} (h : 0 < β i) :
    addE i (subE i β) = β := by
  funext j
  by_cases hj : j = i
  · subst hj
    have : β j - 1 + 1 = β j := Nat.succ_pred_eq_of_pos h
    simpa [addE, subE] using this
  · rw [addE_apply_ne hj, subE_apply_ne hj]

lemma mdeg_addE {d : ℕ} (i : Fin d) (α : MIdx d) : mdeg (addE i α) = mdeg α + 1 := by
  unfold mdeg addE
  rw [Finset.sum_update_of_mem (Finset.mem_univ i), Finset.sdiff_singleton_eq_erase,
    ← Finset.add_sum_erase Finset.univ α (Finset.mem_univ i)]
  ring

lemma mdeg_subE {d : ℕ} {i : Fin d} {β : MIdx d} (h : 0 < β i) :
    mdeg (subE i β) = mdeg β - 1 := by
  have h2 := mdeg_addE i (subE i β)
  rw [addE_subE h] at h2
  omega

lemma addE_mem {d n : ℕ} {i : Fin d} {α : MIdx d} (h : α ∈ idxOf d n) :
    addE i α ∈ idxOf d (n + 1) := by
  rw [mem_idxOf] at h ⊢
  rw [mdeg_addE, h]

lemma subE_mem {d n : ℕ} {i : Fin d} {β : MIdx d} (hb : β ∈ idxOf d (n + 1))
    (h : 0 < β i) : subE i β ∈ idxOf d n := by
  rw [mem_idxOf] at hb ⊢
  rw [mdeg_subE h, hb]
  omega

lemma mfact_addE {d : ℕ} (i : Fin d) (α : MIdx d) :
    (mfact (addE i α) : ℝ) = ((α i : ℝ) + 1) * (mfact α : ℝ) := by
  have h1 : mfact (addE i α)
      = (α i + 1)! * ∏ j ∈ Finset.univ.erase i, (α j)! := by
    rw [mfact, ← Finset.mul_prod_erase Finset.univ (fun j => (addE i α j)!)
      (Finset.mem_univ i), addE_apply_self]
    congr 1
    exact Finset.prod_congr rfl fun j hj => by
      rw [addE_apply_ne (Finset.ne_of_mem_erase hj)]
  have h2 : mfact α = (α i)! * ∏ j ∈ Finset.univ.erase i, (α j)! := by
    rw [mfact, ← Finset.mul_prod_erase Finset.univ (fun j => (α j)!) (Finset.mem_univ i)]
  rw [h1, h2, Nat.factorial_succ]
  push_cast
  ring

lemma mpow_addE {d : ℕ} (v : Vec d) (i : Fin d) (α : MIdx d) :
    mpow v (addE i α) = v i * mpow v α := by
  have h1 : mpow v (addE i α)
      = v i ^ (α i + 1) * ∏ j ∈ Finset.univ.erase i, v j ^ α j := by
    rw [mpow, ← Finset.mul_prod_erase Finset.univ (fun j => v j ^ addE i α j)
      (Finset.mem_univ i), addE_apply_self]
    congr 1
    exact Finset.prod_congr rfl fun j hj => by
      rw [addE_apply_ne (Finset.ne_of_mem_erase hj)]
  have h2 : mpow v α = v i ^ α i * ∏ j ∈ Finset.univ.erase i, v j ^ α j := by
    rw [mpow, ← Finset.mul_prod_erase Finset.univ (fun j => v j ^ α j) (Finset.mem_univ i)]
  rw [h1, h2, pow_succ]
  ring

/-- `∑ᵢ vᵢ² = 1` for a unit vector. -/
lemma sum_sq_eq_one {d : ℕ} {v : Vec d} (hv : ‖v‖ = 1) : ∑ i, v i ^ 2 = 1 := by
  have h : ⟪v, v⟫ = (1 : ℝ) := by
    rw [real_inner_self_eq_norm_sq, hv, one_pow]
  rw [PiLp.inner_apply] at h
  simpa [RCLike.inner_apply, pow_two] using h

/- LaTeX — `main.tex`, Lemma 2.1 (Hermite ridge identity):
"For every $n \in \mathbb{N}$, $v \in S^{d-1}$, and $x \in \mathbb{R}^d$,
$$h_n(\langle v, x\rangle) = \sum_{|\alpha|=n}\frac{n!}{\alpha!}v^\alpha H_\alpha(x).$$"
-/
/-- **Lemma 2.1 (Hermite ridge identity).** -/
theorem hermite_ridge_identity {d : ℕ} (n : ℕ) (v : Vec d) (hv : ‖v‖ = 1)
    (x : Vec d) :
    hfun n ⟪v, x⟫ =
      ∑ α ∈ idxOf d n, ((n ! : ℝ) / (mfact α : ℝ)) * mpow v α * Hfun α x := by
  classical
  have hinner : ⟪v, x⟫ = ∑ i, v i * x i := by
    rw [PiLp.inner_apply]
    simp [RCLike.inner_apply, mul_comm]
  -- exp(t⟨v,x⟩ - t²/2) = ∏ᵢ exp(tvᵢxᵢ - (tvᵢ)²/2).
  have hexponent :
      (∑ i, PowerSeries.rescale (v i) (HermiteGenerating.exponent (x i))) =
        HermiteGenerating.exponent ⟪v, x⟫ := by
    simp_rw [HermiteGenerating.rescale_exponent]
    rw [Finset.sum_sub_distrib, ← Finset.sum_mul, ← map_sum,
      ← Finset.sum_mul, ← map_sum, ← Finset.sum_div, sum_sq_eq_one hv,
      HermiteGenerating.exponent, hinner]
  have hproduct : HermiteGenerating.series ⟪v, x⟫ =
      ∏ i, PowerSeries.rescale (v i) (HermiteGenerating.series (x i)) := by
    rw [← HermiteGenerating.generating_function, ← hexponent,
      HermiteGenerating.formalExp_sum]
    · apply Finset.prod_congr rfl
      intro i _
      rw [← HermiteGenerating.rescale_formalExp _ (HermiteGenerating.constant_exponent _),
        HermiteGenerating.generating_function]
    · intro i _
      rw [← PowerSeries.coeff_zero_eq_constantCoeff, PowerSeries.coeff_rescale,
        pow_zero, one_mul, PowerSeries.coeff_zero_eq_constantCoeff,
        HermiteGenerating.constant_exponent]
  -- Compare the coefficients of tⁿ, and multiply by n!.
  have hcoeff := congrArg (PowerSeries.coeff n) hproduct
  rw [HermiteGenerating.coeff_series, HermiteGenerating.coeff_prod_series] at hcoeff
  calc
    hfun n ⟪v, x⟫ = (n ! : ℝ) * (hfun n ⟪v, x⟫ / (n ! : ℝ)) := by
      field_simp
    _ = (n ! : ℝ) * ∑ α ∈ idxOf d n, mpow v α * Hfun α x / (mfact α : ℝ) := by
      rw [hcoeff]
    _ = _ := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun _ _ => by ring

end

end GaussianDepthSeparation
