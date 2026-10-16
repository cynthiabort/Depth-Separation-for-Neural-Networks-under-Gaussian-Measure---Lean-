/-
GaussianDepthSeparation §2 — Hermite ridge identity (Lemma 2.1).

Lemma 2.1 is proved by strong induction from the three-term recurrence
`h_{n+1}(z) = z·h_n(z) − n·h_{n−1}(z)` — pure finite multi-index algebra
(no generating functions): multiplying the level-`n` ridge sum by
`⟨v,x⟩ = ∑ᵢ vᵢxᵢ` raises/lowers one coordinate index, and the two index
shifts `α ± eᵢ` rearrange into the levels `n+1` and `n−1`.
-/
import GaussianDepthSeparation.Spectral

namespace GaussianDepthSeparation

open MeasureTheory Polynomial
open scoped RealInnerProductSpace Nat

noncomputable section

/-! ### The three-term recurrence, function level -/

/-- `h_{n+1}(z) = z·h_n(z) − n·h_{n−1}(z)` (with the `ℕ`-subtraction convention;
for `n = 0` the last term has coefficient `0`). -/
lemma hfun_succ_eq (n : ℕ) (z : ℝ) :
    hfun (n + 1) z = z * hfun n z - n * hfun (n - 1) z := by
  rw [hfun_eq_hR_eval, hR_succ, Polynomial.eval_sub, Polynomial.eval_mul,
    Polynomial.eval_X, derivative_hR, Polynomial.eval_mul, Polynomial.eval_natCast,
    hfun_eq_hR_eval, hfun_eq_hR_eval]

/-- The raising form: `z·h_k(z) = h_{k+1}(z) + k·h_{k−1}(z)`. -/
lemma mul_hfun_eq (k : ℕ) (z : ℝ) :
    z * hfun k z = hfun (k + 1) z + k * hfun (k - 1) z := by
  rw [hfun_succ_eq]; ring

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

/-- Splitting the tensor Hermite at coordinate `i`. -/
lemma Hfun_split {d : ℕ} (i : Fin d) (α : MIdx d) (x : Vec d) :
    Hfun α x = hfun (α i) (x i) * ∏ j ∈ Finset.univ.erase i, hfun (α j) (x j) :=
  (Finset.mul_prod_erase Finset.univ (fun j => hfun (α j) (x j)) (Finset.mem_univ i)).symm

lemma Hfun_addE {d : ℕ} (i : Fin d) (α : MIdx d) (x : Vec d) :
    Hfun (addE i α) x
      = hfun (α i + 1) (x i) * ∏ j ∈ Finset.univ.erase i, hfun (α j) (x j) := by
  rw [Hfun_split i (addE i α) x, addE_apply_self]
  congr 1
  exact Finset.prod_congr rfl fun j hj => by
    rw [addE_apply_ne (Finset.ne_of_mem_erase hj)]

lemma Hfun_subE {d : ℕ} (i : Fin d) (α : MIdx d) (x : Vec d) :
    Hfun (subE i α) x
      = hfun (α i - 1) (x i) * ∏ j ∈ Finset.univ.erase i, hfun (α j) (x j) := by
  rw [Hfun_split i (subE i α) x, subE_apply_self]
  congr 1
  exact Finset.prod_congr rfl fun j hj => by
    rw [subE_apply_ne (Finset.ne_of_mem_erase hj)]

/-- The coordinate raising/lowering identity:
`xᵢ·H_α(x) = H_{α+eᵢ}(x) + αᵢ·H_{α−eᵢ}(x)`. -/
lemma coord_mul_Hfun {d : ℕ} (i : Fin d) (α : MIdx d) (x : Vec d) :
    x i * Hfun α x = Hfun (addE i α) x + (α i : ℝ) * Hfun (subE i α) x := by
  rw [Hfun_split i α x, Hfun_addE, Hfun_subE, ← mul_assoc, mul_hfun_eq (α i) (x i)]
  ring

/-- `∑ᵢ vᵢ² = 1` for a unit vector. -/
lemma sum_sq_eq_one {d : ℕ} {v : Vec d} (hv : ‖v‖ = 1) : ∑ i, v i ^ 2 = 1 := by
  have h : ⟪v, v⟫ = (1 : ℝ) := by
    rw [real_inner_self_eq_norm_sq, hv, one_pow]
  rw [PiLp.inner_apply] at h
  simpa [RCLike.inner_apply, pow_two] using h

/-! ### The two reindexing sums -/

/-- Raising sum: shifting `β = α + eᵢ` and summing over `i` gives the level-`n+1`
ridge sum. -/
lemma raising_sum {d : ℕ} (n : ℕ) (v x : Vec d) :
    ∑ i, ∑ α ∈ idxOf d n,
        ((n ! : ℝ) / (mfact α : ℝ)) * (v i * mpow v α) * Hfun (addE i α) x
      = ∑ β ∈ idxOf d (n + 1),
          (((n + 1)! : ℝ) / (mfact β : ℝ)) * mpow v β * Hfun β x := by
  have hstep : ∀ i : Fin d,
      ∑ α ∈ idxOf d n, ((n ! : ℝ) / (mfact α : ℝ)) * (v i * mpow v α) * Hfun (addE i α) x
        = ∑ β ∈ idxOf d (n + 1),
            ((n ! : ℝ) * (β i : ℝ) / (mfact β : ℝ)) * mpow v β * Hfun β x := by
    intro i
    have hbij : ∑ α ∈ idxOf d n,
        ((n ! : ℝ) / (mfact α : ℝ)) * (v i * mpow v α) * Hfun (addE i α) x
        = ∑ β ∈ (idxOf d (n + 1)).filter (fun β => 0 < β i),
            ((n ! : ℝ) * (β i : ℝ) / (mfact β : ℝ)) * mpow v β * Hfun β x := by
      refine Finset.sum_nbij' (addE i) (subE i)
        (fun α hα => Finset.mem_filter.mpr ⟨addE_mem hα, by simp⟩)
        (fun β hβ => subE_mem (Finset.mem_filter.mp hβ).1 (Finset.mem_filter.mp hβ).2)
        (fun α _ => subE_addE i α)
        (fun β hβ => addE_subE (Finset.mem_filter.mp hβ).2)
        (fun α hα => ?_)
      rw [mfact_addE, mpow_addE, addE_apply_self]
      have h1 : ((α i : ℝ) + 1) ≠ 0 := by positivity
      have h2 : (mfact α : ℝ) ≠ 0 := mfact_ne_zero α
      push_cast
      field_simp
    rw [hbij]
    refine Finset.sum_subset (Finset.filter_subset _ _) fun β hβ hβn => ?_
    have hzero : β i = 0 := by
      by_contra h
      exact hβn (Finset.mem_filter.mpr ⟨hβ, Nat.pos_of_ne_zero h⟩)
    rw [hzero]
    simp
  rw [Finset.sum_congr rfl fun i _ => hstep i, Finset.sum_comm]
  refine Finset.sum_congr rfl fun β hβ => ?_
  have hd : mdeg β = n + 1 := mem_idxOf.mp hβ
  have hsum : ∑ i, (β i : ℝ) = (n : ℝ) + 1 := by
    have : ∑ i, β i = n + 1 := hd
    exact_mod_cast congrArg (Nat.cast : ℕ → ℝ) this
  calc ∑ i, ((n ! : ℝ) * (β i : ℝ) / (mfact β : ℝ)) * mpow v β * Hfun β x
      = (∑ i, (β i : ℝ)) * (((n ! : ℝ) / (mfact β : ℝ)) * mpow v β * Hfun β x) := by
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun i _ => by ring
    _ = (((n + 1)! : ℝ) / (mfact β : ℝ)) * mpow v β * Hfun β x := by
        rw [hsum, Nat.factorial_succ]
        push_cast
        ring

/-- Lowering sum: shifting `η = α − eᵢ` and summing over `i` gives the level-`m`
ridge sum, with the factor `∑ᵢ vᵢ² = 1`. -/
lemma lowering_sum {d : ℕ} (m : ℕ) (v x : Vec d) (hv : ‖v‖ = 1) :
    ∑ i, ∑ α ∈ idxOf d (m + 1),
        (((m + 1)! : ℝ) / (mfact α : ℝ)) * (α i : ℝ) * (v i * mpow v α)
          * Hfun (subE i α) x
      = ((m : ℝ) + 1) * ∑ η ∈ idxOf d m,
          ((m ! : ℝ) / (mfact η : ℝ)) * mpow v η * Hfun η x := by
  have hstep : ∀ i : Fin d,
      ∑ α ∈ idxOf d (m + 1),
          (((m + 1)! : ℝ) / (mfact α : ℝ)) * (α i : ℝ) * (v i * mpow v α)
            * Hfun (subE i α) x
        = v i ^ 2 * ∑ η ∈ idxOf d m,
            (((m + 1)! : ℝ) / (mfact η : ℝ)) * mpow v η * Hfun η x := by
    intro i
    have hdrop : ∑ α ∈ idxOf d (m + 1),
        (((m + 1)! : ℝ) / (mfact α : ℝ)) * (α i : ℝ) * (v i * mpow v α)
          * Hfun (subE i α) x
        = ∑ α ∈ (idxOf d (m + 1)).filter (fun α => 0 < α i),
            (((m + 1)! : ℝ) / (mfact α : ℝ)) * (α i : ℝ) * (v i * mpow v α)
              * Hfun (subE i α) x := by
      refine (Finset.sum_subset (Finset.filter_subset _ _) fun α hα hαn => ?_).symm
      have hzero : α i = 0 := by
        by_contra h
        exact hαn (Finset.mem_filter.mpr ⟨hα, Nat.pos_of_ne_zero h⟩)
      rw [hzero]
      simp
    rw [hdrop]
    have hbij : ∑ α ∈ (idxOf d (m + 1)).filter (fun α => 0 < α i),
        (((m + 1)! : ℝ) / (mfact α : ℝ)) * (α i : ℝ) * (v i * mpow v α)
          * Hfun (subE i α) x
        = ∑ η ∈ idxOf d m,
            v i ^ 2 * ((((m + 1)! : ℝ) / (mfact η : ℝ)) * mpow v η * Hfun η x) := by
      refine Finset.sum_nbij' (subE i) (addE i)
        (fun α hα => subE_mem (Finset.mem_filter.mp hα).1 (Finset.mem_filter.mp hα).2)
        (fun η hη => Finset.mem_filter.mpr ⟨addE_mem hη, by simp⟩)
        (fun α hα => addE_subE (Finset.mem_filter.mp hα).2)
        (fun η _ => subE_addE i η)
        (fun α hα => ?_)
      obtain ⟨hαm, hαi⟩ := Finset.mem_filter.mp hα
      set η := subE i α with hη
      have hrec : α = addE i η := (addE_subE hαi).symm
      rw [hrec, mfact_addE, mpow_addE, addE_apply_self]
      have h1 : ((η i : ℝ) + 1) ≠ 0 := by positivity
      have h2 : (mfact η : ℝ) ≠ 0 := mfact_ne_zero η
      push_cast
      field_simp
    rw [hbij, ← Finset.mul_sum]
  rw [Finset.sum_congr rfl fun i _ => hstep i, ← Finset.sum_mul, sum_sq_eq_one hv,
    one_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun η hη => ?_
  rw [Nat.factorial_succ]
  push_cast
  ring

/-- The key raising identity for the ridge sums:
`⟨v,x⟩·S_n = S_{n+1} + n·S_{n−1}`. -/
lemma inner_mul_ridge_sum {d : ℕ} (n : ℕ) (v x : Vec d) (hv : ‖v‖ = 1) :
    ⟪v, x⟫ * ∑ α ∈ idxOf d n, ((n ! : ℝ) / (mfact α : ℝ)) * mpow v α * Hfun α x
      = (∑ β ∈ idxOf d (n + 1), (((n + 1)! : ℝ) / (mfact β : ℝ)) * mpow v β * Hfun β x)
        + n * ∑ η ∈ idxOf d (n - 1),
            (((n - 1)! : ℝ) / (mfact η : ℝ)) * mpow v η * Hfun η x := by
  have hinner : ⟪v, x⟫ = ∑ i, v i * x i := by
    rw [PiLp.inner_apply]
    simp [RCLike.inner_apply, mul_comm]
  rw [hinner, Finset.sum_mul]
  have hsplit : ∀ i : Fin d,
      (v i * x i) * ∑ α ∈ idxOf d n, ((n ! : ℝ) / (mfact α : ℝ)) * mpow v α * Hfun α x
        = (∑ α ∈ idxOf d n,
            ((n ! : ℝ) / (mfact α : ℝ)) * (v i * mpow v α) * Hfun (addE i α) x)
          + ∑ α ∈ idxOf d n,
              ((n ! : ℝ) / (mfact α : ℝ)) * (α i : ℝ) * (v i * mpow v α)
                * Hfun (subE i α) x := by
    intro i
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun α hα => ?_
    have hkey := coord_mul_Hfun i α x
    calc (v i * x i) * (((n ! : ℝ) / (mfact α : ℝ)) * mpow v α * Hfun α x)
        = ((n ! : ℝ) / (mfact α : ℝ)) * (v i * mpow v α) * (x i * Hfun α x) := by ring
      _ = ((n ! : ℝ) / (mfact α : ℝ)) * (v i * mpow v α)
            * (Hfun (addE i α) x + (α i : ℝ) * Hfun (subE i α) x) := by rw [hkey]
      _ = ((n ! : ℝ) / (mfact α : ℝ)) * (v i * mpow v α) * Hfun (addE i α) x
            + ((n ! : ℝ) / (mfact α : ℝ)) * (α i : ℝ) * (v i * mpow v α)
              * Hfun (subE i α) x := by ring
  rw [Finset.sum_congr rfl fun i _ => hsplit i, Finset.sum_add_distrib, raising_sum]
  congr 1
  rcases n with _ | m
  · -- n = 0: every α ∈ idxOf d 0 has α i = 0, so the lowering block vanishes
    have hz : ∀ i : Fin d, ∑ α ∈ idxOf d 0,
        ((0! : ℝ) / (mfact α : ℝ)) * (α i : ℝ) * (v i * mpow v α)
          * Hfun (subE i α) x = 0 := by
      intro i
      refine Finset.sum_eq_zero fun α hα => ?_
      have h0 : mdeg α = 0 := mem_idxOf.mp hα
      have : α i = 0 := by
        have := Finset.sum_eq_zero_iff.mp h0 i (Finset.mem_univ i)
        exact this
      rw [this]
      simp
    rw [Finset.sum_congr rfl fun i _ => hz i]
    simp
  · -- n = m + 1: the lowering sum
    rw [lowering_sum m v x hv]
    have hred : m + 1 - 1 = m := rfl
    rw [hred]
    push_cast
    ring

/- LaTeX — `main.tex`, Lemma 2.1 (Hermite ridge identity):
"For every $n \in \mathbb{N}$, $v \in S^{d-1}$, and $x \in \mathbb{R}^d$,
$$h_n(\langle v, x\rangle) = \sum_{|\alpha|=n}\frac{n!}{\alpha!}v^\alpha H_\alpha(x).$$"
-/
/-- **Lemma 2.1 (Hermite ridge identity).** -/
theorem hermite_ridge_identity {d : ℕ} (n : ℕ) (v : Vec d) (hv : ‖v‖ = 1)
    (x : Vec d) :
    hfun n ⟪v, x⟫ =
      ∑ α ∈ idxOf d n, ((n ! : ℝ) / (mfact α : ℝ)) * mpow v α * Hfun α x := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases n with _ | m
    · -- base case n = 0
      rw [idxOf, Finset.Nat.antidiagonalTuple_zero_right, Finset.sum_singleton]
      simp [mfact, mpow, Hfun]
    · -- step: h_{m+1} = z·h_m − m·h_{m−1}, then the raising identity
      have h1 := ih m (by omega)
      have h2 := ih (m - 1) (by omega)
      rw [hfun_succ_eq m ⟪v, x⟫, h1, h2, inner_mul_ridge_sum m v x hv]
      ring

end

end GaussianDepthSeparation
