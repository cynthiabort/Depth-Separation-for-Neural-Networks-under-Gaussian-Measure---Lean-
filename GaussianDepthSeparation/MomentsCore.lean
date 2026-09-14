/-
GaussianDepthSeparation — the Gaussian-moment engine behind §3 (M8):
- coordinate sign-flip and permutation symmetries of `γ^d` and the sphere moments,
- odd-moment vanishing,
- the multinomial theorem over `idxOf` (raising-sum reindexing),
- Gaussian product moments `𝔼[X^α] = ∏ (αᵢ−1)!!`,
- the norm moments `𝔼[‖X‖^{2m}] = d(d+2)⋯(d+2m−2)` by a Stein recursion,
- the radius–direction factorization `𝔼[X^α] = 𝔼[‖X‖^n]·𝔼[V^α]` (Haar trick).
-/
import GaussianDepthSeparation.Radialization

namespace GaussianDepthSeparation

open MeasureTheory ProbabilityTheory Polynomial Filter
open scoped RealInnerProductSpace ENNReal Nat Topology

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

noncomputable section

/-! ### Sign-flip and permutation symmetries -/

/-- Negate the `i`-th coordinate: an isometry of `ℝ^d`. -/
def flipLIE (d : ℕ) (i : Fin d) : Vec d ≃ₗᵢ[ℝ] Vec d :=
  LinearIsometryEquiv.piLpCongrRight 2
    (fun j => if j = i then LinearIsometryEquiv.neg ℝ else LinearIsometryEquiv.refl ℝ ℝ)

lemma flipLIE_apply_self {d : ℕ} (i : Fin d) (x : Vec d) :
    flipLIE d i x i = -(x i) := by
  simp [flipLIE, LinearIsometryEquiv.piLpCongrRight_apply]

lemma flipLIE_apply_ne {d : ℕ} {i j : Fin d} (h : j ≠ i) (x : Vec d) :
    flipLIE d i x j = x j := by
  simp [flipLIE, LinearIsometryEquiv.piLpCongrRight_apply, h]

lemma measurePreserving_flipLIE (d : ℕ) (i : Fin d) :
    MeasurePreserving (flipLIE d i) (γ d) (γ d) :=
  ⟨(flipLIE d i).continuous.measurable, by rw [γ]; exact stdGaussian_map (flipLIE d i)⟩

/-- `u^α` changes sign under an odd-coordinate flip. -/
lemma mpow_flipLIE {d : ℕ} (i : Fin d) {α : MIdx d} (hodd : Odd (α i)) (u : Vec d) :
    mpow (flipLIE d i u) α = -mpow u α := by
  rw [mpow, mpow,
    ← Finset.mul_prod_erase Finset.univ (fun j => flipLIE d i u j ^ α j) (Finset.mem_univ i),
    ← Finset.mul_prod_erase Finset.univ (fun j => u j ^ α j) (Finset.mem_univ i),
    flipLIE_apply_self, hodd.neg_pow]
  have hprod : ∏ j ∈ Finset.univ.erase i, flipLIE d i u j ^ α j
      = ∏ j ∈ Finset.univ.erase i, u j ^ α j :=
    Finset.prod_congr rfl fun j hj => by
      rw [flipLIE_apply_ne (Finset.ne_of_mem_erase hj)]
  rw [hprod]
  ring

/-- General change of variables for `sphereMoment` along a Gaussian-preserving
norm-preserving map. -/
lemma sphereMoment_comp_map {d : ℕ} (α : MIdx d) {T : Vec d → Vec d}
    (hT : MeasurePreserving T (γ d) (γ d)) (hnorm : ∀ x, ‖T x‖ = ‖x‖) :
    sphereMoment d α = ∫ x, mpow (‖x‖⁻¹ • T x) α ∂(γ d) := by
  have hnormalize : Measurable fun y : Vec d => (‖y‖⁻¹ • y : Vec d) := by fun_prop
  have hasm : AEStronglyMeasurable (fun y : Vec d => mpow (‖y‖⁻¹ • y) α)
      (Measure.map T (γ d)) :=
    ((continuous_mpow α).measurable.comp hnormalize).aestronglyMeasurable
  have h := integral_map hT.aemeasurable hasm
  rw [hT.map_eq] at h
  rw [sphereMoment_eq_integral, h]
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  show mpow (‖T x‖⁻¹ • T x) α = mpow (‖x‖⁻¹ • T x) α
  have hx : (‖T x‖⁻¹ • T x : Vec d) = ‖x‖⁻¹ • T x := by rw [hnorm]
  rw [hx]

/-- **Odd sphere moments vanish** (LaTeX — `paper.tex`, Lemma 3.3:
"If some $\alpha_i$ is odd, then $\mathbb{E}[V^\alpha] = 0$"). -/
theorem sphereMoment_eq_zero_of_odd {d : ℕ} {α : MIdx d}
    (hα : ∃ i, ¬ Even (α i)) : sphereMoment d α = 0 := by
  obtain ⟨i, hi⟩ := hα
  have hodd : Odd (α i) := Nat.not_even_iff_odd.mp hi
  have h1 := sphereMoment_comp_map α (measurePreserving_flipLIE d i)
    (fun x => (flipLIE d i).norm_map x)
  have h2 : ∀ x : Vec d, mpow (‖x‖⁻¹ • flipLIE d i x) α = -mpow (‖x‖⁻¹ • x) α := by
    intro x
    have hsmul : (‖x‖⁻¹ • flipLIE d i x : Vec d) = flipLIE d i (‖x‖⁻¹ • x) := by
      rw [map_smul]
    rw [hsmul, mpow_flipLIE i hodd]
  rw [integral_congr_ae (ae_of_all _ h2), integral_neg, ← sphereMoment_eq_integral] at h1
  linarith

/-! ### The multinomial theorem over `idxOf` -/

/-- Raising reindexing for plain powers (the `Hfun`-free version of
`raising_sum`): `∑ᵢ ∑_{|β|=m} (m!/β!)·aᵢ·a^β = ∑_{|β'|=m+1} ((m+1)!/β'!)·a^{β'}`. -/
lemma raising_sum_pow {d : ℕ} (m : ℕ) (a : Vec d) :
    ∑ i, ∑ β ∈ idxOf d m, ((m ! : ℝ) / (mfact β : ℝ)) * (a i * mpow a β)
      = ∑ β ∈ idxOf d (m + 1), (((m + 1)! : ℝ) / (mfact β : ℝ)) * mpow a β := by
  have hstep : ∀ i : Fin d,
      ∑ β ∈ idxOf d m, ((m ! : ℝ) / (mfact β : ℝ)) * (a i * mpow a β)
        = ∑ β ∈ idxOf d (m + 1),
            ((m ! : ℝ) * (β i : ℝ) / (mfact β : ℝ)) * mpow a β := by
    intro i
    have hbij : ∑ β ∈ idxOf d m, ((m ! : ℝ) / (mfact β : ℝ)) * (a i * mpow a β)
        = ∑ β ∈ (idxOf d (m + 1)).filter (fun β => 0 < β i),
            ((m ! : ℝ) * (β i : ℝ) / (mfact β : ℝ)) * mpow a β := by
      refine Finset.sum_nbij' (addE i) (subE i)
        (fun β hβ => Finset.mem_filter.mpr ⟨addE_mem hβ, by simp⟩)
        (fun β hβ => subE_mem (Finset.mem_filter.mp hβ).1 (Finset.mem_filter.mp hβ).2)
        (fun β _ => subE_addE i β)
        (fun β hβ => addE_subE (Finset.mem_filter.mp hβ).2)
        (fun β hβ => ?_)
      rw [mfact_addE, mpow_addE, addE_apply_self]
      have h1 : ((β i : ℝ) + 1) ≠ 0 := by positivity
      have h2 : (mfact β : ℝ) ≠ 0 := mfact_ne_zero β
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
  have hd : mdeg β = m + 1 := mem_idxOf.mp hβ
  have hsum : ∑ i, (β i : ℝ) = (m : ℝ) + 1 := by
    have h : ∑ i, β i = m + 1 := hd
    exact_mod_cast congrArg (Nat.cast : ℕ → ℝ) h
  calc ∑ i, ((m ! : ℝ) * (β i : ℝ) / (mfact β : ℝ)) * mpow a β
      = (∑ i, (β i : ℝ)) * (((m ! : ℝ) / (mfact β : ℝ)) * mpow a β) := by
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun i _ => by ring
    _ = (((m + 1)! : ℝ) / (mfact β : ℝ)) * mpow a β := by
        rw [hsum, Nat.factorial_succ]
        push_cast
        ring

/-- **The multinomial theorem** over the level sets `idxOf`. -/
theorem sum_pow_multinomial {d : ℕ} (m : ℕ) (a : Vec d) :
    (∑ i, a i) ^ m
      = ∑ β ∈ idxOf d m, ((m ! : ℝ) / (mfact β : ℝ)) * mpow a β := by
  induction m with
  | zero =>
    rw [pow_zero, idxOf, Finset.Nat.antidiagonalTuple_zero_right, Finset.sum_singleton]
    simp [mfact, mpow]
  | succ m ih =>
    rw [pow_succ, ih, mul_comm, Finset.mul_sum]
    have hexp : ∑ β ∈ idxOf d m, (∑ i, a i) * (((m ! : ℝ) / (mfact β : ℝ)) * mpow a β)
        = ∑ i, ∑ β ∈ idxOf d m, ((m ! : ℝ) / (mfact β : ℝ)) * (a i * mpow a β) := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun β _ => ?_
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => by ring
    rw [hexp, raising_sum_pow]

/-! ### Gaussian product moments -/

/-- `𝔼[X^α] = ∏ᵢ (αᵢ−1)!!` (zero when some `αᵢ` is odd). -/
theorem integral_mpow_gaussian {d : ℕ} (α : MIdx d) :
    ∫ x, mpow x α ∂(γ d)
      = ∏ i, (if Even (α i) then (((α i - 1)‼ : ℕ) : ℝ) else 0) := by
  rw [integral_gaussD_eq_pi _ (continuous_mpow α).aestronglyMeasurable]
  have hrw : (fun y : Fin d → ℝ => mpow (WithLp.toLp 2 y) α)
      = fun y => ∏ i, (fun t => t ^ α i) (y i) := by
    funext y
    rw [mpow]
  rw [hrw, MeasureTheory.integral_fintype_prod_eq_prod
    (f := fun i (t : ℝ) => t ^ α i)]
  exact Finset.prod_congr rfl fun i _ => integral_pow_gaussian (α i)

/-- Integrability of monomials under `γ^d`. -/
lemma integrable_mpow {d : ℕ} (α : MIdx d) : Integrable (fun x => mpow x α) (γ d) := by
  rw [integrable_gaussD_iff_pi _ (continuous_mpow α).aestronglyMeasurable]
  have hrw : (fun y : Fin d → ℝ => mpow (WithLp.toLp 2 y) α)
      = fun y => ∏ i, (fun t => t ^ α i) (y i) := by
    funext y
    rw [mpow]
  rw [hrw]
  refine Integrable.fintype_prod fun i => ?_
  have h : Integrable (fun t : ℝ => t ^ α i) γ₁ := by
    have h2 := integrable_polyEval_gaussian (X ^ α i)
    refine h2.congr (ae_of_all _ fun t => ?_)
    simp only [Polynomial.eval_pow, Polynomial.eval_X]
  exact h

/-! ### The norm moments `𝔼‖X‖^{2m}` (Stein-sum recursion) -/

/-- `D(β) = ∏ᵢ (2βᵢ−1)!!`. -/
def dfProd {d : ℕ} (β : MIdx d) : ℝ := ∏ i, (((2 * β i - 1)‼ : ℕ) : ℝ)

/-- The Stein sum `S_m = ∑_{|β|=m} (m!/β!)·D(β)` (which is `𝔼‖X‖^{2m}`). -/
def steinSum (d m : ℕ) : ℝ :=
  ∑ β ∈ idxOf d m, ((m ! : ℝ) / (mfact β : ℝ)) * dfProd β

lemma dfProd_addE {d : ℕ} (i : Fin d) (β : MIdx d) :
    dfProd (addE i β) = (2 * (β i : ℝ) + 1) * dfProd β := by
  rw [dfProd, dfProd,
    ← Finset.mul_prod_erase Finset.univ
      (fun j => (((2 * addE i β j - 1)‼ : ℕ) : ℝ)) (Finset.mem_univ i),
    ← Finset.mul_prod_erase Finset.univ
      (fun j => (((2 * β j - 1)‼ : ℕ) : ℝ)) (Finset.mem_univ i)]
  have hprod : ∏ j ∈ Finset.univ.erase i, (((2 * addE i β j - 1)‼ : ℕ) : ℝ)
      = ∏ j ∈ Finset.univ.erase i, (((2 * β j - 1)‼ : ℕ) : ℝ) :=
    Finset.prod_congr rfl fun j hj => by
      rw [addE_apply_ne (Finset.ne_of_mem_erase hj)]
  rw [hprod, addE_apply_self]
  have hval : ((2 * (β i + 1) - 1)‼ : ℕ) = (2 * β i + 1) * (2 * β i - 1)‼ := by
    have h1 : 2 * (β i + 1) - 1 = 2 * β i + 1 := by omega
    rw [h1]
    exact Nat.doubleFactorial_add_one (2 * β i)
  rw [hval]
  push_cast
  ring

/-- The Stein recursion `S_{m+1} = (d + 2m)·S_m`. -/
lemma steinSum_succ (d m : ℕ) :
    steinSum d (m + 1) = ((d : ℝ) + 2 * m) * steinSum d m := by
  have hstep : ∀ i : Fin d,
      ∑ β' ∈ idxOf d (m + 1), ((m ! : ℝ) * (β' i : ℝ) / (mfact β' : ℝ)) * dfProd β'
        = ∑ β ∈ idxOf d m,
            ((m ! : ℝ) / (mfact β : ℝ)) * ((2 * (β i : ℝ) + 1) * dfProd β) := by
    intro i
    have hdrop : ∑ β' ∈ idxOf d (m + 1),
        ((m ! : ℝ) * (β' i : ℝ) / (mfact β' : ℝ)) * dfProd β'
        = ∑ β' ∈ (idxOf d (m + 1)).filter (fun β' => 0 < β' i),
            ((m ! : ℝ) * (β' i : ℝ) / (mfact β' : ℝ)) * dfProd β' := by
      refine (Finset.sum_subset (Finset.filter_subset _ _) fun β' hβ' hβn => ?_).symm
      have hzero : β' i = 0 := by
        by_contra h
        exact hβn (Finset.mem_filter.mpr ⟨hβ', Nat.pos_of_ne_zero h⟩)
      rw [hzero]
      simp
    rw [hdrop]
    refine Finset.sum_nbij' (subE i) (addE i)
      (fun β' hβ' => subE_mem (Finset.mem_filter.mp hβ').1 (Finset.mem_filter.mp hβ').2)
      (fun β hβ => Finset.mem_filter.mpr ⟨addE_mem hβ, by simp⟩)
      (fun β' hβ' => addE_subE (Finset.mem_filter.mp hβ').2)
      (fun β _ => subE_addE i β)
      (fun β' hβ' => ?_)
    obtain ⟨hβm, hβi⟩ := Finset.mem_filter.mp hβ'
    set β := subE i β' with hβdef
    have hrec : β' = addE i β := (addE_subE hβi).symm
    rw [hrec, mfact_addE, dfProd_addE, addE_apply_self]
    have h1 : ((β i : ℝ) + 1) ≠ 0 := by positivity
    have h2 : (mfact β : ℝ) ≠ 0 := mfact_ne_zero β
    push_cast
    field_simp
  have htotal : steinSum d (m + 1)
      = ∑ i, ∑ β' ∈ idxOf d (m + 1),
          ((m ! : ℝ) * (β' i : ℝ) / (mfact β' : ℝ)) * dfProd β' := by
    rw [steinSum, Finset.sum_comm]
    refine Finset.sum_congr rfl fun β' hβ' => ?_
    have hd : mdeg β' = m + 1 := mem_idxOf.mp hβ'
    have hsum : ∑ i, (β' i : ℝ) = (m : ℝ) + 1 := by
      have h : ∑ i, β' i = m + 1 := hd
      exact_mod_cast congrArg (Nat.cast : ℕ → ℝ) h
    calc (((m + 1)! : ℝ) / (mfact β' : ℝ)) * dfProd β'
        = (∑ i, (β' i : ℝ)) * (((m ! : ℝ) / (mfact β' : ℝ)) * dfProd β') := by
          rw [hsum, Nat.factorial_succ]
          push_cast
          ring
      _ = ∑ i, ((m ! : ℝ) * (β' i : ℝ) / (mfact β' : ℝ)) * dfProd β' := by
          rw [Finset.sum_mul]
          exact Finset.sum_congr rfl fun i _ => by ring
  rw [htotal, Finset.sum_congr rfl fun i _ => hstep i, Finset.sum_comm, steinSum,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun β hβ => ?_
  have hd : mdeg β = m := mem_idxOf.mp hβ
  have hsum : ∑ i, (β i : ℝ) = (m : ℝ) := by
    have h : ∑ i, β i = m := hd
    exact_mod_cast congrArg (Nat.cast : ℕ → ℝ) h
  have hcard : (Finset.univ : Finset (Fin d)).card = d := by
    rw [Finset.card_univ, Fintype.card_fin]
  calc ∑ i, ((m ! : ℝ) / (mfact β : ℝ)) * ((2 * (β i : ℝ) + 1) * dfProd β)
      = (∑ i, (2 * (β i : ℝ) + 1)) * (((m ! : ℝ) / (mfact β : ℝ)) * dfProd β) := by
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun i _ => by ring
    _ = ((d : ℝ) + 2 * m) * (((m ! : ℝ) / (mfact β : ℝ)) * dfProd β) := by
        congr 1
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, hsum, Finset.sum_const, hcard]
        ring

/-- `S_m = d(d+2)⋯(d+2m−2)` in closed form. -/
lemma steinSum_eq (d m : ℕ) :
    steinSum d m = ∏ i ∈ Finset.range m, ((d : ℝ) + 2 * i) := by
  induction m with
  | zero =>
    rw [steinSum, idxOf, Finset.Nat.antidiagonalTuple_zero_right, Finset.sum_singleton]
    simp [mfact, dfProd]
  | succ m ih =>
    rw [steinSum_succ, ih, Finset.prod_range_succ]
    ring

lemma mpow_sq {d : ℕ} (x : Vec d) (β : MIdx d) :
    mpow (WithLp.toLp 2 (fun i => x i ^ 2)) β = mpow x (fun i => 2 * β i) := by
  rw [mpow, mpow]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [show (WithLp.toLp 2 fun j => x j ^ 2) i = x i ^ 2 from rfl, ← pow_mul]

/-- The pointwise multinomial expansion of `‖x‖^{2m}`. -/
lemma norm_pow_expand {d : ℕ} (m : ℕ) (x : Vec d) :
    ‖x‖ ^ (2 * m)
      = ∑ β ∈ idxOf d m, ((m ! : ℝ) / (mfact β : ℝ)) * mpow x (fun i => 2 * β i) := by
  have h1 : ‖x‖ ^ (2 * m) = (∑ i, x i ^ 2) ^ m := by
    rw [pow_mul, norm_sq_eq_sum]
  have h2 := sum_pow_multinomial m (WithLp.toLp 2 (fun i => x i ^ 2))
  have h3 : (∑ i, (WithLp.toLp 2 fun j => x j ^ 2) i) = ∑ i, x i ^ 2 := rfl
  rw [h1, ← h3, h2]
  exact Finset.sum_congr rfl fun β _ => by rw [mpow_sq]

/-- **The Gaussian norm moments**:
`𝔼‖X‖^{2m} = d(d+2)⋯(d+2m−2)` (LaTeX — `paper.tex` §3:
"$\mathbb{E}[\|G\|_2^{2m}] = \prod_{i=0}^{m-1}(d+2i)$"). -/
theorem integral_norm_pow_even (d m : ℕ) :
    ∫ x, ‖x‖ ^ (2 * m) ∂(γ d) = ∏ i ∈ Finset.range m, ((d : ℝ) + 2 * i) := by
  rw [← steinSum_eq]
  rw [integral_congr_ae (ae_of_all _ (norm_pow_expand m)),
    integral_finsetSum _ (fun β _ => (integrable_mpow _).const_mul _)]
  rw [steinSum]
  refine Finset.sum_congr rfl fun β hβ => ?_
  rw [integral_const_mul, integral_mpow_gaussian]
  congr 1
  rw [dfProd]
  exact Finset.prod_congr rfl fun i _ => by rw [ite_eq_left (even_two_mul _)]

lemma integrable_norm_pow_even (d m : ℕ) :
    Integrable (fun x : Vec d => ‖x‖ ^ (2 * m)) (γ d) := by
  rw [show (fun x : Vec d => ‖x‖ ^ (2 * m))
      = fun x => ∑ β ∈ idxOf d m, ((m ! : ℝ) / (mfact β : ℝ)) * mpow x (fun i => 2 * β i)
    from funext (norm_pow_expand m)]
  exact integrable_finsetSum _ fun β _ => (integrable_mpow _).const_mul _

lemma integrable_norm_pow (d n : ℕ) :
    Integrable (fun x : Vec d => ‖x‖ ^ n) (γ d) := by
  refine Integrable.mono' ((integrable_const (1 : ℝ)).add (integrable_norm_pow_even d n))
    (Continuous.aestronglyMeasurable (by fun_prop)) (ae_of_all _ fun x => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  rcases le_total ‖x‖ 1 with h | h
  · calc ‖x‖ ^ n ≤ 1 := pow_le_one₀ (norm_nonneg _) h
      _ ≤ 1 + ‖x‖ ^ (2 * n) := le_add_of_nonneg_right (by positivity)
  · calc ‖x‖ ^ n ≤ ‖x‖ ^ (2 * n) := pow_le_pow_right₀ h (by omega)
      _ ≤ 1 + ‖x‖ ^ (2 * n) := le_add_of_nonneg_left one_pos.le

/-! ### The radius–direction factorization (Haar trick with a weight) -/

/-- **The factorization** `𝔼[X^α] = 𝔼[‖X‖^{|α|}]·𝔼[V^α]` (LaTeX — `paper.tex` §3:
"$\mathbb{E}[G^\alpha] = \mathbb{E}[\|G\|_2^n]\mathbb{E}[V^\alpha]$"). -/
theorem mpow_factor {d : ℕ} (hd : 0 < d) (α : MIdx d) :
    ∫ x, mpow x α ∂(γ d)
      = (∫ x, ‖x‖ ^ (mdeg α) ∂(γ d)) * sphereMoment d α := by
  set n := mdeg α with hn
  -- rewrite the integrand radially
  have hae : ∀ᵐ x ∂(γ d), mpow x α = ‖x‖ ^ n * mpow (‖x‖⁻¹ • x) α := by
    have hne : ∀ᵐ x ∂(γ d), x ≠ 0 := by
      have hset : {x : Vec d | ¬ x ≠ 0} = ({0} : Set (Vec d)) := by
        ext x; simp
      rw [ae_iff, hset]
      exact gaussD_singleton_zero hd
    filter_upwards [hne] with x hx
    have hxnorm : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
    conv_lhs => rw [show x = ‖x‖ • (‖x‖⁻¹ • x) from by
      rw [smul_smul, mul_inv_cancel₀ hxnorm, one_smul]]
    rw [mpow_smul, ← hn]
  rw [integral_congr_ae hae]
  -- the weighted double average
  set G : Od d × Vec d → ℝ :=
    fun p => ‖p.2‖ ^ n * mpow (actMap p.1 (‖p.2‖⁻¹ • p.2)) α with hG
  have hGmeas : AEStronglyMeasurable G ((haarOd d).prod (γ d)) := by
    have hev : Continuous fun p : Od d × Vec d => actMap p.1 p.2 := by
      have h1 : Continuous fun p : (Vec d →L[ℝ] Vec d) × Vec d => p.1 p.2 :=
        isBoundedBilinearMap_apply.continuous
      exact h1.comp (Continuous.prodMk
        (continuous_subtype_val.comp continuous_fst) continuous_snd)
    have hnmes : Measurable fun p : Od d × Vec d => (p.1, (‖p.2‖⁻¹ • p.2 : Vec d)) := by
      fun_prop
    have hmp : Measurable fun p : Od d × Vec d => mpow (actMap p.1 (‖p.2‖⁻¹ • p.2)) α :=
      ((continuous_mpow α).comp hev).measurable.comp hnmes
    exact ((measurable_norm.comp measurable_snd).pow_const n |>.mul hmp).aestronglyMeasurable
  have hGbdd : ∀ p : Od d × Vec d, ‖G p‖ ≤ ‖p.2‖ ^ n := by
    intro p
    rw [hG, Real.norm_eq_abs, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ ‖p.2‖ ^ n)]
    have hb : |mpow (actMap p.1 (‖p.2‖⁻¹ • p.2)) α| ≤ 1 := by
      refine abs_mpow_le_one ?_ α
      rw [actMap_norm]
      rcases eq_or_ne p.2 0 with h0 | h0
      · simp [h0]
      · rw [norm_smul, norm_inv, norm_norm,
          inv_mul_cancel₀ (norm_ne_zero_iff.mpr h0)]
    calc ‖p.2‖ ^ n * |mpow (actMap p.1 (‖p.2‖⁻¹ • p.2)) α| ≤ ‖p.2‖ ^ n * 1 :=
          mul_le_mul_of_nonneg_left hb (by positivity)
      _ = ‖p.2‖ ^ n := mul_one _
  have hwint : Integrable (fun p : Od d × Vec d => ‖p.2‖ ^ n) ((haarOd d).prod (γ d)) := by
    have hmap : Measure.map (Prod.snd : Od d × Vec d → Vec d) ((haarOd d).prod (γ d))
        = γ d := by
      rw [Measure.map_snd_prod]
      simp
    have hasm2 : AEStronglyMeasurable (fun x : Vec d => ‖x‖ ^ n)
        (Measure.map (Prod.snd : Od d × Vec d → Vec d) ((haarOd d).prod (γ d))) := by
      rw [hmap]
      exact Continuous.aestronglyMeasurable (by fun_prop)
    exact (integrable_map_measure hasm2 measurable_snd.aemeasurable).mp
      (by rw [hmap]; exact integrable_norm_pow d n)
  have hGint : Integrable G ((haarOd d).prod (γ d)) :=
    Integrable.mono' hwint hGmeas (ae_of_all _ hGbdd)
  -- inner-U-first
  have hinner : ∫ x, ∫ U, G (U, x) ∂(haarOd d) ∂(γ d)
      = (∫ x, ‖x‖ ^ n ∂(γ d)) * sphereMoment d α := by
    have hae2 : ∀ᵐ x ∂(γ d), ∫ U, G (U, x) ∂(haarOd d)
        = ‖x‖ ^ n * sphereMoment d α := by
      have hne : ∀ᵐ x ∂(γ d), x ≠ 0 := by
        have hset : {x : Vec d | ¬ x ≠ 0} = ({0} : Set (Vec d)) := by
          ext x; simp
        rw [ae_iff, hset]
        exact gaussD_singleton_zero hd
      filter_upwards [hne] with x hx
      have hxu : ‖(‖x‖⁻¹ • x : Vec d)‖ = 1 := norm_smul_inv_norm hx
      rw [show (fun U => G (U, x))
          = fun U => ‖x‖ ^ n * mpow (actMap U (‖x‖⁻¹ • x)) α from rfl]
      rw [integral_const_mul, haar_orbit_moment α hxu]
    rw [integral_congr_ae hae2, integral_mul_const]
  -- inner-x-first
  have houter : ∫ U, ∫ x, G (U, x) ∂(γ d) ∂(haarOd d)
      = ∫ x, ‖x‖ ^ n * mpow (‖x‖⁻¹ • x) α ∂(γ d) := by
    have hUeq : ∀ U : Od d, ∫ x, G (U, x) ∂(γ d)
        = ∫ x, ‖x‖ ^ n * mpow (‖x‖⁻¹ • x) α ∂(γ d) := by
      intro U
      have hnormalize : Measurable fun y : Vec d =>
          (‖y‖ ^ n * mpow (‖y‖⁻¹ • y) α : ℝ) := by
        have h1 : Measurable fun y : Vec d => (‖y‖⁻¹ • y : Vec d) := by fun_prop
        exact (measurable_norm.pow_const n).mul
          ((continuous_mpow α).measurable.comp h1)
      have hptwise : ∀ x : Vec d,
          G (U, x) = ‖actMap U x‖ ^ n * mpow (‖actMap U x‖⁻¹ • actMap U x) α := by
        intro x
        show ‖x‖ ^ n * mpow (actMap U (‖x‖⁻¹ • x)) α = _
        rw [actMap_norm]
        congr 2
        show (U : Vec d →L[ℝ] Vec d) (‖x‖⁻¹ • x) = ‖x‖⁻¹ • (U : Vec d →L[ℝ] Vec d) x
        exact map_smul _ _ _
      rw [integral_congr_ae (ae_of_all _ hptwise)]
      have hasm : AEStronglyMeasurable
          (fun y : Vec d => ‖y‖ ^ n * mpow (‖y‖⁻¹ • y) α)
          (Measure.map (actMap U) (γ d)) := hnormalize.aestronglyMeasurable
      have h := integral_map (measurePreserving_actMap U).aemeasurable hasm
      rw [(measurePreserving_actMap U).map_eq] at h
      exact h.symm
    rw [integral_congr_ae (ae_of_all _ hUeq), integral_const]
    simp
  have hswap := MeasureTheory.integral_integral_swap
    (f := fun U x => G (U, x)) (by exact hGint)
  rw [← houter, hswap, hinner]

end

end GaussianDepthSeparation
