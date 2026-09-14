/-
GaussianDepthSeparation §3 — Spherical Moments (Lemma 3.3, Proposition 3.4, and the
remark `K_n ≤ (n/(d+n))^{n/2}` used by Theorem 1.2(i)).

Built on `MomentsCore`: odd vanishing, the factorization
`𝔼[X^α] = 𝔼[‖X‖^n]·𝔼[V^α]`, product moments and the Stein-sum norm moments.
The Hölder step of Proposition 3.4 is the weighted AM–GM inequality applied
pointwise (no `Lp` duality needed).
-/
import GaussianDepthSeparation.MomentsCore

namespace GaussianDepthSeparation

open MeasureTheory ProbabilityTheory Filter
open scoped RealInnerProductSpace ENNReal Nat Topology

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

noncomputable section

/-! ### Half-index bookkeeping -/

lemma mdeg_halfIdx {d : ℕ} {α : MIdx d} (hα : ∀ i, Even (α i)) :
    2 * mdeg (halfIdx α) = mdeg α := by
  rw [mdeg, mdeg, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  obtain ⟨k, hk⟩ := hα i
  rw [halfIdx, hk]
  omega

lemma halfIdx_double {d : ℕ} (β : MIdx d) : halfIdx (fun i => 2 * β i) = β := by
  funext i
  rw [halfIdx]
  omega

lemma double_halfIdx {d : ℕ} {η : MIdx d} (hη : ∀ i, Even (η i)) :
    (fun i => 2 * halfIdx η i) = η := by
  funext i
  obtain ⟨k, hk⟩ := hη i
  rw [halfIdx, hk]
  omega

/-- `(2k−1)!! = (2k)!/(2^k·k!)` over `ℝ`. -/
lemma doubleFactorial_cast_eq (k : ℕ) :
    (((2 * k - 1)‼ : ℕ) : ℝ) = ((2 * k)! : ℝ) / (2 ^ k * (k ! : ℝ)) := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  have h1 : (2 * k - 1) + 1 = 2 * k := by omega
  have h2 : ((2 * k - 1) + 1)! = ((2 * k - 1) + 1)‼ * (2 * k - 1)‼ :=
    Nat.factorial_eq_mul_doubleFactorial _
  rw [h1, Nat.doubleFactorial_two_mul] at h2
  have h4 : ((2 * k)! : ℝ) = (2 ^ k * (k ! : ℝ)) * (((2 * k - 1)‼ : ℕ) : ℝ) := by
    exact_mod_cast congrArg (Nat.cast : ℕ → ℝ) h2
  have h5 : ((2 : ℝ) ^ k * (k ! : ℝ)) ≠ 0 := by positivity
  rw [h4]
  field_simp

/-- `D(β) = (2β)!/(2^{|β|}·β!)`. -/
lemma dfProd_eq {d : ℕ} (β : MIdx d) :
    dfProd β = (mfact (fun i => 2 * β i) : ℝ) / (2 ^ (mdeg β) * (mfact β : ℝ)) := by
  rw [dfProd]
  have hterm : ∀ i : Fin d, (((2 * β i - 1)‼ : ℕ) : ℝ)
      = ((2 * β i)! : ℝ) / (2 ^ (β i) * ((β i)! : ℝ)) :=
    fun i => doubleFactorial_cast_eq (β i)
  rw [Finset.prod_congr rfl fun i _ => hterm i, Finset.prod_div_distrib,
    Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  rw [mfact, mfact, mdeg]
  push_cast
  rfl

/-- Gaussian product moments in factorial form (all-even case). -/
lemma integral_mpow_gaussian_even {d : ℕ} {α : MIdx d} (hα : ∀ i, Even (α i)) :
    ∫ x, mpow x α ∂(γ d)
      = (mfact α : ℝ) / (2 ^ (mdeg (halfIdx α)) * (mfact (halfIdx α) : ℝ)) := by
  rw [integral_mpow_gaussian]
  have h1 : (∏ i, if Even (α i) then (((α i - 1)‼ : ℕ) : ℝ) else 0)
      = dfProd (halfIdx α) := by
    rw [dfProd]
    refine Finset.prod_congr rfl fun i _ => ?_
    obtain ⟨k, hk⟩ := hα i
    have hki : halfIdx α i = k := by rw [halfIdx, hk]; omega
    rw [ite_eq_left (hα i), hki, show α i = 2 * k from by omega]
  rw [h1, dfProd_eq, double_halfIdx hα]

/-! ### Lemma 3.3, even case -/

/- LaTeX — `paper.tex`, Lemma 3.3:
"If all $\alpha_i$ are even, then
$$\mathbb{E}[V^\alpha] = \frac{\frac{\alpha!}{(\alpha/2)!}}
{\sum_{|\eta|=n,\ \eta\ {\rm even}}\frac{(n/2)!}{(\eta/2)!}\frac{\eta!}{(\eta/2)!}}.$$"
-/
/-- **Lemma 3.3, even case.** -/
theorem sphereMoment_of_even {d : ℕ} (hd : 0 < d) {α : MIdx d}
    (hα : ∀ i, Even (α i)) :
    sphereMoment d α =
      ((mfact α : ℝ) / (mfact (halfIdx α) : ℝ)) /
        (∑ η ∈ (idxOf d (mdeg α)).filter (fun η => ∀ i, Even (η i)),
          (((mdeg α / 2)! : ℝ) / (mfact (halfIdx η) : ℝ)) *
            ((mfact η : ℝ) / (mfact (halfIdx η) : ℝ))) := by
  set n := mdeg α with hn
  set m := mdeg (halfIdx α) with hm
  have hnm : n = 2 * m := (mdeg_halfIdx hα).symm
  have hn2 : n / 2 = m := by omega
  -- the statement's denominator equals `2^m · steinSum d m` (doubling bijection)
  have hdenom : (∑ η ∈ (idxOf d n).filter (fun η => ∀ i, Even (η i)),
      (((n / 2)! : ℝ) / (mfact (halfIdx η) : ℝ)) *
        ((mfact η : ℝ) / (mfact (halfIdx η) : ℝ)))
      = 2 ^ m * steinSum d m := by
    rw [steinSum, Finset.mul_sum, hn2]
    refine Finset.sum_nbij' (fun η => halfIdx η) (fun β => fun i => 2 * β i)
      ?_ ?_ ?_ ?_ ?_
    · intro η hη
      obtain ⟨hη1, hη2⟩ := Finset.mem_filter.mp hη
      rw [mem_idxOf]
      show mdeg (halfIdx η) = m
      have := mdeg_halfIdx hη2
      have hηn : mdeg η = n := mem_idxOf.mp hη1
      omega
    · intro β hβ
      refine Finset.mem_filter.mpr ⟨?_, fun i => ⟨β i, by show 2 * β i = β i + β i; ring⟩⟩
      rw [mem_idxOf]
      show mdeg (fun i => 2 * β i) = n
      have hβm : mdeg β = m := mem_idxOf.mp hβ
      have h2 : mdeg (fun i => 2 * β i) = 2 * mdeg β := by
        rw [mdeg, mdeg, Finset.mul_sum]
      omega
    · intro η hη
      exact double_halfIdx (Finset.mem_filter.mp hη).2
    · intro β _
      exact halfIdx_double β
    · intro η hη
      obtain ⟨hη1, hη2⟩ := Finset.mem_filter.mp hη
      rw [dfProd_eq, double_halfIdx hη2]
      have hdeg : mdeg (halfIdx η) = m := by
        have := mdeg_halfIdx hη2
        have hηn : mdeg η = n := mem_idxOf.mp hη1
        omega
      rw [hdeg]
      have h2 : ((2 : ℝ) ^ m) ≠ 0 := by positivity
      have h3 : (mfact (halfIdx η) : ℝ) ≠ 0 := mfact_ne_zero _
      field_simp
  -- the factorization
  have hfac := mpow_factor hd α
  rw [integral_mpow_gaussian_even hα, ← hm] at hfac
  have hnormval : ∫ x, ‖x‖ ^ n ∂(γ d) = steinSum d m := by
    rw [hnm, integral_norm_pow_even d m, steinSum_eq]
  rw [← hn, hnormval] at hfac
  have hS_pos : 0 < steinSum d m := by
    rw [steinSum_eq]
    refine Finset.prod_pos fun i _ => ?_
    have hd' : (0 : ℝ) < d := by exact_mod_cast hd
    positivity
  rw [hdenom]
  have h2m : (0 : ℝ) < 2 ^ m := by positivity
  have hhf : (mfact (halfIdx α) : ℝ) ≠ 0 := mfact_ne_zero _
  -- solve for the sphere moment
  rw [eq_div_iff (by positivity)]
  rw [eq_comm, ← sub_eq_zero]
  have hgoal : (mfact α : ℝ) / (2 ^ m * (mfact (halfIdx α) : ℝ))
      = steinSum d m * sphereMoment d α := hfac
  field_simp at hgoal ⊢
  nlinarith [hgoal]

/-! ### Proposition 3.4 -/

/-- The `n·e₀` index behind `K_n`. -/
lemma mdeg_Kidx {d : ℕ} (hd : 0 < d) (n : ℕ) :
    mdeg (fun i : Fin d => if (i : ℕ) = 0 then n else 0) = n := by
  rw [mdeg]
  rw [show (fun i : Fin d => if (i : ℕ) = 0 then n else 0)
      = fun i => if i = ⟨0, hd⟩ then n else 0 from funext fun i => by
        congr 1
        apply propext
        exact ⟨fun h => Fin.ext h, fun h => by rw [h]⟩]
  rw [Finset.sum_ite_eq' Finset.univ (⟨0, hd⟩ : Fin d) (fun _ => n),
    ite_eq_left (Finset.mem_univ _)]

/-- `𝔼[X^{n·e₀}] = (n−1)!!` for even `n`. -/
lemma integral_mpow_Kidx {d : ℕ} (hd : 0 < d) (n : ℕ) :
    ∫ x, mpow x (fun i : Fin d => if (i : ℕ) = 0 then n else 0) ∂(γ d)
      = if Even n then (((n - 1)‼ : ℕ) : ℝ) else 0 := by
  rw [integral_mpow_gaussian,
    ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ (⟨0, hd⟩ : Fin d))]
  have h0 : ((⟨0, hd⟩ : Fin d) : ℕ) = 0 := rfl
  have hrest : ∏ j ∈ Finset.univ.erase (⟨0, hd⟩ : Fin d),
      (if Even (if (j : ℕ) = 0 then n else 0) then
        ((((if (j : ℕ) = 0 then n else 0) - 1)‼ : ℕ) : ℝ) else 0) = 1 := by
    refine Finset.prod_eq_one fun j hj => ?_
    have hj0 : (j : ℕ) ≠ 0 := by
      intro hcon
      exact (Finset.ne_of_mem_erase hj) (Fin.ext hcon)
    rw [ite_eq_right hj0, ite_eq_left ⟨0, rfl⟩]
    norm_num [Nat.doubleFactorial]
  rw [hrest, mul_one, ite_eq_left rfl]

/- LaTeX — `paper.tex`, Proposition 3.4 (The maximal even moment): "For even $n$ …
$$K_n = \prod_{i=0}^{n/2-1}\frac{2i+1}{d+2i}.$$" -/
/-- **Proposition 3.4, closed form.** -/
theorem Kmom_eq {d : ℕ} (hd : 0 < d) {n : ℕ} (hn : Even n) :
    Kmom d n = ∏ i ∈ Finset.range (n / 2), ((2 * i + 1 : ℝ) / (d + 2 * i)) := by
  obtain ⟨m, hm⟩ := hn
  have hn2 : n = 2 * m := by omega
  have hfac := mpow_factor hd (fun i : Fin d => if (i : ℕ) = 0 then n else 0)
  rw [mdeg_Kidx hd, integral_mpow_Kidx hd, ite_eq_left ⟨m, hm⟩] at hfac
  have hnormval : ∫ x, ‖x‖ ^ n ∂(γ d) = ∏ i ∈ Finset.range m, ((d : ℝ) + 2 * i) := by
    rw [hn2, integral_norm_pow_even]
  rw [hnormval] at hfac
  have hpos : (0 : ℝ) < ∏ i ∈ Finset.range m, ((d : ℝ) + 2 * i) := by
    refine Finset.prod_pos fun i _ => ?_
    have hd' : (0 : ℝ) < d := by exact_mod_cast hd
    positivity
  have hdf : (((n - 1)‼ : ℕ) : ℝ) = ∏ i ∈ Finset.range m, (2 * (i : ℝ) + 1) := by
    rcases Nat.eq_zero_or_pos m with rfl | hm1
    · have : n = 0 := by omega
      subst this
      simp [Nat.doubleFactorial]
    · obtain ⟨k, hk⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
      subst hk
      have h1 : n - 1 = 2 * k + 1 := by omega
      rw [h1, Nat.doubleFactorial_eq_prod_odd]
      push_cast
      rw [Finset.prod_range_succ']
      have h0 : (2 * ((0:ℕ) : ℝ) + 1) = 1 := by norm_num
      rw [h0, mul_one]
      exact Finset.prod_congr rfl fun i _ => by push_cast; ring
  rw [hdf] at hfac
  have hKn : Kmom d n
      = (∏ i ∈ Finset.range m, (2 * (i : ℝ) + 1)) / ∏ i ∈ Finset.range m, ((d : ℝ) + 2 * i) := by
    rw [Kmom]
    field_simp at hfac ⊢
    linarith [hfac]
  rw [hKn, hn2, show 2 * m / 2 = m from by omega, ← Finset.prod_div_distrib]

theorem Kmom_nonneg {d : ℕ} (hd : 0 < d) {n : ℕ} (hn : Even n) :
    0 ≤ Kmom d n := by
  rw [Kmom_eq hd hn]
  refine Finset.prod_nonneg fun i _ => ?_
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  positivity

theorem Kmom_pos {d : ℕ} (hd : 0 < d) {n : ℕ} (hn : Even n) :
    0 < Kmom d n := by
  rw [Kmom_eq hd hn]
  refine Finset.prod_pos fun i _ => ?_
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  positivity

/-- `K` is nonincreasing along even degrees (used in Cor 5.1). -/
theorem Kmom_antitone {d : ℕ} (hd : 0 < d) {n n' : ℕ} (hn : Even n)
    (hn' : Even n') (h : n ≤ n') :
    Kmom d n' ≤ Kmom d n := by
  rw [Kmom_eq hd hn, Kmom_eq hd hn']
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  obtain ⟨k, hk⟩ : ∃ k, n' / 2 = n / 2 + k := ⟨n' / 2 - n / 2, by omega⟩
  rw [hk, Finset.prod_range_add]
  have h1 : (0 : ℝ) ≤ ∏ i ∈ Finset.range (n / 2), ((2 * i + 1 : ℝ) / (d + 2 * i)) :=
    Finset.prod_nonneg fun i _ => by positivity
  refine mul_le_of_le_one_right h1 ?_
  refine Finset.prod_le_one (fun i _ => by positivity) fun i _ => ?_
  rw [div_le_one (by positivity)]
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  push_cast
  linarith

/- LaTeX — `paper.tex`, Remark after Proposition 3.4: "when $d \ge n$,
$K_n \le (n/(d+n))^{n/2}$." -/
/-- Remark after Proposition 3.4 (used in Theorem 1.2(i)). -/
theorem Kmom_le_pow {d n : ℕ} (hd : 0 < d) (hn : Even n) (hnd : n ≤ d) :
    Kmom d n ≤ ((n : ℝ) / (d + n)) ^ (n / 2) := by
  rw [Kmom_eq hd hn]
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  calc ∏ i ∈ Finset.range (n / 2), ((2 * i + 1 : ℝ) / (d + 2 * i))
      ≤ ∏ _i ∈ Finset.range (n / 2), ((n : ℝ) / (d + n)) := by
        refine Finset.prod_le_prod (fun i _ => by positivity) fun i hi => ?_
        have hi2 : 2 * i + 2 ≤ n := by
          have := Finset.mem_range.mp hi
          obtain ⟨m, hm⟩ := hn
          omega
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        have hcast : (2 * (i : ℝ) + 2) ≤ n := by exact_mod_cast hi2
        have hnd' : (n : ℝ) ≤ d := by exact_mod_cast hnd
        nlinarith
    _ = ((n : ℝ) / (d + n)) ^ (n / 2) := by
        rw [Finset.prod_const, Finset.card_range]

/-- `K_d ≤ 2^{−d/2}` (LaTeX — `paper.tex`, proof of Theorem 1.2(i):
"$K_d \le (d/(d+d))^{d/2} = 2^{-d/2}$"). -/
theorem Kmom_le_two_pow {d : ℕ} (hd : 0 < d) (hde : Even d) :
    Kmom d d ≤ (2 : ℝ) ^ (-(d : ℝ) / 2) := by
  have h1 := Kmom_le_pow hd hde le_rfl
  have h2 : ((d : ℝ) / (d + d)) = 1 / 2 := by
    have hd' : (0 : ℝ) < d := by exact_mod_cast hd
    field_simp
    ring
  rw [h2] at h1
  refine h1.trans_eq ?_
  obtain ⟨m, hm⟩ := hde
  have hd2 : d / 2 = m := by omega
  have hdr : (d : ℝ) = 2 * m := by exact_mod_cast (by omega : d = 2 * m)
  rw [hd2, hdr]
  rw [show (-(2 * (m : ℝ)) / 2) = -(m : ℝ) from by ring]
  rw [Real.rpow_neg (by norm_num), Real.rpow_natCast]
  rw [one_div, inv_pow]

/-! ### Proposition 3.4, maximality (weighted AM–GM) -/

lemma sphereUnif_ae_norm_one {d : ℕ} (hd : 0 < d) :
    ∀ᵐ v ∂(sphereUnif d), ‖v‖ = 1 := by
  rw [sphereUnif]
  rw [ae_map_iff (Measurable.aemeasurable (by fun_prop))
    (measurableSet_eq_fun measurable_norm measurable_const)]
  have hne : ∀ᵐ x ∂(γ d), x ≠ 0 := by
    have hset : {x : Vec d | ¬ x ≠ 0} = ({0} : Set (Vec d)) := by
      ext x; simp
    rw [ae_iff, hset]
    exact gaussD_singleton_zero hd
  filter_upwards [hne] with x hx
  exact norm_smul_inv_norm hx

lemma integrable_sphere_of_bounded {d : ℕ} (hd : 0 < d) {f : Vec d → ℝ}
    (hf : Measurable f) (C : ℝ) (hC : ∀ v, ‖v‖ = 1 → |f v| ≤ C) :
    Integrable f (sphereUnif d) := by
  refine ⟨hf.aestronglyMeasurable, HasFiniteIntegral.of_bounded (C := C) ?_⟩
  filter_upwards [sphereUnif_ae_norm_one hd] with v hv
  rw [Real.norm_eq_abs]
  exact hC v hv

/-- Permutation invariance of the sphere moments. -/
lemma sphereMoment_comp_perm {d : ℕ} (α : MIdx d) (σ : Equiv.Perm (Fin d)) :
    sphereMoment d (α ∘ σ) = sphereMoment d α := by
  set P := LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ σ with hP
  have hmp : MeasurePreserving (⇑P) (γ d) (γ d) :=
    ⟨P.continuous.measurable, by rw [γ]; exact stdGaussian_map P⟩
  have hkey := sphereMoment_comp_map α hmp (fun x => P.norm_map x)
  have hpt : ∀ x : Vec d, mpow (‖x‖⁻¹ • P x) α = mpow (‖x‖⁻¹ • x) (α ∘ σ) := by
    intro x
    have hsmul : (‖x‖⁻¹ • P x : Vec d) = P (‖x‖⁻¹ • x) := (map_smul _ _ _).symm
    rw [hsmul, mpow, mpow]
    calc ∏ i, (P (‖x‖⁻¹ • x)) i ^ α i
        = ∏ i, (P (‖x‖⁻¹ • x)) (σ i) ^ α (σ i) := (Equiv.prod_comp σ _).symm
      _ = ∏ i, (‖x‖⁻¹ • x : Vec d) i ^ (α ∘ σ) i := by
          refine Finset.prod_congr rfl fun i _ => ?_
          congr 1
          rw [hP, LinearIsometryEquiv.piLpCongrLeft_apply, Equiv.piCongrLeft'_apply,
            Equiv.symm_apply_apply]
  rw [integral_congr_ae (ae_of_all _ hpt), ← sphereMoment_eq_integral] at hkey
  exact hkey.symm

/-- `𝔼[Vᵢⁿ] = K_n` for every coordinate. -/
lemma sphereMoment_single {d : ℕ} (hd : 0 < d) (n : ℕ) (i : Fin d) :
    sphereMoment d (fun j => if j = i then n else 0) = Kmom d n := by
  rw [Kmom]
  set σ : Equiv.Perm (Fin d) := Equiv.swap i ⟨0, hd⟩ with hσ
  have hcomp : (fun j : Fin d => if (j : ℕ) = 0 then n else 0) ∘ σ
      = fun j => if j = i then n else 0 := by
    funext j
    simp only [Function.comp_apply]
    have hiff : ((σ j : ℕ) = 0) ↔ (j = i) := by
      constructor
      · intro h
        have h1 : σ j = ⟨0, hd⟩ := Fin.ext h
        have h2 : j = σ ⟨0, hd⟩ := by
          rw [← h1, hσ]
          rw [Equiv.swap_apply_self]
        rw [h2, hσ, Equiv.swap_apply_right]
      · intro h
        rw [h, hσ, Equiv.swap_apply_left]
    by_cases h : j = i
    · rw [ite_eq_left h, ite_eq_left (hiff.mpr h)]
    · rw [ite_eq_right h, ite_eq_right (fun hc => h (hiff.mp hc))]
  rw [← hcomp, sphereMoment_comp_perm]

/- LaTeX — `paper.tex`, Proposition 3.4: "Moreover, for every $\alpha$ with
$|\alpha| = n$, $|\mathbb{E}[V^\alpha]| \le K_n$." -/
/-- **Proposition 3.4, maximality** (weighted AM–GM + coordinate symmetry). -/
theorem abs_sphereMoment_le_Kmom {d : ℕ} (hd : 0 < d) {α : MIdx d} {n : ℕ}
    (hα : mdeg α = n) (hn : Even n) :
    |sphereMoment d α| ≤ Kmom d n := by
  by_cases hall : ∀ i, Even (α i)
  swap
  · push Not at hall
    rw [sphereMoment_eq_zero_of_odd
      ⟨hall.choose, hall.choose_spec⟩, abs_zero]
    exact Kmom_nonneg hd hn
  rcases Nat.eq_zero_or_pos n with rfl | hnpos
  · -- n = 0 : α ≡ 0, both sides equal 1
    have hα0 : α = fun _ => 0 := by
      funext i
      have h1 : ∑ j, α j = 0 := hα
      exact Finset.sum_eq_zero_iff.mp h1 i (Finset.mem_univ i)
    have hone : sphereMoment d α = 1 := by
      rw [sphereMoment, hα0]
      have : ∀ v : Vec d, mpow v (fun _ => 0) = 1 := fun v => by
        rw [mpow]; simp
      rw [integral_congr_ae (ae_of_all _ this)]
      simp
    have hK : Kmom d 0 = 1 := by
      rw [Kmom_eq hd ⟨0, rfl⟩]
      simp
    rw [hone, hK]
    norm_num
  -- main case: AM–GM pointwise then integrate
  have hnpos' : (0 : ℝ) < n := by exact_mod_cast hnpos
  have hsumw : ∑ i, ((α i : ℝ) / n) = 1 := by
    rw [← Finset.sum_div]
    have hsn : ∑ i, (α i : ℝ) = n := by
      have h : ∑ i, α i = n := hα
      exact_mod_cast congrArg (Nat.cast : ℕ → ℝ) h
    rw [hsn]
    field_simp
  have hptwise : ∀ v : Vec d, |mpow v α| ≤ ∑ i, ((α i : ℝ) / n) * |v i| ^ n := by
    intro v
    have habs : |mpow v α| = ∏ i, |v i| ^ α i := by
      rw [mpow, Finset.abs_prod]
      exact Finset.prod_congr rfl fun i _ => by rw [abs_pow]
    have hfactor : ∀ i : Fin d, |v i| ^ α i = (|v i| ^ n) ^ ((α i : ℝ) / n) := by
      intro i
      rw [← Real.rpow_natCast (|v i|) (α i), ← Real.rpow_natCast (|v i|) n,
        ← Real.rpow_mul (abs_nonneg _)]
      congr 1
      field_simp
    rw [habs, Finset.prod_congr rfl fun i _ => hfactor i]
    exact Real.geom_mean_le_arith_mean_weighted Finset.univ
      (fun i => (α i : ℝ) / n) (fun i => |v i| ^ n)
      (fun i _ => by positivity) (by simpa using hsumw) (fun i _ => by positivity)
  have hmeas : Measurable fun v : Vec d => mpow v α := (continuous_mpow α).measurable
  have hint1 : Integrable (fun v => mpow v α) (sphereUnif d) :=
    integrable_sphere_of_bounded hd hmeas 1 fun v hv => abs_mpow_le_one (le_of_eq hv) α
  have hint2 : ∀ i : Fin d, Integrable (fun v : Vec d => |v i| ^ n) (sphereUnif d) := by
    intro i
    have hci : Continuous fun v : Vec d => |v i| ^ n := by
      have hcoord : Continuous fun v : Vec d => v i := by fun_prop
      exact (hcoord.abs).pow n
    refine integrable_sphere_of_bounded hd hci.measurable 1 fun v hv => ?_
    rw [abs_of_nonneg (by positivity)]
    exact pow_le_one₀ (abs_nonneg _) ((abs_coord_le_norm v i).trans (le_of_eq hv))
  have hcoordmom : ∀ i : Fin d,
      ∫ v, |v i| ^ n ∂(sphereUnif d) = Kmom d n := by
    intro i
    have heq : ∀ v : Vec d, |v i| ^ n = mpow v (fun j => if j = i then n else 0) := by
      intro v
      rw [hn.pow_abs, mpow,
        ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i), ite_eq_left rfl]
      have h1 : ∏ j ∈ Finset.univ.erase i, v j ^ (if j = i then n else 0) = 1 :=
        Finset.prod_eq_one fun j hj => by
          rw [ite_eq_right (Finset.ne_of_mem_erase hj), pow_zero]
      rw [h1, mul_one]
    rw [integral_congr_ae (ae_of_all _ heq)]
    exact sphereMoment_single hd n i
  calc |sphereMoment d α|
      ≤ ∫ v, |mpow v α| ∂(sphereUnif d) := by
        rw [sphereMoment]
        exact abs_integral_le_integral_abs
    _ ≤ ∫ v, ∑ i, ((α i : ℝ) / n) * |v i| ^ n ∂(sphereUnif d) :=
        integral_mono_ae hint1.abs
          (integrable_finsetSum _ fun i _ => (hint2 i).const_mul _)
          (ae_of_all _ hptwise)
    _ = ∑ i, ((α i : ℝ) / n) * ∫ v, |v i| ^ n ∂(sphereUnif d) := by
        rw [integral_finsetSum _ fun i _ => (hint2 i).const_mul _]
        exact Finset.sum_congr rfl fun i _ => integral_const_mul _ _
    _ = ∑ i, ((α i : ℝ) / n) * Kmom d n :=
        Finset.sum_congr rfl fun i _ => by rw [hcoordmom i]
    _ = Kmom d n := by
        rw [← Finset.sum_mul, hsumw, one_mul]

end

end GaussianDepthSeparation
