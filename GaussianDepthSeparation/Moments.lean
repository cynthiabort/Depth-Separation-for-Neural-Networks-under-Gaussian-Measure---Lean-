/-
GaussianDepthSeparation §3 — Spherical Moments (Lemma 3.3, Proposition 3.4, and the
remark `K_n ≤ (n/(d+n))^{n/2}` used by Theorem 1.3(i)).

Built on `MomentsCore`: odd vanishing, the factorization
`𝔼[X^α] = 𝔼[‖X‖^n]·𝔼[V^α]`, product moments and the Stein-sum norm moments.
The maximal-moment bound follows the manuscript’s generalized Hölder
inequality, with weights `α i / n` (zero weights contribute factors equal to one).
-/
import GaussianDepthSeparation.SphereFunkHecke
import Mathlib.MeasureTheory.Integral.MeanInequalities

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

/- LaTeX — `main.tex`, Lemma 3.3:
"If all $\alpha_i$ are even, then
$$\mathbb{E}[V^\alpha] = \frac{\frac{\alpha!}{(\alpha/2)!}}
{\sum_{|\beta|=n,\ \beta\ {\rm even}}\frac{(n/2)!}{(\beta/2)!}\frac{\beta!}{(\beta/2)!}}.$$"
-/
/-- **Lemma 3.3, even case.** -/
theorem sphereMoment_of_even {d : ℕ} (hd : 0 < d) {α : MIdx d}
    (hα : ∀ i, Even (α i)) :
    sphereMoment d α =
      ((mfact α : ℝ) / (mfact (halfIdx α) : ℝ)) /
        (∑ β ∈ (idxOf d (mdeg α)).filter (fun β => ∀ i, Even (β i)),
          (((mdeg α / 2)! : ℝ) / (mfact (halfIdx β) : ℝ)) *
            ((mfact β : ℝ) / (mfact (halfIdx β) : ℝ))) := by
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

/- LaTeX — `main.tex`, Proposition 3.4: "Assume $d\ge 1$. … For even $n\ge 2$,
set $K_n:=\mathbb E[V_1^n]$. … Moreover,
$$K_n = \frac{(n-1)(n-3)\cdots 1}{d(d+2)\cdots(d+n-2)}
  = \prod_{i=0}^{n/2-1}\frac{2i+1}{d+2i}.$$" -/
/-- **Proposition 3.4, closed form.** -/
theorem Kmom_eq {d : ℕ} (hd : 0 < d) {n : ℕ} (hn : Even n) :
    Kmom d n = ∏ i ∈ Finset.range (n / 2), ((2 * i + 1 : ℝ) / (d + 2 * i)) := by
  by_cases hd1 : d = 1
  · subst d
    -- In dimension one, the sphere consists of ±1.
    have hK : Kmom 1 n = 1 := by
      rw [Kmom_eq_coordinate_integral hd]
      apply integral_eq_const
      filter_upwards [sphereUnif_ae_norm_one hd] with v hv
      have hs : v (0 : Fin 1) ^ 2 = 1 := by simpa using sum_sq_eq_one hv
      have ha : |v (0 : Fin 1)| = 1 := by
        nlinarith [sq_abs (v (0 : Fin 1)), abs_nonneg (v (0 : Fin 1))]
      rw [show (⟨0, hd⟩ : Fin 1) = 0 from Subsingleton.elim _ _, ← hn.pow_abs,
        ha, one_pow]
    rw [hK]
    symm
    apply Finset.prod_eq_one
    intro i _
    norm_num only [Nat.cast_one]
    have hpos : (0 : ℝ) < 1 + 2 * i := by positivity
    apply (div_eq_one_iff_eq hpos.ne').mpr
    ring
  · have hd2 : 2 ≤ d := by omega
    obtain ⟨m, hm⟩ := hn
    have hn2 : n = 2 * m := by omega
    -- Degree-zero Funk–Hecke, followed by u=t² and the beta integral.
    have hslice := sphere_coordinate_funkHecke hd2 (fun t => t ^ n) (continuous_pow n)
    rw [← Kmom_eq_coordinate_integral hd] at hslice
    calc
      Kmom d n = sphereSliceConstant d *
          (∫ t in Set.Ioo (-1 : ℝ) 1, t ^ n * sphereSliceWeight d t) := hslice
      _ = gammaCoordinateMoment d m := by rw [hn2, sphereSlice_even_gamma hd2 m]
      -- Gamma recurrence gives the displayed finite product.
      _ = _ := by
        rw [gammaCoordinateMoment_product hd, hn2, show 2 * m / 2 = m from by omega]

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

/- LaTeX — `main.tex`, Remark after Proposition 3.4: "when $d \ge n$,
$K_n \le (n/(d+n))^{n/2}$." -/
/-- Remark after Proposition 3.4 (used in Theorem 1.3(i)). -/
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

/-- `K_d ≤ 2^{−d/2}` (LaTeX — `main.tex`, proof of Theorem 1.3(i):
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

/-! ### Proposition 3.4, maximality (generalized Hölder) -/

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

/- LaTeX — `main.tex`, Proposition 3.4: "Assume $d\ge 1$. … For even $n\ge 2$,
set $K_n:=\mathbb E[V_1^n]$. Then $|\mathbb{E}[V^\alpha]|\le K_n$ for every
$\alpha\in\mathbb N^d$ with $|\alpha|=n$." -/
/-- **Proposition 3.4, maximality** (generalized Hölder + coordinate symmetry). -/
theorem abs_sphereMoment_le_Kmom {d : ℕ} (hd : 0 < d) {α : MIdx d} {n : ℕ}
    (hα : mdeg α = n) (hn : Even n) :
    |sphereMoment d α| ≤ Kmom d n := by
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
  -- Generalized Hölder with reciprocal exponents αᵢ/n.
  have hnpos' : (0 : ℝ) < n := by exact_mod_cast hnpos
  have hsumw : ∑ i, ((α i : ℝ) / n) = 1 := by
    rw [← Finset.sum_div]
    have hsn : ∑ i, (α i : ℝ) = n := by
      have h : ∑ i, α i = n := hα
      exact_mod_cast congrArg (Nat.cast : ℕ → ℝ) h
    rw [hsn]
    field_simp
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
  have hHolder := ENNReal.lintegral_prod_norm_pow_le
    (μ := sphereUnif d) Finset.univ
    (f := fun i v => ENNReal.ofReal (|v i| ^ n))
    (p := fun i => (α i : ℝ) / n)
    (fun i _ => ((hint2 i).aestronglyMeasurable.aemeasurable.ennreal_ofReal))
    hsumw (fun i _ => by positivity)
  have hprod (v : Vec d) :
      (∏ i, ENNReal.ofReal (|v i| ^ n) ^ ((α i : ℝ) / n)) =
        ENNReal.ofReal |mpow v α| := by
    simp_rw [ENNReal.ofReal_rpow_of_nonneg (by positivity : 0 ≤ |v _| ^ n)
      (by positivity : 0 ≤ (α _ : ℝ) / n)]
    rw [← ENNReal.ofReal_prod_of_nonneg (fun i _ => Real.rpow_nonneg (by positivity) _)]
    congr 1
    rw [mpow, Finset.abs_prod]
    apply Finset.prod_congr rfl
    intro i _
    rw [abs_pow, ← Real.rpow_natCast (|v i|) n,
      ← Real.rpow_mul (abs_nonneg _)]
    have he : (n : ℝ) * ((α i : ℝ) / n) = α i := by field_simp
    rw [he, Real.rpow_natCast]
  have hcoord (i : Fin d) :
      (∫⁻ v, ENNReal.ofReal (|v i| ^ n) ∂(sphereUnif d)) =
        ENNReal.ofReal (Kmom d n) := by
    rw [← ofReal_integral_eq_lintegral_ofReal (hint2 i) (ae_of_all _ fun _ => by positivity),
      hcoordmom]
  simp_rw [hprod, hcoord, ENNReal.ofReal_rpow_of_pos (Kmom_pos hd hn)] at hHolder
  rw [← ofReal_integral_eq_lintegral_ofReal hint1.abs
      (ae_of_all _ fun _ => abs_nonneg _),
    ← ENNReal.ofReal_prod_of_nonneg (fun i _ => Real.rpow_nonneg (Kmom_nonneg hd hn) _),
    ← Real.rpow_sum_of_pos (Kmom_pos hd hn), hsumw, Real.rpow_one] at hHolder
  calc |sphereMoment d α|
      ≤ ∫ v, |mpow v α| ∂(sphereUnif d) := abs_integral_le_integral_abs
    _ ≤ Kmom d n := (ENNReal.ofReal_le_ofReal_iff (Kmom_nonneg hd hn)).mp hHolder

end

end GaussianDepthSeparation
