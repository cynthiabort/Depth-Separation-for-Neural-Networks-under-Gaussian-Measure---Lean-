/-
Infrastructure for the cited degree-zero Funk–Hecke theorem. We establish
the spherical coordinate law from Gaussian polar moments and polynomial
approximation. Proposition 3.4 itself uses the slice formula, beta substitution,
and Gamma recurrence, as in the paper.
-/
import GaussianDepthSeparation.MomentsCore
import GaussianDepthSeparation.SphereBeta
import Mathlib.Topology.ContinuousMap.Weierstrass

namespace GaussianDepthSeparation

open MeasureTheory ProbabilityTheory Real Set Polynomial Filter
open scoped Nat ENNReal Topology

noncomputable section

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

private theorem coordinateMoment_product {d : ℕ} (hd : 0 < d) {n : ℕ} (hn : Even n) :
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


def gammaCoordinateMoment (d m : ℕ) : ℝ :=
  Gamma ((d : ℝ) / 2) * Gamma ((m : ℝ) + 1 / 2) /
    (sqrt π * Gamma ((d : ℝ) / 2 + m))

/-- The Gamma recurrence gives the product displayed in Proposition 3.4. -/
theorem gammaCoordinateMoment_product {d : ℕ} (hd : 0 < d) (m : ℕ) :
    gammaCoordinateMoment d m =
      ∏ i ∈ Finset.range m, ((2 * i + 1 : ℝ) / (d + 2 * i)) := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  induction m with
  | zero =>
    simp only [gammaCoordinateMoment, Nat.cast_zero, zero_add, add_zero,
      Gamma_one_half_eq, Finset.prod_range_zero]
    field_simp [(Gamma_pos_of_pos (show (0 : ℝ) < d / 2 by positivity)).ne', pi_pos.ne']
  | succ m ih =>
    rw [Finset.prod_range_succ, ← ih]
    unfold gammaCoordinateMoment
    have hg : Gamma ((d : ℝ) / 2 + m) ≠ 0 := (Gamma_pos_of_pos (by positivity)).ne'
    have hg' : (d : ℝ) / 2 + m ≠ 0 := by positivity
    rw [Nat.cast_succ, show (m : ℝ) + 1 + 1 / 2 = (m + 1 / 2) + 1 by ring,
      show (d : ℝ) / 2 + ((m : ℝ) + 1) = (d / 2 + m) + 1 by ring,
      Gamma_add_one (by positivity : (m : ℝ) + 1 / 2 ≠ 0), Gamma_add_one hg']
    field_simp

lemma Kmom_eq_coordinate_integral {d : ℕ} (hd : 0 < d) (n : ℕ) :
    Kmom d n = ∫ v, (v (⟨0, hd⟩ : Fin d)) ^ n ∂sphereUnif d := by
  unfold Kmom sphereMoment
  apply integral_congr_ae
  filter_upwards [] with v
  rw [mpow, Finset.prod_eq_single (⟨0, hd⟩ : Fin d)]
  · simp
  · intro j _ hj
    have hj0 : (j : ℕ) ≠ 0 := fun h => hj (Fin.ext h)
    simp [hj0]
  · simp

private lemma coordinateMoment_even_gamma {d : ℕ} (hd : 0 < d) (m : ℕ) :
    (∫ v, (v (⟨0, hd⟩ : Fin d)) ^ (2 * m) ∂sphereUnif d) = gammaCoordinateMoment d m := by
  rw [← Kmom_eq_coordinate_integral hd, coordinateMoment_product hd (even_two_mul m),
    gammaCoordinateMoment_product hd, Nat.mul_div_cancel_left m (by norm_num : 0 < 2)]

private lemma coordinateMoment_odd {d : ℕ} (hd : 0 < d) {n : ℕ} (hn : Odd n) :
    (∫ v, (v (⟨0, hd⟩ : Fin d)) ^ n ∂sphereUnif d) = 0 := by
  rw [← Kmom_eq_coordinate_integral hd]
  apply sphereMoment_eq_zero_of_odd
  refine ⟨⟨0, hd⟩, ?_⟩
  simpa using Nat.not_even_iff_odd.mpr hn

def sphereSliceConstant (d : ℕ) : ℝ :=
  Gamma ((d : ℝ) / 2) / (sqrt π * Gamma (((d : ℝ) - 1) / 2))

def sphereSliceWeight (d : ℕ) (t : ℝ) : ℝ := (1 - t ^ 2) ^ (((d : ℝ) - 3) / 2)

lemma sphereSliceConstant_pos {d : ℕ} (hd : 2 ≤ d) : 0 < sphereSliceConstant d := by
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  unfold sphereSliceConstant
  exact div_pos (Gamma_pos_of_pos (by linarith))
    (mul_pos (sqrt_pos.2 pi_pos) (Gamma_pos_of_pos (by linarith)))

lemma sphereSliceWeight_nonneg {d : ℕ} {t : ℝ} (ht : t ∈ Icc (-1 : ℝ) 1) :
    0 ≤ sphereSliceWeight d t := by
  apply Real.rpow_nonneg
  nlinarith [ht.1, ht.2]

lemma integrable_sphereSlice_monomial {d : ℕ} (hd : 2 ≤ d) (n : ℕ) :
    IntegrableOn (fun t : ℝ => t ^ n * sphereSliceWeight d t) (Ioo (-1) 1) := by
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have h := integrableOn_sphereSlice_monomial n (b := ((d : ℝ) - 1) / 2) (by linarith)
  simpa only [show ((d : ℝ) - 1) / 2 - 1 = (d - 3) / 2 by ring, sphereSliceWeight] using h

lemma sphereSlice_even_gamma {d : ℕ} (hd : 2 ≤ d) (m : ℕ) :
    sphereSliceConstant d *
      (∫ t in Ioo (-1 : ℝ) 1, t ^ (2 * m) * sphereSliceWeight d t) =
        gammaCoordinateMoment d m := by
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hb : 0 < ((d : ℝ) - 1) / 2 := by linarith
  have h := sphereSlice_even_moment (2 * m) (even_two_mul m) hb
  rw [show ((d : ℝ) - 1) / 2 - 1 = (d - 3) / 2 by ring] at h
  simp only [sphereSliceWeight]
  rw [h]
  have he1 : (((2 * m : ℕ) : ℝ) + 1) / 2 = (m : ℝ) + 1 / 2 := by push_cast; ring
  have he2 : (m : ℝ) + 1 / 2 + ((d : ℝ) - 1) / 2 = d / 2 + m := by ring
  rw [he1, he2, sphereSliceConstant, gammaCoordinateMoment]
  field_simp [(Gamma_pos_of_pos hb).ne']

lemma sphereSlice_mass {d : ℕ} (hd : 2 ≤ d) :
    sphereSliceConstant d * (∫ t in Ioo (-1 : ℝ) 1, sphereSliceWeight d t) = 1 := by
  have h := sphereSlice_even_gamma hd 0
  rw [gammaCoordinateMoment_product (by omega), Finset.prod_range_zero] at h
  simpa using h

private lemma coordinateMoment_eq_slice {d : ℕ} (hd : 2 ≤ d) (n : ℕ) :
    (∫ v, (v (⟨0, by omega⟩ : Fin d)) ^ n ∂sphereUnif d) =
      sphereSliceConstant d * (∫ t in Ioo (-1 : ℝ) 1, t ^ n * sphereSliceWeight d t) := by
  rcases Nat.even_or_odd n with hn | hn
  · obtain ⟨m, hm⟩ := hn
    have he : n = 2 * m := by omega
    rw [he, coordinateMoment_even_gamma (by omega), sphereSlice_even_gamma hd]
  · rw [coordinateMoment_odd (by omega) hn]
    have hb : 0 < ((d : ℝ) - 1) / 2 := by
      have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
      linarith
    have h := sphereSlice_odd_moment n hn hb
    rw [show ((d : ℝ) - 1) / 2 - 1 = (d - 3) / 2 by ring] at h
    simp only [sphereSliceWeight, h, mul_zero]

lemma integrable_sphere_coordinate_continuous {d : ℕ} (hd : 0 < d)
    {f : ℝ → ℝ} (hf : Continuous f) :
    Integrable (fun v => f (v (⟨0, hd⟩ : Fin d))) (sphereUnif d) := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hf.continuousOn
  refine integrable_sphere_of_bounded hd (by fun_prop) C fun v hv => ?_
  have hc : |v (⟨0, hd⟩ : Fin d)| ≤ 1 := (abs_coord_le_norm v _).trans hv.le
  simpa [Real.norm_eq_abs] using hC (v (⟨0, hd⟩ : Fin d))
    (show v (⟨0, hd⟩ : Fin d) ∈ Icc (-1 : ℝ) 1 from abs_le.mp hc)

lemma integrable_sphereSlice_continuous {d : ℕ} (hd : 2 ≤ d)
    {f : ℝ → ℝ} (hf : Continuous f) :
    IntegrableOn (fun t => f t * sphereSliceWeight d t) (Ioo (-1) 1) := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hf.continuousOn
  have hw : IntegrableOn (sphereSliceWeight d) (Ioo (-1) 1) := by
    simpa using integrable_sphereSlice_monomial hd 0
  refine Integrable.mono' (hw.norm.const_mul C) (by apply Measurable.aestronglyMeasurable; unfold sphereSliceWeight; fun_prop) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right (hC t (Ioo_subset_Icc_self ht)) (norm_nonneg _)

private lemma coordinate_polynomial_eq_slice {d : ℕ} (hd : 2 ≤ d) (p : Polynomial ℝ) :
    (∫ v, p.eval (v (⟨0, by omega⟩ : Fin d)) ∂sphereUnif d) =
      sphereSliceConstant d * (∫ t in Ioo (-1 : ℝ) 1, p.eval t * sphereSliceWeight d t) := by
  simp_rw [p.eval_eq_sum_range, Finset.sum_mul, mul_assoc]
  rw [integral_finsetSum _ (fun n _ =>
    (integrable_sphere_coordinate_continuous (by omega) (continuous_pow n)).const_mul _),
    integral_finsetSum _ (fun n _ => (integrable_sphereSlice_monomial hd n).const_mul _)]
  simp_rw [integral_const_mul, coordinateMoment_eq_slice hd]
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => by ring

lemma sphere_coordinate_abs_integral_le {d : ℕ} (hd : 0 < d) (f : ℝ → ℝ) {C : ℝ}
    (hC : ∀ t ∈ Icc (-1 : ℝ) 1, |f t| ≤ C) :
    |∫ v, f (v (⟨0, hd⟩ : Fin d)) ∂sphereUnif d| ≤ C := by
  have h := norm_integral_le_of_norm_le_const
    (μ := sphereUnif d) (f := fun v => f (v (⟨0, hd⟩ : Fin d))) (C := C) ?_
  · simpa [Real.norm_eq_abs] using h
  · filter_upwards [sphereUnif_ae_norm_one hd] with v hv
    rw [Real.norm_eq_abs]
    apply hC
    exact abs_le.mp ((abs_coord_le_norm v _).trans hv.le)

lemma sphereSlice_abs_integral_le {d : ℕ} (hd : 2 ≤ d) (f : ℝ → ℝ) {C : ℝ}
    (hC : ∀ t ∈ Icc (-1 : ℝ) 1, |f t| ≤ C) :
    |sphereSliceConstant d * (∫ t in Ioo (-1 : ℝ) 1, f t * sphereSliceWeight d t)| ≤ C := by
  have hw : IntegrableOn (sphereSliceWeight d) (Ioo (-1) 1) := by
    simpa using integrable_sphereSlice_monomial hd 0
  have hbound : |∫ t in Ioo (-1 : ℝ) 1, f t * sphereSliceWeight d t| ≤
      C * (∫ t in Ioo (-1 : ℝ) 1, sphereSliceWeight d t) := by
    have h := norm_integral_le_of_norm_le (f := fun t => f t * sphereSliceWeight d t)
      (hw.const_mul C) ?_
    · simpa only [Real.norm_eq_abs, integral_const_mul] using h
    · filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
      have hw0 := sphereSliceWeight_nonneg (d := d) (Ioo_subset_Icc_self ht)
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hw0]
      exact mul_le_mul_of_nonneg_right (hC t (Ioo_subset_Icc_self ht)) hw0
  rw [abs_mul, abs_of_pos (sphereSliceConstant_pos hd)]
  calc
    _ ≤ sphereSliceConstant d *
        (C * (∫ t in Ioo (-1 : ℝ) 1, sphereSliceWeight d t)) := by
      exact mul_le_mul_of_nonneg_left hbound (sphereSliceConstant_pos hd).le
    _ = C := by rw [mul_left_comm, sphereSlice_mass hd, mul_one]

/-- The degree-zero Funk–Hecke formula for every continuous test function.
This supplies the external result cited by the paper, independently of
Proposition 3.4. Its proof extends equality of coordinate moments by
Weierstrass approximation. -/
theorem sphere_coordinate_funkHecke {d : ℕ} (hd : 2 ≤ d)
    (f : ℝ → ℝ) (hf : Continuous f) :
    (∫ v, f (v (⟨0, by omega⟩ : Fin d)) ∂sphereUnif d) =
      sphereSliceConstant d * (∫ t in Ioo (-1 : ℝ) 1, f t * sphereSliceWeight d t) := by
  apply eq_of_forall_dist_le
  intro ε hε
  obtain ⟨p, hp⟩ := exists_polynomial_near_of_continuousOn (-1) 1 f hf.continuousOn
    (ε / 2) (by positivity)
  have hpcont : Continuous (fun t => p.eval t) := p.continuous
  have hs := sphere_coordinate_abs_integral_le (d := d) (by omega)
    (fun t => f t - p.eval t) (C := ε / 2) (fun t ht => by
      rw [abs_sub_comm]; exact (hp t ht).le)
  have ht := sphereSlice_abs_integral_le hd (fun t => p.eval t - f t)
    (C := ε / 2) (fun t ht => (hp t ht).le)
  rw [integral_sub (integrable_sphere_coordinate_continuous (by omega) hf)
    (integrable_sphere_coordinate_continuous (by omega) hpcont)] at hs
  simp_rw [sub_mul] at ht
  rw [integral_sub (integrable_sphereSlice_continuous hd hpcont)
    (integrable_sphereSlice_continuous hd hf), mul_sub] at ht
  rw [coordinate_polynomial_eq_slice hd p] at hs
  rw [Real.dist_eq]
  have htriangle := abs_add_le
    ((∫ v, f (v (⟨0, by omega⟩ : Fin d)) ∂sphereUnif d) -
      sphereSliceConstant d * (∫ t in Ioo (-1 : ℝ) 1, p.eval t * sphereSliceWeight d t))
    (sphereSliceConstant d * (∫ t in Ioo (-1 : ℝ) 1, p.eval t * sphereSliceWeight d t) -
      sphereSliceConstant d * (∫ t in Ioo (-1 : ℝ) 1, f t * sphereSliceWeight d t))
  rw [sub_add_sub_cancel] at htriangle
  linarith

end

end GaussianDepthSeparation
