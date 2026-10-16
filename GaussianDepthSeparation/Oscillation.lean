/-
GaussianDepthSeparation §5 — the sign-change estimate in Lemma 5.3.
Discard half-period interiors containing polynomial roots, count the
remaining maximal constant-sign blocks, and sum opposing half-periods.
-/
import GaussianDepthSeparation.SignBlocks

namespace GaussianDepthSeparation

open MeasureTheory Real Set Polynomial
open intervalIntegral
open scoped Interval NNReal ENNReal Nat

noncomputable section

private def halfStart (m y : ℝ) : ℤ := ⌊m - y⌋ + 1
private def halfCount (y : ℝ) : ℕ := 2 * ⌊y⌋₊ - 2

lemma halfInterval_pairwise_disjoint (a : ℤ) :
    (Set.univ : Set ℕ).Pairwise (Function.onFun Disjoint (halfInterval a)) := by
  intro i _ j _ hij
  change Disjoint (halfInterval a i) (halfInterval a j)
  rw [Set.disjoint_left]
  intro s hi hj
  dsimp [halfInterval] at hi hj
  rcases lt_or_gt_of_ne hij with h | h
  · have hR : (i : ℝ) + 1 ≤ j := by exact_mod_cast h
    linarith [hi.2, hj.1]
  · have hR : (j : ℝ) + 1 ≤ i := by exact_mod_cast h
    linarith [hj.2, hi.1]

lemma halfInterval_subset_window {m y : ℝ} (hy : 2 ≤ y) {j : ℕ}
    (hj : j < halfCount y) : halfInterval (halfStart m y) j ⊆ Icc (m - y) (m + y) := by
  intro s hs
  have hfloor := Int.floor_le (m - y)
  have hfloor' := Int.lt_floor_add_one (m - y)
  have hfy := Nat.floor_le (by linarith : 0 ≤ y)
  have hfy2 : 2 ≤ ⌊y⌋₊ := Nat.le_floor hy
  have hjN : j + 1 ≤ 2 * ⌊y⌋₊ - 2 := Nat.succ_le_iff.mpr hj
  have hjR : (j : ℝ) + 1 ≤ 2 * (⌊y⌋₊ : ℝ) - 2 := by
    have h : ((j + 1 + 2 : ℕ) : ℝ) ≤ ((2 * ⌊y⌋₊ : ℕ) : ℝ) := by
      exact_mod_cast (show j + 1 + 2 ≤ 2 * ⌊y⌋₊ by omega)
    push_cast at h
    linarith
  dsimp [halfInterval, halfStart] at hs
  push_cast at hs
  constructor <;> linarith [hs.1, hs.2]

lemma halfCount_gt (y : ℝ) (hy : 2 ≤ y) : 2 * y - 4 < (halfCount y : ℝ) := by
  have hfy2 : 2 ≤ ⌊y⌋₊ := Nat.le_floor hy
  have hfy := Nat.lt_floor_add_one y
  dsimp [halfCount]
  rw [Nat.cast_sub (by omega)]
  push_cast
  linarith

private def retainedOpposite (m y : ℝ) (q : Polynomial ℝ) : Finset ℕ :=
  if q = 0 then Finset.range (halfCount y)
  else oppositeHalves (fun s => q.eval (s / m)) (halfStart m y) (halfCount y)

lemma retainedOpposite_mem_range {m y : ℝ} {q : Polynomial ℝ} {j : ℕ}
    (hj : j ∈ retainedOpposite m y q) : j < halfCount y := by
  classical
  by_cases hq : q = 0
  · simpa [retainedOpposite, hq] using hj
  · rw [retainedOpposite, ite_eq_right hq] at hj
    exact Finset.mem_range.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hj).1).1

lemma retainedOpposite_integral_lower {m y : ℝ} (q : Polynomial ℝ) {j : ℕ}
    (hj : j ∈ retainedOpposite m y q) :
    1 / 2 ≤ ∫ s in halfInterval (halfStart m y) j, scaledRadialError m q s := by
  classical
  by_cases hq : q = 0
  · subst q
    simp only [scaledRadialError, Polynomial.eval_zero, sub_zero]
    exact (half_sine_integral _ _).ge
  · rw [retainedOpposite, ite_eq_right hq] at hj
    exact oppositeHalf_integral_lower m q hj

lemma retainedOpposite_card_lower {m y : ℝ} {n₀ : ℕ} (hy : 4 * n₀ ≤ y)
    (hn₀ : 2 ≤ n₀) (hm : m ≠ 0) (q : Polynomial.degreeLT ℝ (n₀ / 2)) :
    y / 4 ≤ ((retainedOpposite m y q).card : ℝ) := by
  classical
  have hnR : (2 : ℝ) ≤ n₀ := by exact_mod_cast hn₀
  have hy2 : 2 ≤ y := by linarith
  have hN := halfCount_gt y hy2
  by_cases hq : (q : Polynomial ℝ) = 0
  · simp only [retainedOpposite, ite_eq_left hq, Finset.card_range]
    linarith
  · have hdegree : q.val.natDegree < n₀ / 2 :=
      (Polynomial.natDegree_lt_iff_degree_lt hq).2 (Polynomial.mem_degreeLT.mp q.property)
    have hdeg : 2 * q.val.natDegree + 1 ≤ n₀ := by omega
    have hcount := oppositeHalves_card_lower q hq m hm (halfStart m y) (halfCount y)
    have hbound : halfCount y ≤
        2 * (oppositeHalves (fun s => q.val.eval (s / m)) (halfStart m y) (halfCount y)).card
          + n₀ := by omega
    have hboundR : (halfCount y : ℝ) ≤
        2 * ((retainedOpposite m y q).card : ℝ) + n₀ := by
      simpa only [retainedOpposite, ite_eq_right hq, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
        using (show (halfCount y : ℝ) ≤
          ((2 * (oppositeHalves (fun s => q.val.eval (s / m)) (halfStart m y)
            (halfCount y)).card + n₀ : ℕ) : ℝ) from by exact_mod_cast hbound)
    linarith

/-- The half-period/block proof of Lemma 5.3, expressed in `s = mt` so the
half-periods have integer endpoints. The paper's coordinate is `u = π(s-m)`. -/
theorem scaledRadialError_window_lower {m y : ℝ} {n₀ : ℕ}
    (hy : 4 * n₀ ≤ y) (hn₀ : 2 ≤ n₀) (hm : m ≠ 0)
    (q : Polynomial.degreeLT ℝ (n₀ / 2)) :
    y / 8 ≤ ∫ s in Icc (m - y) (m + y), scaledRadialError m q s := by
  classical
  have hy2 : 2 ≤ y := by
    have hnR : (2 : ℝ) ≤ n₀ := by exact_mod_cast hn₀
    linarith
  let good := retainedOpposite m y q
  have hcard : y / 4 ≤ (good.card : ℝ) := retainedOpposite_card_lower hy hn₀ hm q
  have hpairwise : (↑good : Set ℕ).Pairwise
      (Function.onFun Disjoint (halfInterval (halfStart m y))) := by
    intro i _ j _ hij
    exact halfInterval_pairwise_disjoint _ (Set.mem_univ i) (Set.mem_univ j) hij
  have hblockInt (j : ℕ) (_hj : j ∈ good) :
      IntegrableOn (scaledRadialError m q) (halfInterval (halfStart m y) j) :=
    (continuous_scaledRadialError m q).integrableOn_Icc.mono_set Ioo_subset_Icc_self
  have hsum := integral_biUnion_finset good
    (fun _j _ => measurableSet_Ioo) hpairwise hblockInt
  have hunion : (⋃ j ∈ good, halfInterval (halfStart m y) j) ⊆ Icc (m - y) (m + y) := by
    intro s hs
    simp only [Set.mem_iUnion] at hs
    obtain ⟨j, hj, hs⟩ := hs
    exact halfInterval_subset_window hy2 (retainedOpposite_mem_range hj) hs
  calc
    y / 8 ≤ (good.card : ℝ) / 2 := by linarith
    _ = ∑ _j ∈ good, (1 / 2 : ℝ) := by simp [div_eq_mul_inv]
    _ ≤ ∑ j ∈ good, ∫ s in halfInterval (halfStart m y) j, scaledRadialError m q s :=
      Finset.sum_le_sum fun j hj => retainedOpposite_integral_lower q hj
    _ = ∫ s in ⋃ j ∈ good, halfInterval (halfStart m y) j, scaledRadialError m q s := hsum.symm
    _ ≤ ∫ s in Icc (m - y) (m + y), scaledRadialError m q s :=
      setIntegral_mono_set (continuous_scaledRadialError m q).integrableOn_Icc
        (ae_of_all _ fun _ => sq_nonneg _) (ae_of_all _ hunion)

/-- The integrand after the paper's substitution `u = πm(t-1)`. -/
def phaseRadialError (m : ℝ) (q : Polynomial ℝ) (u : ℝ) : ℝ :=
  (sin (π * m + u) - q.eval (1 + u / (π * m))) ^ 2

lemma phaseRadialError_affine (m : ℝ) (hm : m ≠ 0) (q : Polynomial ℝ) (s : ℝ) :
    phaseRadialError m q (π * s + -(π * m)) = scaledRadialError m q s := by
  unfold phaseRadialError scaledRadialError
  congr 2
  · congr 1; ring
  · congr 1; field_simp; ring

lemma phaseRadialError_window_lower {m y : ℝ} {n₀ : ℕ}
    (hy : 4 * n₀ ≤ y) (hn₀ : 2 ≤ n₀) (hm : m ≠ 0)
    (q : Polynomial.degreeLT ℝ (n₀ / 2)) :
    π * y / 8 ≤ ∫ u in Icc (-(π * y)) (π * y), phaseRadialError m q u := by
  have hy0 : 0 ≤ y := le_trans (by positivity) hy
  have hchange :
      π * (∫ s in Icc (m - y) (m + y), scaledRadialError m q s) =
        ∫ u in Icc (-(π * y)) (π * y), phaseRadialError m q u := by
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith),
      integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by nlinarith [mul_nonneg pi_pos.le hy0])]
    have h := intervalIntegral.smul_integral_comp_mul_add
      (a := m - y) (b := m + y) (phaseRadialError m q) π (-(π * m))
    simp only [smul_eq_mul, phaseRadialError_affine m hm] at h
    convert h using 1
    congr 1 <;> ring
  rw [← hchange]
  have h := mul_le_mul_of_nonneg_left (scaledRadialError_window_lower hy hn₀ hm q) pi_pos.le
  simpa [mul_div_assoc] using h

lemma phaseRadialError_original (m : ℝ) (hm : m ≠ 0) (q : Polynomial ℝ) (t : ℝ) :
    phaseRadialError m q ((π * m) * t + -(π * m)) = radialError m q t := by
  unfold phaseRadialError radialError
  congr 2
  · congr 1; ring
  · congr 1; field_simp; ring

/-- The unweighted local estimate in the original chi-square coordinate. -/
theorem radialError_local_lower (d n₀ : ℕ) (hd : 0 < d) (hn₀ : 2 ≤ n₀)
    (m : ℝ) (hm : 4 * n₀ * sqrt d ≤ m)
    (q : Polynomial.degreeLT ℝ (n₀ / 2)) :
    1 / (8 * sqrt d) ≤
      ∫ t in Icc (1 - 1 / sqrt d) (1 + 1 / sqrt d), radialError m q t := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hsqrt : 0 < sqrt d := sqrt_pos.2 hdR
  have hmpos : 0 < m := lt_of_lt_of_le (by positivity) hm
  let y : ℝ := m / sqrt d
  have hy : 4 * (n₀ : ℝ) ≤ y := by
    dsimp [y]
    exact (le_div_iff₀ hsqrt).2 (by simpa using hm)
  have hwindow := phaseRadialError_window_lower hy hn₀ hmpos.ne' q
  have hab : (1 - 1 / sqrt d : ℝ) ≤ 1 + 1 / sqrt d := by
    have hinv : 0 < (1 : ℝ) / sqrt d := div_pos one_pos hsqrt
    linarith
  have hy0 : 0 ≤ y := le_trans (by positivity) hy
  -- The exact substitution in the manuscript, including its Jacobian πm.
  have hchange :
      (π * m) * (∫ t in Icc (1 - 1 / sqrt d) (1 + 1 / sqrt d), radialError m q t) =
        ∫ u in Icc (-(π * y)) (π * y), phaseRadialError m q u := by
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab,
      integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by nlinarith [mul_nonneg pi_pos.le hy0])]
    have h := intervalIntegral.smul_integral_comp_mul_add
      (a := 1 - 1 / sqrt d) (b := 1 + 1 / sqrt d)
      (phaseRadialError m q) (π * m) (-(π * m))
    simp only [smul_eq_mul, phaseRadialError_original m hmpos.ne'] at h
    convert h using 1
    congr 1 <;> dsimp [y] <;> field_simp <;> ring
  have hleft : (π * m) * (1 / (8 * sqrt d)) = π * y / 8 := by
    dsimp [y]
    field_simp
  have hmπ : 0 < π * m := mul_pos pi_pos hmpos
  nlinarith [hwindow, hchange, hleft]

/-- Lemmas 5.2 and the local sign-change estimate combine to give the
uniform weighted approximation lower bound used in Lemma 5.3. -/
theorem radialError_weighted_lower (d n₀ : ℕ) (hd : chiSquareThreshold ≤ d) (hn₀ : 2 ≤ n₀)
    (m : ℝ) (hm : 4 * n₀ * sqrt d ≤ m)
    (q : Polynomial.degreeLT ℝ (n₀ / 2)) :
    (exp (-2) / 8) / 8 ≤ ∫ t in Ioi (0 : ℝ), radialError m q t * chiSqDensity d t := by
  have hd16 : 16 ≤ d := chiSquareThreshold_ge_sixteen.trans hd
  have hdpos : 0 < d := by omega
  have hdR : (0 : ℝ) < d := by exact_mod_cast hdpos
  have hsqrt : 0 < sqrt d := sqrt_pos.2 hdR
  have hsqrt4 : (4 : ℝ) ≤ sqrt d := by
    have hd16R : (16 : ℝ) ≤ d := by exact_mod_cast hd16
    nlinarith [sq_sqrt hdR.le, sqrt_nonneg (d : ℝ)]
  let J : Set ℝ := Icc (1 - 1 / sqrt d) (1 + 1 / sqrt d)
  have hJsub : J ⊆ Ioi (0 : ℝ) := by
    intro t ht
    have hinv : (1 : ℝ) / sqrt d ≤ 1 / 4 := by
      rw [div_le_iff₀ hsqrt]
      nlinarith
    exact (by dsimp [J] at ht; linarith [ht.1] : 0 < t)
  have hlocal := radialError_local_lower d n₀ hdpos hn₀ m hm q
  have herrLocal : IntegrableOn (radialError m q) J := by
    apply Continuous.integrableOn_Icc
    unfold radialError
    fun_prop
  have hglobal : Integrable (fun t => radialError m q t * chiSqDensity d t) :=
    integrable_mul_chiSqDensity hdpos (radialError m q)
      (integrable_radialError_chiSqMeasure hdpos m q)
  have hweightedLocal :
      (exp (-2) / 8) * sqrt d * (∫ t in J, radialError m q t) ≤
        ∫ t in J, radialError m q t * chiSqDensity d t := by
    rw [← MeasureTheory.integral_const_mul]
    refine setIntegral_mono_on (herrLocal.const_mul _) hglobal.integrableOn measurableSet_Icc ?_
    intro t ht
    simpa [radialError, mul_comm, mul_left_comm, mul_assoc] using
      mul_le_mul_of_nonneg_left (chi_square_local_density d hd t ht)
        (sq_nonneg (sin (π * m * t) - q.val.eval t))
  have hconstant : (exp (-2) / 8) / 8 ≤
      (exp (-2) / 8) * sqrt d * (∫ t in J, radialError m q t) := by
    have hnonneg : 0 ≤ (exp (-2) / 8) * sqrt (d : ℝ) :=
      mul_nonneg (by positivity) (sqrt_nonneg (d : ℝ))
    have hmul : ((exp (-2) / 8) * sqrt d) * (1 / (8 * sqrt d)) ≤
        ((exp (-2) / 8) * sqrt d) * (∫ t in J, radialError m q t) :=
      mul_le_mul_of_nonneg_left hlocal hnonneg
    have hsimplify : (exp (-2) / 8) * sqrt d * (1 / (8 * sqrt d)) =
        (exp (-2) / 8) / 8 := by
      field_simp
    rw [hsimplify] at hmul
    exact hmul
  calc
    (exp (-2) / 8) / 8 ≤ ∫ t in J, radialError m q t * chiSqDensity d t :=
      hconstant.trans hweightedLocal
    _ ≤ ∫ t in Ioi (0 : ℝ), radialError m q t * chiSqDensity d t :=
      setIntegral_mono_set hglobal.integrableOn
        (ae_of_all _ fun t => mul_nonneg (sq_nonneg _) (chiSqDensity_nonneg hdpos t))
        (ae_of_all _ hJsub)

end

end GaussianDepthSeparation
