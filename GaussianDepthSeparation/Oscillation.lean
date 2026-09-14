/-
GaussianDepthSeparation §5 — the sign-change estimate used in Lemma 5.3.
-/
import GaussianDepthSeparation.RadialDistance
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Algebra.Order.Floor.Ring

namespace GaussianDepthSeparation

open MeasureTheory Real Set Polynomial
open intervalIntegral
open scoped Interval NNReal ENNReal Nat

noncomputable section

def scaledRadialError (m : ℝ) (q : Polynomial ℝ) (s : ℝ) : ℝ :=
  (sin (π * s) - q.eval (s / m)) ^ 2

lemma continuous_scaledRadialError (m : ℝ) (q : Polynomial ℝ) :
    Continuous (scaledRadialError m q) := by
  unfold scaledRadialError
  fun_prop

lemma continuous_pos_on_Ioo_of_no_zero {f : ℝ → ℝ} {a b x₀ : ℝ}
    (hf : Continuous f) (hx₀ : x₀ ∈ Ioo a b) (hpos : 0 < f x₀)
    (hzero : ∀ x ∈ Ioo a b, f x ≠ 0) {x : ℝ} (hx : x ∈ Ioo a b) :
    0 < f x := by
  by_contra hnot
  have hxnonpos : f x ≤ 0 := le_of_not_gt hnot
  rcases le_total x x₀ with hxx₀ | hx₀x
  · have hmem : (0 : ℝ) ∈ Icc (f x) (f x₀) := ⟨hxnonpos, hpos.le⟩
    obtain ⟨z, hz, hzf⟩ :=
      (intermediate_value_Icc hxx₀ hf.continuousOn hmem)
    exact hzero z ⟨lt_of_lt_of_le hx.1 hz.1, lt_of_le_of_lt hz.2 hx₀.2⟩ hzf
  · have hmem : (0 : ℝ) ∈ Icc (f x) (f x₀) := ⟨hxnonpos, hpos.le⟩
    obtain ⟨z, hz, hzf⟩ :=
      (intermediate_value_Icc' hx₀x hf.continuousOn hmem)
    exact hzero z ⟨lt_of_lt_of_le hx₀.1 hz.1, lt_of_le_of_lt hz.2 hx.2⟩ hzf

lemma continuous_neg_on_Ioo_of_no_zero {f : ℝ → ℝ} {a b x₀ : ℝ}
    (hf : Continuous f) (hx₀ : x₀ ∈ Ioo a b) (hneg : f x₀ < 0)
    (hzero : ∀ x ∈ Ioo a b, f x ≠ 0) {x : ℝ} (hx : x ∈ Ioo a b) :
    f x < 0 := by
  have hp := continuous_pos_on_Ioo_of_no_zero hf.neg hx₀ (by simpa) (fun y hy h =>
    hzero y hy (neg_eq_zero.mp h)) hx
  simpa using hp

lemma sin_pi_mul_nonneg_first_half (z : ℤ) {s : ℝ}
    (hs : s ∈ Ioo (2 * (z : ℝ)) (2 * (z : ℝ) + 1)) :
    0 ≤ sin (π * s) := by
  let u := π * (s - 2 * (z : ℝ))
  have hu0 : 0 ≤ u := by
    dsimp [u]
    exact mul_nonneg Real.pi_pos.le (by linarith [hs.1])
  have hupi : u ≤ π := by
    dsimp [u]
    have h := mul_le_mul_of_nonneg_left (show s - 2 * (z : ℝ) ≤ 1 by linarith [hs.2])
      Real.pi_pos.le
    simpa using h
  have harg : π * s = u + z * (2 * π) := by
    dsimp [u]
    ring
  rw [harg, Real.sin_add_int_mul_two_pi]
  exact sin_nonneg_of_nonneg_of_le_pi hu0 hupi

lemma sin_pi_mul_nonpos_second_half (z : ℤ) {s : ℝ}
    (hs : s ∈ Ioo (2 * (z : ℝ) + 1) (2 * (z : ℝ) + 2)) :
    sin (π * s) ≤ 0 := by
  let u := π * (s - (2 * (z : ℝ) + 2))
  have hu0 : u ≤ 0 := by
    dsimp [u]
    exact mul_nonpos_of_nonneg_of_nonpos Real.pi_pos.le (by linarith [hs.2])
  have hupi : -π ≤ u := by
    dsimp [u]
    have h := mul_le_mul_of_nonneg_left
      (show (-1 : ℝ) ≤ s - (2 * (z : ℝ) + 2) by linarith [hs.1]) Real.pi_pos.le
    nlinarith
  have harg : π * s = u + ((z + 1 : ℤ) : ℝ) * (2 * π) := by
    dsimp [u]
    push_cast
    ring
  rw [harg, Real.sin_add_int_mul_two_pi]
  exact sin_nonpos_of_nonpos_of_neg_pi_le hu0 hupi

lemma integral_sin_sq_first_half (z : ℤ) :
    ∫ s in Ioo (2 * (z : ℝ)) (2 * (z : ℝ) + 1), sin (π * s) ^ 2 = 1 / 2 := by
  rw [← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le (by linarith)]
  have h := intervalIntegral.mul_integral_comp_mul_left
    (a := 2 * (z : ℝ)) (b := 2 * (z : ℝ) + 1)
    (f := fun u : ℝ => sin u ^ 2) π
  rw [integral_sin_sq] at h
  have hsin0 : sin (π * (2 * (z : ℝ))) = 0 := by
    rw [show π * (2 * (z : ℝ)) = (2 * z : ℤ) * π by push_cast; ring,
      Real.sin_int_mul_pi]
  have hsin1 : sin (π * (2 * (z : ℝ) + 1)) = 0 := by
    rw [show π * (2 * (z : ℝ) + 1) = (2 * z + 1 : ℤ) * π by push_cast; ring,
      Real.sin_int_mul_pi]
  simp only [hsin0, hsin1, zero_mul, sub_zero, zero_add] at h
  have hpi : π ≠ 0 := ne_of_gt Real.pi_pos
  apply (mul_left_cancel₀ hpi)
  calc
    π * (∫ (x : ℝ) in 2 * (z : ℝ)..2 * (z : ℝ) + 1, sin (π * x) ^ 2) =
        (π * (2 * (z : ℝ) + 1) - π * (2 * (z : ℝ))) / 2 := h
    _ = π * (1 / 2) := by ring

lemma integral_sin_sq_second_half (z : ℤ) :
    ∫ s in Ioo (2 * (z : ℝ) + 1) (2 * (z : ℝ) + 2), sin (π * s) ^ 2 = 1 / 2 := by
  rw [← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le (by linarith)]
  have h := intervalIntegral.mul_integral_comp_mul_left
    (a := 2 * (z : ℝ) + 1) (b := 2 * (z : ℝ) + 2)
    (f := fun u : ℝ => sin u ^ 2) π
  rw [integral_sin_sq] at h
  have hsin1 : sin (π * (2 * (z : ℝ) + 1)) = 0 := by
    rw [show π * (2 * (z : ℝ) + 1) = (2 * z + 1 : ℤ) * π by push_cast; ring,
      Real.sin_int_mul_pi]
  have hsin2 : sin (π * (2 * (z : ℝ) + 2)) = 0 := by
    rw [show π * (2 * (z : ℝ) + 2) = (2 * z + 2 : ℤ) * π by push_cast; ring,
      Real.sin_int_mul_pi]
  simp only [hsin1, hsin2, zero_mul, sub_zero, zero_add] at h
  have hpi : π ≠ 0 := ne_of_gt Real.pi_pos
  apply (mul_left_cancel₀ hpi)
  calc
    π * (∫ (x : ℝ) in 2 * (z : ℝ) + 1..2 * (z : ℝ) + 2,
        sin (π * x) ^ 2) =
        (π * (2 * (z : ℝ) + 2) - π * (2 * (z : ℝ) + 1)) / 2 := h
    _ = π * (1 / 2) := by ring

/-- A root-free full sine period contains a half-period on which the
polynomial and sine have opposite signs. -/
lemma scaledRadialError_block_lower {m : ℝ} (q : Polynomial ℝ)
    (z : ℤ)
    (hzero : ∀ s ∈ Ioo (2 * (z : ℝ)) (2 * (z : ℝ) + 2),
      q.eval (s / m) ≠ 0) :
    1 / 2 ≤ ∫ s in Ioo (2 * (z : ℝ)) (2 * (z : ℝ) + 2),
      scaledRadialError m q s := by
  let f : ℝ → ℝ := fun s => q.eval (s / m)
  have hf : Continuous f := by dsimp [f]; fun_prop
  have hx₀ : (2 * (z : ℝ) + 1 : ℝ) ∈
      Ioo (2 * (z : ℝ)) (2 * (z : ℝ) + 2) := by constructor <;> linarith
  have hmid : f (2 * (z : ℝ) + 1) ≠ 0 := hzero _ hx₀
  have herr : IntegrableOn (scaledRadialError m q)
      (Ioo (2 * (z : ℝ)) (2 * (z : ℝ) + 2)) :=
    (continuous_scaledRadialError m q).integrableOn_Icc.mono_set Ioo_subset_Icc_self
  rcases lt_or_gt_of_ne hmid with hneg | hpos
  · have hnegall : ∀ s ∈ Ioo (2 * (z : ℝ)) (2 * (z : ℝ) + 2), f s < 0 :=
      fun s hs => continuous_neg_on_Ioo_of_no_zero hf hx₀ hneg hzero hs
    have hhalf : ∫ s in Ioo (2 * (z : ℝ)) (2 * (z : ℝ) + 1), sin (π * s) ^ 2 ≤
        ∫ s in Ioo (2 * (z : ℝ)) (2 * (z : ℝ) + 1), scaledRadialError m q s := by
      have hsinInt : IntegrableOn (fun s : ℝ => sin (π * s) ^ 2)
          (Ioo (2 * (z : ℝ)) (2 * (z : ℝ) + 1)) :=
        (by fun_prop : Continuous (fun s : ℝ => sin (π * s) ^ 2)).integrableOn_Icc.mono_set
          Ioo_subset_Icc_self
      have herrHalf : IntegrableOn (scaledRadialError m q)
          (Ioo (2 * (z : ℝ)) (2 * (z : ℝ) + 1)) :=
        (continuous_scaledRadialError m q).integrableOn_Icc.mono_set Ioo_subset_Icc_self
      refine setIntegral_mono_on
        hsinInt herrHalf measurableSet_Ioo fun s hs => ?_
      have hsin := sin_pi_mul_nonneg_first_half z hs
      have hq : q.eval (s / m) < 0 := hnegall s ⟨hs.1, by linarith [hs.2]⟩
      unfold scaledRadialError
      nlinarith [sq_nonneg (q.eval (s / m)),
        mul_nonpos_of_nonneg_of_nonpos hsin hq.le]
    calc
      1 / 2 = ∫ s in Ioo (2 * (z : ℝ)) (2 * (z : ℝ) + 1),
          sin (π * s) ^ 2 := (integral_sin_sq_first_half z).symm
      _ ≤ ∫ s in Ioo (2 * (z : ℝ)) (2 * (z : ℝ) + 1),
          scaledRadialError m q s := hhalf
      _ ≤ ∫ s in Ioo (2 * (z : ℝ)) (2 * (z : ℝ) + 2),
          scaledRadialError m q s := setIntegral_mono_set herr
            (ae_of_all _ fun _ => sq_nonneg _)
            (Filter.Eventually.of_forall fun s hs => ⟨hs.1, by linarith [hs.2]⟩)
  · have hposall : ∀ s ∈ Ioo (2 * (z : ℝ)) (2 * (z : ℝ) + 2), 0 < f s :=
      fun s hs => continuous_pos_on_Ioo_of_no_zero hf hx₀ hpos hzero hs
    have hhalf : ∫ s in Ioo (2 * (z : ℝ) + 1) (2 * (z : ℝ) + 2),
        sin (π * s) ^ 2 ≤
        ∫ s in Ioo (2 * (z : ℝ) + 1) (2 * (z : ℝ) + 2),
          scaledRadialError m q s := by
      have hsinInt : IntegrableOn (fun s : ℝ => sin (π * s) ^ 2)
          (Ioo (2 * (z : ℝ) + 1) (2 * (z : ℝ) + 2)) :=
        (by fun_prop : Continuous (fun s : ℝ => sin (π * s) ^ 2)).integrableOn_Icc.mono_set
          Ioo_subset_Icc_self
      have herrHalf : IntegrableOn (scaledRadialError m q)
          (Ioo (2 * (z : ℝ) + 1) (2 * (z : ℝ) + 2)) :=
        (continuous_scaledRadialError m q).integrableOn_Icc.mono_set Ioo_subset_Icc_self
      refine setIntegral_mono_on
        hsinInt herrHalf measurableSet_Ioo fun s hs => ?_
      have hsin := sin_pi_mul_nonpos_second_half z hs
      have hq : 0 < q.eval (s / m) := hposall s ⟨by linarith [hs.1], hs.2⟩
      unfold scaledRadialError
      nlinarith [sq_nonneg (q.eval (s / m)),
        mul_nonpos_of_nonpos_of_nonneg hsin hq.le]
    calc
      1 / 2 = ∫ s in Ioo (2 * (z : ℝ) + 1) (2 * (z : ℝ) + 2),
          sin (π * s) ^ 2 := (integral_sin_sq_second_half z).symm
      _ ≤ ∫ s in Ioo (2 * (z : ℝ) + 1) (2 * (z : ℝ) + 2),
          scaledRadialError m q s := hhalf
      _ ≤ ∫ s in Ioo (2 * (z : ℝ)) (2 * (z : ℝ) + 2),
          scaledRadialError m q s := setIntegral_mono_set herr
            (ae_of_all _ fun _ => sq_nonneg _)
            (Filter.Eventually.of_forall fun s hs => ⟨by linarith [hs.1], hs.2⟩)

lemma scaledRadialError_block_lower_zero (m : ℝ) (z : ℤ) :
    1 / 2 ≤ ∫ s in Ioo (2 * (z : ℝ)) (2 * (z : ℝ) + 2),
      scaledRadialError m 0 s := by
  have herr : IntegrableOn (scaledRadialError m 0)
      (Ioo (2 * (z : ℝ)) (2 * (z : ℝ) + 2)) :=
    (continuous_scaledRadialError m 0).integrableOn_Icc.mono_set Ioo_subset_Icc_self
  calc
    1 / 2 = ∫ s in Ioo (2 * (z : ℝ)) (2 * (z : ℝ) + 1),
        sin (π * s) ^ 2 := (integral_sin_sq_first_half z).symm
    _ = ∫ s in Ioo (2 * (z : ℝ)) (2 * (z : ℝ) + 1),
        scaledRadialError m 0 s := by simp [scaledRadialError]
    _ ≤ ∫ s in Ioo (2 * (z : ℝ)) (2 * (z : ℝ) + 2),
        scaledRadialError m 0 s := setIntegral_mono_set herr
          (ae_of_all _ fun _ => sq_nonneg _)
          (Filter.Eventually.of_forall fun s hs => ⟨hs.1, by linarith [hs.2]⟩)

private def periodStart (m y : ℝ) : ℤ := ⌊(m - y) / 2⌋ + 1

private def periodCount (y : ℝ) : ℕ := ⌊y⌋₊ - 1

private def periodBlock (m y : ℝ) (j : ℕ) : Set ℝ :=
  Ioo (2 * ((periodStart m y + j : ℤ) : ℝ))
    (2 * ((periodStart m y + j : ℤ) : ℝ) + 2)

lemma periodBlock_pairwise_disjoint (m y : ℝ) :
    (Set.univ : Set ℕ).Pairwise (Function.onFun Disjoint (periodBlock m y)) := by
  intro i _ j _ hij
  change Disjoint (periodBlock m y i) (periodBlock m y j)
  dsimp only [periodBlock]
  rw [Set.Ioo_disjoint_Ioo]
  rcases lt_or_gt_of_ne hij with hijlt | hjilt
  ·
    have hij' : (i : ℝ) + 1 ≤ j := by exact_mod_cast (Nat.succ_le_iff.mpr hijlt)
    have hends : 2 * ((periodStart m y + i : ℤ) : ℝ) + 2 ≤
        2 * ((periodStart m y + j : ℤ) : ℝ) := by
      push_cast
      linarith
    exact (min_le_left _ _).trans (hends.trans (le_max_right _ _))
  ·
    have hji' : (j : ℝ) + 1 ≤ i := by exact_mod_cast (Nat.succ_le_iff.mpr hjilt)
    have hends : 2 * ((periodStart m y + j : ℤ) : ℝ) + 2 ≤
        2 * ((periodStart m y + i : ℤ) : ℝ) := by
      push_cast
      linarith
    exact (min_le_right _ _).trans (hends.trans (le_max_left _ _))

lemma periodBlock_subset_window {m y : ℝ} (hy : 2 ≤ y) {j : ℕ}
    (hj : j < periodCount y) : periodBlock m y j ⊆ Icc (m - y) (m + y) := by
  intro s hs
  have hleftFloor := Int.lt_floor_add_one ((m - y) / 2)
  have hfloorY := Nat.floor_le (by linarith : 0 ≤ y)
  have hfloorTwo : 2 ≤ ⌊y⌋₊ := Nat.le_floor hy
  have hcount : periodCount y + 1 = ⌊y⌋₊ := by
    dsimp [periodCount]
    omega
  have hjle : j + 1 ≤ periodCount y := Nat.succ_le_iff.mpr hj
  have hjR : (j : ℝ) + 2 ≤ y := by
    have hjfloor : j + 2 ≤ ⌊y⌋₊ := by rw [← hcount]; omega
    have hjcast : ((j + 2 : ℕ) : ℝ) ≤ (⌊y⌋₊ : ℝ) := by exact_mod_cast hjfloor
    push_cast at hjcast
    exact hjcast.trans (by linarith [hfloorY])
  constructor
  · have h := hs.1
    dsimp [periodBlock, periodStart] at h
    push_cast at h
    linarith
  · have hfloorStart := Int.floor_le ((m - y) / 2)
    have h := hs.2
    dsimp [periodBlock, periodStart] at h
    push_cast at h
    linarith

private def blockHasRoot (m y : ℝ) (q : Polynomial ℝ) (j : ℕ) : Prop :=
  ∃ s ∈ periodBlock m y j, q.eval (s / m) = 0

private noncomputable def badPeriods (m y : ℝ) (q : Polynomial ℝ) : Finset ℕ :=
  @Finset.filter ℕ (blockHasRoot m y q) (fun _ => Classical.propDecidable _)
    (Finset.range (periodCount y))

lemma badPeriods_card_le_natDegree {m y : ℝ} (hm : m ≠ 0) {q : Polynomial ℝ}
    (hq : q ≠ 0) : (badPeriods m y q).card ≤ q.natDegree := by
  classical
  let root : {j // j ∈ badPeriods m y q} → ℝ := fun j =>
    Classical.choose (by
      have hjmem := j.property
      change j.val ∈ (Finset.range (periodCount y)).filter (blockHasRoot m y q) at hjmem
      rw [Finset.mem_filter] at hjmem
      exact hjmem.2)
  have hroot (j : {j // j ∈ badPeriods m y q}) :
      root j ∈ periodBlock m y j ∧ q.eval (root j / m) = 0 :=
    Classical.choose_spec (by
      have hjmem := j.property
      change j.val ∈ (Finset.range (periodCount y)).filter (blockHasRoot m y q) at hjmem
      rw [Finset.mem_filter] at hjmem
      exact hjmem.2)
  let toRoot : {j // j ∈ badPeriods m y q} → {x // x ∈ q.roots.toFinset} := fun j =>
    ⟨root j / m, by
      rw [Multiset.mem_toFinset, Polynomial.mem_roots hq]
      exact (hroot j).2⟩
  have htoRoot : Function.Injective toRoot := by
    intro i j hij
    have hquot : root i / m = root j / m := congrArg Subtype.val hij
    have hrootEq : root i = root j := by
      calc
        root i = (root i / m) * m := by field_simp
        _ = (root j / m) * m := by rw [hquot]
        _ = root j := by field_simp
    apply Subtype.ext
    by_contra hne
    have hdisjoint := periodBlock_pairwise_disjoint m y
      (Set.mem_univ i.val) (Set.mem_univ j.val) hne
    exact (Set.disjoint_left.mp hdisjoint) (hroot i).1
      (by simpa [hrootEq] using (hroot j).1)
  calc
    (badPeriods m y q).card = Fintype.card {j // j ∈ badPeriods m y q} := by simp
    _ ≤ Fintype.card {x // x ∈ q.roots.toFinset} :=
      Fintype.card_le_of_injective toRoot htoRoot
    _ = q.roots.toFinset.card := by simp
    _ ≤ q.roots.card := Multiset.toFinset_card_le _
    _ ≤ q.natDegree := Polynomial.card_roots' q

private noncomputable def usablePeriods (m y : ℝ) (q : Polynomial ℝ) : Finset ℕ :=
  if q = 0 then Finset.range (periodCount y)
  else @Finset.filter ℕ (fun j => ¬blockHasRoot m y q j)
    (fun j => @instDecidableNot (blockHasRoot m y q j) (Classical.propDecidable _))
    (Finset.range (periodCount y))

lemma usablePeriods_mem_range {m y : ℝ} {q : Polynomial ℝ} {j : ℕ}
    (hj : j ∈ usablePeriods m y q) : j < periodCount y := by
  classical
  by_cases hq : q = 0
  · simpa [usablePeriods, hq] using hj
  · have hj' := hj
    rw [usablePeriods, ite_eq_right hq] at hj'
    exact Finset.mem_range.mp (Finset.mem_filter.mp hj').1

lemma usablePeriods_block_lower {m y : ℝ} (q : Polynomial ℝ) {j : ℕ}
    (hj : j ∈ usablePeriods m y q) :
    1 / 2 ≤ ∫ s in periodBlock m y j, scaledRadialError m q s := by
  classical
  by_cases hq : q = 0
  · subst q
    exact scaledRadialError_block_lower_zero m (periodStart m y + j)
  · have hj' := hj
    rw [usablePeriods, ite_eq_right hq] at hj'
    have hno := (Finset.mem_filter.mp hj').2
    apply scaledRadialError_block_lower q (periodStart m y + j)
    intro s hs hroot
    exact hno ⟨s, hs, hroot⟩

lemma periodCount_gt_sub_two {y : ℝ} (hy : 2 ≤ y) :
    y - 2 < (periodCount y : ℝ) := by
  have hfloorTwo : 2 ≤ ⌊y⌋₊ := Nat.le_floor hy
  have hlt := Nat.lt_floor_add_one y
  have hcast : (periodCount y : ℝ) = (⌊y⌋₊ : ℝ) - 1 := by
    dsimp [periodCount]
    rw [Nat.cast_sub (by omega)]
    norm_num
  rw [hcast]
  linarith

lemma usablePeriods_card_lower {m y : ℝ} {n₀ : ℕ} (hy : 4 * n₀ ≤ y)
    (hn₀ : 2 ≤ n₀) (hm : m ≠ 0) (q : Polynomial.degreeLT ℝ (n₀ / 2)) :
    y / 4 ≤ ((usablePeriods m y q : Finset ℕ).card : ℝ) := by
  classical
  have hy2 : 2 ≤ y := by
    have hn₀R : (2 : ℝ) ≤ n₀ := by exact_mod_cast hn₀
    linarith
  have hcount := periodCount_gt_sub_two hy2
  by_cases hq : (q : Polynomial ℝ) = 0
  · have hcard : (usablePeriods m y q).card = periodCount y := by
      simp [usablePeriods, hq]
    rw [hcard]
    have hn₀R : (2 : ℝ) ≤ n₀ := by exact_mod_cast hn₀
    linarith

  · have hdegree : q.val.natDegree < n₀ / 2 :=
      (Polynomial.natDegree_lt_iff_degree_lt hq).2
        (Polynomial.mem_degreeLT.mp q.property)
    have hbadNat : (badPeriods m y q).card ≤ n₀ :=
      (badPeriods_card_le_natDegree hm hq).trans (by omega)
    have haddNat : (badPeriods m y q).card + (usablePeriods m y q).card =
        periodCount y := by
      have huse : usablePeriods m y q =
          (Finset.range (periodCount y)).filter
            (fun j => ¬blockHasRoot m y q j) := by
        unfold usablePeriods
        rw [ite_eq_right hq]
      have hbad : badPeriods m y q =
          (Finset.range (periodCount y)).filter (blockHasRoot m y q) := by
        unfold badPeriods
        exact Finset.filter_congr_decidable _ _ _
      rw [hbad, huse]
      simpa using Finset.card_filter_add_card_filter_not
        (s := Finset.range (periodCount y)) (blockHasRoot m y q)
    have hbadR : ((badPeriods m y q).card : ℝ) ≤ n₀ := by exact_mod_cast hbadNat
    have haddR : ((badPeriods m y q).card : ℝ) +
        ((usablePeriods m y q).card : ℝ) = periodCount y := by exact_mod_cast haddNat
    have hn₀R : (2 : ℝ) ≤ n₀ := by exact_mod_cast hn₀
    linarith

/-- The paper's root-counting estimate in the rescaled variable `s = m t`.
At least a fixed fraction of the periods in the central window are root-free. -/
theorem scaledRadialError_window_lower {m y : ℝ} {n₀ : ℕ}
    (hy : 4 * n₀ ≤ y) (hn₀ : 2 ≤ n₀) (hm : m ≠ 0)
    (q : Polynomial.degreeLT ℝ (n₀ / 2)) :
    y / 8 ≤ ∫ s in Icc (m - y) (m + y), scaledRadialError m q s := by
  classical
  have hy2 : 2 ≤ y := by
    have hn₀R : (2 : ℝ) ≤ n₀ := by exact_mod_cast hn₀
    linarith
  let good := usablePeriods m y q
  have hcard : y / 4 ≤ (good.card : ℝ) := usablePeriods_card_lower hy hn₀ hm q
  have hpairwise : (↑good : Set ℕ).Pairwise
      (Function.onFun Disjoint (periodBlock m y)) := by
    intro i _ j _ hij
    exact periodBlock_pairwise_disjoint m y (Set.mem_univ i) (Set.mem_univ j) hij
  have hblockInt (j : ℕ) (hj : j ∈ good) :
      IntegrableOn (scaledRadialError m q) (periodBlock m y j) :=
    (continuous_scaledRadialError m q).integrableOn_Icc.mono_set Ioo_subset_Icc_self
  have hsum := integral_biUnion_finset good
    (fun _j _ => measurableSet_Ioo) hpairwise hblockInt
  have hunion : (⋃ j ∈ good, periodBlock m y j) ⊆ Icc (m - y) (m + y) := by
    intro s hs
    simp only [Set.mem_iUnion] at hs
    obtain ⟨j, hj, hs⟩ := hs
    exact periodBlock_subset_window hy2 (usablePeriods_mem_range hj) hs
  have hwindowInt : IntegrableOn (scaledRadialError m q) (Icc (m - y) (m + y)) :=
    (continuous_scaledRadialError m q).integrableOn_Icc
  calc
    y / 8 ≤ (good.card : ℝ) / 2 := by linarith
    _ = ∑ _j ∈ good, (1 / 2 : ℝ) := by simp [div_eq_mul_inv]
    _ ≤ ∑ j ∈ good, ∫ s in periodBlock m y j, scaledRadialError m q s := by
      exact Finset.sum_le_sum fun j hj => usablePeriods_block_lower q hj
    _ = ∫ s in ⋃ j ∈ good, periodBlock m y j, scaledRadialError m q s := hsum.symm
    _ ≤ ∫ s in Icc (m - y) (m + y), scaledRadialError m q s :=
      setIntegral_mono_set hwindowInt (ae_of_all _ fun _ => sq_nonneg _)
        (ae_of_all _ hunion)

lemma scaledRadialError_mul (m : ℝ) (hm : m ≠ 0) (q : Polynomial ℝ) (t : ℝ) :
    scaledRadialError m q (m * t) = radialError m q t := by
  simp [scaledRadialError, radialError, hm]
  congr 2
  ring_nf

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
  have hwindow := scaledRadialError_window_lower hy hn₀ hmpos.ne' q
  have hab : (1 - 1 / sqrt d : ℝ) ≤ 1 + 1 / sqrt d := by
    have hinv : 0 < (1 : ℝ) / sqrt d := div_pos one_pos hsqrt
    linarith
  have hwindowEnds : m - y ≤ m + y := by
    have hy0 : 0 ≤ y := le_trans (by positivity) hy
    linarith
  have hchange :
      m * (∫ t in Icc (1 - 1 / sqrt d) (1 + 1 / sqrt d), radialError m q t) =
        ∫ s in Icc (m - y) (m + y), scaledRadialError m q s := by
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab,
      integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hwindowEnds]
    calc
      m * (∫ t in (1 - 1 / sqrt d)..(1 + 1 / sqrt d), radialError m q t) =
          m * (∫ t in (1 - 1 / sqrt d)..(1 + 1 / sqrt d),
            scaledRadialError m q (m * t)) := by
              congr 2 with t
              exact (scaledRadialError_mul m hmpos.ne' q t).symm
      _ = ∫ s in m * (1 - 1 / sqrt d)..m * (1 + 1 / sqrt d),
          scaledRadialError m q s := intervalIntegral.mul_integral_comp_mul_left m
      _ = ∫ s in (m - y)..(m + y), scaledRadialError m q s := by
          congr 2 <;> dsimp [y] <;> field_simp
  have hleft : m * (1 / (8 * sqrt d)) = y / 8 := by
    dsimp [y]
    field_simp
  nlinarith [hwindow, hchange, hleft]

/-- Lemmas 5.2 and the local sign-change estimate combine to give the
uniform weighted approximation lower bound used in Lemma 5.3. -/
theorem radialError_weighted_lower (d n₀ : ℕ) (hd : 16 ≤ d) (hn₀ : 2 ≤ n₀)
    (m : ℝ) (hm : 4 * n₀ * sqrt d ≤ m)
    (q : Polynomial.degreeLT ℝ (n₀ / 2)) :
    (exp (-2) / 8) / 8 ≤ ∫ t in Ioi (0 : ℝ), radialError m q t * chiSqDensity d t := by
  have hd16 : 16 ≤ d := hd
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
