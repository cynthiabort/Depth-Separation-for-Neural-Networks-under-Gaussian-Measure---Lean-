/-
The half-period and maximal-sign-block count in manuscript Lemma 5.3.
A block starts at a retained half-period whose predecessor was discarded
or had the other polynomial sign. Zeros at shared endpoints are included.
-/
import GaussianDepthSeparation.SineIntervals

namespace GaussianDepthSeparation

open MeasureTheory Real Set Polynomial
open scoped Nat

noncomputable section

def halfInterval (a : ℤ) (j : ℕ) : Set ℝ :=
  Ioo ((a : ℝ) + j) ((a : ℝ) + j + 1)

def halfMid (a : ℤ) (j : ℕ) : ℝ := (a : ℝ) + j + 1 / 2

def halfGood (f : ℝ → ℝ) (a : ℤ) (j : ℕ) : Prop :=
  ∀ s ∈ halfInterval a j, f s ≠ 0

def halfPositive (f : ℝ → ℝ) (a : ℤ) (j : ℕ) : Prop := 0 < f (halfMid a j)

def goodHalves (f : ℝ → ℝ) (a : ℤ) (N : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range N).filter (halfGood f a)

def signBlockStarts (f : ℝ → ℝ) (a : ℤ) (N : ℕ) : Finset ℕ := by
  classical
  exact (goodHalves f a N).filter (fun j => j = 0 ∨ ¬halfGood f a (j - 1) ∨
    ¬(halfPositive f a j ↔ halfPositive f a (j - 1)))

def oppositeHalves (f : ℝ → ℝ) (a : ℤ) (N : ℕ) : Finset ℕ := by
  classical
  exact (goodHalves f a N).filter (fun j => Even (a + (j : ℤ)) ↔ ¬halfPositive f a j)

lemma halfMid_mem (a : ℤ) (j : ℕ) : halfMid a j ∈ halfInterval a j := by
  constructor <;> dsimp [halfMid, halfInterval] <;> linarith

/-- In a constant-sign block, each matching half-period other than the first
has an opposing predecessor. This is the paper's `floor(s_g/2) ≥ (s_g-1)/2`
count, summed over the blocks. -/
lemma goodHalves_card_le_twice_opposite_add_blocks (f : ℝ → ℝ) (a : ℤ) (N : ℕ) :
    (goodHalves f a N).card ≤
      2 * (oppositeHalves f a N).card + (signBlockStarts f a N).card := by
  classical
  let G := goodHalves f a N
  let O := oppositeHalves f a N
  let B := signBlockStarts f a N
  have hOG : O ⊆ G := Finset.filter_subset _ _
  have hpred : ∀ j ∈ (G \ O) \ B, 0 < j ∧ j - 1 ∈ O := by
    intro j hj
    obtain ⟨hjGO, hjB⟩ := Finset.mem_sdiff.mp hj
    obtain ⟨hjG, hjO⟩ := Finset.mem_sdiff.mp hjGO
    have hjB' : ¬(j = 0 ∨ ¬halfGood f a (j - 1) ∨
        ¬(halfPositive f a j ↔ halfPositive f a (j - 1))) := by
      intro h
      exact hjB (Finset.mem_filter.mpr ⟨hjG, h⟩)
    push Not at hjB'
    have hjpos : 0 < j := Nat.pos_of_ne_zero hjB'.1
    refine ⟨hjpos, Finset.mem_filter.mpr ⟨?_, ?_⟩⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by
        have hlt := Finset.mem_range.mp (Finset.mem_filter.mp hjG).1; omega), hjB'.2.1⟩
    · have hnot : ¬(Even (a + (j : ℤ)) ↔ ¬halfPositive f a j) := by
        intro h; exact hjO (Finset.mem_filter.mpr ⟨hjG, h⟩)
      have hpar : Even (a + (j : ℤ)) ↔ ¬Even (a + ((j - 1 : ℕ) : ℤ)) := by
        have he : (j : ℤ) = ((j - 1 : ℕ) : ℤ) + 1 := by omega
        rw [he, ← add_assoc, Int.even_add_one, Int.not_even_iff_odd]
      tauto
  have hcard : ((G \ O) \ B).card ≤ O.card :=
    Finset.card_le_card_of_injOn (fun j => j - 1)
      (fun j hj => (hpred j hj).2) (fun i hi j hj he => by
        change i - 1 = j - 1 at he
        have := (hpred i hi).1
        have := (hpred j hj).1
        omega)
  have h1 := Finset.card_sdiff_add_card_eq_card hOG
  have h2 := Finset.card_le_card_sdiff_add_card (s := G \ O) (t := B)
  change G.card ≤ 2 * O.card + B.card
  omega

/-- A sign change across two retained adjacent intervals forces a zero at
their common endpoint, including the case the zero is not in either interior. -/
lemma endpoint_zero_of_sign_change {f : ℝ → ℝ} (hf : Continuous f) (b : ℝ)
    (hl : ∀ s ∈ Ioo (b - 1) b, f s ≠ 0)
    (hr : ∀ s ∈ Ioo b (b + 1), f s ≠ 0)
    (hs : ¬(0 < f (b + 1 / 2) ↔ 0 < f (b - 1 / 2))) : f b = 0 := by
  by_contra hb
  have hzero : ∀ s ∈ Ioo (b - 1) (b + 1), f s ≠ 0 := by
    intro s hs
    rcases lt_trichotomy s b with h | rfl | h
    · exact hl s ⟨hs.1, h⟩
    · exact hb
    · exact hr s ⟨h, hs.2⟩
  have hleft : b - 1 / 2 ∈ Ioo (b - 1) (b + 1) := by constructor <;> linarith
  have hright : b + 1 / 2 ∈ Ioo (b - 1) (b + 1) := by constructor <;> linarith
  rcases lt_or_gt_of_ne (hzero _ hleft) with hn | hp
  · have hn' := continuous_neg_on_Ioo_of_no_zero hf hleft hn hzero hright
    exact hs (by constructor <;> intro h <;> linarith)
  · have hp' := continuous_pos_on_Ioo_of_no_zero hf hleft hp hzero hright
    exact hs (by constructor <;> intro _ <;> assumption)

lemma signBlockStart_has_root {f : ℝ → ℝ} (hf : Continuous f) {a : ℤ} {N j : ℕ}
    (hj : j ∈ signBlockStarts f a N) (hj0 : j ≠ 0) :
    ∃ s ∈ Ioc ((j : ℝ) + a - 1) ((j : ℝ) + a), f s = 0 := by
  classical
  obtain ⟨hjG, hjstart⟩ := Finset.mem_filter.mp hj
  have hjgood := (Finset.mem_filter.mp hjG).2
  have hjpos : 0 < j := Nat.pos_of_ne_zero hj0
  have he : ((j - 1 : ℕ) : ℝ) = (j : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]; norm_num
  rcases hjstart with h0 | hbad | hsign
  · exact False.elim (hj0 h0)
  · simp only [halfGood] at hbad
    push Not at hbad
    obtain ⟨s, hs, hroot⟩ := hbad
    refine ⟨s, ?_, hroot⟩
    dsimp [halfInterval] at hs
    rw [he] at hs
    constructor <;> linarith [hs.1, hs.2]
  · by_cases hprev : halfGood f a (j - 1)
    · refine ⟨(j : ℝ) + a, ⟨by linarith, le_rfl⟩, ?_⟩
      apply endpoint_zero_of_sign_change hf
      · simpa [halfGood, halfInterval, he, add_comm, add_left_comm, add_assoc,
          sub_eq_add_neg] using hprev
      · simpa [halfGood, halfInterval, add_comm] using hjgood
      · have hR : halfMid a j = (j : ℝ) + a + 1 / 2 := by dsimp [halfMid]; ring
        have hL : halfMid a (j - 1) = (j : ℝ) + a - 1 / 2 := by
          dsimp [halfMid]; rw [he]; ring
        simpa only [halfPositive, hR, hL] using hsign
    · simp only [halfGood] at hprev
      push Not at hprev
      obtain ⟨s, hs, hroot⟩ := hprev
      refine ⟨s, ?_, hroot⟩
      dsimp [halfInterval] at hs
      rw [he] at hs
      constructor <;> linarith [hs.1, hs.2]

/-- Distinct half-open root windows contain distinct roots. -/
lemma polynomial_root_windows_card_le (q : Polynomial ℝ) (hq : q ≠ 0)
    (m : ℝ) (hm : m ≠ 0) (c : ℝ) (S : Finset ℕ)
    (hroot : ∀ j ∈ S, ∃ s ∈ Ioc ((j : ℝ) + c - 1) ((j : ℝ) + c),
      q.eval (s / m) = 0) : S.card ≤ q.natDegree := by
  classical
  let root (j : {j // j ∈ S}) := (hroot j j.property).choose
  have hr (j : {j // j ∈ S}) :
      root j ∈ Ioc ((j : ℝ) + c - 1) ((j : ℝ) + c) ∧ q.eval (root j / m) = 0 :=
    (hroot j j.property).choose_spec
  let toRoot : {j // j ∈ S} → {x // x ∈ q.roots.toFinset} := fun j =>
    ⟨root j / m, by simpa [Polynomial.mem_roots hq] using (hr j).2⟩
  have hinj : Function.Injective toRoot := by
    intro i j hij
    have he : root i = root j := (div_left_inj' hm).mp (congrArg Subtype.val hij)
    apply Subtype.ext
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · have hc : (i.val : ℝ) + 1 ≤ j.val := by exact_mod_cast hlt
      have hi := (hr i).1.2
      have hj := (hr j).1.1
      change root i ≤ (i.val : ℝ) + c at hi
      change (j.val : ℝ) + c - 1 < root j at hj
      linarith
    · have hc : (j.val : ℝ) + 1 ≤ i.val := by exact_mod_cast hlt
      have hi := (hr i).1.1
      have hj := (hr j).1.2
      change (i.val : ℝ) + c - 1 < root i at hi
      change root j ≤ (j.val : ℝ) + c at hj
      linarith
  calc
    S.card = Fintype.card {j // j ∈ S} := by simp
    _ ≤ Fintype.card {x // x ∈ q.roots.toFinset} := Fintype.card_le_of_injective toRoot hinj
    _ = q.roots.toFinset.card := by simp
    _ ≤ q.roots.card := Multiset.toFinset_card_le _
    _ ≤ q.natDegree := Polynomial.card_roots' q

lemma goodHalves_card_lower (q : Polynomial ℝ) (hq : q ≠ 0)
    (m : ℝ) (hm : m ≠ 0) (a : ℤ) (N : ℕ) :
    N ≤ (goodHalves (fun s => q.eval (s / m)) a N).card + q.natDegree := by
  classical
  let G := goodHalves (fun s => q.eval (s / m)) a N
  have hbad : ((Finset.range N) \ G).card ≤ q.natDegree := by
    apply polynomial_root_windows_card_le q hq m hm ((a : ℝ) + 1)
    intro j hj
    obtain ⟨hjN, hjG⟩ := Finset.mem_sdiff.mp hj
    have hnot : ¬halfGood (fun s => q.eval (s / m)) a j := by
      intro h; exact hjG (Finset.mem_filter.mpr ⟨hjN, h⟩)
    simp only [halfGood] at hnot
    push Not at hnot
    obtain ⟨s, hs, hr⟩ := hnot
    refine ⟨s, ?_, hr⟩
    dsimp [halfInterval] at hs
    constructor <;> linarith [hs.1, hs.2]
  have he := Finset.card_sdiff_add_card_eq_card
    (show G ⊆ Finset.range N from Finset.filter_subset _ _)
  simp only [Finset.card_range] at he
  change N ≤ G.card + q.natDegree
  omega

lemma signBlockStarts_card_upper (q : Polynomial ℝ) (hq : q ≠ 0)
    (m : ℝ) (hm : m ≠ 0) (a : ℤ) (N : ℕ) :
    (signBlockStarts (fun s => q.eval (s / m)) a N).card ≤ q.natDegree + 1 := by
  classical
  let B := signBlockStarts (fun s => q.eval (s / m)) a N
  have hroots : (B.erase 0).card ≤ q.natDegree := by
    apply polynomial_root_windows_card_le q hq m hm a
    intro j hj
    exact signBlockStart_has_root (by fun_prop) (Finset.mem_erase.mp hj).2
      (Finset.mem_erase.mp hj).1
  have hc := Finset.pred_card_le_card_erase (s := B) (a := 0)
  change B.card ≤ q.natDegree + 1
  omega

/-- The manuscript's bound `2 M_opp ≥ N' - G`, with `N' ≥ N - degree(q)`
and `G ≤ degree(q)+1`. -/
theorem oppositeHalves_card_lower (q : Polynomial ℝ) (hq : q ≠ 0)
    (m : ℝ) (hm : m ≠ 0) (a : ℤ) (N : ℕ) :
    N ≤ 2 * (oppositeHalves (fun s => q.eval (s / m)) a N).card + 2 * q.natDegree + 1 := by
  have hgood := goodHalves_card_lower q hq m hm a N
  have hblocks := signBlockStarts_card_upper q hq m hm a N
  have hcount := goodHalves_card_le_twice_opposite_add_blocks
    (fun s => q.eval (s / m)) a N
  omega

lemma half_sine_integral (a : ℤ) (j : ℕ) :
    ∫ s in halfInterval a j, sin (π * s) ^ 2 = 1 / 2 := by
  obtain ⟨k, hk | hk⟩ := Int.even_or_odd' (a + (j : ℤ))
  · have h : (a : ℝ) + j = 2 * (k : ℝ) := by exact_mod_cast hk
    simpa [halfInterval, h] using integral_sin_sq_first_half k
  · have h : (a : ℝ) + j = 2 * (k : ℝ) + 1 := by exact_mod_cast hk
    simpa [halfInterval, h, show (2 * (k : ℝ) + 1) + 1 = 2 * k + 2 by ring]
      using integral_sin_sq_second_half k

lemma half_sine_nonneg {a : ℤ} {j : ℕ} (he : Even (a + (j : ℤ)))
    {s : ℝ} (hs : s ∈ halfInterval a j) : 0 ≤ sin (π * s) := by
  obtain ⟨k, hk⟩ := he
  have h : (a : ℝ) + j = 2 * (k : ℝ) := by
    have h' : a + (j : ℤ) = 2 * k := by linarith
    exact_mod_cast h'
  exact sin_pi_mul_nonneg_first_half k (by simpa [halfInterval, h] using hs)

lemma half_sine_nonpos {a : ℤ} {j : ℕ} (he : ¬Even (a + (j : ℤ)))
    {s : ℝ} (hs : s ∈ halfInterval a j) : sin (π * s) ≤ 0 := by
  obtain ⟨k, hk⟩ := Int.not_even_iff_odd.mp he
  have h : (a : ℝ) + j = 2 * (k : ℝ) + 1 := by exact_mod_cast hk
  exact sin_pi_mul_nonpos_second_half k (by
    simpa [halfInterval, h, show (2 * (k : ℝ) + 1) + 1 = 2 * k + 2 by ring] using hs)

/-- Every opposing retained half-period contributes `1/2` in the coordinate
`s = (u + πm)/π`; equivalently it contributes `π/2` in the paper's `u` coordinate. -/
lemma oppositeHalf_integral_lower (m : ℝ) (q : Polynomial ℝ) {a : ℤ} {N j : ℕ}
    (hj : j ∈ oppositeHalves (fun s => q.eval (s / m)) a N) :
    1 / 2 ≤ ∫ s in halfInterval a j, scaledRadialError m q s := by
  classical
  obtain ⟨hjG, hjopp⟩ := Finset.mem_filter.mp hj
  have hgood := (Finset.mem_filter.mp hjG).2
  have hmid := hgood _ (halfMid_mem a j)
  have hprod : ∀ s ∈ halfInterval a j, sin (π * s) * q.eval (s / m) ≤ 0 := by
    intro s hs
    by_cases he : Even (a + (j : ℤ))
    · have hn : q.eval (halfMid a j / m) < 0 := by
        have hnot := hjopp.mp he
        dsimp [halfPositive] at hnot
        exact lt_of_le_of_ne (le_of_not_gt hnot) hmid
      have hn' := continuous_neg_on_Ioo_of_no_zero
        (by fun_prop : Continuous (fun s => q.eval (s / m)))
        (halfMid_mem a j) hn hgood hs
      exact mul_nonpos_of_nonneg_of_nonpos (half_sine_nonneg he hs) hn'.le
    · have hp : 0 < q.eval (halfMid a j / m) := by
        have : halfPositive (fun s => q.eval (s / m)) a j := by tauto
        exact this
      have hp' := continuous_pos_on_Ioo_of_no_zero
        (by fun_prop : Continuous (fun s => q.eval (s / m)))
        (halfMid_mem a j) hp hgood hs
      exact mul_nonpos_of_nonpos_of_nonneg (half_sine_nonpos he hs) hp'.le
  rw [← half_sine_integral a j]
  refine setIntegral_mono_on
    ((by fun_prop : Continuous (fun s : ℝ => sin (π * s) ^ 2)).integrableOn_Icc.mono_set
      Ioo_subset_Icc_self)
    ((continuous_scaledRadialError m q).integrableOn_Icc.mono_set Ioo_subset_Icc_self)
    measurableSet_Ioo fun s hs => ?_
  dsimp [scaledRadialError]
  nlinarith [hprod s hs, sq_nonneg (q.eval (s / m))]

end

end GaussianDepthSeparation
