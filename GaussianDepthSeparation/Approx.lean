/-
GaussianDepthSeparation — one-dimensional ReLU (hinge) approximation of Lipschitz functions.

`hinge` builds the piecewise-linear interpolant of `φ` on a uniform grid of `N`
cells over `[a,b]`, written as a sum of ReLU "ramps".  `hinge_approx` bounds the
sup error by `2·L·h` (`h = (b−a)/N`) for `L`-Lipschitz `φ`.  This is the analytic
core of the depth-3 upper bound (Theorem 1.3(ii)).
-/
import GaussianDepthSeparation.ReLU
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace GaussianDepthSeparation

open scoped RealInnerProductSpace

noncomputable section

/-! ### ReLU basics -/

@[simp] lemma relu_of_nonpos {t : ℝ} (h : t ≤ 0) : relu t = 0 := by
  rw [relu, max_eq_right h]

@[simp] lemma relu_of_nonneg {t : ℝ} (h : 0 ≤ t) : relu t = t := by
  rw [relu, max_eq_left h]

lemma relu_sub_of_le {x t : ℝ} (h : x ≤ t) : relu (x - t) = 0 :=
  relu_of_nonpos (by linarith)

lemma relu_sub_of_ge {x t : ℝ} (h : t ≤ x) : relu (x - t) = x - t :=
  relu_of_nonneg (by linarith)

/-! ### The uniform-grid hinge interpolant -/

section Hinge

variable (a b : ℝ) (N : ℕ)

/-- Grid spacing `h = (b−a)/N`. -/
def gh : ℝ := (b - a) / N

/-- Grid points `t_j = a + j·h`. -/
def gpt (j : ℕ) : ℝ := a + j * gh a b N

/-- Slope of `φ` across the `j`-th cell. -/
def gslope (φ : ℝ → ℝ) (j : ℕ) : ℝ :=
  (φ (gpt a b N (j + 1)) - φ (gpt a b N j)) / gh a b N

/-- The piecewise-linear hinge interpolant of `φ` (a ReLU-ramp sum). -/
def hinge (φ : ℝ → ℝ) (x : ℝ) : ℝ :=
  φ a + ∑ j ∈ Finset.range N,
    gslope a b N φ j * (relu (x - gpt a b N j) - relu (x - gpt a b N (j + 1)))

variable {a b N}

lemma gh_pos (hab : a < b) (hN : 0 < N) : 0 < gh a b N := by
  rw [gh]; apply div_pos <;> [linarith; exact_mod_cast hN]

lemma gpt_zero : gpt a b N 0 = a := by simp [gpt]

lemma gpt_succ (j : ℕ) : gpt a b N (j + 1) = gpt a b N j + gh a b N := by
  simp only [gpt]; push_cast; ring

lemma gpt_mono (hab : a < b) (hN : 0 < N) {i j : ℕ} (h : i ≤ j) :
    gpt a b N i ≤ gpt a b N j := by
  rw [gpt, gpt]
  have hc : (i : ℝ) ≤ j := by exact_mod_cast h
  nlinarith [(gh_pos hab hN).le]

lemma gpt_last (hN : 0 < N) : gpt a b N N = b := by
  have hNne : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  have hcancel : (N : ℝ) * ((b - a) / N) = b - a := by field_simp
  rw [gpt, gh, hcancel]; ring

lemma gpt_mem (hab : a < b) (hN : 0 < N) {k : ℕ} (hk : k ≤ N) :
    gpt a b N k ∈ Set.Icc a b := by
  constructor
  · calc a = gpt a b N 0 := gpt_zero.symm
      _ ≤ gpt a b N k := gpt_mono hab hN (Nat.zero_le k)
  · calc gpt a b N k ≤ gpt a b N N := gpt_mono hab hN hk
      _ = b := gpt_last hN

lemma abs_gslope_le (hab : a < b) (hN : 0 < N) (φ : ℝ → ℝ) (L : ℝ)
    (hlip : ∀ s ∈ Set.Icc a b, ∀ t ∈ Set.Icc a b, |φ s - φ t| ≤ L * |s - t|)
    {j : ℕ} (hj : j + 1 ≤ N) : |gslope a b N φ j| ≤ L := by
  have hgh := gh_pos hab hN
  rw [gslope, abs_div, abs_of_pos hgh, div_le_iff₀ hgh]
  have hdist : |gpt a b N (j + 1) - gpt a b N j| = gh a b N := by
    rw [gpt_succ, add_sub_cancel_left, abs_of_pos hgh]
  have hd := hlip (gpt a b N (j + 1)) (gpt_mem hab hN hj)
    (gpt a b N j) (gpt_mem hab hN (by omega))
  rw [hdist] at hd
  exact hd

/-- Telescoping: the completed ramps below cell `k` sum to `φ(t_k) − φ(a)`. -/
lemma hinge_telescope (φ : ℝ → ℝ) (hab : a < b) (hN : 0 < N) (k : ℕ) :
    ∑ j ∈ Finset.range k, gslope a b N φ j * gh a b N
      = φ (gpt a b N k) - φ (gpt a b N 0) := by
  have hgh : gh a b N ≠ 0 := (gh_pos hab hN).ne'
  have hterm : ∀ j, gslope a b N φ j * gh a b N
      = φ (gpt a b N (j + 1)) - φ (gpt a b N j) := fun j => by
    rw [gslope, div_mul_cancel₀ _ hgh]
  rw [Finset.sum_congr rfl (fun j _ => hterm j)]
  exact Finset.sum_range_sub (fun i => φ (gpt a b N i)) k

/-- The hinge interpolant is extended constantly to the left of its grid. -/
lemma hinge_eq_of_le (φ : ℝ → ℝ) (hab : a < b) (hN : 0 < N) {x : ℝ}
    (hx : x ≤ a) :
    hinge a b N φ x = φ a := by
  have hterm : ∀ j ∈ Finset.range N,
      gslope a b N φ j *
          (relu (x - gpt a b N j) - relu (x - gpt a b N (j + 1))) = 0 := by
    intro j hj
    have hjN : j ≤ N := (Finset.mem_range.mp hj).le
    have hj1N : j + 1 ≤ N := Nat.succ_le_iff.mpr (Finset.mem_range.mp hj)
    have hja : a ≤ gpt a b N j := (gpt_mem hab hN hjN).1
    have hj1a : a ≤ gpt a b N (j + 1) := (gpt_mem hab hN hj1N).1
    rw [relu_sub_of_le (hx.trans hja), relu_sub_of_le (hx.trans hj1a)]
    ring
  rw [hinge, Finset.sum_eq_zero hterm, add_zero]

/-- The hinge interpolant is extended constantly to the right of its grid. -/
lemma hinge_eq_of_ge (φ : ℝ → ℝ) (hab : a < b) (hN : 0 < N) {x : ℝ}
    (hx : b ≤ x) :
    hinge a b N φ x = φ b := by
  have hterm : ∀ j ∈ Finset.range N,
      gslope a b N φ j *
          (relu (x - gpt a b N j) - relu (x - gpt a b N (j + 1))) =
        gslope a b N φ j * gh a b N := by
    intro j hj
    have hjN : j ≤ N := (Finset.mem_range.mp hj).le
    have hj1N : j + 1 ≤ N := Nat.succ_le_iff.mpr (Finset.mem_range.mp hj)
    have hjb : gpt a b N j ≤ b := (gpt_mem hab hN hjN).2
    have hj1b : gpt a b N (j + 1) ≤ b := (gpt_mem hab hN hj1N).2
    rw [relu_sub_of_ge (hjb.trans hx), relu_sub_of_ge (hj1b.trans hx), gpt_succ]
    ring
  rw [hinge, Finset.sum_congr rfl hterm, hinge_telescope φ hab hN N,
    gpt_last hN, gpt_zero]
  ring

/-- Cell selection: every `x ∈ [a,b]` lies in some cell `[t_k, t_{k+1}]`, `k < N`. -/
lemma exists_cell (hab : a < b) (hN : 0 < N) {x : ℝ} (hx : x ∈ Set.Icc a b) :
    ∃ k, k < N ∧ gpt a b N k ≤ x ∧ x ≤ gpt a b N (k + 1) := by
  obtain ⟨hxa, hxb⟩ := hx
  have hghpos := gh_pos hab hN
  set y := (x - a) / gh a b N with hy
  have hy0 : 0 ≤ y := by rw [hy]; apply div_nonneg (by linarith) hghpos.le
  have hNgh : (N : ℝ) * gh a b N = b - a := by rw [gh]; field_simp
  have hyN : y ≤ N := by
    rw [hy, div_le_iff₀ hghpos, hNgh]; linarith [hxb]
  set k := min (⌊y⌋₊) (N - 1) with hk
  have hkN : k < N := by
    have : k ≤ N - 1 := min_le_right _ _
    omega
  have hklef : (k : ℝ) ≤ y := by
    have h1 : (⌊y⌋₊ : ℝ) ≤ y := Nat.floor_le hy0
    have h2 : k ≤ ⌊y⌋₊ := min_le_left _ _
    calc (k : ℝ) ≤ (⌊y⌋₊ : ℝ) := by exact_mod_cast h2
      _ ≤ y := h1
  have hkri : y ≤ (k : ℝ) + 1 := by
    by_cases hle : ⌊y⌋₊ ≤ N - 1
    · have hkeq : k = ⌊y⌋₊ := min_eq_left hle
      rw [hkeq]
      exact (Nat.lt_floor_add_one y).le
    · push Not at hle
      have hkeq : k = N - 1 := min_eq_right (by omega)
      rw [hkeq, show ((N - 1 : ℕ) : ℝ) + 1 = ((N : ℕ) : ℝ) from by
        have hNm : (N - 1 : ℕ) + 1 = N := by omega
        rw [← hNm]; push_cast; ring]
      exact hyN
  refine ⟨k, hkN, ?_, ?_⟩
  · rw [gpt]
    rw [hy, le_div_iff₀ hghpos] at hklef
    linarith [hklef]
  · rw [gpt]
    rw [hy, div_le_iff₀ hghpos] at hkri
    push_cast at hkri ⊢
    linarith [hkri]

/-- The hinge interpolant on cell `k` reduces to the linear interpolant. -/
lemma hinge_eq_on_cell (φ : ℝ → ℝ) (hab : a < b) (hN : 0 < N) {x : ℝ} {k : ℕ}
    (hkN : k < N) (hxl : gpt a b N k ≤ x) (hxr : x ≤ gpt a b N (k + 1)) :
    hinge a b N φ x = φ (gpt a b N k) + gslope a b N φ k * (x - gpt a b N k) := by
  have hsplit : ∑ j ∈ Finset.range N,
      gslope a b N φ j * (relu (x - gpt a b N j) - relu (x - gpt a b N (j + 1)))
      = (∑ j ∈ Finset.range k,
          gslope a b N φ j * (relu (x - gpt a b N j) - relu (x - gpt a b N (j + 1))))
        + gslope a b N φ k * (relu (x - gpt a b N k) - relu (x - gpt a b N (k + 1)))
        + ∑ j ∈ Finset.Ico (k + 1) N,
            gslope a b N φ j * (relu (x - gpt a b N j) - relu (x - gpt a b N (j + 1))) := by
    rw [← Finset.sum_range_succ (fun j => gslope a b N φ j
      * (relu (x - gpt a b N j) - relu (x - gpt a b N (j + 1)))) k,
      Finset.sum_range_add_sum_Ico _ (Nat.succ_le_of_lt hkN)]
  -- below-cell terms become slope·gh
  have hbelow : ∀ j ∈ Finset.range k,
      gslope a b N φ j * (relu (x - gpt a b N j) - relu (x - gpt a b N (j + 1)))
        = gslope a b N φ j * gh a b N := by
    intro j hj
    rw [Finset.mem_range] at hj
    have h1 : gpt a b N (j + 1) ≤ x := le_trans (gpt_mono hab hN (by omega)) hxl
    have h2 : gpt a b N j ≤ x := le_trans (gpt_mono hab hN (by omega)) hxl
    rw [relu_sub_of_ge h2, relu_sub_of_ge h1, gpt_succ]
    ring
  -- above-cell terms vanish
  have habove : ∀ j ∈ Finset.Ico (k + 1) N,
      gslope a b N φ j * (relu (x - gpt a b N j) - relu (x - gpt a b N (j + 1))) = 0 := by
    intro j hj
    rw [Finset.mem_Ico] at hj
    have h1 : x ≤ gpt a b N j := le_trans hxr (gpt_mono hab hN hj.1)
    have h2 : x ≤ gpt a b N (j + 1) := le_trans h1 (gpt_mono hab hN (by omega))
    rw [relu_sub_of_le h1, relu_sub_of_le h2]
    ring
  -- middle term
  have hmid : gslope a b N φ k * (relu (x - gpt a b N k) - relu (x - gpt a b N (k + 1)))
      = gslope a b N φ k * (x - gpt a b N k) := by
    rw [relu_sub_of_ge hxl, relu_sub_of_le hxr, sub_zero]
  rw [hinge, hsplit, Finset.sum_congr rfl hbelow, Finset.sum_congr rfl habove,
    Finset.sum_const_zero, add_zero, hmid, hinge_telescope φ hab hN k, gpt_zero]
  ring

/-- **The hinge approximation bound.** For `L`-Lipschitz `φ` on `[a,b]`, the
`N`-cell hinge interpolant is within `2·L·h` (`h = (b−a)/N`). -/
theorem hinge_approx (φ : ℝ → ℝ) (L : ℝ) (hab : a < b) (hN : 0 < N)
    (hlip : ∀ s ∈ Set.Icc a b, ∀ t ∈ Set.Icc a b, |φ s - φ t| ≤ L * |s - t|)
    {x : ℝ} (hx : x ∈ Set.Icc a b) :
    |hinge a b N φ x - φ x| ≤ 2 * L * gh a b N := by
  obtain ⟨k, hkN, hxl, hxr⟩ := exists_cell hab hN hx
  have hghpos := gh_pos hab hN
  have hmemk : gpt a b N k ∈ Set.Icc a b := by
    refine ⟨?_, ?_⟩
    · calc a = gpt a b N 0 := gpt_zero.symm
        _ ≤ gpt a b N k := gpt_mono hab hN (Nat.zero_le _)
    · calc gpt a b N k ≤ gpt a b N N := gpt_mono hab hN hkN.le
        _ = b := gpt_last hN
  have hmemk1 : gpt a b N (k + 1) ∈ Set.Icc a b := by
    refine ⟨?_, ?_⟩
    · calc a = gpt a b N 0 := gpt_zero.symm
        _ ≤ gpt a b N (k + 1) := gpt_mono hab hN (Nat.zero_le _)
    · calc gpt a b N (k + 1) ≤ gpt a b N N := gpt_mono hab hN (by omega)
        _ = b := gpt_last hN
  -- key per-cell facts
  have hnum : |φ (gpt a b N (k + 1)) - φ (gpt a b N k)| ≤ L * gh a b N := by
    have hl := hlip _ hmemk1 _ hmemk
    rw [gpt_succ, add_sub_cancel_left, abs_of_pos hghpos] at hl
    rw [gpt_succ]; exact hl
  have hL0 : 0 ≤ L := by
    by_contra h
    push Not at h
    have h1 : L * gh a b N < 0 := mul_neg_of_neg_of_pos h hghpos
    have h2 := le_trans (abs_nonneg _) hnum
    linarith
  have hxk : |x - gpt a b N k| ≤ gh a b N := by
    rw [abs_of_nonneg (by linarith)]
    have : x ≤ gpt a b N k + gh a b N := by rw [← gpt_succ]; exact hxr
    linarith
  rw [hinge_eq_on_cell φ hab hN hkN hxl hxr]
  have hslope_bd : |gslope a b N φ k * (x - gpt a b N k)| ≤ L * gh a b N := by
    have hval : gslope a b N φ k * (x - gpt a b N k)
        = (φ (gpt a b N (k + 1)) - φ (gpt a b N k)) * ((x - gpt a b N k) / gh a b N) := by
      rw [gslope]; ring
    rw [hval, abs_mul]
    have hfrac : |(x - gpt a b N k) / gh a b N| ≤ 1 := by
      rw [abs_div, abs_of_pos hghpos, div_le_one hghpos]
      exact hxk
    nlinarith [hnum, hfrac, abs_nonneg (φ (gpt a b N (k + 1)) - φ (gpt a b N k)),
      mul_nonneg (abs_nonneg (φ (gpt a b N (k + 1)) - φ (gpt a b N k)))
        (by linarith [hfrac] : (0:ℝ) ≤ 1 - |(x - gpt a b N k) / gh a b N|)]
  have hphi_bd : |φ (gpt a b N k) - φ x| ≤ L * gh a b N := by
    have hl := hlip _ hmemk _ hx
    calc |φ (gpt a b N k) - φ x| ≤ L * |gpt a b N k - x| := hl
      _ ≤ L * gh a b N := by
          apply mul_le_mul_of_nonneg_left _ hL0
          rw [abs_sub_comm, abs_of_nonneg (by linarith)]
          have : x ≤ gpt a b N k + gh a b N := by rw [← gpt_succ]; exact hxr
          linarith
  calc |φ (gpt a b N k) + gslope a b N φ k * (x - gpt a b N k) - φ x|
      = |gslope a b N φ k * (x - gpt a b N k) + (φ (gpt a b N k) - φ x)| := by ring_nf
    _ ≤ |gslope a b N φ k * (x - gpt a b N k)| + |φ (gpt a b N k) - φ x| := abs_add_le _ _
    _ ≤ L * gh a b N + L * gh a b N := add_le_add hslope_bd hphi_bd
    _ = 2 * L * gh a b N := by ring

/-- A bounded function remains bounded, up to the interpolation error, after the
constant-extension hinge construction on the whole real line. -/
theorem abs_hinge_le_add (φ : ℝ → ℝ) (L C δ : ℝ) (hab : a < b) (hN : 0 < N)
    (hδ : 0 ≤ δ)
    (hlip : ∀ s ∈ Set.Icc a b, ∀ t ∈ Set.Icc a b,
      |φ s - φ t| ≤ L * |s - t|)
    (hφ : ∀ t ∈ Set.Icc a b, |φ t| ≤ C)
    (herr : 2 * L * gh a b N ≤ δ) (x : ℝ) :
    |hinge a b N φ x| ≤ C + δ := by
  by_cases hxa : x < a
  · rw [hinge_eq_of_le φ hab hN hxa.le]
    exact (hφ a ⟨le_rfl, hab.le⟩).trans (le_add_of_nonneg_right hδ)
  by_cases hxb : b < x
  · rw [hinge_eq_of_ge φ hab hN hxb.le]
    exact (hφ b ⟨hab.le, le_rfl⟩).trans (le_add_of_nonneg_right hδ)
  have hx : x ∈ Set.Icc a b := ⟨le_of_not_gt hxa, le_of_not_gt hxb⟩
  have happ := hinge_approx (a := a) (b := b) (N := N) φ L hab hN hlip hx
  calc |hinge a b N φ x|
      = |(hinge a b N φ x - φ x) + φ x| := by ring_nf
    _ ≤ |hinge a b N φ x - φ x| + |φ x| := abs_add_le _ _
    _ ≤ δ + C := add_le_add (happ.trans herr) (hφ x hx)
    _ = C + δ := by ring

/-- The hinge interpolant is bounded by any bound of `φ` on the grid interval:
on each cell its value is a convex combination of two values of `φ`, and it is
constant outside `[a,b]`. -/
theorem abs_hinge_le (φ : ℝ → ℝ) (C : ℝ) (hab : a < b) (hN : 0 < N)
    (hφ : ∀ t ∈ Set.Icc a b, |φ t| ≤ C) (x : ℝ) :
    |hinge a b N φ x| ≤ C := by
  by_cases hxa : x < a
  · rw [hinge_eq_of_le φ hab hN hxa.le]
    exact hφ a ⟨le_rfl, hab.le⟩
  by_cases hxb : b < x
  · rw [hinge_eq_of_ge φ hab hN hxb.le]
    exact hφ b ⟨hab.le, le_rfl⟩
  have hx : x ∈ Set.Icc a b := ⟨le_of_not_gt hxa, le_of_not_gt hxb⟩
  obtain ⟨k, hkN, hxl, hxr⟩ := exists_cell hab hN hx
  rw [hinge_eq_on_cell φ hab hN hkN hxl hxr]
  have hghpos := gh_pos hab hN
  set θ := (x - gpt a b N k) / gh a b N with hθ
  have hθ0 : 0 ≤ θ := div_nonneg (by linarith) hghpos.le
  have hθ1 : θ ≤ 1 := by
    rw [hθ, div_le_one hghpos]
    have := gpt_succ (a := a) (b := b) (N := N) k
    linarith
  have hval : φ (gpt a b N k) + gslope a b N φ k * (x - gpt a b N k)
      = (1 - θ) * φ (gpt a b N k) + θ * φ (gpt a b N (k + 1)) := by
    rw [hθ, gslope]
    ring
  have h1 := hφ _ (gpt_mem hab hN hkN.le)
  have h2 := hφ _ (gpt_mem hab hN (Nat.succ_le_of_lt hkN))
  rw [hval]
  calc |(1 - θ) * φ (gpt a b N k) + θ * φ (gpt a b N (k + 1))|
      ≤ |(1 - θ) * φ (gpt a b N k)| + |θ * φ (gpt a b N (k + 1))| :=
        abs_add_le _ _
    _ = (1 - θ) * |φ (gpt a b N k)| + θ * |φ (gpt a b N (k + 1))| := by
        rw [abs_mul, abs_mul, abs_of_nonneg (by linarith), abs_of_nonneg hθ0]
    _ ≤ (1 - θ) * C + θ * C := by
        gcongr
    _ = C := by ring

end Hinge

end

end GaussianDepthSeparation
