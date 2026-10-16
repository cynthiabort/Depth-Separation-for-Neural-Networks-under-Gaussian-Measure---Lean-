/-
GaussianDepthSeparation — the depth-3 ReLU construction in the proof of Theorem 1.3(ii) of
`main.tex`.  `𝒩_sq(x) = ∑ᵢ (p(xᵢ) + p(-xᵢ))`, where `p` is the clipped-ramp
interpolant of `t²` on the grid `tⱼ = jR/K`; `𝒩_sin` is the clipped-ramp
interpolant of `s ↦ sin(κs)`, `κ = 4π√d`, on the grid `u_l = -1 + l(R²+2)/K'`;
its constant term `sin(κu₀)` is carried by one second-layer unit with zero
incoming weights and bias `1`, since the networks have no output bias.
-/
import GaussianDepthSeparation.ReLUHelpers
import Mathlib.Analysis.Real.Pi.Bounds

namespace GaussianDepthSeparation

open scoped RealInnerProductSpace
open Real

noncomputable section

/-- Centered per-coordinate approximation of `‖x‖²`. -/
def sqApproxC {d : ℕ} (R : ℝ) (M : ℕ) (x : Vec d) : ℝ :=
  ∑ i, (hinge 0 R M (fun t => t ^ 2) (x i) +
    hinge 0 R M (fun t => t ^ 2) (-x i))

/-- Each coordinate contributes only one nonconstant half-line interpolant. -/
lemma sqApproxC_coord_error {R : ℝ} (hR : 0 < R) {M : ℕ} (hM : 0 < M)
    {t : ℝ} (ht : |t| ≤ R) :
    |hinge 0 R M (fun s => s ^ 2) t +
        hinge 0 R M (fun s => s ^ 2) (-t) - t ^ 2| ≤
      2 * (2 * R) * gh 0 R M := by
  have hlip : ∀ s ∈ Set.Icc (0 : ℝ) R, ∀ u ∈ Set.Icc (0 : ℝ) R,
      |s ^ 2 - u ^ 2| ≤ 2 * R * |s - u| := by
    intro s hs u hu
    exact sq_lipschitz s ⟨by linarith [hs.1], hs.2⟩
      u ⟨by linarith [hu.1], hu.2⟩
  by_cases h : 0 ≤ t
  · have htmem : t ∈ Set.Icc (0 : ℝ) R := ⟨h, (abs_le.mp ht).2⟩
    rw [hinge_eq_of_le (a := 0) (b := R) (N := M) (fun s => s ^ 2)
      hR hM (neg_nonpos.mpr h)]
    norm_num
    exact hinge_approx (a := 0) (b := R) (N := M) (fun s => s ^ 2) (2 * R)
      hR hM hlip htmem
  · have hneg : 0 ≤ -t := by linarith
    have htmem : -t ∈ Set.Icc (0 : ℝ) R := by
      rw [abs_le] at ht
      exact ⟨hneg, by linarith [ht.1]⟩
    rw [hinge_eq_of_le (a := 0) (b := R) (N := M) (fun s => s ^ 2)
      hR hM (le_of_not_ge h)]
    norm_num
    simpa only [neg_sq] using
      (hinge_approx (a := 0) (b := R) (N := M) (fun s => s ^ 2) (2 * R)
        hR hM hlip htmem)

/-- Centered squaring error: `4dR²/M`. -/
theorem sqApproxC_error {d : ℕ} {R : ℝ} (hR : 0 < R) {M : ℕ} (hM : 0 < M)
    {x : Vec d} (hx : ‖x‖ ≤ R) :
    |sqApproxC R M x - ‖x‖ ^ 2| ≤
      (d : ℝ) * (2 * (2 * R) * gh 0 R M) := by
  rw [sqApproxC, norm_sq_eq_sum, ← Finset.sum_sub_distrib]
  calc
    |∑ i, (hinge 0 R M (fun t => t ^ 2) (x i) +
        hinge 0 R M (fun t => t ^ 2) (-x i) - (x i) ^ 2)|
        ≤ ∑ i, |hinge 0 R M (fun t => t ^ 2) (x i) +
            hinge 0 R M (fun t => t ^ 2) (-x i) - (x i) ^ 2| :=
          Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin d, 2 * (2 * R) * gh 0 R M := by
      apply Finset.sum_le_sum
      intro i _
      apply sqApproxC_coord_error hR hM
      exact (abs_coord_le_norm x i).trans hx
    _ = (d : ℝ) * (2 * (2 * R) * gh 0 R M) := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
      ring

/-- The ramp form of the centered squaring approximation. -/
def sqRampC {d : ℕ} (R : ℝ) (M : ℕ) (x : Vec d) : ℝ :=
  ∑ i, ∑ q : Fin 2, ∑ j ∈ Finset.range M,
    gslope 0 R M (fun t => t ^ 2) j *
      (relu ((if q = 0 then x i else -x i) - gpt 0 R M j) -
       relu ((if q = 0 then x i else -x i) - gpt 0 R M (j + 1)))

lemma sqApproxC_eq_ramp {d : ℕ} (R : ℝ) (M : ℕ) (x : Vec d) :
    sqApproxC R M x = sqRampC R M x := by
  rw [sqApproxC, sqRampC]
  apply Finset.sum_congr rfl
  intro i _
  rw [Fin.sum_univ_two]
  simp only [Fin.isValue, ↓reduceIte, hinge]
  norm_num

namespace CenteredNetwork

/-- Flat index of a first-layer neuron. Each coordinate has two signs and
two hinge endpoints per interpolation cell. -/
abbrev FirstLayerIndex (d M : ℕ) := Fin (d * (2 * (M * 2)))

/-- Flatten the coordinate/sign/cell/endpoint description of a neuron. -/
def firstLayerEquiv (d M : ℕ) : Fin d × (Fin 2 × (Fin M × Fin 2)) ≃
    FirstLayerIndex d M :=
  ((Equiv.refl (Fin d)).prodCongr
      (((Equiv.refl (Fin 2)).prodCongr finProdFinEquiv).trans finProdFinEquiv)).trans
    finProdFinEquiv

/-- Input coordinate read by a first-layer neuron. -/
def coordinate {d M : ℕ} (j : FirstLayerIndex d M) : Fin d :=
  ((firstLayerEquiv d M).symm j).1

/-- Zero selects the positive input; one selects the negative input. -/
def sign {d M : ℕ} (j : FirstLayerIndex d M) : Fin 2 :=
  ((firstLayerEquiv d M).symm j).2.1

/-- Interpolation cell of a first-layer neuron. -/
def cell {d M : ℕ} (j : FirstLayerIndex d M) : Fin M :=
  ((firstLayerEquiv d M).symm j).2.2.1

/-- Zero selects the left endpoint; one selects the right endpoint. -/
def endpoint {d M : ℕ} (j : FirstLayerIndex d M) : Fin 2 :=
  ((firstLayerEquiv d M).symm j).2.2.2

/-- Grid knot at the selected endpoint. -/
def knot {d M : ℕ} (j : FirstLayerIndex d M) : ℕ :=
  if endpoint j = 0 then (cell j : ℕ) else (cell j : ℕ) + 1

lemma knot_le {d M : ℕ} (j : FirstLayerIndex d M) : knot j ≤ M := by
  have := (cell j).isLt
  unfold knot
  split <;> omega

/-- Signed coordinate weight of the first hidden layer. -/
def firstWeight (d M : ℕ) (j : FirstLayerIndex d M) : Vec d :=
  EuclideanSpace.single (coordinate j) (if sign j = 0 then 1 else -1)

/-- First-layer bias places the hinge at its grid knot. -/
def firstBias (d : ℕ) (R : ℝ) (M : ℕ) (j : FirstLayerIndex d M) : ℝ :=
  -gpt 0 R M (knot j)

/-- The two endpoints of a ramp carry opposite squaring slopes. -/
def secondWeight (d : ℕ) (R : ℝ) (M : ℕ) (j : FirstLayerIndex d M) : ℝ :=
  if endpoint j = 0 then gslope 0 R M (fun t => t ^ 2) (cell j)
    else -gslope 0 R M (fun t => t ^ 2) (cell j)

/-- Interpolation cell of a nonconstant second-layer neuron. -/
def secondCell {M : ℕ} (k : Fin (M * 2)) : Fin M := ((e2 M).symm k).1

/-- Hinge endpoint of a nonconstant second-layer neuron. -/
def secondEndpoint {M : ℕ} (k : Fin (M * 2)) : Fin 2 := ((e2 M).symm k).2

/-- Second-layer knot, before adding the constant neuron. -/
def secondKnot {M : ℕ} (k : Fin (M * 2)) : ℕ :=
  if secondEndpoint k = 0 then (secondCell k : ℕ) else (secondCell k : ℕ) + 1

lemma secondKnot_le {M : ℕ} (k : Fin (M * 2)) : secondKnot k ≤ M := by
  have := (secondCell k).isLt
  unfold secondKnot
  split <;> omega

/-- Second-layer bias places the sine interpolant's hinge. -/
def secondBias (as bs : ℝ) (M : ℕ) (k : Fin (M * 2)) : ℝ :=
  -gpt as bs M (secondKnot k)

end CenteredNetwork

open CenteredNetwork

/-- The centered two-hidden-layer network.  The first second-layer unit is
constant: it has zero incoming weights, bias `1`, and output weight `g as`.
This realizes the constant term in the hinge interpolant without an output
bias, exactly as in the paper's network architecture. -/
def net3c (d : ℕ) (R : ℝ) (M : ℕ) (as bs : ℝ) (M' : ℕ)
    (g : ℝ → ℝ) : Net3 d where
  n1 := d * (2 * (M * 2))
  n2 := M' * 2 + 1
  w1 := firstWeight d M
  b1 := firstBias d R M
  w2 := Fin.cases (fun _ => 0) (fun _ j => secondWeight d R M j)
  b2 := Fin.cases 1 (secondBias as bs M')
  a := Fin.cases (g as) (a2sq as bs M' g)

lemma inner_single_coord_mul {d : ℕ} (i : Fin d) (a : ℝ) (x : Vec d) :
    ⟪(EuclideanSpace.single i a : Vec d), x⟫ = a * x i := by
  rw [EuclideanSpace.inner_single_left]
  simp

lemma net3c_inner {d : ℕ} (R : ℝ) (M : ℕ) (x : Vec d) :
    ∑ j : Fin (d * (2 * (M * 2))), secondWeight d R M j *
        relu (⟪firstWeight d M j, x⟫ + firstBias d R M j) = sqRampC R M x := by
  rw [← Equiv.sum_comp (firstLayerEquiv d M)
    (fun j => secondWeight d R M j * relu (⟪firstWeight d M j, x⟫ + firstBias d R M j)),
    sqRampC, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro q _
  rw [Fintype.sum_prod_type, ← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro jj _
  rw [Fin.sum_univ_two]
  simp only [firstWeight, firstBias, secondWeight, coordinate, sign, knot, cell, endpoint,
    Equiv.symm_apply_apply, inner_single_coord_mul]
  fin_cases q <;> norm_num <;> ring_nf

lemma net3c_outer {d : ℕ} (R : ℝ) (M : ℕ) (as bs : ℝ) (M' : ℕ)
    (g : ℝ → ℝ) (x : Vec d) :
    ∑ k : Fin (M' * 2), a2sq as bs M' g k *
        relu (secondBias as bs M' k + sqRampC R M x) =
      ∑ l ∈ Finset.range M', gslope as bs M' g l *
        (relu (sqApproxC R M x - gpt as bs M' l) -
         relu (sqApproxC R M x - gpt as bs M' (l + 1))) := by
  rw [← Equiv.sum_comp (e2 M')
    (fun k => a2sq as bs M' g k * relu (secondBias as bs M' k + sqRampC R M x)),
    ← Fin.sum_univ_eq_sum_range, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro l _
  rw [Fin.sum_univ_two, sqApproxC_eq_ramp]
  simp only [a2sq, secondBias, secondKnot, secondCell, secondEndpoint, e2,
    Equiv.symm_apply_apply]
  norm_num
  ring_nf

theorem net3c_eval {d : ℕ} (R : ℝ) (M : ℕ) (as bs : ℝ) (M' : ℕ)
    (g : ℝ → ℝ) (x : Vec d) :
    (net3c d R M as bs M' g).eval x = hinge as bs M' g (sqApproxC R M x) := by
  change (∑ k : Fin (M' * 2 + 1),
      Fin.cases (g as) (a2sq as bs M' g) k *
        relu (Fin.cases 1 (secondBias as bs M') k +
          ∑ j : Fin (d * (2 * (M * 2))),
            Fin.cases (fun _ => 0) (fun _ j => secondWeight d R M j) k j *
              relu (⟪firstWeight d M j, x⟫ + firstBias d R M j))) = _
  rw [Fin.sum_univ_succ]
  simp only [Fin.cases_zero, Fin.cases_succ]
  have hconst :
      g as * relu (1 + ∑ j : Fin (d * (2 * (M * 2))),
        0 * relu (⟪firstWeight d M j, x⟫ + firstBias d R M j)) = g as := by
    simp [relu]
  rw [hconst]
  rw [net3c_inner R M x]
  rw [hinge]
  congr 1
  exact net3c_outer R M as bs M' g x

/-- Error bound for the centered two-stage network. -/
theorem net3c_error {d : ℕ} {R : ℝ} (hR : 0 < R) {M : ℕ} (hM : 0 < M)
    {M' : ℕ} (hM' : 0 < M') {ε : ℝ}
    (heSq1 : (d : ℝ) * (2 * (2 * R) * gh 0 R M) ≤ 1)
    (heSq2 : (4 * π * Real.sqrt d) *
      ((d : ℝ) * (2 * (2 * R) * gh 0 R M)) ≤ ε / 2)
    (hSin : 2 * (4 * π * Real.sqrt d) * gh (-1) (R ^ 2 + 1) M' ≤ ε / 2)
    {x : Vec d} (hx : ‖x‖ ≤ R) :
    |(net3c d R M (-1) (R ^ 2 + 1) M'
        (fun s => Real.sin (4 * π * Real.sqrt d * s))).eval x -
      Real.sin (4 * π * Real.sqrt d * ‖x‖ ^ 2)| ≤ ε := by
  set κ := 4 * π * Real.sqrt d with hκdef
  have hκ : 0 ≤ κ := by rw [hκdef]; positivity
  set S := sqApproxC R M x with hSdef
  set eSq := (d : ℝ) * (2 * (2 * R) * gh 0 R M) with heSqdef
  have herrSq : |S - ‖x‖ ^ 2| ≤ eSq := sqApproxC_error hR hM hx
  have hnx : ‖x‖ ^ 2 ≤ R ^ 2 := by nlinarith [norm_nonneg x, hx]
  have hSmem : S ∈ Set.Icc (-1 : ℝ) (R ^ 2 + 1) := by
    rw [abs_le] at herrSq
    exact ⟨by nlinarith [sq_nonneg ‖x‖, herrSq.1, heSq1],
      by nlinarith [herrSq.2, heSq1]⟩
  rw [net3c_eval]
  have hsplit : |hinge (-1) (R ^ 2 + 1) M' (fun s => Real.sin (κ * s)) S -
        Real.sin (κ * ‖x‖ ^ 2)| ≤
      |hinge (-1) (R ^ 2 + 1) M' (fun s => Real.sin (κ * s)) S -
        Real.sin (κ * S)| +
      |Real.sin (κ * S) - Real.sin (κ * ‖x‖ ^ 2)| := by
    calc
      |hinge (-1) (R ^ 2 + 1) M' (fun s => Real.sin (κ * s)) S -
          Real.sin (κ * ‖x‖ ^ 2)| =
        |(hinge (-1) (R ^ 2 + 1) M' (fun s => Real.sin (κ * s)) S -
            Real.sin (κ * S)) +
          (Real.sin (κ * S) - Real.sin (κ * ‖x‖ ^ 2))| := by ring_nf
      _ ≤ _ := abs_add_le _ _
  refine hsplit.trans ?_
  have hhinge : |hinge (-1) (R ^ 2 + 1) M' (fun s => Real.sin (κ * s)) S -
      Real.sin (κ * S)| ≤ ε / 2 := by
    apply (hinge_approx (a := -1) (b := R ^ 2 + 1) (N := M')
      (fun s => Real.sin (κ * s)) κ (by nlinarith [hR]) hM'
      (sinκ_lipschitz hκ (-1) (R ^ 2 + 1)) hSmem).trans
    simpa [κ, hκdef] using hSin
  have hgsin : |Real.sin (κ * S) - Real.sin (κ * ‖x‖ ^ 2)| ≤ ε / 2 := by
    calc
      |Real.sin (κ * S) - Real.sin (κ * ‖x‖ ^ 2)|
          ≤ |κ * S - κ * ‖x‖ ^ 2| := Real.abs_sin_sub_sin_le _ _
      _ = κ * |S - ‖x‖ ^ 2| := by rw [← mul_sub, abs_mul, abs_of_nonneg hκ]
      _ ≤ κ * eSq := mul_le_mul_of_nonneg_left herrSq hκ
      _ ≤ ε / 2 := by simpa [κ, hκdef, eSq, heSqdef] using heSq2
  linarith

/-- All centered-network parameters are `O(√d + R²)`. -/
theorem net3c_weights {d : ℕ} {R : ℝ} (hR : 0 < R) {M : ℕ} (hM : 0 < M)
    {M' : ℕ} (hM' : 0 < M') {κ : ℝ} (hκ : 0 ≤ κ) :
    (net3c d R M (-1) (R ^ 2 + 1) M'
      (fun s => Real.sin (κ * s))).WeightsLe (2 * (R ^ 2 + 1) + κ) := by
  have hR2 : 0 ≤ R ^ 2 := sq_nonneg R
  have hRle : R ≤ R ^ 2 + 1 := by nlinarith [sq_nonneg (R - 1)]
  have hbase : 1 ≤ 2 * (R ^ 2 + 1) + κ := by nlinarith
  have hlip : ∀ s ∈ Set.Icc (0 : ℝ) R, ∀ u ∈ Set.Icc (0 : ℝ) R,
      |s ^ 2 - u ^ 2| ≤ 2 * R * |s - u| := by
    intro s hs u hu
    exact sq_lipschitz s ⟨by linarith [hs.1], hs.2⟩
      u ⟨by linarith [hu.1], hu.2⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro j
    simp only [net3c, firstWeight, PiLp.norm_single, Real.norm_eq_abs]
    split <;> norm_num <;> exact hbase
  · intro j
    simp only [net3c, firstBias, abs_neg]
    have hg := abs_gpt_le (a := 0) (b := R) hR hM (knot_le j) (Or.inr le_rfl)
    exact hg.trans (by nlinarith [hRle])
  · intro k j
    refine Fin.cases ?_ (fun _ => ?_) k
    · simp only [net3c, Fin.cases_zero, abs_zero]
      exact (show (0 : ℝ) ≤ 1 by norm_num).trans hbase
    · simp only [net3c, Fin.cases_succ, secondWeight]
      have hjM : (cell j : ℕ) + 1 ≤ M := by
        have := (cell j).isLt
        omega
      have hg := abs_gslope_le (a := 0) (b := R) hR hM
        (fun t => t ^ 2) (2 * R) hlip hjM
      have hbound : |gslope 0 R M (fun t => t ^ 2)
          (cell j : ℕ)| ≤ 2 * (R ^ 2 + 1) + κ := by
        nlinarith [hg, hRle]
      split <;> simpa only [abs_neg] using hbound
  · intro k
    refine Fin.cases ?_ (fun k => ?_) k
    · simp [net3c]
      exact hbase
    · simp only [net3c, Fin.cases_succ, secondBias, abs_neg]
      have hg := abs_gpt_le (a := -1) (b := R ^ 2 + 1) (by nlinarith) hM'
        (secondKnot_le k) (Or.inl (by norm_num; linarith))
      exact hg.trans (by nlinarith)
  · intro k
    refine Fin.cases ?_ (fun k => ?_) k
    · simp only [net3c, Fin.cases_zero]
      exact (Real.abs_sin_le_one (κ * (-1))).trans hbase
    · simp only [net3c, Fin.cases_succ, a2sq]
      have hkM : (secondCell k : ℕ) + 1 ≤ M' := by
        have := (secondCell k).isLt
        omega
      have hg := abs_gslope_le (a := -1) (b := R ^ 2 + 1) (by nlinarith)
        hM' (fun s => Real.sin (κ * s)) κ
        (sinκ_lipschitz hκ (-1) (R ^ 2 + 1)) hkM
      have hbound : |gslope (-1) (R ^ 2 + 1) M'
          (fun s => Real.sin (κ * s)) (secondCell k : ℕ)| ≤
          2 * (R ^ 2 + 1) + κ := by nlinarith [hg]
      split <;> simpa only [abs_neg, secondCell] using hbound

/-- The grids of the proof of Theorem 1.3(ii).  With `κ = 4π√d`, the paper's
accuracies are `η' = η/(8π√d) = η/(2κ)` for the squaring network and
`η'' = η/2` for the sine network, and the grid sizes are
`K = ⌈4dR²/η'⌉` and `K' = ⌈2κ(R²+2)/η''⌉`. -/
private lemma exists_approximation_grids {d : ℕ} (hd : 0 < d) {R η : ℝ}
    (hR : 0 < R) (hη : 0 < η) (hη1 : η ≤ 1) :
    ∃ K K' : ℕ, 0 < K ∧ 0 < K' ∧
      (d : ℝ) * (2 * (2 * R) * gh 0 R K) ≤ 1 ∧
      (4 * π * Real.sqrt d) * ((d : ℝ) * (2 * (2 * R) * gh 0 R K)) ≤ η / 2 ∧
      2 * (4 * π * Real.sqrt d) * gh (-1) (R ^ 2 + 1) K' ≤ η / 2 ∧
      (K : ℝ) ≤ 8 * (d : ℝ) * R ^ 2 * (4 * π * Real.sqrt d) / η + 1 ∧
      (K' : ℝ) ≤ 4 * (4 * π * Real.sqrt d) * (R ^ 2 + 2) / η + 1 := by
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hsqrt1 : 1 ≤ Real.sqrt d := Real.one_le_sqrt.mpr hdR
  set κ := 4 * π * Real.sqrt d with hκdef
  have hκ1 : 1 ≤ κ := by rw [hκdef]; nlinarith [Real.pi_gt_three]
  have hκ : 0 < κ := by linarith
  set η' := η / (2 * κ) with hη'def
  have hη' : 0 < η' := by positivity
  have hη'1 : η' ≤ 1 := by
    rw [hη'def, div_le_one (by positivity)]
    linarith
  have hx : 0 < 4 * (d : ℝ) * R ^ 2 / η' := by positivity
  have hx' : 0 < 2 * κ * (R ^ 2 + 2) / (η / 2) := by positivity
  set K := ⌈4 * (d : ℝ) * R ^ 2 / η'⌉₊ with hKdef
  set K' := ⌈2 * κ * (R ^ 2 + 2) / (η / 2)⌉₊ with hK'def
  have hK : 0 < K := Nat.ceil_pos.mpr hx
  have hK' : 0 < K' := Nat.ceil_pos.mpr hx'
  have hKr : (0 : ℝ) < K := by exact_mod_cast hK
  have hK'r : (0 : ℝ) < K' := by exact_mod_cast hK'
  have hKge : 4 * (d : ℝ) * R ^ 2 ≤ K * η' := (div_le_iff₀ hη').mp (Nat.le_ceil _)
  have hK'ge : 2 * κ * (R ^ 2 + 2) ≤ K' * (η / 2) :=
    (div_le_iff₀ (by positivity)).mp (Nat.le_ceil _)
  have hghR : gh 0 R K = R / K := by rw [gh]; ring
  have hghS : gh (-1) (R ^ 2 + 1) K' = (R ^ 2 + 2) / K' := by rw [gh]; ring
  -- the squaring error `4dR²/K` is at most `η'`
  have herr : (d : ℝ) * (2 * (2 * R) * gh 0 R K) ≤ η' := by
    rw [hghR, show (d : ℝ) * (2 * (2 * R) * (R / K)) = 4 * (d : ℝ) * R ^ 2 / K by ring,
      div_le_iff₀ hKr]
    nlinarith
  refine ⟨K, K', hK, hK', herr.trans hη'1, ?_, ?_, ?_, ?_⟩
  · calc κ * ((d : ℝ) * (2 * (2 * R) * gh 0 R K)) ≤ κ * η' :=
          mul_le_mul_of_nonneg_left herr hκ.le
      _ = η / 2 := by rw [hη'def]; field_simp
  · rw [hghS, show 2 * κ * ((R ^ 2 + 2) / K') = 2 * κ * (R ^ 2 + 2) / K' by ring,
      div_le_iff₀ hK'r]
    nlinarith
  · calc (K : ℝ) ≤ 4 * (d : ℝ) * R ^ 2 / η' + 1 := (Nat.ceil_lt_add_one hx.le).le
      _ = 8 * (d : ℝ) * R ^ 2 * κ / η + 1 := by rw [hη'def]; field_simp; ring
  · calc (K' : ℝ) ≤ 2 * κ * (R ^ 2 + 2) / (η / 2) + 1 := (Nat.ceil_lt_add_one hx'.le).le
      _ = 4 * κ * (R ^ 2 + 2) / η + 1 := by field_simp; ring

/-- Convert the grid sizes into the width bound `O(d^{5/2}(R²+1)/η)` of the
proof of Theorem 1.3(ii): the first hidden layer has `4dK` units and the
second `2K'+1`. -/
private lemma centered_width_bound {d : ℕ} (hd : 0 < d) {η R : ℝ}
    (hη : 0 < η) (hη1 : η ≤ 1) {K K' : ℕ}
    (hKub : (K : ℝ) ≤ 8 * (d : ℝ) * R ^ 2 * (4 * π * Real.sqrt d) / η + 1)
    (hK'ub : (K' : ℝ) ≤ 4 * (4 * π * Real.sqrt d) * (R ^ 2 + 2) / η + 1) :
    (d : ℝ) * (2 * ((K : ℝ) * 2)) + ((K' : ℝ) * 2 + 1) ≤
      200 * π * ((d : ℝ) ^ 2 * Real.sqrt d) * (R ^ 2 + 1) / η := by
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hπ := Real.pi_gt_three
  have hR2 : 0 ≤ R ^ 2 := sq_nonneg R
  set s := Real.sqrt d with hs
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hs2 : s ^ 2 = d := Real.sq_sqrt (by positivity)
  have hs1 : 1 ≤ s := Real.one_le_sqrt.mpr hd1
  set A := (d : ℝ) ^ 2 * s with hA
  have hdA : (d : ℝ) ≤ A := by rw [hA]; nlinarith
  have hsA : s ≤ A := by rw [hA]; nlinarith
  have hKη : (K : ℝ) * η ≤ 32 * π * (d : ℝ) * R ^ 2 * s + η := by
    have h := mul_le_mul_of_nonneg_right hKub hη.le
    rw [add_mul, div_mul_cancel₀ _ hη.ne', one_mul] at h
    linarith
  have hK'η : (K' : ℝ) * η ≤ 16 * π * s * (R ^ 2 + 2) + η := by
    have h := mul_le_mul_of_nonneg_right hK'ub hη.le
    rw [add_mul, div_mul_cancel₀ _ hη.ne', one_mul] at h
    linarith
  rw [le_div_iff₀ hη]
  have h1 : π * s * R ^ 2 ≤ π * A * R ^ 2 := by gcongr
  have h2 : π * s ≤ π * A := by gcongr
  have h3 : A ≤ π * A := by nlinarith
  have h4 : 0 ≤ π * A * R ^ 2 := by positivity
  calc ((d : ℝ) * (2 * ((K : ℝ) * 2)) + ((K' : ℝ) * 2 + 1)) * η
      = 4 * d * (K * η) + 2 * (K' * η) + η := by ring
    _ ≤ 4 * d * (32 * π * (d : ℝ) * R ^ 2 * s + η) +
          2 * (16 * π * s * (R ^ 2 + 2) + η) + η := by gcongr
    _ ≤ 4 * d * (32 * π * (d : ℝ) * R ^ 2 * s + 1) +
          2 * (16 * π * s * (R ^ 2 + 2) + 1) + 1 := by gcongr
    _ = 128 * (π * A * R ^ 2) + 32 * (π * s * R ^ 2) + 64 * (π * s) + 4 * d + 3 := by
          rw [hA]; ring
    _ ≤ 200 * π * A * (R ^ 2 + 1) := by nlinarith

/-- **Local depth-3 approximation of the proof of Theorem 1.3(ii).**  For every
`R > 0` and `0 < η ≤ 1` the network `𝒩_{R,η} = 𝒩_sin ∘ 𝒩_sq` satisfies
`sup_{‖x‖≤R} |F(x) - 𝒩_{R,η}(x)| ≤ η`, has width `O(d^{5/2}(R²+1)/η)`,
parameters bounded by `2(R²+1) + 4π√d`, and `|𝒩_{R,η}| ≤ 1` everywhere. -/
theorem exists_net3c_approx {d : ℕ} (hd : 0 < d) {η R : ℝ}
    (hη : 0 < η) (hη1 : η ≤ 1) (hR : 0 < R) :
    ∃ N : Net3 d,
      ((N.n1 : ℝ) + N.n2 ≤
        200 * π * ((d : ℝ) ^ 2 * Real.sqrt d) * (R ^ 2 + 1) / η) ∧
      N.WeightsLe (2 * (R ^ 2 + 1) + 4 * π * Real.sqrt d) ∧
      (∀ x : Vec d, ‖x‖ ≤ R →
        |N.eval x - Real.sin (4 * π * Real.sqrt d * ‖x‖ ^ 2)| ≤ η) ∧
      ∀ x : Vec d, |N.eval x| ≤ 1 := by
  have hκ : 0 < 4 * π * Real.sqrt d := by positivity
  obtain ⟨K, K', hK, hK', heSq1, heSq2, hSin, hKub, hK'ub⟩ :=
    exists_approximation_grids hd hR hη hη1
  refine ⟨net3c d R K (-1) (R ^ 2 + 1) K'
    (fun s => Real.sin (4 * π * Real.sqrt d * s)), ?_, ?_, ?_, ?_⟩
  · show ((d * (2 * (K * 2)) : ℕ) : ℝ) + ((K' * 2 + 1 : ℕ) : ℝ) ≤ _
    push_cast
    linarith [centered_width_bound hd hη hη1 hKub hK'ub]
  · exact net3c_weights hR hK hK' hκ.le
  · intro x hx
    exact net3c_error hR hK hK' heSq1 heSq2 hSin hx
  · intro x
    rw [net3c_eval]
    exact abs_hinge_le (a := -1) (b := R ^ 2 + 1) (N := K')
      (fun s => Real.sin (4 * π * Real.sqrt d * s)) 1 (by nlinarith [sq_nonneg R]) hK'
      (fun t _ => Real.abs_sin_le_one _) _

end

end GaussianDepthSeparation
