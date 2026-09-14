/-
GaussianDepthSeparation §4 — Tail Estimate and Lower Bound (Corollary 4.2, Theorem 1.1).

`Pge d n₀ = id − Plt d n₀` is the orthogonal projection onto `(chaosLt d n₀)ᗮ`
(the "`P_{≥n₀}`" of the paper).  The proof stays finite everywhere except one
`HasSum`→`le_of_tendsto` step:
- **finite Bessel** `∑_{n∈s}‖P_n f‖² ≤ ‖f‖²` (finite Parseval + Cauchy–Schwarz);
- the ridge chaos decomposition `g^v = ∑_n P_n(g^v)` (image of the Hermite
  expansion), giving `Pge(g^v) = ∑_{n≥n₀} P_n(g^v)`;
- the cross-term bound via `‖·‖`-Cauchy–Schwarz over a finite index set, the
  per-level correlation bound (Prop 4.1) and `K_n ≤ K_{n₀}`;
- expand the square and discard the nonnegative term.
-/
import GaussianDepthSeparation.Correlation

namespace GaussianDepthSeparation

open MeasureTheory ProbabilityTheory Filter
open scoped RealInnerProductSpace ENNReal Nat Topology

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

noncomputable section

/-! ### Finite Bessel inequality for the chaos projections -/

lemma inner_Pn_orthogonal {d : ℕ} {i n : ℕ} (h : i ≠ n) (f g : L2 d) :
    ⟪Pn d i f, Pn d n g⟫ = 0 :=
  (chaos_isOrtho h).inner_eq (Submodule.starProjection_apply_mem _ _)
    (Submodule.starProjection_apply_mem _ _)

/-- Self-adjoint + idempotent: `⟨P_n f, f⟩ = ‖P_n f‖²`. -/
lemma Pn_inner_eq_normSq {d : ℕ} (f : L2 d) (n : ℕ) :
    ⟪Pn d n f, f⟫ = ‖Pn d n f‖ ^ 2 := by
  have hmem := Submodule.sub_starProjection_mem_orthogonal (K := chaos d n) f
  rw [Submodule.mem_orthogonal] at hmem
  have h0 : ⟪Pn d n f, f - Pn d n f⟫ = 0 :=
    hmem (Pn d n f) (Submodule.starProjection_apply_mem _ _)
  rw [inner_sub_right] at h0
  rw [← real_inner_self_eq_norm_sq]
  linarith [h0]

/-- Finite Parseval `‖∑_{n∈s} P_n f‖² = ∑_{n∈s}‖P_n f‖²`. -/
lemma norm_sum_Pn_sq {d : ℕ} (f : L2 d) (s : Finset ℕ) :
    ‖∑ n ∈ s, Pn d n f‖ ^ 2 = ∑ n ∈ s, ‖Pn d n f‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, sum_inner]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [inner_sum, Finset.sum_eq_single i]
  · rw [real_inner_self_eq_norm_sq]
  · intro j _ hji
    exact inner_Pn_orthogonal (Ne.symm hji) f f
  · intro h; exact absurd hi h

/-- **Finite Bessel** `∑_{n∈s}‖P_n f‖² ≤ ‖f‖²`. -/
lemma sum_Pn_normSq_le {d : ℕ} (f : L2 d) (s : Finset ℕ) :
    ∑ n ∈ s, ‖Pn d n f‖ ^ 2 ≤ ‖f‖ ^ 2 := by
  have hParseval : ‖∑ n ∈ s, Pn d n f‖ ^ 2 = ∑ n ∈ s, ‖Pn d n f‖ ^ 2 :=
    norm_sum_Pn_sq f s
  have hkey : ∑ n ∈ s, ‖Pn d n f‖ ^ 2 = ⟪∑ n ∈ s, Pn d n f, f⟫ := by
    rw [sum_inner]
    exact (Finset.sum_congr rfl fun n _ => Pn_inner_eq_normSq f n).symm
  have hCS : ⟪∑ n ∈ s, Pn d n f, f⟫ ≤ ‖∑ n ∈ s, Pn d n f‖ * ‖f‖ :=
    real_inner_le_norm _ _
  rw [hkey]
  rw [hkey] at hParseval
  nlinarith [hCS, hParseval, norm_nonneg (∑ n ∈ s, Pn d n f), norm_nonneg f,
    sq_nonneg (‖∑ n ∈ s, Pn d n f‖ - ‖f‖)]

/-- `P_n` is self-adjoint (stated in `Pn` terms). -/
lemma Pn_self_adjoint {d : ℕ} (n : ℕ) (a b : L2 d) :
    ⟪Pn d n a, b⟫ = ⟪a, Pn d n b⟫ :=
  Submodule.inner_starProjection_left_eq_right (chaos d n) a b

/-- `P_n` is idempotent. -/
lemma Pn_idem {d : ℕ} (n : ℕ) (a : L2 d) : Pn d n (Pn d n a) = Pn d n a :=
  Submodule.starProjection_eq_self_iff.mpr (Submodule.starProjection_apply_mem _ _)

lemma Pge_apply {d : ℕ} (n₀ : ℕ) (f : L2 d) : Pge d n₀ f = f - Plt d n₀ f := rfl

/-! ### `Pge` and the chaos projections -/

lemma chaosLt_isOrtho_chaos {d : ℕ} {n₀ n : ℕ} (hn : n₀ ≤ n) :
    chaosLt d n₀ ⟂ chaos d n := by
  rw [chaosLt, chaos]
  refine Submodule.isOrtho_span.mpr ?_
  rintro u ⟨β, hβ, rfl⟩ w ⟨α, hα, rfl⟩
  rw [Finset.mem_coe, mem_idxLt] at hβ
  rw [Finset.mem_coe, mem_idxOf] at hα
  rw [HL2_inner, ite_eq_right (by rintro rfl; omega)]

lemma chaos_le_chaosLt {d : ℕ} {n₀ n : ℕ} (hn : n < n₀) :
    chaos d n ≤ chaosLt d n₀ := by
  rw [chaos, chaosLt, Submodule.span_le]
  rintro u ⟨α, hα, rfl⟩
  rw [Finset.mem_coe, mem_idxOf] at hα
  exact Submodule.subset_span ⟨α, by rw [Finset.mem_coe, mem_idxLt]; omega, rfl⟩

/-- `P_n` kills `chaosLt d n₀` when `n ≥ n₀`. -/
lemma Pn_chaosLt_eq_zero {d : ℕ} {n₀ n : ℕ} (hn : n₀ ≤ n) {w : L2 d}
    (hw : w ∈ chaosLt d n₀) : Pn d n w = 0 := by
  have horth : w ∈ (chaos d n)ᗮ :=
    Submodule.isOrtho_iff_le.mp (chaosLt_isOrtho_chaos hn) hw
  rw [Submodule.mem_orthogonal] at horth
  refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero (Submodule.zero_mem _) ?_
  intro u hu
  rw [sub_zero, real_inner_comm]
  exact horth u hu

/-- `Pge d n₀ f ⊥ chaosLt d n₀`. -/
lemma inner_Pge_chaosLt {d : ℕ} {n₀ : ℕ} (f : L2 d) {w : L2 d}
    (hw : w ∈ chaosLt d n₀) : ⟪Pge d n₀ f, w⟫ = 0 := by
  have hPge : Pge d n₀ f = f - Plt d n₀ f := rfl
  rw [hPge, inner_sub_left]
  have h1 : ⟪Plt d n₀ f, w⟫ = ⟪f, w⟫ := by
    rw [Plt, Submodule.inner_starProjection_left_eq_right,
      Submodule.starProjection_eq_self_iff.mpr hw]
  rw [h1, sub_self]

/-- For `n ≥ n₀`, `P_n(Pge f) = P_n f`. -/
lemma Pn_Pge_of_ge {d : ℕ} {n₀ n : ℕ} (hn : n₀ ≤ n) (f : L2 d) :
    Pn d n (Pge d n₀ f) = Pn d n f := by
  have hPge : Pge d n₀ f = f - Plt d n₀ f := rfl
  have hz : Pn d n (Plt d n₀ f) = 0 :=
    Pn_chaosLt_eq_zero hn (Submodule.starProjection_apply_mem _ _)
  rw [hPge, map_sub, hz, sub_zero]

/-- For `n < n₀`, `P_n(Pge f) = 0`. -/
lemma Pn_Pge_of_lt {d : ℕ} {n₀ n : ℕ} (hn : n < n₀) (f : L2 d) :
    Pn d n (Pge d n₀ f) = 0 := by
  refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero (Submodule.zero_mem _) ?_
  intro u hu
  rw [sub_zero]
  exact inner_Pge_chaosLt f (chaos_le_chaosLt hn hu)

/-- `‖Pge f‖ ≤ ‖f‖` (Pge is norm-nonincreasing). -/
lemma norm_Pge_le {d : ℕ} (n₀ : ℕ) (f : L2 d) : ‖Pge d n₀ f‖ ≤ ‖f‖ := by
  have hPge : Pge d n₀ f = f - Plt d n₀ f := rfl
  have hortho : ⟪Plt d n₀ f, f - Plt d n₀ f⟫ = 0 := by
    have hmem := Submodule.sub_starProjection_mem_orthogonal (K := chaosLt d n₀) f
    rw [Submodule.mem_orthogonal] at hmem
    exact hmem (Plt d n₀ f) (Submodule.starProjection_apply_mem _ _)
  have hpyth : ‖f‖ ^ 2 = ‖Plt d n₀ f‖ ^ 2 + ‖f - Plt d n₀ f‖ ^ 2 := by
    have h := norm_add_sq_real (Plt d n₀ f) (f - Plt d n₀ f)
    rw [show Plt d n₀ f + (f - Plt d n₀ f) = f from by abel, hortho] at h
    linarith [h]
  rw [hPge]
  have h1 : ‖f - Plt d n₀ f‖ ^ 2 ≤ ‖f‖ ^ 2 := by nlinarith [sq_nonneg ‖Plt d n₀ f‖]
  nlinarith [norm_nonneg (f - Plt d n₀ f), norm_nonneg f, h1]

lemma Pge_sub {d : ℕ} (n₀ : ℕ) (f g : L2 d) :
    Pge d n₀ (f - g) = Pge d n₀ f - Pge d n₀ g := map_sub _ _ _

/-! ### The ridge chaos decomposition -/

/-- `g^v = ∑_n P_n(g^v)` in `L²` (image of the Hermite expansion). -/
lemma ridge_hasSum_Pn {d : ℕ} (v : Vec d) (hv : ‖v‖ = 1) (g : L2R) :
    HasSum (fun n => Pn d n (ridge v hv g)) (ridge v hv g) := by
  have hL := (hermite_hasSum g).mapL (ridge v hv).toContinuousLinearMap
  refine hL.congr_fun fun n => ?_
  rw [Pn_ridge]
  rfl

/-- `Pge(g^v) = ∑_{n≥n₀} P_n(g^v)`. -/
lemma Pge_ridge_hasSum {d : ℕ} (n₀ : ℕ) (v : Vec d) (hv : ‖v‖ = 1) (g : L2R) :
    HasSum (fun n => if n₀ ≤ n then Pn d n (ridge v hv g) else 0)
      (Pge d n₀ (ridge v hv g)) := by
  have hL := (ridge_hasSum_Pn v hv g).mapL (Pge d n₀)
  refine hL.congr_fun fun n => ?_
  by_cases hn : n₀ ≤ n
  · rw [ite_eq_left hn]
    symm
    show Pge d n₀ (Pn d n (ridge v hv g)) = Pn d n (ridge v hv g)
    rw [Pge_apply]
    have hz : Plt d n₀ (Pn d n (ridge v hv g)) = 0 := by
      refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero
        (Submodule.zero_mem _) ?_
      intro u hu
      rw [sub_zero, real_inner_comm]
      exact (chaosLt_isOrtho_chaos hn).inner_eq hu
        (Submodule.starProjection_apply_mem _ _)
    rw [hz, sub_zero]
  · rw [ite_eq_right hn]
    symm
    show Pge d n₀ (Pn d n (ridge v hv g)) = 0
    push Not at hn
    have hmem : Pn d n (ridge v hv g) ∈ chaosLt d n₀ :=
      chaos_le_chaosLt hn (Submodule.starProjection_apply_mem _ _)
    rw [Pge_apply, Plt, Submodule.starProjection_eq_self_iff.mpr hmem, sub_self]

/-! ### The cross-term bound -/

/-- Per-level bound `|⟨P_n F, P_n g^v⟩| ≤ √K_{n₀}·‖P_n F‖·‖P_n g^v‖` for `n ≥ n₀`
(`n₀` even): even case is Prop 4.1 + `K_n ≤ K_{n₀}`, odd case vanishes. -/
lemma correlation_le_Kmom {d : ℕ} (hd : 0 < d) {n₀ n : ℕ} (hn₀ : Even n₀)
    (hn : n₀ ≤ n) (F : L2 d) (hF : IsRadial F) (g : L2R) (v : Vec d) (hv : ‖v‖ = 1) :
    |⟪Pn d n F, Pn d n (ridge v hv g)⟫| ≤
      Real.sqrt (Kmom d n₀) * ‖Pn d n F‖ * ‖Pn d n (ridge v hv g)‖ := by
  rcases Nat.even_or_odd n with hne | hno
  · calc |⟪Pn d n F, Pn d n (ridge v hv g)⟫|
        ≤ Real.sqrt (Kmom d n) * ‖Pn d n F‖ * ‖Pn d n (ridge v hv g)‖ :=
          correlation_bound_of_even hd hne F hF g v hv
      _ ≤ Real.sqrt (Kmom d n₀) * ‖Pn d n F‖ * ‖Pn d n (ridge v hv g)‖ := by
          gcongr
          exact Kmom_antitone hd hn₀ hne hn
  · rw [correlation_eq_zero_of_odd hno F hF g v hv, abs_zero]
    positivity

/-- **The cross-term bound**
`|⟨Pge F, Pge g^v⟩| ≤ √K_{n₀}·‖Pge F‖·‖g‖`. -/
theorem cross_bound {d : ℕ} (hd : 0 < d) {n₀ : ℕ} (hn₀ : Even n₀)
    (F : L2 d) (hF : IsRadial F) (g : L2R) (v : Vec d) (hv : ‖v‖ = 1) :
    |⟪Pge d n₀ F, Pge d n₀ (ridge v hv g)⟫| ≤
      Real.sqrt (Kmom d n₀) * ‖Pge d n₀ F‖ * ‖g‖ := by
  set B := Real.sqrt (Kmom d n₀) * ‖Pge d n₀ F‖ * ‖g‖ with hB
  have hSum : HasSum (fun n => if n₀ ≤ n then ⟪Pn d n F, Pn d n (ridge v hv g)⟫ else 0)
      ⟪Pge d n₀ F, Pge d n₀ (ridge v hv g)⟫ := by
    have h := (Pge_ridge_hasSum n₀ v hv g).mapL (innerSL ℝ (Pge d n₀ F))
    refine h.congr_fun fun n => ?_
    show (if n₀ ≤ n then ⟪Pn d n F, Pn d n (ridge v hv g)⟫ else 0)
      = ⟪Pge d n₀ F, if n₀ ≤ n then Pn d n (ridge v hv g) else 0⟫
    by_cases hn : n₀ ≤ n
    · rw [ite_eq_left hn, ite_eq_left hn]
      symm
      calc ⟪Pge d n₀ F, Pn d n (ridge v hv g)⟫
          = ⟪Pn d n (Pge d n₀ F), ridge v hv g⟫ :=
            (Pn_self_adjoint n (Pge d n₀ F) (ridge v hv g)).symm
        _ = ⟪Pn d n F, ridge v hv g⟫ := by rw [Pn_Pge_of_ge hn]
        _ = ⟪Pn d n (Pn d n F), ridge v hv g⟫ := by rw [Pn_idem]
        _ = ⟪Pn d n F, Pn d n (ridge v hv g)⟫ :=
            Pn_self_adjoint n (Pn d n F) (ridge v hv g)
    · rw [ite_eq_right hn, ite_eq_right hn, inner_zero_right]
  have hfin : ∀ s : Finset ℕ,
      |∑ n ∈ s, (if n₀ ≤ n then ⟪Pn d n F, Pn d n (ridge v hv g)⟫ else 0)| ≤ B := by
    intro s
    set a : ℕ → ℝ := fun n => if n₀ ≤ n then ‖Pn d n F‖ else 0 with ha
    set b : ℕ → ℝ := fun n => ‖Pn d n (ridge v hv g)‖ with hb
    have hstep1 : |∑ n ∈ s, (if n₀ ≤ n then ⟪Pn d n F, Pn d n (ridge v hv g)⟫ else 0)|
        ≤ ∑ n ∈ s, Real.sqrt (Kmom d n₀) * (a n * b n) := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      refine Finset.sum_le_sum fun n _ => ?_
      by_cases hn : n₀ ≤ n
      · rw [ite_eq_left hn]
        simp only [ha, hb, ite_eq_left hn]
        rw [show Real.sqrt (Kmom d n₀) * (‖Pn d n F‖ * ‖Pn d n (ridge v hv g)‖)
            = Real.sqrt (Kmom d n₀) * ‖Pn d n F‖ * ‖Pn d n (ridge v hv g)‖ from by ring]
        exact correlation_le_Kmom hd hn₀ hn F hF g v hv
      · rw [ite_eq_right hn, abs_zero]
        simp only [ha, hb, ite_eq_right hn, zero_mul, mul_zero, le_refl]
    have hCS : (∑ n ∈ s, a n * b n) ^ 2 ≤ (∑ n ∈ s, a n ^ 2) * ∑ n ∈ s, b n ^ 2 :=
      Finset.sum_mul_sq_le_sq_mul_sq s a b
    have hSa : ∑ n ∈ s, a n ^ 2 ≤ ‖Pge d n₀ F‖ ^ 2 := by
      have heq : ∀ n ∈ s, a n ^ 2 = ‖Pn d n (Pge d n₀ F)‖ ^ 2 := by
        intro n _
        simp only [ha]
        by_cases hn : n₀ ≤ n
        · rw [ite_eq_left hn, Pn_Pge_of_ge hn]
        · rw [ite_eq_right hn, Pn_Pge_of_lt (by omega) F, norm_zero]
      rw [Finset.sum_congr rfl heq]
      exact sum_Pn_normSq_le (Pge d n₀ F) s
    have hSb : ∑ n ∈ s, b n ^ 2 ≤ ‖g‖ ^ 2 := by
      have h := sum_Pn_normSq_le (ridge v hv g) s
      rw [ridge_norm] at h
      exact h
    have habnn : 0 ≤ ∑ n ∈ s, a n * b n :=
      Finset.sum_nonneg fun n _ => by rw [ha, hb]; positivity
    have hab_le : ∑ n ∈ s, a n * b n ≤ ‖Pge d n₀ F‖ * ‖g‖ := by
      have hprod : (∑ n ∈ s, a n * b n) ^ 2 ≤ (‖Pge d n₀ F‖ * ‖g‖) ^ 2 := by
        calc (∑ n ∈ s, a n * b n) ^ 2
            ≤ (∑ n ∈ s, a n ^ 2) * ∑ n ∈ s, b n ^ 2 := hCS
          _ ≤ ‖Pge d n₀ F‖ ^ 2 * ‖g‖ ^ 2 := by
              apply mul_le_mul hSa hSb (Finset.sum_nonneg fun n _ => sq_nonneg _)
              positivity
          _ = (‖Pge d n₀ F‖ * ‖g‖) ^ 2 := by ring
      nlinarith [habnn, mul_nonneg (norm_nonneg (Pge d n₀ F)) (norm_nonneg g)]
    calc |∑ n ∈ s, (if n₀ ≤ n then ⟪Pn d n F, Pn d n (ridge v hv g)⟫ else 0)|
        ≤ ∑ n ∈ s, Real.sqrt (Kmom d n₀) * (a n * b n) := hstep1
      _ = Real.sqrt (Kmom d n₀) * ∑ n ∈ s, a n * b n := by rw [Finset.mul_sum]
      _ ≤ Real.sqrt (Kmom d n₀) * (‖Pge d n₀ F‖ * ‖g‖) :=
          mul_le_mul_of_nonneg_left hab_le (Real.sqrt_nonneg _)
      _ = B := by rw [hB]; ring
  have hle : ⟪Pge d n₀ F, Pge d n₀ (ridge v hv g)⟫ ≤ B :=
    le_of_tendsto' hSum fun s => (le_abs_self _).trans (hfin s)
  have hge : -B ≤ ⟪Pge d n₀ F, Pge d n₀ (ridge v hv g)⟫ :=
    ge_of_tendsto' hSum fun s => (neg_le_neg (hfin s)).trans (neg_abs_le _)
  exact abs_le.mpr ⟨hge, hle⟩

/-! ### Corollary 4.2 and Theorem 1.1 -/

/- LaTeX — `paper.tex`, Corollary 4.2 (Tail estimate): see file header. -/
/-- **Corollary 4.2 (Tail estimate).** -/
theorem tail_estimate {d : ℕ} (hd : 0 < d) {n₀ : ℕ} (hn₀ : Even n₀)
    (F : L2 d) (hF : IsRadial F) {r : ℕ} (g : Fin r → L2R) (v : Fin r → Vec d)
    (hv : ∀ j, ‖v j‖ = 1) :
    ‖Pge d n₀ F‖ ^ 2 -
        2 * Real.sqrt (Kmom d n₀) * ‖Pge d n₀ F‖ * ∑ j, ‖g j‖ ≤
      ‖F - ∑ j, ridge (v j) (hv j) (g j)‖ ^ 2 := by
  set S : L2 d := ∑ j, ridge (v j) (hv j) (g j) with hS
  have hcontr : ‖Pge d n₀ (F - S)‖ ^ 2 ≤ ‖F - S‖ ^ 2 := by
    have := norm_Pge_le n₀ (F - S)
    nlinarith [norm_nonneg (Pge d n₀ (F - S)), norm_nonneg (F - S)]
  refine le_trans ?_ hcontr
  rw [Pge_sub, map_sum]
  set PF := Pge d n₀ F with hPF
  set PS : L2 d := ∑ j, Pge d n₀ (ridge (v j) (hv j) (g j)) with hPS
  have hexpand : ‖PF - PS‖ ^ 2 = ‖PF‖ ^ 2 - 2 * ⟪PF, PS⟫ + ‖PS‖ ^ 2 :=
    norm_sub_sq_real PF PS
  rw [hexpand]
  have hcross : ⟪PF, PS⟫ = ∑ j, ⟪PF, Pge d n₀ (ridge (v j) (hv j) (g j))⟫ := by
    rw [hPS, inner_sum]
  have hbound : ∑ j, ⟪PF, Pge d n₀ (ridge (v j) (hv j) (g j))⟫
      ≤ Real.sqrt (Kmom d n₀) * ‖PF‖ * ∑ j, ‖g j‖ := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun j _ => ?_
    calc ⟪PF, Pge d n₀ (ridge (v j) (hv j) (g j))⟫
        ≤ |⟪PF, Pge d n₀ (ridge (v j) (hv j) (g j))⟫| := le_abs_self _
      _ ≤ Real.sqrt (Kmom d n₀) * ‖PF‖ * ‖g j‖ :=
          cross_bound hd hn₀ F hF (g j) (v j) (hv j)
  calc ‖PF‖ ^ 2 - 2 * Real.sqrt (Kmom d n₀) * ‖PF‖ * ∑ j, ‖g j‖
      ≤ ‖PF‖ ^ 2 - 2 * ⟪PF, PS⟫ := by rw [hcross]; nlinarith [hbound]
    _ ≤ ‖PF‖ ^ 2 - 2 * ⟪PF, PS⟫ + ‖PS‖ ^ 2 := by nlinarith [sq_nonneg ‖PS‖]

/- LaTeX — `paper.tex`, Theorem 1.1 (Lower bound for ridge approximation). -/
/-- **Theorem 1.1 (Lower bound for ridge approximation).** -/
theorem ridge_lower_bound {d : ℕ} (hd : 0 < d) {n₀ : ℕ} (hn₀ : Even n₀)
    (F : L2 d) (hF : IsRadial F) {r : ℕ} (g : Fin r → L2R) (v : Fin r → Vec d)
    (hv : ∀ j, ‖v j‖ = 1) {M : ℝ} (hM : 0 < M) (hgM : ∀ j, ‖g j‖ ≤ M)
    (happrox : ‖F - ∑ j, ridge (v j) (hv j) (g j)‖ ^ 2 ≤ ‖Pge d n₀ F‖ ^ 2 / 2) :
    ‖Pge d n₀ F‖ / (4 * M * Real.sqrt (Kmom d n₀)) ≤ (r : ℝ) := by
  set A := ‖Pge d n₀ F‖ with hA
  set K := Real.sqrt (Kmom d n₀) with hK
  have hAnn : 0 ≤ A := norm_nonneg _
  have hKpos : 0 < K := Real.sqrt_pos.mpr (Kmom_pos hd hn₀)
  have htail := tail_estimate hd hn₀ F hF g v hv
  have hsumg : ∑ j, ‖g j‖ ≤ (r : ℝ) * M := by
    calc ∑ j : Fin r, ‖g j‖ ≤ ∑ _j : Fin r, M := Finset.sum_le_sum fun j _ => hgM j
      _ = (r : ℝ) * M := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]; ring
  have hchain : A ^ 2 - 2 * K * A * ((r : ℝ) * M) ≤ A ^ 2 / 2 := by
    have h2 : A ^ 2 - 2 * K * A * ((r : ℝ) * M) ≤ A ^ 2 - 2 * K * A * ∑ j, ‖g j‖ := by
      have : 2 * K * A * ∑ j, ‖g j‖ ≤ 2 * K * A * ((r : ℝ) * M) :=
        mul_le_mul_of_nonneg_left hsumg (by positivity)
      linarith
    linarith [happrox, htail]
  rcases eq_or_lt_of_le hAnn with hA0 | hApos
  · rw [← hA0, zero_div]; positivity
  · have hkey : A ≤ 4 * M * K * r := by nlinarith [hApos, hKpos, hM]
    rw [div_le_iff₀ (by positivity)]
    nlinarith [hkey]

end

end GaussianDepthSeparation
