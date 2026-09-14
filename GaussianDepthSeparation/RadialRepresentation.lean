/-
GaussianDepthSeparation §5, Lemma 5.1 — radial low-chaos elements are polynomials in the
normalized squared radius.
-/
import GaussianDepthSeparation.RadialMeasure
import GaussianDepthSeparation.RadialPolynomial
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.RingTheory.Polynomial.DegreeLT

namespace GaussianDepthSeparation

open MeasureTheory ProbabilityTheory Real Set Polynomial
open scoped RealInnerProductSpace ENNReal Nat

noncomputable section

/-- The continuous Hermite-polynomial representative of a finite low-chaos
combination. -/
def chaosPolynomialRep {d : ℕ} (n₀ : ℕ) (c : MIdx d → ℝ) (x : Vec d) : ℝ :=
  ∑ α ∈ idxLt d n₀, c α * Hfun α x

lemma continuous_chaosPolynomialRep {d n₀ : ℕ} (c : MIdx d → ℝ) :
    Continuous (chaosPolynomialRep n₀ c) := by
  exact continuous_finsetSum _ fun α _ =>
    continuous_const.mul (continuous_Hfun α)

/-- A finite Hermite combination has its expected pointwise representative. -/
lemma chaosCombination_coeFn {d : ℕ} (s : Finset (MIdx d)) (c : MIdx d → ℝ) :
    ⇑(∑ α ∈ s, c α • HL2 α) =ᵐ[γ d]
      fun x => ∑ α ∈ s, c α * Hfun α x := by
  induction s using Finset.induction_on with
  | empty =>
      filter_upwards [Lp.coeFn_zero (E := ℝ) (p := (2 : ℝ≥0∞)) (μ := γ d)] with x hx
      simp
  | @insert α s hα ih =>
      simp only [Finset.sum_insert hα]
      filter_upwards [Lp.coeFn_add (c α • HL2 α) (∑ β ∈ s, c β • HL2 β),
        Lp.coeFn_smul (c α) (HL2 α), MemLp.coeFn_toLp (memLp_Hfun α), ih]
        with x hadd hsmul hH hs
      rw [hadd]
      change (c α • HL2 α : L2 d) x + (∑ β ∈ s, c β • HL2 β) x = _
      rw [hsmul, hs]
      change c α * ((memLp_Hfun α).toLp) x + _ = _
      rw [hH]

/-- Every element of the finite low-chaos span has explicit Hermite
coefficients. -/
lemma chaosLt_exists_coeff {d n₀ : ℕ} {G : L2 d} (hG : G ∈ chaosLt d n₀) :
    ∃ c : MIdx d → ℝ, ∑ α ∈ idxLt d n₀, c α • HL2 α = G := by
  rw [chaosLt, Submodule.mem_span_image_finset_iff_exists_fun'] at hG
  exact hG

lemma chaosLt_exists_continuous_rep {d n₀ : ℕ} {G : L2 d}
    (hG : G ∈ chaosLt d n₀) :
    ∃ c : MIdx d → ℝ, ⇑G =ᵐ[γ d] chaosPolynomialRep n₀ c := by
  obtain ⟨c, hc⟩ := chaosLt_exists_coeff hG
  refine ⟨c, ?_⟩
  rw [← hc]
  exact chaosCombination_coeFn (idxLt d n₀) c

/-- Restriction of the multivariate Hermite representative to the line
`t ↦ t e_i`. -/
def axisPolynomial {d : ℕ} (n₀ : ℕ) (c : MIdx d → ℝ) (i : Fin d) : Polynomial ℝ :=
  ∑ α ∈ idxLt d n₀, c α •
    ∏ j, (hR (α j)).comp (if j = i then X else 0)

lemma axisPolynomial_eval {d n₀ : ℕ} (c : MIdx d → ℝ) (i : Fin d) (t : ℝ) :
    (axisPolynomial n₀ c i).eval t =
      chaosPolynomialRep n₀ c (t • EuclideanSpace.single i (1 : ℝ)) := by
  simp only [axisPolynomial, chaosPolynomialRep, Polynomial.eval_finsetSum,
    Polynomial.eval_smul, Polynomial.eval_prod, Polynomial.eval_comp]
  refine Finset.sum_congr rfl fun α hα => ?_
  congr 1
  refine Finset.prod_congr rfl fun j _ => ?_
  by_cases hji : j = i
  · subst j
    simp
    exact (hfun_eq_hR_eval _ _).symm
  · simp [hji]
    exact (hfun_eq_hR_eval _ _).symm

lemma axisPolynomial_natDegree_lt {d n₀ : ℕ} (hn₀ : 0 < n₀)
    (c : MIdx d → ℝ) (i : Fin d) :
    (axisPolynomial n₀ c i).natDegree < n₀ := by
  apply lt_of_le_of_lt (Polynomial.natDegree_sum_le_of_forall_le _ _ ?_) (Nat.sub_lt hn₀ zero_lt_one)
  intro α hα
  apply (Polynomial.natDegree_smul_le _ _).trans
  apply (Polynomial.natDegree_prod_le _ _).trans
  calc
    ∑ j, ((hR (α j)).comp (if j = i then X else 0)).natDegree
        ≤ ∑ j, α j := by
          exact Finset.sum_le_sum fun j _ => by
            refine Polynomial.natDegree_comp_le.trans ?_
            rw [natDegree_hR]
            by_cases hji : j = i
            · simp [hji]
            · simp [hji]
    _ = mdeg α := rfl
    _ ≤ n₀ - 1 := by
      rw [mem_idxLt] at hα
      omega

/-- Radiality in `L²`, together with the full support of the Gaussian,
upgrades to pointwise rotation-invariance of the continuous polynomial
representative. -/
lemma chaosPolynomialRep_rotation_invariant {d n₀ : ℕ} {G : L2 d}
    (hG : IsRadial G) (c : MIdx d → ℝ)
    (hc : ⇑G =ᵐ[γ d] chaosPolynomialRep n₀ c) (U : Od d) (x : Vec d) :
    chaosPolynomialRep n₀ c (actMap U x) = chaosPolynomialRep n₀ c x := by
  have hccomp : (⇑G) ∘ actMap U =ᵐ[γ d]
      (chaosPolynomialRep n₀ c) ∘ actMap U := by
    refine MeasureTheory.ae_eq_comp (measurePreserving_actMap U).aemeasurable ?_
    rw [(measurePreserving_actMap U).map_eq]
    exact hc
  have hact := act_coeFn U G
  rw [hG U] at hact
  have hae : (chaosPolynomialRep n₀ c) ∘ actMap U =ᵐ[γ d]
      chaosPolynomialRep n₀ c :=
    hccomp.symm.trans (hact.symm.trans hc)
  have hcontU : Continuous ((chaosPolynomialRep n₀ c) ∘ actMap U) :=
    (continuous_chaosPolynomialRep c).comp
      ((U : Vec d →L[ℝ] Vec d).continuous)
  have hall := MeasureTheory.Measure.eq_of_ae_eq hae hcontU
    (continuous_chaosPolynomialRep c)
  exact congrFun hall x

/-- The axis restriction of a radial low-chaos representative is even. -/
lemma axisPolynomial_eval_neg {d n₀ : ℕ} {G : L2 d}
    (hG : IsRadial G) (c : MIdx d → ℝ)
    (hc : ⇑G =ᵐ[γ d] chaosPolynomialRep n₀ c) (i : Fin d) (t : ℝ) :
    (axisPolynomial n₀ c i).eval (-t) = (axisPolynomial n₀ c i).eval t := by
  let e : Vec d := EuclideanSpace.single i (1 : ℝ)
  have he : ‖e‖ = 1 := by simp [e]
  obtain ⟨U, hU⟩ := exists_actMap_eq he (by simpa using he : ‖-e‖ = 1)
  rw [axisPolynomial_eval, axisPolynomial_eval]
  have hinv := chaosPolynomialRep_rotation_invariant hG c hc U (t • e)
  have hmap : actMap U (t • e) = (-t) • e := by
    change (U : Vec d →L[ℝ] Vec d) (t • e) = (-t) • e
    rw [map_smul]
    change t • actMap U e = (-t) • e
    rw [hU]
    simp
  rw [hmap] at hinv
  simpa [e] using hinv

/-! ### Even univariate polynomials -/

/-- Replace every even monomial `a X^(2k)` by `a X^k`, dropping odd
monomials. -/
def evenSqrtPolynomial (R : Polynomial ℝ) : Polynomial ℝ :=
  R.sum fun n a => if Even n then monomial (n / 2) a else 0

lemma coeff_eq_zero_of_eval_neg_eq {R : Polynomial ℝ}
    (hR : ∀ t : ℝ, R.eval (-t) = R.eval t) {n : ℕ} (hn : Odd n) :
    R.coeff n = 0 := by
  have hpoly : R.comp (-X) = R := by
    apply Polynomial.funext
    intro t
    rw [eval_comp]
    simpa using hR t
  have hc := congrArg (fun P : Polynomial ℝ => P.coeff n) hpoly
  have hnegX : (-X : Polynomial ℝ) = C (-1 : ℝ) * X := by simp
  rw [hnegX] at hc
  change (R.comp (C (-1 : ℝ) * X)).coeff n = R.coeff n at hc
  rw [comp_C_mul_X_coeff, hn.neg_one_pow] at hc
  linarith

lemma evenSqrtPolynomial_eval_sq {R : Polynomial ℝ}
    (hR : ∀ t : ℝ, R.eval (-t) = R.eval t) (t : ℝ) :
    (evenSqrtPolynomial R).eval (t ^ 2) = R.eval t := by
  rw [evenSqrtPolynomial, Polynomial.eval_sum, Polynomial.eval_eq_sum]
  rw [Polynomial.sum_def, Polynomial.sum_def]
  refine Finset.sum_congr rfl fun n hnmem => ?_
  by_cases hn : Even n
  · obtain ⟨k, rfl⟩ := hn
    have hdiv : (k + k) / 2 = k := by omega
    have heven : Even (k + k) := ⟨k, rfl⟩
    rw [ite_eq_left heven, Polynomial.eval_monomial, hdiv, pow_two, mul_pow, pow_add]
  · have hnodd : Odd n := by simpa using hn
    have hcoeff := coeff_eq_zero_of_eval_neg_eq hR hnodd
    simp [hn, hcoeff]

lemma evenSqrtPolynomial_natDegree_lt {R : Polynomial ℝ} {n₀ : ℕ}
    (hn₀ : 0 < n₀) (hn₀e : Even n₀) (hdeg : R.natDegree < n₀) :
    (evenSqrtPolynomial R).natDegree < n₀ / 2 := by
  have hhalf : 0 < n₀ / 2 := by
    obtain ⟨k, rfl⟩ := hn₀e
    omega
  rw [evenSqrtPolynomial, Polynomial.sum_def]
  apply lt_of_le_of_lt
    (Polynomial.natDegree_sum_le_of_forall_le _ _ (fun n hnmem => ?_))
    (Nat.sub_lt hhalf zero_lt_one)
  by_cases hn : Even n
  · simp only [hn, ite_true]
    apply (Polynomial.natDegree_monomial_le _).trans
    have hnle : n ≤ R.natDegree := Polynomial.le_natDegree_of_mem_supp n hnmem
    have hnlt : n < n₀ := hnle.trans_lt hdeg
    obtain ⟨k, hk⟩ := hn
    obtain ⟨l, hl⟩ := hn₀e
    omega
  · simp [hn]

lemma evenSqrtPolynomial_coeff (R : Polynomial ℝ) (k : ℕ) :
    (evenSqrtPolynomial R).coeff k = R.coeff (2 * k) := by
  rw [evenSqrtPolynomial, Polynomial.coeff_sum, Polynomial.sum_def]
  rw [Finset.sum_eq_single (2 * k)]
  · rw [ite_eq_left (even_two_mul k), Polynomial.coeff_monomial, ite_eq_left (by omega)]
  · intro n hn hne
    by_cases he : Even n
    · rw [ite_eq_left he, Polynomial.coeff_monomial, ite_eq_right]
      intro hdiv
      apply hne
      obtain ⟨j, rfl⟩ := he
      omega
    · simp [he]
  · intro hnot
    have hz : R.coeff (2 * k) = 0 := Polynomial.notMem_support_iff.mp hnot
    simp [hz]

/-- Taking the polynomial in the squared variable is linear. -/
def evenSqrtLinear : Polynomial ℝ →ₗ[ℝ] Polynomial ℝ where
  toFun := evenSqrtPolynomial
  map_add' R S := by
    ext k
    simp only [evenSqrtPolynomial_coeff, coeff_add]
  map_smul' a R := by
    ext k
    simp only [evenSqrtPolynomial_coeff, coeff_smul]
    simp

/-- Composition with the scaling polynomial `cX`, as a linear map in the
outer polynomial. -/
def compScaleLinear (c : ℝ) : Polynomial ℝ →ₗ[ℝ] Polynomial ℝ where
  toFun R := R.comp (C c * X)
  map_add' R S := by
    apply Polynomial.funext
    intro t
    simp
  map_smul' a R := by
    apply Polynomial.funext
    intro t
    simp

/-! ### Canonical radial-polynomial coordinates -/

/-- The canonical Hermite coefficient of an `L²` class. -/
def hermiteCoefficient {d : ℕ} (G : L2 d) (α : MIdx d) : ℝ :=
  ⟪G, HL2 α⟫ / (mfact α : ℝ)

/-- On the finite low-chaos space, the canonical Hermite coefficients give
the expected continuous representative. -/
lemma chaosLt_canonical_coeFn {d n₀ : ℕ} {G : L2 d}
    (hG : G ∈ chaosLt d n₀) :
    ⇑G =ᵐ[γ d] chaosPolynomialRep n₀ (hermiteCoefficient G) := by
  obtain ⟨c, hc⟩ := chaosLt_exists_coeff hG
  have hcoeff : ∀ α ∈ idxLt d n₀, c α = hermiteCoefficient G α := by
    intro α hα
    have hi := congrArg (fun W : L2 d => ⟪W, HL2 α⟫) hc
    change ⟪∑ β ∈ idxLt d n₀, c β • HL2 β, HL2 α⟫ = ⟪G, HL2 α⟫ at hi
    rw [sum_inner] at hi
    have hterm : ∀ β ∈ idxLt d n₀,
        ⟪c β • HL2 β, HL2 α⟫ = if β = α then c α * (mfact α : ℝ) else 0 := by
      intro β _
      rw [real_inner_smul_left, HL2_inner]
      by_cases hβα : β = α
      · subst β
        simp
      · simp [hβα]
    rw [Finset.sum_congr rfl hterm,
      Finset.sum_ite_eq' (idxLt d n₀) α (fun _ => c α * (mfact α : ℝ)),
      ite_eq_left hα] at hi
    rw [hermiteCoefficient, ← hi, mul_div_cancel_right₀ _ (mfact_ne_zero α)]
  have hsum := chaosCombination_coeFn (idxLt d n₀) c
  rw [hc] at hsum
  filter_upwards [hsum] with x hx
  rw [hx]
  exact Finset.sum_congr rfl fun α hα => by rw [hcoeff α hα]

/-- Restrict the canonical continuous Hermite representative to an axis. -/
def canonicalAxisLinear {d : ℕ} (n₀ : ℕ) (i : Fin d) :
    L2 d →ₗ[ℝ] Polynomial ℝ where
  toFun G := axisPolynomial n₀ (hermiteCoefficient G) i
  map_add' G H := by
    simp only [axisPolynomial, hermiteCoefficient]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [inner_add_left, add_div, add_smul]
  map_smul' a G := by
    simp only [axisPolynomial, hermiteCoefficient, real_inner_smul_left]
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [smul_smul]
    congr 1
    simp
    ring

/-- Canonical polynomial coordinate of a radial low-chaos function. -/
def radialPolynomialMap {d n₀ : ℕ} (hd : 0 < d) :
    radialChaosLt d n₀ →ₗ[ℝ] Polynomial ℝ :=
  (compScaleLinear (d : ℝ)).comp
    (evenSqrtLinear.comp ((canonicalAxisLinear n₀ ⟨0, hd⟩).comp
      (radialChaosLt d n₀).subtype))

lemma radialPolynomialMap_degree_lt {d n₀ : ℕ} (hd : 0 < d)
    (hn₀ : 0 < n₀) (hn₀e : Even n₀) (G : radialChaosLt d n₀) :
    (radialPolynomialMap hd G).natDegree < n₀ / 2 := by
  let c : MIdx d → ℝ := hermiteCoefficient (G : L2 d)
  let R : Polynomial ℝ := axisPolynomial n₀ c ⟨0, hd⟩
  have hc := chaosLt_canonical_coeFn G.2.2
  have hRdeg : R.natDegree < n₀ := axisPolynomial_natDegree_lt hn₀ c ⟨0, hd⟩
  have hReven : ∀ t : ℝ, R.eval (-t) = R.eval t :=
    axisPolynomial_eval_neg G.2.1 c hc ⟨0, hd⟩
  have hQdeg := evenSqrtPolynomial_natDegree_lt hn₀ hn₀e hRdeg
  have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hd)
  change ((evenSqrtPolynomial R).comp (C (d : ℝ) * X)).natDegree < n₀ / 2
  apply lt_of_le_of_lt Polynomial.natDegree_comp_le
  rw [Polynomial.natDegree_C_mul_X (d : ℝ) hdR, mul_one]
  exact hQdeg

/-! ### Radial low-chaos representation -/

lemma chaosPolynomialRep_eq_axis_radius {d n₀ : ℕ} (hd : 0 < d) {G : L2 d}
    (hG : IsRadial G) (c : MIdx d → ℝ)
    (hc : ⇑G =ᵐ[γ d] chaosPolynomialRep n₀ c) (x : Vec d) :
    chaosPolynomialRep n₀ c x =
      (axisPolynomial n₀ c ⟨0, hd⟩).eval ‖x‖ := by
  let i : Fin d := ⟨0, hd⟩
  let e : Vec d := EuclideanSpace.single i (1 : ℝ)
  have he : ‖e‖ = 1 := by simp [e]
  rcases eq_or_ne x 0 with rfl | hx
  · rw [norm_zero, axisPolynomial_eval]
    simp
  · let w : Vec d := ‖x‖⁻¹ • x
    have hw : ‖w‖ = 1 := norm_smul_inv_norm hx
    obtain ⟨U, hU⟩ := exists_actMap_eq he hw
    have hmap : actMap U (‖x‖ • e) = x := by
      change (U : Vec d →L[ℝ] Vec d) (‖x‖ • e) = x
      rw [map_smul]
      change ‖x‖ • actMap U e = x
      rw [hU]
      change ‖x‖ • (‖x‖⁻¹ • x) = x
      rw [smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hx), one_smul]
    have hinv := chaosPolynomialRep_rotation_invariant hG c hc U (‖x‖ • e)
    rw [hmap] at hinv
    rw [axisPolynomial_eval]
    simpa [i, e] using hinv

/-- Every radial element of chaos degree `< n₀` is represented by a
univariate polynomial in `‖x‖² / d` of degree `< n₀/2`. -/
theorem radial_chaosLt_exists_polynomial {d n₀ : ℕ} (hd : 0 < d)
    (hn₀ : 0 < n₀) (hn₀e : Even n₀) {G : L2 d}
    (hGrad : IsRadial G) (hGchaos : G ∈ chaosLt d n₀) :
    ∃ q : Polynomial ℝ, q.natDegree < n₀ / 2 ∧
      ⇑G =ᵐ[γ d] fun x => q.eval (‖x‖ ^ 2 / d) := by
  obtain ⟨c, hc⟩ := chaosLt_exists_continuous_rep hGchaos
  let R : Polynomial ℝ := axisPolynomial n₀ c ⟨0, hd⟩
  let Q : Polynomial ℝ := evenSqrtPolynomial R
  let q : Polynomial ℝ := Q.comp (C (d : ℝ) * X)
  have hRdeg : R.natDegree < n₀ := axisPolynomial_natDegree_lt hn₀ c ⟨0, hd⟩
  have hReven : ∀ t : ℝ, R.eval (-t) = R.eval t :=
    axisPolynomial_eval_neg hGrad c hc ⟨0, hd⟩
  have hQdeg : Q.natDegree < n₀ / 2 :=
    evenSqrtPolynomial_natDegree_lt hn₀ hn₀e hRdeg
  have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hd)
  refine ⟨q, ?_, ?_⟩
  · change (Q.comp (C (d : ℝ) * X)).natDegree < n₀ / 2
    apply lt_of_le_of_lt Polynomial.natDegree_comp_le
    rw [Polynomial.natDegree_C_mul_X (d : ℝ) hdR, mul_one]
    exact hQdeg
  · filter_upwards [hc] with x hx
    rw [hx]
    have haxis := chaosPolynomialRep_eq_axis_radius hd hGrad c hc x
    rw [haxis]
    change R.eval ‖x‖ = q.eval (‖x‖ ^ 2 / d)
    dsimp only [q]
    rw [eval_comp]
    have hscale : (C (d : ℝ) * X).eval (‖x‖ ^ 2 / d) = ‖x‖ ^ 2 := by
      simp only [eval_mul, eval_C, eval_X]
      field_simp
    rw [hscale, ← evenSqrtPolynomial_eval_sq hReven]

lemma radialPolynomialMap_coeFn {d n₀ : ℕ} (hd : 0 < d)
    (G : radialChaosLt d n₀) :
    ⇑(G : L2 d) =ᵐ[γ d] fun x => (radialPolynomialMap hd G).eval (‖x‖ ^ 2 / d) := by
  let c : MIdx d → ℝ := hermiteCoefficient (G : L2 d)
  let R : Polynomial ℝ := axisPolynomial n₀ c ⟨0, hd⟩
  have hc := chaosLt_canonical_coeFn G.2.2
  have hReven : ∀ t : ℝ, R.eval (-t) = R.eval t :=
    axisPolynomial_eval_neg G.2.1 c hc ⟨0, hd⟩
  filter_upwards [hc] with x hx
  rw [hx]
  have haxis := chaosPolynomialRep_eq_axis_radius hd G.2.1 c hc x
  rw [haxis]
  change R.eval ‖x‖ =
    ((evenSqrtPolynomial R).comp (C (d : ℝ) * X)).eval (‖x‖ ^ 2 / d)
  rw [eval_comp]
  have hscale : (C (d : ℝ) * X).eval (‖x‖ ^ 2 / d) = ‖x‖ ^ 2 := by
    simp only [eval_mul, eval_C, eval_X]
    field_simp
  rw [hscale, ← evenSqrtPolynomial_eval_sq hReven]

lemma radialPolynomialMap_injective {d n₀ : ℕ} (hd : 0 < d)
    : Function.Injective (radialPolynomialMap (d := d) (n₀ := n₀) hd) := by
  intro G H hGH
  apply sub_eq_zero.mp
  let K : radialChaosLt d n₀ := G - H
  have hKmap : radialPolynomialMap hd K = 0 := by
    change radialPolynomialMap hd (G - H) = 0
    rw [map_sub, hGH, sub_self]
  have hrep := radialPolynomialMap_coeFn hd K
  apply Subtype.ext
  change (K : L2 d) = 0
  apply Lp.ext
  filter_upwards [hrep, Lp.coeFn_zero (E := ℝ) (p := 2) (μ := γ d)] with x hx hzero
  rw [hx, hKmap]
  simpa only [Polynomial.eval_zero, Pi.zero_apply] using hzero.symm

/-! ### The converse: every polynomial in the squared radius is low-chaos -/

lemma rho_mem_chaos {d n : ℕ} : rho d n ∈ chaos d n := by
  rw [rho]
  exact Submodule.sum_mem _ fun α hα => Submodule.smul_mem _ _
    (Submodule.subset_span ⟨α, by simpa using hα, rfl⟩)

lemma rho_ne_zero_of_even {d n : ℕ} (hd : 0 < d) (hn : Even n) :
    rho d n ≠ 0 := by
  intro hz
  have hs := norm_rho_sq hd n
  rw [hz, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] at hs
  have hK := Kmom_pos hd hn
  have hfac : (0 : ℝ) < n ! := by positivity
  nlinarith

lemma rho_mem_radialChaosLt {d n₀ n : ℕ} (hd : 0 < d) (hn : n < n₀) :
    rho d n ∈ radialChaosLt d n₀ := by
  refine ⟨?_, chaos_le_chaosLt hn rho_mem_chaos⟩
  let e : Vec d := EuclideanSpace.single (⟨0, hd⟩ : Fin d) 1
  have he : ‖e‖ = 1 := by simp [e]
  have hr := isRadial_radAvgFun (ridgeHermite n e he)
  rw [radAvg_ridgeHermite] at hr
  exact hr

instance finiteDimensional_radialChaosLt (d n₀ : ℕ) :
    FiniteDimensional ℝ (radialChaosLt d n₀) :=
  Submodule.finiteDimensional_of_le inf_le_right

/-- The even radial chaos components below `n₀` are linearly independent. -/
lemma linearIndependent_even_rho {d n₀ : ℕ} (hd : 0 < d) (hn₀e : Even n₀) :
    LinearIndependent ℝ (fun k : Fin (n₀ / 2) =>
      (⟨rho d (2 * (k : ℕ)), rho_mem_radialChaosLt hd (by
        obtain ⟨r, hr⟩ := hn₀e
        have hk := k.isLt
        omega)⟩ : radialChaosLt d n₀)) := by
  let v : Fin (n₀ / 2) → radialChaosLt d n₀ := fun k =>
    ⟨rho d (2 * (k : ℕ)), rho_mem_radialChaosLt hd (by
      obtain ⟨r, hr⟩ := hn₀e
      have hk := k.isLt
      omega)⟩
  change LinearIndependent ℝ v
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  have hgL2 : ∑ j, g j • rho d (2 * (j : ℕ)) = 0 := by
    have := congrArg (fun W : radialChaosLt d n₀ => (W : L2 d)) hg
    simpa [v] using this
  have hi := congrArg (fun W : L2 d => ⟪W, rho d (2 * (i : ℕ))⟫) hgL2
  change ⟪∑ j, g j • rho d (2 * (j : ℕ)), rho d (2 * (i : ℕ))⟫ =
    ⟪0, rho d (2 * (i : ℕ))⟫ at hi
  rw [sum_inner, inner_zero_left] at hi
  have hterm : ∀ j : Fin (n₀ / 2),
      ⟪g j • rho d (2 * (j : ℕ)), rho d (2 * (i : ℕ))⟫ =
        if j = i then g i * ‖rho d (2 * (i : ℕ))‖ ^ 2 else 0 := by
    intro j
    rw [real_inner_smul_left]
    by_cases hji : j = i
    · subst j
      rw [ite_eq_left rfl, real_inner_self_eq_norm_sq]
    · rw [ite_eq_right hji]
      have hdeg : 2 * (j : ℕ) ≠ 2 * (i : ℕ) := by
        intro h
        apply hji
        ext
        omega
      rw [(chaos_isOrtho hdeg).inner_eq rho_mem_chaos rho_mem_chaos, mul_zero]
  rw [Finset.sum_congr rfl fun j _ => hterm j,
    Finset.sum_ite_eq' Finset.univ i (fun _ => g i * ‖rho d (2 * (i : ℕ))‖ ^ 2),
    ite_eq_left (Finset.mem_univ i)] at hi
  have hrho : rho d (2 * (i : ℕ)) ≠ 0 :=
    rho_ne_zero_of_even hd (even_two_mul (i : ℕ))
  exact (mul_eq_zero.mp hi).resolve_right
    (pow_ne_zero 2 (norm_ne_zero_iff.mpr hrho))

lemma finrank_radialChaosLt {d n₀ : ℕ} (hd : 0 < d) (hn₀ : 0 < n₀)
    (hn₀e : Even n₀) :
    Module.finrank ℝ (radialChaosLt d n₀) = n₀ / 2 := by
  let Φ : radialChaosLt d n₀ →ₗ[ℝ] Polynomial.degreeLT ℝ (n₀ / 2) :=
    LinearMap.codRestrict (Polynomial.degreeLT ℝ (n₀ / 2))
      (radialPolynomialMap hd) fun G => by
        rw [Polynomial.mem_degreeLT]
        by_cases hzero : radialPolynomialMap hd G = 0
        · simp [hzero]
        · exact (Polynomial.natDegree_lt_iff_degree_lt hzero).mp
            (radialPolynomialMap_degree_lt hd hn₀ hn₀e G)
  have hΦinj : Function.Injective Φ := by
    intro G H h
    apply radialPolynomialMap_injective hd
    exact congrArg Subtype.val h
  have hu : Module.finrank ℝ (radialChaosLt d n₀) ≤ n₀ / 2 := by
    calc
      Module.finrank ℝ (radialChaosLt d n₀)
          ≤ Module.finrank ℝ (Polynomial.degreeLT ℝ (n₀ / 2)) :=
        LinearMap.finrank_le_finrank_of_injective hΦinj
      _ = n₀ / 2 := by
        rw [Module.finrank_eq_card_basis (Polynomial.degreeLT.basis ℝ (n₀ / 2))]
        simp
  have hl : n₀ / 2 ≤ Module.finrank ℝ (radialChaosLt d n₀) := by
    simpa using (linearIndependent_even_rho hd hn₀e).fintype_card_le_finrank
  omega

/-- Converse half of the paper's radial-polynomial characterization. -/
theorem polynomial_exists_radial_chaosLt {d n₀ : ℕ} (hd : 0 < d)
    (hn₀ : 0 < n₀) (hn₀e : Even n₀) (q : Polynomial ℝ)
    (hq : q.natDegree < n₀ / 2) :
    ∃ G : radialChaosLt d n₀,
      ⇑(G : L2 d) =ᵐ[γ d] fun x => q.eval (‖x‖ ^ 2 / d) := by
  have hqmem : q ∈ Polynomial.degreeLT ℝ (n₀ / 2) := by
    rw [Polynomial.mem_degreeLT]
    by_cases hzero : q = 0
    · simp [hzero]
    · exact (Polynomial.natDegree_lt_iff_degree_lt hzero).mp hq
  let Φ : radialChaosLt d n₀ →ₗ[ℝ] Polynomial.degreeLT ℝ (n₀ / 2) :=
    LinearMap.codRestrict (Polynomial.degreeLT ℝ (n₀ / 2))
      (radialPolynomialMap hd) fun G => by
        rw [Polynomial.mem_degreeLT]
        by_cases hzero : radialPolynomialMap hd G = 0
        · simp [hzero]
        · exact (Polynomial.natDegree_lt_iff_degree_lt hzero).mp
            (radialPolynomialMap_degree_lt hd hn₀ hn₀e G)
  have hdim : Module.finrank ℝ (radialChaosLt d n₀) =
      Module.finrank ℝ (Polynomial.degreeLT ℝ (n₀ / 2)) := by
    rw [finrank_radialChaosLt hd hn₀ hn₀e,
      Module.finrank_eq_card_basis (Polynomial.degreeLT.basis ℝ (n₀ / 2))]
    simp
  have hsurj : Function.Surjective Φ :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp (by
      intro G H h
      apply radialPolynomialMap_injective hd
      exact congrArg Subtype.val h)
  obtain ⟨G, hG⟩ := hsurj ⟨q, hqmem⟩
  refine ⟨G, ?_⟩
  have hrep := radialPolynomialMap_coeFn hd G
  filter_upwards [hrep] with x hx
  rw [hx]
  have hpoly : radialPolynomialMap hd G = q := congrArg Subtype.val hG
  rw [hpoly]

end

end GaussianDepthSeparation
