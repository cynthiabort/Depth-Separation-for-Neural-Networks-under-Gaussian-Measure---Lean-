/-
GaussianDepthSeparation — totality of the Hermite system in `L²(γ)` (the 1-D Gaussian moment
problem) and the Hermite expansion `g = ∑ (⟨g,h_n⟩/n!) h_n`.

Route: a `g ⊥` all Hermite classes is `⊥` all polynomial classes
(triangularity: monomials lie in the Hermite span); the two finite measures
`γ.withDensity g⁺`, `γ.withDensity g⁻` then have equal moments, and — since the
Gaussian has all exponential moments — equal characteristic functions
(dominated convergence of the exponential partial sums; no analyticity theory
needed), hence are equal (`Measure.ext_of_charFun`), forcing `g = 0`.  The
normalized Hermite classes then form a `HilbertBasis`.
-/
import GaussianDepthSeparation.Chaos
import Mathlib.Analysis.InnerProductSpace.l2Space

namespace GaussianDepthSeparation

open MeasureTheory ProbabilityTheory Polynomial Filter Complex
open scoped RealInnerProductSpace ENNReal NNReal Nat Topology

noncomputable section

/-! ### Exponential integrability of the Gaussian -/

/-- `e^{ct}` is `γ`-integrable (complete the square). -/
lemma integrable_exp_mul_gaussian (c : ℝ) :
    Integrable (fun t => Real.exp (c * t)) γ₁ := by
  rw [γ₁, gaussianReal_of_var_ne_zero _ one_ne_zero,
    integrable_withDensity_iff (measurable_gaussianPDF 0 1)
      (ae_of_all _ fun _ => gaussianPDF_lt_top)]
  have hrw : (fun t => Real.exp (c * t) * (gaussianPDF 0 1 t).toReal)
      = fun t => ((Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (c ^ 2 / 2)) *
          Real.exp (-(1/2) * (t - c) ^ 2) := by
    funext t
    rw [toReal_gaussianPDF, gaussianPDFReal_zero_one]
    rw [show (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (c ^ 2 / 2) * Real.exp (-(1/2) * (t - c) ^ 2)
        = (Real.sqrt (2 * Real.pi))⁻¹ * (Real.exp (c ^ 2 / 2) * Real.exp (-(1/2) * (t - c) ^ 2))
      from by ring, ← Real.exp_add]
    rw [show Real.exp (c * t) * ((Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-t ^ 2 / 2))
        = (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (c * t + -t ^ 2 / 2) from by
      rw [Real.exp_add]; ring]
    congr 1
    ring_nf
  rw [hrw]
  exact ((integrable_exp_neg_mul_sq (by norm_num : (0:ℝ) < 1/2)).comp_sub_right c).const_mul _

/-- `e^{c|t|}` is `γ`-integrable. -/
lemma integrable_exp_abs_mul_gaussian (c : ℝ) :
    Integrable (fun t => Real.exp (c * |t|)) γ₁ := by
  refine Integrable.mono' ((integrable_exp_mul_gaussian c).add
    (integrable_exp_mul_gaussian (-c))) ?_ (ae_of_all _ fun t => ?_)
  · exact (Real.continuous_exp.comp (continuous_const.mul continuous_abs)).aestronglyMeasurable
  · rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    rcases abs_choice t with h | h
    · rw [h]
      exact le_add_of_nonneg_right (Real.exp_pos _).le
    · rw [h, mul_neg, ← neg_mul]
      exact le_add_of_nonneg_left (Real.exp_pos _).le

lemma memLp_exp_abs_mul_gaussian (c : ℝ) :
    MemLp (fun t => Real.exp (c * |t|)) 2 γ₁ := by
  have hcont : Continuous fun t : ℝ => Real.exp (c * |t|) :=
    Real.continuous_exp.comp (continuous_const.mul continuous_abs)
  rw [memLp_two_iff_integrable_sq hcont.aestronglyMeasurable]
  have hrw : (fun t => Real.exp (c * |t|) ^ 2) = fun t => Real.exp ((2 * c) * |t|) := by
    funext t
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  rw [hrw]
  exact integrable_exp_abs_mul_gaussian (2 * c)

/-! ### The 1-D Gaussian moment problem -/

/-- The exponential series over `ℂ`. -/
lemma hasSum_cexp (z : ℂ) : HasSum (fun k => z ^ k / (k ! : ℂ)) (Complex.exp z) := by
  rw [Complex.exp_eq_exp_ℂ, NormedSpace.exp_eq_tsum_div]
  exact (NormedSpace.expSeries_div_summable z).hasSum

/-- An `L²(γ)` class orthogonal to all monomials is zero. -/
theorem eq_zero_of_forall_integral_pow_mul (g : L2R)
    (h : ∀ k : ℕ, ∫ t, t ^ k * g t ∂γ₁ = 0) : g = 0 := by
  have hgm : StronglyMeasurable (⇑g : ℝ → ℝ) := Lp.stronglyMeasurable g
  have hg2 : MemLp (⇑g) 2 γ₁ := Lp.memLp g
  have hgint : Integrable (⇑g) γ₁ := hg2.integrable one_le_two
  -- integrability of g x * x^k (Cauchy–Schwarz)
  have hgk : ∀ k : ℕ, Integrable (fun x => g x * x ^ k) γ₁ := by
    intro k
    have h2 : MemLp (fun x : ℝ => x ^ k) 2 γ₁ := by
      have := memLp_polyEval_gaussian (X ^ k)
      simpa using this
    exact hg2.integrable_mul h2
  -- the key vanishing of the Fourier-type integral
  have hkey : ∀ t : ℝ, ∫ x, g x • Complex.exp (x * t * I) ∂γ₁ = 0 := by
    intro t
    set F : ℕ → ℝ → ℂ :=
      fun n x => ∑ k ∈ Finset.range n, g x • ((↑x * ↑t * I) ^ k / (k ! : ℂ)) with hF
    have hterm_int : ∀ k : ℕ,
        Integrable (fun x => g x • ((↑x * ↑t * I) ^ k / (k ! : ℂ))) γ₁ := by
      intro k
      have hfact : ∀ x : ℝ, g x • (((x : ℂ) * ↑t * I) ^ k / (k ! : ℂ))
          = (g x * x ^ k) • (((t : ℂ) * I) ^ k / (k ! : ℂ)) := by
        intro x
        rw [Complex.real_smul, Complex.real_smul]
        push_cast
        ring
      rw [show (fun x => g x • (((x : ℂ) * ↑t * I) ^ k / (k ! : ℂ)))
          = fun x => (g x * x ^ k) • (((t : ℂ) * I) ^ k / (k ! : ℂ)) from funext hfact]
      exact (hgk k).smul_const _
    have hmeas : ∀ n, AEStronglyMeasurable (F n) γ₁ := fun n =>
      (integrable_finsetSum (Finset.range n) fun k _ => hterm_int k).aestronglyMeasurable
    have hbound : ∀ n, ∀ᵐ x ∂γ₁, ‖F n x‖ ≤ |g x| * Real.exp (|t| * |x|) := by
      intro n
      refine ae_of_all _ fun x => ?_
      calc ‖F n x‖ ≤ ∑ k ∈ Finset.range n, ‖g x • ((↑x * ↑t * I) ^ k / (k ! : ℂ))‖ :=
            norm_sum_le _ _
        _ = |g x| * ∑ k ∈ Finset.range n, (|x| * |t|) ^ k / (k !) := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun k _ => ?_
            rw [norm_smul, Real.norm_eq_abs, norm_div, norm_pow]
            congr 2
            · rw [show ((x : ℂ) * ↑t * I) = ((x : ℂ) * ↑t) * I from rfl, norm_mul,
                Complex.norm_I, mul_one, norm_mul, Complex.norm_real, Complex.norm_real,
                Real.norm_eq_abs, Real.norm_eq_abs]
            · rw [Complex.norm_natCast]
        _ ≤ |g x| * Real.exp (|x| * |t|) := by
            refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
            exact Real.sum_le_exp_of_nonneg (by positivity) n
        _ = |g x| * Real.exp (|t| * |x|) := by rw [mul_comm |x| |t|]
    have hint : Integrable (fun x => |g x| * Real.exp (|t| * |x|)) γ₁ := by
      have h1 : MemLp (fun x => |g x|) 2 γ₁ := hg2.abs
      exact h1.integrable_mul (memLp_exp_abs_mul_gaussian |t|)
    have hlim : ∀ᵐ x ∂γ₁, Tendsto (fun n => F n x) atTop
        (𝓝 (g x • Complex.exp (↑x * ↑t * I))) := by
      refine ae_of_all _ fun x => ?_
      have hs := (hasSum_cexp ((x : ℂ) * ↑t * I)).tendsto_sum_nat
      have hsm := hs.const_smul (g x)
      refine hsm.congr fun n => ?_
      rw [hF, Finset.smul_sum]
    have hdct := tendsto_integral_of_dominated_convergence _ hmeas hint hbound hlim
    have hFn : ∀ n, ∫ x, F n x ∂γ₁ = 0 := by
      intro n
      rw [hF, integral_finsetSum _ fun k _ => hterm_int k]
      refine Finset.sum_eq_zero fun k _ => ?_
      have hfact : ∀ x : ℝ, g x • (((x : ℂ) * ↑t * I) ^ k / (k ! : ℂ))
          = (g x * x ^ k) • (((t : ℂ) * I) ^ k / (k ! : ℂ)) := by
        intro x
        rw [Complex.real_smul, Complex.real_smul]
        push_cast
        ring
      rw [integral_congr_ae (ae_of_all _ hfact), integral_smul_const]
      have hgc : ∫ x, g x * x ^ k ∂γ₁ = 0 := by
        rw [← h k]
        exact integral_congr_ae (ae_of_all _ fun x => mul_comm _ _)
      rw [hgc, zero_smul]
    have hconst : Tendsto (fun n => ∫ x, F n x ∂γ₁) atTop (𝓝 0) := by
      rw [show (fun n => ∫ x, F n x ∂γ₁) = fun _ => (0 : ℂ) from funext hFn]
      exact tendsto_const_nhds
    exact tendsto_nhds_unique hdct hconst
  -- the two positive-part measures
  set μp := γ₁.withDensity (fun t => ENNReal.ofReal (g t)) with hμp
  set μm := γ₁.withDensity (fun t => ENNReal.ofReal (-(g t))) with hμm
  have : IsFiniteMeasure μp := isFiniteMeasure_withDensity_ofReal hgint.2
  have : IsFiniteMeasure μm := isFiniteMeasure_withDensity_ofReal hgint.neg.2
  have htoReal : ∀ a : ℝ, (ENNReal.ofReal a).toReal = max a 0 := fun a => by
    rw [ENNReal.ofReal, ENNReal.coe_toReal, Real.coe_toNNReal']
  have hcexp_cont : ∀ t : ℝ, Continuous fun x : ℝ => Complex.exp ((⟪x, t⟫ : ℝ) * I) := by
    intro t
    refine Complex.continuous_exp.comp (Continuous.mul ?_ continuous_const)
    exact Complex.continuous_ofReal.comp (continuous_id.inner continuous_const)
  have hnorm_cexp : ∀ (x t : ℝ), ‖Complex.exp (((⟪x, t⟫ : ℝ) : ℂ) * I)‖ = 1 :=
    fun x t => Complex.norm_exp_ofReal_mul_I _
  have hintp : ∀ t : ℝ, Integrable
      (fun x => (ENNReal.ofReal (g x)).toReal • Complex.exp ((⟪x, t⟫ : ℝ) * I)) γ₁ := by
    intro t
    refine Integrable.mono' hgint.abs (AEStronglyMeasurable.smul
      (hgm.measurable.ennreal_ofReal.ennreal_toReal).aestronglyMeasurable
      (hcexp_cont t).aestronglyMeasurable) (ae_of_all _ fun x => ?_)
    rw [norm_smul, hnorm_cexp, mul_one, Real.norm_eq_abs, htoReal,
      abs_of_nonneg (le_max_right _ _)]
    exact max_le (le_abs_self _) (abs_nonneg _)
  have hintm : ∀ t : ℝ, Integrable
      (fun x => (ENNReal.ofReal (-(g x))).toReal • Complex.exp ((⟪x, t⟫ : ℝ) * I)) γ₁ := by
    intro t
    refine Integrable.mono' hgint.abs (AEStronglyMeasurable.smul
      (hgm.measurable.neg.ennreal_ofReal.ennreal_toReal).aestronglyMeasurable
      (hcexp_cont t).aestronglyMeasurable) (ae_of_all _ fun x => ?_)
    rw [norm_smul, hnorm_cexp, mul_one, Real.norm_eq_abs, htoReal,
      abs_of_nonneg (le_max_right _ _)]
    exact max_le (neg_le_abs _) (abs_nonneg _)
  have hchar : charFun μp = charFun μm := by
    funext t
    rw [charFun_apply, charFun_apply, hμp, hμm]
    conv_lhs =>
      rw [integral_withDensity_eq_integral_toReal_smul
        (hgm.measurable.ennreal_ofReal) (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
    conv_rhs =>
      rw [integral_withDensity_eq_integral_toReal_smul
        (f := fun x => ENNReal.ofReal (-(g x)))
        (hgm.measurable.neg.ennreal_ofReal) (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
    rw [← sub_eq_zero, ← integral_sub (hintp t) (hintm t)]
    have hpt : ∀ x : ℝ,
        (ENNReal.ofReal (g x)).toReal • Complex.exp ((⟪x, t⟫ : ℝ) * I)
          - (ENNReal.ofReal (-(g x))).toReal • Complex.exp ((⟪x, t⟫ : ℝ) * I)
        = g x • Complex.exp ((x : ℂ) * ↑t * I) := by
      intro x
      rw [← sub_smul, htoReal, htoReal]
      have hmax : max (g x) 0 - max (-(g x)) 0 = g x := by
        rcases le_total 0 (g x) with hc | hc
        · rw [max_eq_left hc, max_eq_right (by linarith), sub_zero]
        · rw [max_eq_right hc, max_eq_left (by linarith)]
          ring
      rw [hmax]
      congr 2
      rw [show (⟪x, t⟫ : ℝ) = x * t from by rw [RCLike.inner_apply, conj_trivial]; ring,
        Complex.ofReal_mul]
    rw [integral_congr_ae (ae_of_all _ hpt)]
    exact hkey t
  have heq : μp = μm := Measure.ext_of_charFun hchar
  have hae : (fun t => ENNReal.ofReal (g t)) =ᵐ[γ₁] fun t => ENNReal.ofReal (-(g t)) := by
    refine ae_eq_of_forall_setLIntegral_eq_of_sigmaFinite
      (hgm.measurable.ennreal_ofReal) (hgm.measurable.neg.ennreal_ofReal) ?_
    intro s hs _
    rw [← withDensity_apply _ hs, ← withDensity_apply _ hs, ← hμp, ← hμm, heq]
  have hzero : (⇑g : ℝ → ℝ) =ᵐ[γ₁] 0 := by
    filter_upwards [hae] with x hx
    rcases lt_trichotomy (g x) 0 with hlt | heq0 | hgt
    · exfalso
      rw [ENNReal.ofReal_eq_zero.mpr hlt.le] at hx
      have : ENNReal.ofReal (-(g x)) ≠ 0 := by
        rw [Ne, ENNReal.ofReal_eq_zero, not_le]
        linarith
      exact this hx.symm
    · exact heq0
    · exfalso
      rw [ENNReal.ofReal_eq_zero.mpr (by linarith : -(g x) ≤ 0)] at hx
      have : ENNReal.ofReal (g x) ≠ 0 := by
        rw [Ne, ENNReal.ofReal_eq_zero, not_le]
        exact hgt
      exact this hx
  apply Lp.ext
  filter_upwards [hzero, Lp.coeFn_zero (E := ℝ) (p := 2) (μ := γ₁)] with x h1 h2
  rw [h1, h2]

/-! ### Triangularity: monomials lie in the Hermite span -/

lemma hR_monic (n : ℕ) : (hR n).Monic :=
  (hermite_monic n).map _

lemma natDegree_hR (n : ℕ) : (hR n).natDegree = n := by
  rw [hR, (hermite_monic n).natDegree_map, natDegree_hermite]

/-- Every monomial lies in the span of the real Hermite polynomials. -/
theorem X_pow_mem_span_hR (k : ℕ) :
    (X : Polynomial ℝ) ^ k ∈ Submodule.span ℝ (Set.range hR) := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · rw [pow_zero, ← hR_zero]
      exact Submodule.subset_span ⟨0, rfl⟩
    have hkX : (X : Polynomial ℝ) ^ k = hR k - (hR k - X ^ k) := by ring
    rw [hkX]
    refine Submodule.sub_mem _ (Submodule.subset_span ⟨k, rfl⟩) ?_
    set Q : Polynomial ℝ := hR k - X ^ k with hQ
    have hcoeff : ∀ j, k ≤ j → Q.coeff j = 0 := by
      intro j hj
      rw [hQ, Polynomial.coeff_sub, Polynomial.coeff_X_pow]
      rcases eq_or_lt_of_le hj with rfl | hlt
      · rw [ite_eq_left rfl]
        have hlead : (hR k).coeff k = 1 := by
          have hm := hR_monic k
          rw [Polynomial.Monic, Polynomial.leadingCoeff, natDegree_hR] at hm
          exact hm
        rw [hlead, sub_self]
      · rw [ite_eq_right (by omega), Polynomial.coeff_eq_zero_of_natDegree_lt
          (by rw [natDegree_hR]; omega), sub_zero]
    have hdegQ : Q.natDegree < k := by
      have hle : Q.natDegree ≤ k - 1 := Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
        (fun m hm => hcoeff m (by omega))
      omega
    have hexp : Q = ∑ j ∈ Finset.range (Q.natDegree + 1),
        Polynomial.C (Q.coeff j) * X ^ j := Polynomial.as_sum_range_C_mul_X_pow Q
    rw [hexp]
    refine Submodule.sum_mem _ fun j hj => ?_
    have hjk : j < k := by
      have hj' := Finset.mem_range.mp hj
      omega
    rw [show Polynomial.C (Q.coeff j) * (X : Polynomial ℝ) ^ j
        = Q.coeff j • (X : Polynomial ℝ) ^ j from by rw [Polynomial.smul_eq_C_mul]]
    exact Submodule.smul_mem _ _ (ih j hjk)

/-- The `L²(γ)`-class map on polynomials, as a linear map. -/
def polyL2 : Polynomial ℝ →ₗ[ℝ] L2R where
  toFun P := (memLp_polyEval_gaussian P).toLp
  map_add' P Q := by
    apply Lp.ext
    filter_upwards [MemLp.coeFn_toLp (memLp_polyEval_gaussian (P + Q)),
      MemLp.coeFn_toLp (memLp_polyEval_gaussian P),
      MemLp.coeFn_toLp (memLp_polyEval_gaussian Q),
      Lp.coeFn_add ((memLp_polyEval_gaussian P).toLp) ((memLp_polyEval_gaussian Q).toLp)]
      with t h1 h2 h3 h4
    rw [h1, h4]
    simp only [Pi.add_apply, h2, h3, Polynomial.eval_add]
  map_smul' c P := by
    apply Lp.ext
    filter_upwards [MemLp.coeFn_toLp (memLp_polyEval_gaussian (c • P)),
      MemLp.coeFn_toLp (memLp_polyEval_gaussian P),
      Lp.coeFn_smul c ((memLp_polyEval_gaussian P).toLp)] with t h1 h2 h3
    rw [h1]
    rw [show ((RingHom.id ℝ) c • MemLp.toLp (fun t => eval t P) (memLp_polyEval_gaussian P))
        = c • (memLp_polyEval_gaussian P).toLp from rfl, h3]
    simp only [Pi.smul_apply, h2, Polynomial.eval_smul, smul_eq_mul]

lemma polyL2_hR (n : ℕ) : polyL2 (hR n) = hermiteL2 n := rfl

lemma polyL2_coeFn (P : Polynomial ℝ) : ⇑(polyL2 P) =ᵐ[γ₁] fun t => P.eval t :=
  MemLp.coeFn_toLp (memLp_polyEval_gaussian P)

/-- Monomial classes lie in the span of the Hermite classes. -/
lemma polyL2_X_pow_mem_span (k : ℕ) :
    polyL2 (X ^ k) ∈ Submodule.span ℝ (Set.range hermiteL2) := by
  have h1 : polyL2 (X ^ k) ∈ Submodule.map polyL2 (Submodule.span ℝ (Set.range hR)) :=
    Submodule.mem_map_of_mem (X_pow_mem_span_hR k)
  rw [Submodule.map_span] at h1
  have h2 : ⇑polyL2 '' Set.range hR = Set.range hermiteL2 := by
    ext f
    constructor
    · rintro ⟨_, ⟨n, rfl⟩, rfl⟩
      exact ⟨n, (polyL2_hR n).symm⟩
    · rintro ⟨n, rfl⟩
      exact ⟨hR n, ⟨n, rfl⟩, polyL2_hR n⟩
  rwa [h2] at h1

/-! ### The Hermite Hilbert basis of `L²(γ)` -/

/-- **Totality of the Hermite system**: nothing is orthogonal to all Hermite
classes (the Gaussian moment problem). -/
theorem hermite_span_orthogonal_eq_bot :
    (Submodule.span ℝ (Set.range hermiteL2))ᗮ = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro g hg
  rw [Submodule.mem_orthogonal] at hg
  refine eq_zero_of_forall_integral_pow_mul g fun k => ?_
  have h1 : ⟪polyL2 (X ^ k), g⟫ = 0 := hg _ (polyL2_X_pow_mem_span k)
  rw [L2.inner_def] at h1
  rw [← h1]
  refine integral_congr_ae ?_
  filter_upwards [polyL2_coeFn (X ^ k)] with t ht
  rw [RCLike.inner_apply, conj_trivial, ht]
  simp [mul_comm]

/-- The normalized Hermite classes. -/
def hermNorm (n : ℕ) : L2R := ((Real.sqrt (n !))⁻¹ : ℝ) • hermiteL2 n

lemma sqrt_factorial_pos (n : ℕ) : 0 < Real.sqrt (n !) :=
  Real.sqrt_pos.mpr (by positivity)

lemma orthonormal_hermNorm : Orthonormal ℝ hermNorm := by
  rw [orthonormal_iff_ite]
  intro m n
  rw [hermNorm, hermNorm, real_inner_smul_left, real_inner_smul_right, hermiteL2_inner]
  by_cases h : m = n
  · subst h
    rw [ite_eq_left rfl, ite_eq_left rfl]
    have hsq : Real.sqrt (m !) * Real.sqrt (m !) = (m ! : ℝ) :=
      Real.mul_self_sqrt (by positivity)
    have hstep : (Real.sqrt (m !))⁻¹ * ((Real.sqrt (m !))⁻¹ * (m ! : ℝ))
        = ((m ! : ℝ)) / (Real.sqrt (m !) * Real.sqrt (m !)) := by ring
    rw [hstep, hsq, div_self (by positivity : ((m ! : ℕ) : ℝ) ≠ 0)]
  · rw [ite_eq_right h, ite_eq_right h, mul_zero, mul_zero]

lemma span_hermNorm_eq :
    Submodule.span ℝ (Set.range hermNorm) = Submodule.span ℝ (Set.range hermiteL2) := by
  refine le_antisymm (Submodule.span_le.mpr ?_) (Submodule.span_le.mpr ?_)
  · rintro f ⟨n, rfl⟩
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨n, rfl⟩)
  · rintro f ⟨n, rfl⟩
    have h : hermiteL2 n = Real.sqrt (n !) • hermNorm n := by
      rw [hermNorm, smul_smul, mul_inv_cancel₀ (sqrt_factorial_pos n).ne', one_smul]
    rw [h]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨n, rfl⟩)

/-- The Hermite Hilbert basis of `L²(γ)`. -/
def hermBasis : HilbertBasis ℕ ℝ L2R :=
  HilbertBasis.mkOfOrthogonalEqBot orthonormal_hermNorm
    (by rw [span_hermNorm_eq]; exact hermite_span_orthogonal_eq_bot)

/-- **The Hermite expansion** `g = ∑ₙ (⟨g,hₙ⟩/n!)·hₙ` in `L²(γ)`
(LaTeX — `main.tex` §3: "Its Hermite expansion in $L^2(\gamma)$ is
$g = \sum_{n=0}^\infty \frac{\langle g, h_n\rangle}{n!}h_n$"). -/
theorem hermite_hasSum (g : L2R) :
    HasSum (fun n => (⟪g, hermiteL2 n⟫ / (n ! : ℝ)) • hermiteL2 n) g := by
  have h := hermBasis.hasSum_repr g
  have hterm : ∀ n, (hermBasis.repr g n) • hermBasis n
      = (⟪g, hermiteL2 n⟫ / (n ! : ℝ)) • hermiteL2 n := by
    intro n
    have hcoe : (hermBasis n : L2R) = hermNorm n := by
      rw [hermBasis, HilbertBasis.coe_mkOfOrthogonalEqBot]
    have hrepr : hermBasis.repr g n = ⟪hermNorm n, g⟫ := by
      rw [HilbertBasis.repr_apply_apply, hcoe]
    rw [hrepr, hcoe, hermNorm, real_inner_smul_left, smul_smul,
      real_inner_comm (hermiteL2 n) g]
    congr 1
    field_simp
    rw [Real.sq_sqrt (by positivity : (0:ℝ) ≤ ((n ! : ℕ) : ℝ))]
    ring
  rw [show (fun n => (⟪g, hermiteL2 n⟫ / (n ! : ℝ)) • hermiteL2 n)
      = fun n => (hermBasis.repr g n) • hermBasis n from funext fun n => (hterm n).symm]
  exact h

end

end GaussianDepthSeparation
