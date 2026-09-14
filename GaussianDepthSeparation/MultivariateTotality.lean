/-
GaussianDepthSeparation — completeness of the tensor Hermite system in `L²(γ^d)`.

The one-dimensional moment problem is proved in `Totality`.  Here we reduce
directional monomials to one-dimensional Hermite expansions and then use the
characteristic-function argument in arbitrary finite dimension.  This closes
the analytic point needed to identify the complementary projection `Pge` with
the infinite chaos tail for every `L²` function.
-/
import GaussianDepthSeparation.Energy
import GaussianDepthSeparation.GaussianTail

namespace GaussianDepthSeparation

open MeasureTheory ProbabilityTheory Polynomial Filter Complex
open scoped RealInnerProductSpace ENNReal NNReal Nat Topology

noncomputable section

/-- The algebraic span of all tensor Hermite classes. -/
def tensorHermiteSpan (d : ℕ) : Submodule ℝ (L2 d) :=
  Submodule.span ℝ (Set.range HL2)

/-- Pulling a monomial class along a unit direction produces an element of the
tensor-Hermite span. -/
lemma ridge_polyL2_X_pow_mem_tensorHermiteSpan {d k : ℕ} (v : Vec d)
    (hv : ‖v‖ = 1) :
    ridge v hv (polyL2 (X ^ k)) ∈ tensorHermiteSpan d := by
  have hp := polyL2_X_pow_mem_span k
  revert hp
  refine Submodule.span_induction
    (p := fun f _ => ridge v hv f ∈ tensorHermiteSpan d) ?_ ?_ ?_ ?_
  · rintro f ⟨n, rfl⟩
    change ridgeHermite n v hv ∈ tensorHermiteSpan d
    rw [ridgeHermite_eq_sum]
    exact Submodule.sum_mem _ fun α hα => Submodule.smul_mem _ _
      (Submodule.subset_span ⟨α, rfl⟩)
  · simp
  · intro f g _ _ hf hg
    simpa using (tensorHermiteSpan d).add_mem hf hg
  · intro c f _ hf
    simpa using (tensorHermiteSpan d).smul_mem c hf

/-- A pulled-back polynomial class has its expected pointwise representative. -/
lemma ridge_polyL2_coeFn {d : ℕ} (v : Vec d) (hv : ‖v‖ = 1)
    (P : Polynomial ℝ) :
    ⇑(ridge v hv (polyL2 P)) =ᵐ[γ d] fun x => P.eval ⟪v, x⟫ := by
  have hpoly : (⇑(polyL2 P)) ∘ ridgeMap v =ᵐ[γ d]
      (fun t => P.eval t) ∘ ridgeMap v := by
    refine MeasureTheory.ae_eq_comp (measurePreserving_ridgeMap hv).aemeasurable ?_
    rw [(measurePreserving_ridgeMap hv).map_eq]
    exact polyL2_coeFn P
  filter_upwards [ridge_coeFn v hv (polyL2 P), hpoly] with x h1 h2
  rw [h1, h2]
  rfl

/-- Orthogonality to all tensor Hermites forces every unit-direction moment to
vanish. -/
lemma integral_inner_pow_mul_eq_zero_of_mem_orthogonal {d k : ℕ}
    (g : L2 d) (hg : g ∈ (tensorHermiteSpan d)ᗮ) (v : Vec d) (hv : ‖v‖ = 1) :
    ∫ x, ⟪v, x⟫ ^ k * g x ∂(γ d) = 0 := by
  rw [Submodule.mem_orthogonal] at hg
  have hi := hg _ (ridge_polyL2_X_pow_mem_tensorHermiteSpan (k := k) v hv)
  rw [L2.inner_def] at hi
  rw [← hi]
  refine integral_congr_ae ?_
  filter_upwards [ridge_polyL2_coeFn v hv (X ^ k)] with x hx
  rw [RCLike.inner_apply, conj_trivial, hx]
  simp [mul_comm]

/-- Every directional monomial is square-integrable under the multivariate
standard Gaussian. -/
lemma memLp_inner_pow_gaussD {d : ℕ} (t : Vec d) (k : ℕ) :
    MemLp (fun x : Vec d => ⟪t, x⟫ ^ k) 2 (γ d) := by
  by_cases ht : t = 0
  · subst t
    simpa using (memLp_const (α := Vec d) (μ := γ d) (p := (2 : ℝ≥0∞))
      ((0 : ℝ) ^ k))
  · let v : Vec d := ‖t‖⁻¹ • t
    have hv : ‖v‖ = 1 := norm_smul_inv_norm ht
    have hbase : MemLp (fun x : Vec d => ⟪v, x⟫ ^ k) 2 (γ d) := by
      have h := (memLp_polyEval_gaussian (X ^ k)).comp_measurePreserving
        (measurePreserving_ridgeMap hv)
      simpa [Function.comp_def, ridgeMap] using h
    have hscaled := hbase.const_mul (‖t‖ ^ k)
    refine (memLp_congr_ae (ae_of_all _ fun x => ?_)).mp hscaled
    dsimp [v]
    rw [real_inner_smul_left]
    have hnorm : ‖t‖ ≠ 0 := norm_ne_zero_iff.mpr ht
    calc
      ‖t‖ ^ k * (‖t‖⁻¹ * ⟪t, x⟫) ^ k =
          (‖t‖ * ‖t‖⁻¹) ^ k * ⟪t, x⟫ ^ k := by rw [mul_pow]; ring
      _ = ⟪t, x⟫ ^ k := by rw [mul_inv_cancel₀ hnorm, one_pow, one_mul]

/-- Exponential-linear growth is in `L²(γ^d)`.  The proof uses
`2c‖x‖ ≤ 4c² + ‖x‖²/4` and the quadratic exponential established in
`GaussianTail`. -/
lemma memLp_exp_norm_mul_gaussD (d : ℕ) (c : ℝ) :
    MemLp (fun x : Vec d => Real.exp (c * ‖x‖)) 2 (γ d) := by
  have hcont : Continuous (fun x : Vec d => Real.exp (c * ‖x‖)) := by fun_prop
  rw [memLp_two_iff_integrable_sq hcont.aestronglyMeasurable]
  have hrw : (fun x : Vec d => Real.exp (c * ‖x‖) ^ 2) =
      fun x => Real.exp ((2 * c) * ‖x‖) := by
    funext x
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  rw [hrw]
  refine Integrable.mono'
    ((integrable_exp_quarter_norm_sq_gaussD d).const_mul (Real.exp (4 * c ^ 2)))
    (Real.continuous_exp.comp (continuous_const.mul continuous_norm)).aestronglyMeasurable
    (ae_of_all _ fun x => ?_)
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  nlinarith [sq_nonneg (‖x‖ - 4 * c)]

/-- Orthogonality to the tensor Hermites gives all multivariate directional
moments. -/
lemma all_directional_moments_eq_zero {d : ℕ} (hd : 0 < d) (g : L2 d)
    (hg : g ∈ (tensorHermiteSpan d)ᗮ) :
    ∀ (t : Vec d) (k : ℕ), ∫ x, ⟪t, x⟫ ^ k * g x ∂(γ d) = 0 := by
  intro t k
  by_cases ht : t = 0
  · subst t
    cases k with
    | zero =>
        let e : Vec d := EuclideanSpace.single (⟨0, hd⟩ : Fin d) 1
        have he : ‖e‖ = 1 := by
          dsimp [e]
          rw [PiLp.norm_single, norm_one]
        simpa using
          (integral_inner_pow_mul_eq_zero_of_mem_orthogonal g hg e he (k := 0))
    | succ k => simp
  · let v : Vec d := ‖t‖⁻¹ • t
    have hv : ‖v‖ = 1 := norm_smul_inv_norm ht
    have hu := integral_inner_pow_mul_eq_zero_of_mem_orthogonal g hg v hv (k := k)
    have ht_repr : t = ‖t‖ • v := by
      dsimp [v]
      rw [smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr ht), one_smul]
    calc
      ∫ x, ⟪t, x⟫ ^ k * g x ∂(γ d) =
          ‖t‖ ^ k * ∫ x, ⟪v, x⟫ ^ k * g x ∂(γ d) := by
        rw [← integral_const_mul]
        refine integral_congr_ae (ae_of_all _ fun x => ?_)
        simp only
        have hi : ⟪t, x⟫ = ‖t‖ * ⟪v, x⟫ := by
          conv_lhs => rw [ht_repr]
          rw [real_inner_smul_left]
        rw [hi, mul_pow]
        ring
      _ = 0 := by rw [hu, mul_zero]

/-- A multivariate `L²(γ^d)` class whose directional moments all vanish is
zero.  This is the finite-dimensional Gaussian moment problem, proved by
dominated convergence of the complex exponential series and uniqueness of
characteristic functions. -/
theorem eq_zero_of_forall_integral_inner_pow_mul {d : ℕ} (g : L2 d)
    (h : ∀ (t : Vec d) (k : ℕ), ∫ x, ⟪t, x⟫ ^ k * g x ∂(γ d) = 0) :
    g = 0 := by
  have hgm : StronglyMeasurable (⇑g : Vec d → ℝ) := Lp.stronglyMeasurable g
  have hg2 : MemLp (⇑g) 2 (γ d) := Lp.memLp g
  have hgint : Integrable (⇑g) (γ d) := hg2.integrable one_le_two
  have hgk : ∀ (t : Vec d) (k : ℕ),
      Integrable (fun x => g x * ⟪x, t⟫ ^ k) (γ d) := by
    intro t k
    have hp : MemLp (fun x : Vec d => ⟪x, t⟫ ^ k) 2 (γ d) := by
      simpa only [real_inner_comm] using memLp_inner_pow_gaussD t k
    exact hg2.integrable_mul hp
  have hkey : ∀ t : Vec d,
      ∫ x, g x • Complex.exp ((((⟪x, t⟫ : ℝ) : ℂ)) * I) ∂(γ d) = 0 := by
    intro t
    set F : ℕ → Vec d → ℂ := fun n x =>
      ∑ k ∈ Finset.range n,
        g x • (((((⟪x, t⟫ : ℝ) : ℂ)) * I) ^ k / (k ! : ℂ)) with hF
    have hterm_int : ∀ k : ℕ, Integrable (fun x =>
        g x • (((((⟪x, t⟫ : ℝ) : ℂ)) * I) ^ k / (k ! : ℂ))) (γ d) := by
      intro k
      have hfact : ∀ x : Vec d,
          g x • (((((⟪x, t⟫ : ℝ) : ℂ)) * I) ^ k / (k ! : ℂ)) =
            (g x * ⟪x, t⟫ ^ k) • (I ^ k / (k ! : ℂ)) := by
        intro x
        rw [Complex.real_smul, Complex.real_smul]
        push_cast
        ring
      rw [show (fun x => g x • (((((⟪x, t⟫ : ℝ) : ℂ)) * I) ^ k /
          (k ! : ℂ))) = fun x => (g x * ⟪x, t⟫ ^ k) •
          (I ^ k / (k ! : ℂ)) from funext hfact]
      exact (hgk t k).smul_const _
    have hmeas : ∀ n, AEStronglyMeasurable (F n) (γ d) := fun n =>
      (integrable_finsetSum (Finset.range n) fun k _ => hterm_int k).aestronglyMeasurable
    have hbound : ∀ n, ∀ᵐ x ∂(γ d),
        ‖F n x‖ ≤ |g x| * Real.exp (‖t‖ * ‖x‖) := by
      intro n
      refine ae_of_all _ fun x => ?_
      calc
        ‖F n x‖ ≤ ∑ k ∈ Finset.range n,
            ‖g x • (((((⟪x, t⟫ : ℝ) : ℂ)) * I) ^ k / (k ! : ℂ))‖ :=
          norm_sum_le _ _
        _ = |g x| * ∑ k ∈ Finset.range n, |⟪x, t⟫| ^ k / (k !) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [norm_smul, Real.norm_eq_abs, norm_div, norm_pow, norm_mul,
            Complex.norm_real, Complex.norm_I, mul_one, Complex.norm_natCast,
            Real.norm_eq_abs]
        _ ≤ |g x| * Real.exp |⟪x, t⟫| := by
          refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
          exact Real.sum_le_exp_of_nonneg (abs_nonneg _) n
        _ ≤ |g x| * Real.exp (‖t‖ * ‖x‖) := by
          refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (abs_nonneg _)
          rw [mul_comm ‖t‖ ‖x‖]
          exact abs_real_inner_le_norm x t
    have hint : Integrable (fun x => |g x| * Real.exp (‖t‖ * ‖x‖)) (γ d) := by
      have h1 : MemLp (fun x => |g x|) 2 (γ d) := hg2.abs
      exact h1.integrable_mul (memLp_exp_norm_mul_gaussD d ‖t‖)
    have hlim : ∀ᵐ x ∂(γ d), Tendsto (fun n => F n x) atTop
        (𝓝 (g x • Complex.exp ((((⟪x, t⟫ : ℝ) : ℂ)) * I))) := by
      refine ae_of_all _ fun x => ?_
      have hs := (hasSum_cexp (((⟪x, t⟫ : ℝ) : ℂ) * I)).tendsto_sum_nat
      have hsm := hs.const_smul (g x)
      refine hsm.congr fun n => ?_
      rw [hF, Finset.smul_sum]
    have hdct := tendsto_integral_of_dominated_convergence _ hmeas hint hbound hlim
    have hFn : ∀ n, ∫ x, F n x ∂(γ d) = 0 := by
      intro n
      rw [hF, integral_finsetSum _ fun k _ => hterm_int k]
      refine Finset.sum_eq_zero fun k _ => ?_
      have hfact : ∀ x : Vec d,
          g x • (((((⟪x, t⟫ : ℝ) : ℂ)) * I) ^ k / (k ! : ℂ)) =
            (g x * ⟪x, t⟫ ^ k) • (I ^ k / (k ! : ℂ)) := by
        intro x
        rw [Complex.real_smul, Complex.real_smul]
        push_cast
        ring
      rw [integral_congr_ae (ae_of_all _ hfact), integral_smul_const]
      have hgc : ∫ x, g x * ⟪x, t⟫ ^ k ∂(γ d) = 0 := by
        rw [← h t k]
        exact integral_congr_ae (ae_of_all _ fun x => by
          change g x * ⟪x, t⟫ ^ k = ⟪t, x⟫ ^ k * g x
          rw [real_inner_comm]; ring)
      rw [hgc, zero_smul]
    have hconst : Tendsto (fun n => ∫ x, F n x ∂(γ d)) atTop (𝓝 0) := by
      rw [show (fun n => ∫ x, F n x ∂(γ d)) = fun _ => (0 : ℂ) from funext hFn]
      exact tendsto_const_nhds
    exact tendsto_nhds_unique hdct hconst
  set μp := (γ d).withDensity (fun x => ENNReal.ofReal (g x)) with hμp
  set μm := (γ d).withDensity (fun x => ENNReal.ofReal (-(g x))) with hμm
  have : IsFiniteMeasure μp := isFiniteMeasure_withDensity_ofReal hgint.2
  have : IsFiniteMeasure μm := isFiniteMeasure_withDensity_ofReal hgint.neg.2
  have htoReal : ∀ a : ℝ, (ENNReal.ofReal a).toReal = max a 0 := fun a => by
    rw [ENNReal.ofReal, ENNReal.coe_toReal, Real.coe_toNNReal']
  have hcexp_cont : ∀ t : Vec d, Continuous fun x : Vec d =>
      Complex.exp ((((⟪x, t⟫ : ℝ) : ℂ)) * I) := by
    intro t
    refine Complex.continuous_exp.comp (Continuous.mul ?_ continuous_const)
    exact Complex.continuous_ofReal.comp (continuous_id.inner continuous_const)
  have hnorm_cexp : ∀ (x t : Vec d),
      ‖Complex.exp ((((⟪x, t⟫ : ℝ) : ℂ)) * I)‖ = 1 :=
    fun x t => Complex.norm_exp_ofReal_mul_I _
  have hintp : ∀ t : Vec d, Integrable (fun x =>
      (ENNReal.ofReal (g x)).toReal •
        Complex.exp ((((⟪x, t⟫ : ℝ) : ℂ)) * I)) (γ d) := by
    intro t
    refine Integrable.mono' hgint.abs (AEStronglyMeasurable.smul
      (hgm.measurable.ennreal_ofReal.ennreal_toReal).aestronglyMeasurable
      (hcexp_cont t).aestronglyMeasurable) (ae_of_all _ fun x => ?_)
    rw [norm_smul, hnorm_cexp, mul_one, Real.norm_eq_abs, htoReal,
      abs_of_nonneg (le_max_right _ _)]
    exact max_le (le_abs_self _) (abs_nonneg _)
  have hintm : ∀ t : Vec d, Integrable (fun x =>
      (ENNReal.ofReal (-(g x))).toReal •
        Complex.exp ((((⟪x, t⟫ : ℝ) : ℂ)) * I)) (γ d) := by
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
    have hpt : ∀ x : Vec d,
        (ENNReal.ofReal (g x)).toReal •
            Complex.exp ((((⟪x, t⟫ : ℝ) : ℂ)) * I)
          - (ENNReal.ofReal (-(g x))).toReal •
            Complex.exp ((((⟪x, t⟫ : ℝ) : ℂ)) * I)
        = g x • Complex.exp ((((⟪x, t⟫ : ℝ) : ℂ)) * I) := by
      intro x
      rw [← sub_smul, htoReal, htoReal]
      have hmax : max (g x) 0 - max (-(g x)) 0 = g x := by
        rcases le_total 0 (g x) with hc | hc
        · rw [max_eq_left hc, max_eq_right (by linarith), sub_zero]
        · rw [max_eq_right hc, max_eq_left (by linarith)]
          ring
      rw [hmax]
    rw [integral_congr_ae (ae_of_all _ hpt)]
    exact hkey t
  have heq : μp = μm := Measure.ext_of_charFun hchar
  have hae : (fun x => ENNReal.ofReal (g x)) =ᵐ[γ d]
      fun x => ENNReal.ofReal (-(g x)) := by
    refine ae_eq_of_forall_setLIntegral_eq_of_sigmaFinite
      (hgm.measurable.ennreal_ofReal) (hgm.measurable.neg.ennreal_ofReal) ?_
    intro s hs _
    rw [← withDensity_apply _ hs, ← withDensity_apply _ hs, ← hμp, ← hμm, heq]
  have hzero : (⇑g : Vec d → ℝ) =ᵐ[γ d] 0 := by
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
  filter_upwards [hzero, Lp.coeFn_zero (E := ℝ) (p := 2) (μ := γ d)] with x h1 h2
  rw [h1, h2]

/-- Totality of the tensor Hermite system in positive dimension. -/
theorem tensorHermiteSpan_orthogonal_eq_bot {d : ℕ} (hd : 0 < d) :
    (tensorHermiteSpan d)ᗮ = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro g hg
  exact eq_zero_of_forall_integral_inner_pow_mul g
    (all_directional_moments_eq_zero hd g hg)

/-! ### Completeness of the chaos decomposition -/

/-- The finite low-chaos spaces increase with the cutoff. -/
lemma monotone_chaosLt (d : ℕ) : Monotone (chaosLt d) := by
  intro m n hmn
  rw [chaosLt, chaosLt, Submodule.span_le]
  rintro f ⟨α, hα, rfl⟩
  rw [Finset.mem_coe, mem_idxLt] at hα
  exact Submodule.subset_span ⟨α, by
    rw [Finset.mem_coe, mem_idxLt]
    omega, rfl⟩

/-- Every tensor Hermite lies in a sufficiently large finite low-chaos space. -/
lemma tensorHermiteSpan_le_iSup_chaosLt (d : ℕ) :
    tensorHermiteSpan d ≤ ⨆ n, chaosLt d n := by
  rw [tensorHermiteSpan, Submodule.span_le]
  rintro f ⟨α, rfl⟩
  refine (le_iSup (chaosLt d) (mdeg α + 1)) ?_
  rw [chaosLt]
  exact Submodule.subset_span ⟨α, by
    rw [Finset.mem_coe, mem_idxLt]
    omega, rfl⟩

/-- The increasing union of finite chaos spaces is dense. -/
lemma iSup_chaosLt_dense {d : ℕ} (hd : 0 < d) :
    ⊤ ≤ (⨆ n, chaosLt d n).topologicalClosure := by
  have hclosure : (tensorHermiteSpan d).topologicalClosure = ⊤ :=
    (Submodule.topologicalClosure_eq_top_iff).2
      (tensorHermiteSpan_orthogonal_eq_bot hd)
  calc
    ⊤ = (tensorHermiteSpan d).topologicalClosure := hclosure.symm
    _ ≤ (⨆ n, chaosLt d n).topologicalClosure :=
      Submodule.topologicalClosure_mono (tensorHermiteSpan_le_iSup_chaosLt d)

/-- The full Wiener-chaos expansion, for every `L²(γ^d)` class. -/
theorem chaos_hasSum_Pn {d : ℕ} (hd : 0 < d) (f : L2 d) :
    HasSum (fun n => Pn d n f) f := by
  have hV : OrthogonalFamily ℝ (fun n => chaos d n)
      (fun n => (chaos d n).subtypeₗᵢ) :=
    OrthogonalFamily.of_pairwise fun i j hij => chaos_isOrtho hij
  let pf : ∀ n, chaos d n :=
    fun n => ⟨Pn d n f, Submodule.starProjection_apply_mem _ _⟩
  have hsquares : Summable (fun n => ‖Pn d n f‖ ^ 2) :=
    summable_of_sum_le (fun _ => sq_nonneg _) (fun s => sum_Pn_normSq_le f s)
  have hs : Summable (fun n => Pn d n f) := by
    have hs' := (hV.summable_iff_norm_sq_summable pf).2 (by
      simpa [pf] using hsquares)
    simpa [pf] using hs'
  have hproj : Tendsto (fun n => Plt d n f) atTop (𝓝 f) := by
    simpa [Plt] using Submodule.starProjection_tendsto_self
      (chaosLt d) (monotone_chaosLt d) f (iSup_chaosLt_dense hd)
  have hpartial : Tendsto (fun n => ∑ k ∈ Finset.range n, Pn d k f)
      atTop (𝓝 f) := by
    simpa only [← Plt_eq_sum] using hproj
  have htsum : ∑' n, Pn d n f = f :=
    tendsto_nhds_unique hs.hasSum.tendsto_sum_nat hpartial
  simpa only [htsum] using hs.hasSum

/-- `Pge` fixes an individual chaos component at or above the cutoff. -/
lemma Pge_Pn_of_ge {d n₀ n : ℕ} (hn : n₀ ≤ n) (f : L2 d) :
    Pge d n₀ (Pn d n f) = Pn d n f := by
  rw [Pge_apply]
  have hz : Plt d n₀ (Pn d n f) = 0 := by
    refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero
      (Submodule.zero_mem _) ?_
    intro u hu
    rw [sub_zero, real_inner_comm]
    exact (chaosLt_isOrtho_chaos hn).inner_eq hu
      (Submodule.starProjection_apply_mem _ _)
  rw [hz, sub_zero]

/-- `Pge` kills an individual chaos component below the cutoff. -/
lemma Pge_Pn_of_lt {d n₀ n : ℕ} (hn : n < n₀) (f : L2 d) :
    Pge d n₀ (Pn d n f) = 0 := by
  have hmem : Pn d n f ∈ chaosLt d n₀ :=
    chaos_le_chaosLt hn (Submodule.starProjection_apply_mem _ _)
  rw [Pge_apply, Plt, Submodule.starProjection_eq_self_iff.mpr hmem, sub_self]

/-- The definition `Pge = I - P_{<n₀}` agrees with the paper's infinite tail
series for every `L²` function. -/
theorem Pge_hasSum {d : ℕ} (hd : 0 < d) (n₀ : ℕ) (f : L2 d) :
    HasSum (fun n => if n₀ ≤ n then Pn d n f else 0) (Pge d n₀ f) := by
  have hL := (chaos_hasSum_Pn hd f).mapL (Pge d n₀)
  refine hL.congr_fun fun n => ?_
  by_cases hn : n₀ ≤ n
  · rw [ite_eq_left hn, Pge_Pn_of_ge hn]
  · rw [ite_eq_right hn]
    push Not at hn
    rw [Pge_Pn_of_lt hn]

end

end GaussianDepthSeparation
