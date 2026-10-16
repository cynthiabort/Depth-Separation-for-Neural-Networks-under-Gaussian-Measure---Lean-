/-
GaussianDepthSeparation §3 — the radial averaging operator Π_Rad (Proposition 3.1).

The Haar probability measure on the compact group `O(d)` and the Bochner
average `Π_Rad f = ∫_{O(d)} T_U f dU`.  Everything grounded:
- compactness of `O(d)` (closed + bounded in the finite-dimensional operator
  algebra, Heine–Borel);
- Haar probability measure via `MeasureTheory.Measure.haarMeasure`;
- right- and inversion-invariance from *uniqueness* of Haar measure
  (`O(d)` is noncommutative, so Mathlib's ready-made instances don't apply);
- strong continuity of `U ↦ T_U f` (dominated convergence on the dense
  bounded-continuous class + the ε/3 isometry argument);
- Proposition 3.1: `Π_Rad` is the orthogonal projection onto the radial
  subspace and commutes with every chaos projection (via Lemma 2.2).
-/
import GaussianDepthSeparation.Chaos
import Mathlib.Topology.Algebra.Star.Unitary
import Mathlib.MeasureTheory.Function.ContinuousMapDense

namespace GaussianDepthSeparation

open MeasureTheory ProbabilityTheory Filter
open scoped RealInnerProductSpace ENNReal NNReal Topology

noncomputable section

/-! ### Group-action plumbing -/

lemma act_mul {d : ℕ} (U V : Od d) (f : L2 d) :
    act V (act U f) = act (U * V) f :=
  (Lp.compMeasurePreserving_comp_apply f (measurePreserving_actMap U)
    (measurePreserving_actMap V)).symm

lemma act_one {d : ℕ} (f : L2 d) : act (1 : Od d) f = f :=
  Lp.compMeasurePreserving_id_apply f

@[simp] lemma act_act_inv {d : ℕ} (U : Od d) (f : L2 d) :
    act U (act U⁻¹ f) = f := by
  rw [act_mul, inv_mul_cancel, act_one]

/-! ### Compactness of `O(d)` and the Haar probability measure -/

instance (d : ℕ) : CompactSpace (Od d) := by
  have hc : IsCompact (unitary (Vec d →L[ℝ] Vec d) : Set (Vec d →L[ℝ] Vec d)) := by
    refine Metric.isCompact_of_isClosed_isBounded isClosed_unitary ?_
    refine (Metric.isBounded_closedBall (x := (0 : Vec d →L[ℝ] Vec d)) (r := 1)).subset ?_
    intro U hU
    rw [Metric.mem_closedBall, dist_zero_right]
    exact ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => by
      rw [ContinuousLinearMap.norm_map_of_mem_unitary hU, one_mul]
  exact isCompact_iff_compactSpace.mp hc

/-- The full group as a positive compact (for Haar normalization). -/
def univCompacts (d : ℕ) : TopologicalSpace.PositiveCompacts (Od d) where
  carrier := Set.univ
  isCompact' := isCompact_univ
  interior_nonempty' := by
    rw [interior_univ]
    exact ⟨1, trivial⟩

/-- The Haar probability measure on `O(d)`. -/
def haarOd (d : ℕ) : Measure (Od d) := Measure.haarMeasure (univCompacts d)

instance haarOd_prob (d : ℕ) : IsProbabilityMeasure (haarOd d) :=
  ⟨by simpa [haarOd, univCompacts] using
    Measure.haarMeasure_self (K₀ := univCompacts d)⟩

instance haarOd_leftInvariant (d : ℕ) : (haarOd d).IsMulLeftInvariant := by
  rw [haarOd]; infer_instance

instance haarOd_regular (d : ℕ) : (haarOd d).Regular := by
  rw [haarOd]; infer_instance

instance haarOd_isHaar (d : ℕ) : (haarOd d).IsHaarMeasure := by
  rw [haarOd]; infer_instance

/-- Right invariance of Haar measure on the compact group `O(d)`, from
uniqueness of left Haar measure. -/
theorem haarOd_mulRightInvariant (d : ℕ) : (haarOd d).IsMulRightInvariant := by
  constructor
  intro g
  set ν := (haarOd d).map (· * g) with hν
  have : IsProbabilityMeasure ν :=
    Measure.isProbabilityMeasure_map (measurable_mul_const g).aemeasurable
  have : ν.IsMulLeftInvariant := by
    constructor
    intro h
    rw [hν, Measure.map_map (measurable_const_mul h) (measurable_mul_const g)]
    have hcomm : ((h * ·) ∘ (· * g)) = ((· * g) ∘ (h * ·)) := by
      funext x
      simp [mul_assoc]
    rw [hcomm, ← Measure.map_map (measurable_mul_const g) (measurable_const_mul h),
      MeasureTheory.map_mul_left_eq_self]
  have : ν.Regular := by
    have h : ν = Measure.map (Homeomorph.mulRight g) (haarOd d) := by rw [hν]; rfl
    rw [h]
    exact Measure.Regular.map (Homeomorph.mulRight g)
  have huniq : ν = (Measure.haarScalarFactor ν (haarOd d)) • (haarOd d) :=
    Measure.isMulLeftInvariant_eq_smul_of_regular ν (haarOd d)
  have h1 : ν Set.univ = 1 := measure_univ
  rw [huniq, Measure.smul_apply, measure_univ] at h1
  have hc1 : ν.haarScalarFactor (haarOd d) = 1 := by
    simpa [ENNReal.smul_def] using h1
  rw [huniq, hc1, one_smul]

attribute [instance] haarOd_mulRightInvariant

/-- Inversion invariance of Haar measure on `O(d)`. -/
theorem haarOd_invInvariant (d : ℕ) : (haarOd d).IsInvInvariant := by
  constructor
  set ν := (haarOd d).inv with hν
  have : IsProbabilityMeasure ν :=
    Measure.isProbabilityMeasure_map measurable_inv.aemeasurable
  have : ν.IsMulLeftInvariant := by
    rw [hν]; infer_instance
  have : ν.Regular := by
    have h : ν = Measure.map (Homeomorph.inv (Od d)) (haarOd d) := by rw [hν]; rfl
    rw [h]
    exact Measure.Regular.map (Homeomorph.inv (Od d))
  have huniq : ν = (Measure.haarScalarFactor ν (haarOd d)) • (haarOd d) :=
    Measure.isMulLeftInvariant_eq_smul_of_regular ν (haarOd d)
  have h1 : ν Set.univ = 1 := measure_univ
  rw [huniq, Measure.smul_apply, measure_univ] at h1
  have hc1 : ν.haarScalarFactor (haarOd d) = 1 := by
    simpa [ENNReal.smul_def] using h1
  rw [huniq, hc1, one_smul]

attribute [instance] haarOd_invInvariant

/-! ### Strong continuity of the action -/

/-- Evaluation `U ↦ Ux` is continuous on `O(d)`. -/
lemma continuous_actMap_eval {d : ℕ} (x : Vec d) :
    Continuous fun U : Od d => actMap U x :=
  ((ContinuousLinearMap.apply ℝ (Vec d) x).continuous).comp continuous_subtype_val

/-- Core convergence: for a bounded continuous representative, `T_{W_n} ĝ → ĝ`
in `L²` as `W_n → 1` (dominated convergence). -/
lemma tendsto_act_one_bcf {d : ℕ} (g : BoundedContinuousFunction (Vec d) ℝ)
    (ĝ : L2 d) (hĝ : ⇑ĝ =ᵐ[γ d] ⇑g) {W : ℕ → Od d}
    (hW : Tendsto W atTop (𝓝 1)) :
    Tendsto (fun n => ‖act (W n) ĝ - ĝ‖) atTop (𝓝 0) := by
  have hnorm : ∀ n, ‖act (W n) ĝ - ĝ‖ ^ 2
      = ∫ x, (g (actMap (W n) x) - g x) ^ 2 ∂(γ d) := by
    intro n
    rw [norm_sq_eq_integral]
    refine integral_congr_ae ?_
    have hcomp : (⇑ĝ) ∘ actMap (W n) =ᵐ[γ d] (⇑g) ∘ actMap (W n) := by
      refine MeasureTheory.ae_eq_comp (measurePreserving_actMap (W n)).aemeasurable ?_
      rw [(measurePreserving_actMap (W n)).map_eq]
      exact hĝ
    filter_upwards [Lp.coeFn_sub (act (W n) ĝ) ĝ, act_coeFn (W n) ĝ, hcomp, hĝ]
      with x h1 h2 h3 h4
    rw [h1]
    simp only [Pi.sub_apply]
    rw [h2, show (⇑ĝ ∘ actMap (W n)) x = (⇑g ∘ actMap (W n)) x from h3, h4]
    rfl
  have hsq : Tendsto (fun n => ∫ x, (g (actMap (W n) x) - g x) ^ 2 ∂(γ d))
      atTop (𝓝 0) := by
    have h0 : (0 : ℝ) = ∫ _ : Vec d, (0 : ℝ) ∂(γ d) := by simp
    rw [h0]
    refine tendsto_integral_of_dominated_convergence (fun _ => (2 * ‖g‖) ^ 2)
      (fun n => ?_) (integrable_const _) (fun n => ?_) ?_
    · have hc : Continuous fun x : Vec d => g (actMap (W n) x) - g x :=
        (g.continuous.comp ((W n : Vec d →L[ℝ] Vec d)).continuous).sub g.continuous
      exact (hc.pow 2).aestronglyMeasurable
    · refine ae_of_all _ fun x => ?_
      rw [Real.norm_eq_abs, abs_pow, sq_abs]
      have h1 : |g (actMap (W n) x) - g x| ≤ 2 * ‖g‖ := by
        have ha := g.norm_coe_le_norm (actMap (W n) x)
        have hb := g.norm_coe_le_norm x
        rw [Real.norm_eq_abs] at ha hb
        calc |g (actMap (W n) x) - g x|
            ≤ |g (actMap (W n) x)| + |g x| := abs_sub _ _
          _ ≤ ‖g‖ + ‖g‖ := add_le_add ha hb
          _ = 2 * ‖g‖ := by ring
      calc (g (actMap (W n) x) - g x) ^ 2
          = |g (actMap (W n) x) - g x| ^ 2 := (sq_abs _).symm
        _ ≤ (2 * ‖g‖) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h1 2
    · refine ae_of_all _ fun x => ?_
      have hx : Tendsto (fun n => actMap (W n) x) atTop (𝓝 x) := by
        have hev := (continuous_actMap_eval (d := d) x).continuousAt (x := (1 : Od d))
        change Tendsto ((fun U : Od d => actMap U x) ∘ W) atTop (𝓝 x)
        exact hev.tendsto.comp hW
      have hgx : Tendsto (fun n => g (actMap (W n) x) - g x) atTop (𝓝 0) := by
        have h := ((g.continuous.tendsto x).comp hx).sub
          (tendsto_const_nhds (x := g x))
        simpa using h
      have h := hgx.pow 2
      simpa using h
  have hsq' : Tendsto (fun n => ‖act (W n) ĝ - ĝ‖ ^ 2) atTop (𝓝 0) := by
    have hfe : (fun n => ‖act (W n) ĝ - ĝ‖ ^ 2)
        = fun n => ∫ x, (g (actMap (W n) x) - g x) ^ 2 ∂(γ d) := funext hnorm
    rw [hfe]
    exact hsq
  have h2 := (Real.continuous_sqrt.tendsto 0).comp hsq'
  simp only [Function.comp_def, Real.sqrt_zero] at h2
  refine h2.congr fun n => ?_
  rw [Real.sqrt_sq (norm_nonneg _)]

/-- Strong continuity at the identity, general `f` (ε/3 argument). -/
lemma tendsto_act_one {d : ℕ} (f : L2 d) {W : ℕ → Od d}
    (hW : Tendsto W atTop (𝓝 1)) :
    Tendsto (fun n => act (W n) f) atTop (𝓝 f) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨g, hgnorm, hgmem⟩ := (Lp.memLp f).exists_boundedContinuous_eLpNorm_sub_le
    (by norm_num : (2 : ℝ≥0∞) ≠ ∞)
    (ε := ENNReal.ofReal (ε / 3)) (by simp [ENNReal.ofReal_eq_zero]; positivity)
  set ĝ : L2 d := hgmem.toLp with hĝdef
  have hfg : ‖f - ĝ‖ ≤ ε / 3 := by
    rw [Lp.norm_def]
    have hcongr : eLpNorm (⇑(f - ĝ)) 2 (γ d) = eLpNorm (⇑f - ⇑g) 2 (γ d) := by
      apply eLpNorm_congr_ae
      filter_upwards [Lp.coeFn_sub f ĝ, hgmem.coeFn_toLp] with x h1 h2
      rw [h1]
      simp only [Pi.sub_apply]
      rw [h2]
    rw [hcongr]
    calc (eLpNorm (⇑f - ⇑g) 2 (γ d)).toReal
        ≤ (ENNReal.ofReal (ε / 3)).toReal :=
          ENNReal.toReal_mono ENNReal.ofReal_ne_top hgnorm
      _ = ε / 3 := ENNReal.toReal_ofReal (by positivity)
  have hmid := tendsto_act_one_bcf g ĝ hgmem.coeFn_toLp hW
  have hmid' : ∀ᶠ n in atTop, ‖act (W n) ĝ - ĝ‖ < ε / 3 :=
    hmid.eventually_lt_const (by positivity)
  obtain ⟨N, hN⟩ := eventually_atTop.mp hmid'
  refine ⟨N, fun n hn => ?_⟩
  have hiso : dist (act (W n) f) (act (W n) ĝ) = ‖f - ĝ‖ := by
    rw [dist_eq_norm, ← map_sub, act_norm]
  calc dist (act (W n) f) f
      ≤ dist (act (W n) f) (act (W n) ĝ) + dist (act (W n) ĝ) ĝ + dist ĝ f :=
        dist_triangle4 _ _ _ _
    _ < ε / 3 + ε / 3 + ε / 3 := by
        have h1 : dist (act (W n) f) (act (W n) ĝ) ≤ ε / 3 := by rw [hiso]; exact hfg
        have h2 : dist (act (W n) ĝ) ĝ < ε / 3 := by
          rw [dist_eq_norm]; exact hN n hn
        have h3 : dist ĝ f ≤ ε / 3 := by
          rw [dist_comm, dist_eq_norm]; exact hfg
        have := add_lt_add_of_lt_of_le (add_lt_add_of_le_of_lt h1 h2) h3
        linarith
    _ = ε := by ring

/-- Strong continuity of the action: `U ↦ T_U f` is continuous. -/
lemma continuous_act_apply {d : ℕ} (f : L2 d) :
    Continuous fun U : Od d => act U f := by
  rw [continuous_iff_seqContinuous]
  intro V U₀ hV
  have hW : Tendsto (fun n => V n * U₀⁻¹) atTop (𝓝 1) := by
    have h := hV.mul (tendsto_const_nhds (x := U₀⁻¹))
    simpa using h
  have hkey := tendsto_act_one f hW
  have hcomp : Tendsto (fun n => act U₀ (act (V n * U₀⁻¹) f)) atTop
      (𝓝 (act U₀ f)) := ((act U₀).continuous.tendsto f).comp hkey
  refine hcomp.congr fun n => ?_
  show act U₀ (act (V n * U₀⁻¹) f) = act (V n) f
  rw [act_mul, inv_mul_cancel_right]

/-! ### The radial average Π_Rad -/

lemma integrable_act {d : ℕ} (f : L2 d) :
    Integrable (fun U : Od d => act U f) (haarOd d) := by
  refine ⟨(continuous_act_apply f).aestronglyMeasurable, ?_⟩
  refine HasFiniteIntegral.of_bounded (C := ‖f‖) (ae_of_all _ fun U => ?_)
  rw [act_norm]

/- LaTeX — `main.tex` §3: "Define
$$\Pi_{\mathrm{Rad}}f(x) = \int_{O(d)} f(Ux)\,dU,$$
where $dU$ is Haar probability measure on $O(d)$."
-/
/-- The radial average `Π_Rad f = ∫_{O(d)} T_U f dU` (Bochner, in `L²(γ^d)`). -/
def radAvgFun {d : ℕ} (f : L2 d) : L2 d := ∫ U, act U f ∂(haarOd d)

lemma radAvgFun_add {d : ℕ} (f g : L2 d) :
    radAvgFun (f + g) = radAvgFun f + radAvgFun g := by
  have h : (fun U : Od d => act U (f + g)) = fun U => act U f + act U g :=
    funext fun U => map_add _ f g
  rw [radAvgFun, h, integral_add (integrable_act f) (integrable_act g)]
  rfl

lemma radAvgFun_smul {d : ℕ} (c : ℝ) (f : L2 d) :
    radAvgFun (c • f) = c • radAvgFun f := by
  have h : (fun U : Od d => act U (c • f)) = fun U => c • act U f :=
    funext fun U => map_smul _ c f
  rw [radAvgFun, h, integral_smul]
  rfl

/-- `Π_Rad` is an `L²` contraction ("an average of unitary operators"). -/
lemma radAvgFun_norm_le {d : ℕ} (f : L2 d) : ‖radAvgFun f‖ ≤ ‖f‖ := by
  refine (norm_integral_le_integral_norm _).trans ?_
  simp only [act_norm]
  simp

/-- `Π_Rad f` is invariant under every rotation (Haar right-invariance). -/
lemma act_radAvgFun {d : ℕ} (V : Od d) (f : L2 d) :
    act V (radAvgFun f) = radAvgFun f := by
  rw [radAvgFun]
  have h1 : act V (∫ U, act U f ∂(haarOd d))
      = ∫ U, act V (act U f) ∂(haarOd d) :=
    ((act V).toContinuousLinearMap.integral_comp_comm (integrable_act f)).symm
  rw [h1, integral_congr_ae (ae_of_all _ fun U => act_mul U V f)]
  exact (measurePreserving_mul_right (haarOd d) V).integral_comp
    (Homeomorph.mulRight V).measurableEmbedding (fun W => act W f)

lemma isRadial_radAvgFun {d : ℕ} (f : L2 d) : IsRadial (radAvgFun f) :=
  fun V => act_radAvgFun V f

/-- `Π_Rad` fixes radial functions. -/
lemma radAvgFun_of_isRadial {d : ℕ} {f : L2 d} (hf : IsRadial f) :
    radAvgFun f = f := by
  rw [radAvgFun, integral_congr_ae (ae_of_all _ fun U => hf U)]
  simp

/-- `Π_Rad` is self-adjoint (Haar inversion-invariance). -/
lemma inner_radAvgFun {d : ℕ} (f g : L2 d) :
    ⟪radAvgFun f, g⟫ = ⟪f, radAvgFun g⟫ := by
  have h1 : ⟪radAvgFun f, g⟫ = ∫ U, ⟪act U f, g⟫ ∂(haarOd d) := by
    rw [radAvgFun, real_inner_comm, ← integral_inner (integrable_act f) g]
    exact integral_congr_ae (ae_of_all _ fun U => real_inner_comm _ _)
  have h2 : ∀ U : Od d, ⟪act U f, g⟫ = ⟪f, act U⁻¹ g⟫ := by
    intro U
    calc ⟪act U f, g⟫ = ⟪act U f, act U (act U⁻¹ g)⟫ := by rw [act_act_inv]
      _ = ⟪f, act U⁻¹ g⟫ := (act U).inner_map_map f (act U⁻¹ g)
  have h3 : ∫ U, ⟪f, act U⁻¹ g⟫ ∂(haarOd d) = ∫ U, ⟪f, act U g⟫ ∂(haarOd d) := by
    have := haarOd_invInvariant d
    exact MeasureTheory.integral_inv_eq_self (fun U => ⟪f, act U g⟫) (haarOd d)
  have h4 : ⟪f, radAvgFun g⟫ = ∫ U, ⟪f, act U g⟫ ∂(haarOd d) := by
    rw [radAvgFun, ← integral_inner (integrable_act g) f]
  rw [h1, integral_congr_ae (ae_of_all _ h2), h3, h4]

/- LaTeX — `main.tex` §3: "Note that $\Pi_{\mathrm{Rad}}$ is the orthogonal
projection of $L^2(\gamma^d)$ onto the subspace of radial functions." -/
/-- Radial averaging is the orthogonal projection onto radial functions. -/
theorem radAvg_eq_starProjection (d : ℕ) (f : L2 d) :
    radAvgFun f = (radialSub d).starProjection f := by
  symm
  refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero
    (isRadial_radAvgFun f) fun w hw => ?_
  rw [inner_sub_left]
  have h1 : ⟪radAvgFun f, w⟫ = ⟪f, w⟫ := by
    rw [inner_radAvgFun, radAvgFun_of_isRadial hw]
  rw [h1, sub_self]

/- LaTeX — `main.tex`, Proposition 3.1: "For every $n\in\mathbb N$, it holds that
$$P_n\Pi_{\mathrm{Rad}} = \Pi_{\mathrm{Rad}}P_n.$$" -/
/-- Lemma 2.2 implies that each chaos projection preserves the radial subspace. -/
lemma isRadial_Pn {d : ℕ} {f : L2 d} (hf : IsRadial f) (n : ℕ) :
    IsRadial (Pn d n f) := by
  intro U
  rw [← Pn_comp_rotation, hf U]

/-- Self-adjointness then implies preservation of the orthogonal complement,
as in the proof of Proposition 3.1. -/
lemma Pn_mem_radial_orthogonal {d n : ℕ} {f : L2 d}
    (hf : f ∈ (radialSub d)ᗮ) : Pn d n f ∈ (radialSub d)ᗮ := by
  rw [Submodule.mem_orthogonal] at hf ⊢
  intro g hg
  change ⟪g, (chaos d n).starProjection f⟫ = 0
  rw [← Submodule.inner_starProjection_left_eq_right]
  exact hf (Pn d n g) (isRadial_Pn hg n)

/-- **Proposition 3.1.** Preserve the radial subspace and its orthogonal
complement, then use the orthogonal decomposition of `f`. -/
theorem radAvg_comm_Pn (d n : ℕ) (f : L2 d) :
    Pn d n (radAvgFun f) = radAvgFun (Pn d n f) := by
  rw [radAvg_eq_starProjection, radAvg_eq_starProjection]
  symm
  apply Submodule.eq_starProjection_of_mem_orthogonal
  · exact isRadial_Pn ((radialSub d).starProjection_apply_mem f) n
  · rw [← map_sub]
    exact Pn_mem_radial_orthogonal
      (Submodule.sub_starProjection_mem_orthogonal (K := radialSub d) f)

end

end GaussianDepthSeparation
