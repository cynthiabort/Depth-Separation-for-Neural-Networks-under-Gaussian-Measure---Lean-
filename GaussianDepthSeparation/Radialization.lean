/-
GaussianDepthSeparation §3 — Radialization of Ridge Functions (Proposition 3.2).

Key supporting facts, all grounded:
- transitivity of `O(d)` on the unit sphere (via `reflection_sub`);
- **Haar-orbit moments equal the Gaussian-sphere moments**
  (`∫_{O(d)} (Uv)^α dU = 𝔼[V^α]`), by the Fubini trick: the orbit average is
  constant over unit vectors, and averaging that constant against the
  normalized-Gaussian direction recovers `sphereMoment` — no
  uniqueness-of-invariant-measure theory needed;
- `Π_Rad h_n^v = ρ_n := ∑_{|α|=n} (n!/α!) 𝔼[V^α] H_α`;
- Proposition 3.2 from the Hermite expansion of `g` (totality) mapped through the
  continuous operator `Π_Rad ∘ (·)^v`.
-/
import GaussianDepthSeparation.RadialAverage
import GaussianDepthSeparation.Totality

namespace GaussianDepthSeparation

open MeasureTheory ProbabilityTheory Filter
open scoped RealInnerProductSpace ENNReal Nat Topology

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

noncomputable section

/-! ### Coordinate bounds and continuity -/

lemma abs_mpow_le_one {d : ℕ} {v : Vec d} (hv : ‖v‖ ≤ 1) (α : MIdx d) :
    |mpow v α| ≤ 1 := by
  rw [mpow, Finset.abs_prod]
  refine Finset.prod_le_one (fun i _ => abs_nonneg _) fun i _ => ?_
  rw [abs_pow]
  exact pow_le_one₀ (abs_nonneg _) ((abs_coord_le_norm v i).trans hv)

lemma continuous_mpow {d : ℕ} (α : MIdx d) : Continuous fun v : Vec d => mpow v α := by
  unfold mpow
  refine continuous_finsetProd _ fun i _ => ?_
  have hcoord : Continuous fun v : Vec d => v i := by fun_prop
  exact hcoord.pow _

/-- Unit vectors force positive dimension. -/
lemma dim_pos_of_unit {d : ℕ} {v : Vec d} (hv : ‖v‖ = 1) : 0 < d := by
  rcases Nat.eq_zero_or_pos d with rfl | h
  · exfalso
    have h0 : v = 0 := Subsingleton.elim _ _
    rw [h0, norm_zero] at hv
    norm_num at hv
  · exact h

/-- The Gaussian carries no mass at the origin (positive dimension). -/
lemma gaussD_singleton_zero {d : ℕ} (hd : 0 < d) : γ d ({0} : Set (Vec d)) = 0 := by
  set i : Fin d := ⟨0, hd⟩
  set v : Vec d := EuclideanSpace.single i (1 : ℝ) with hv
  have hunit : ‖v‖ = 1 := by
    rw [hv, PiLp.norm_single, norm_one]
  have hmp := measurePreserving_ridgeMap (v := v) hunit
  have hsub : ({0} : Set (Vec d)) ⊆ (ridgeMap v) ⁻¹' ({0} : Set ℝ) := by
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    simp [ridgeMap]
  refine le_antisymm ?_ bot_le
  calc γ d ({0} : Set (Vec d)) ≤ γ d ((ridgeMap v) ⁻¹' ({0} : Set ℝ)) :=
        measure_mono hsub
    _ = γ₁ ({0} : Set ℝ) := by
        rw [← hmp.map_eq]
        exact (Measure.map_apply hmp.measurable (measurableSet_singleton 0)).symm
    _ = 0 := by
        have : NullSingletonClass γ₁ := by
          rw [γ₁]
          exact nullSingletonClass_gaussianReal one_ne_zero
        exact measure_singleton 0

/-! ### Transitivity of `O(d)` on the unit sphere -/

theorem exists_actMap_eq {d : ℕ} {v w : Vec d} (hv : ‖v‖ = 1) (hw : ‖w‖ = 1) :
    ∃ Q : Od d, actMap Q v = w := by
  refine ⟨Unitary.linearIsometryEquiv.symm ((ℝ ∙ (v - w))ᗮ.reflection), ?_⟩
  show ((Unitary.linearIsometryEquiv.symm ((ℝ ∙ (v - w))ᗮ.reflection) : Od d) :
    Vec d →L[ℝ] Vec d) v = w
  rw [Unitary.coe_symm_linearIsometryEquiv_apply]
  exact Submodule.reflection_sub (by rw [hv, hw])

/-! ### Haar-orbit moments = Gaussian-sphere moments -/

lemma sphereMoment_eq_integral (d : ℕ) (α : MIdx d) :
    sphereMoment d α = ∫ x, mpow (‖x‖⁻¹ • x) α ∂(γ d) := by
  rw [sphereMoment, sphereUnif, integral_map]
  · exact (Measurable.aemeasurable (by fun_prop))
  · exact (continuous_mpow α).aestronglyMeasurable

/-- Bounded–continuous functions on the compact group are integrable. -/
lemma integrable_of_bounded_continuous_haar {d : ℕ} {f : Od d → ℝ} (hf : Continuous f)
    (C : ℝ) (hC : ∀ U, |f U| ≤ C) : Integrable f (haarOd d) :=
  ⟨hf.aestronglyMeasurable,
    HasFiniteIntegral.of_bounded (C := C) (ae_of_all _ fun U => by
      rw [Real.norm_eq_abs]; exact hC U)⟩

/-- The orbit average is the same for all unit starting vectors. -/
lemma orbit_avg_const {d : ℕ} (α : MIdx d) {v w : Vec d} (hv : ‖v‖ = 1)
    (hw : ‖w‖ = 1) :
    ∫ U, mpow (actMap U w) α ∂(haarOd d) = ∫ U, mpow (actMap U v) α ∂(haarOd d) := by
  obtain ⟨Q, hQ⟩ := exists_actMap_eq hv hw
  have h1 : ∀ U : Od d, mpow (actMap U w) α = mpow (actMap (U * Q) v) α := by
    intro U
    rw [← hQ, actMap_actMap]
  rw [integral_congr_ae (ae_of_all _ h1)]
  exact (measurePreserving_mul_right (haarOd d) Q).integral_comp
    (Homeomorph.mulRight Q).measurableEmbedding (fun W => mpow (actMap W v) α)

/-- **Haar-orbit moments equal the Gaussian-sphere moments** (Fubini trick). -/
theorem haar_orbit_moment {d : ℕ} (α : MIdx d) {v : Vec d} (hv : ‖v‖ = 1) :
    ∫ U, mpow (actMap U v) α ∂(haarOd d) = sphereMoment d α := by
  have hd : 0 < d := dim_pos_of_unit hv
  -- the doubly-averaged quantity
  set F : Od d × Vec d → ℝ := fun p => mpow (actMap p.1 (‖p.2‖⁻¹ • p.2)) α with hF
  have hFmeas : AEStronglyMeasurable F ((haarOd d).prod (γ d)) := by
    have hev : Continuous fun p : Od d × Vec d => actMap p.1 p.2 := by
      have h1 : Continuous fun p : (Vec d →L[ℝ] Vec d) × Vec d => p.1 p.2 :=
        isBoundedBilinearMap_apply.continuous
      exact h1.comp (Continuous.prodMk
        (continuous_subtype_val.comp continuous_fst) continuous_snd)
    have hn : Measurable fun p : Od d × Vec d => (p.1, (‖p.2‖⁻¹ • p.2 : Vec d)) := by
      fun_prop
    exact ((continuous_mpow α).comp hev).measurable.comp hn |>.aestronglyMeasurable
  have hFbdd : ∀ p : Od d × Vec d, |F p| ≤ 1 := by
    intro p
    refine abs_mpow_le_one ?_ α
    rw [actMap_norm]
    rcases eq_or_ne p.2 0 with h0 | h0
    · simp [h0]
    · rw [norm_smul, norm_inv, norm_norm,
        inv_mul_cancel₀ (norm_ne_zero_iff.mpr h0)]
  have hFint : Integrable F ((haarOd d).prod (γ d)) :=
    ⟨hFmeas, HasFiniteIntegral.of_bounded (C := 1) (ae_of_all _ fun p => by
      rw [Real.norm_eq_abs]; exact hFbdd p)⟩
  -- inner-U-first evaluation
  have hinner : ∫ x, ∫ U, F (U, x) ∂(haarOd d) ∂(γ d)
      = ∫ U, mpow (actMap U v) α ∂(haarOd d) := by
    have hae : ∀ᵐ x ∂(γ d), ∫ U, F (U, x) ∂(haarOd d)
        = ∫ U, mpow (actMap U v) α ∂(haarOd d) := by
      have hne : ∀ᵐ x ∂(γ d), x ≠ 0 := by
        have hset : {x : Vec d | ¬ x ≠ 0} = ({0} : Set (Vec d)) := by
          ext x; simp
        rw [ae_iff, hset]
        exact gaussD_singleton_zero hd
      filter_upwards [hne] with x hx
      have hxu : ‖(‖x‖⁻¹ • x : Vec d)‖ = 1 := norm_smul_inv_norm hx
      exact orbit_avg_const α hv hxu
    rw [integral_congr_ae hae, integral_const]
    simp
  -- inner-x-first evaluation
  have houter : ∫ U, ∫ x, F (U, x) ∂(γ d) ∂(haarOd d) = sphereMoment d α := by
    have hUeq : ∀ U : Od d, ∫ x, F (U, x) ∂(γ d) = sphereMoment d α := by
      intro U
      have hptwise : ∀ x : Vec d,
          F (U, x) = mpow (‖actMap U x‖⁻¹ • actMap U x) α := by
        intro x
        show mpow (actMap U (‖x‖⁻¹ • x)) α = mpow (‖actMap U x‖⁻¹ • actMap U x) α
        rw [actMap_norm]
        congr 1
        show (U : Vec d →L[ℝ] Vec d) (‖x‖⁻¹ • x) = ‖x‖⁻¹ • (U : Vec d →L[ℝ] Vec d) x
        exact map_smul _ _ _
      have hnormalize : Measurable fun y : Vec d => (‖y‖⁻¹ • y : Vec d) := by fun_prop
      calc ∫ x, F (U, x) ∂(γ d)
          = ∫ x, mpow (‖actMap U x‖⁻¹ • actMap U x) α ∂(γ d) :=
            integral_congr_ae (ae_of_all _ hptwise)
        _ = ∫ y, mpow (‖y‖⁻¹ • y) α ∂(γ d) := by
            conv_rhs => rw [← (measurePreserving_actMap U).map_eq]
            have hasm : AEStronglyMeasurable (fun y : Vec d => mpow (‖y‖⁻¹ • y) α)
                (Measure.map (actMap U) (γ d)) :=
              ((continuous_mpow α).measurable.comp hnormalize).aestronglyMeasurable
            rw [integral_map (measurePreserving_actMap U).aemeasurable hasm]
        _ = sphereMoment d α := (sphereMoment_eq_integral d α).symm
    rw [integral_congr_ae (ae_of_all _ hUeq), integral_const]
    simp
  -- Fubini
  have hswap := MeasureTheory.integral_integral_swap
    (f := fun U x => F (U, x)) (by exact hFint)
  rw [← hinner, ← hswap, houter]

/-! ### `Π_Rad` of a ridge Hermite: the averaged expansion `ρ_n` -/

/-- `ρ_n = ∑_{|α|=n} (n!/α!)·𝔼[V^α]·H_α`. -/
def rho (d n : ℕ) : L2 d :=
  ∑ α ∈ idxOf d n, (((n ! : ℝ) / (mfact α : ℝ)) * sphereMoment d α) • HL2 α

theorem radAvg_ridgeHermite {d : ℕ} (n : ℕ) (v : Vec d) (hv : ‖v‖ = 1) :
    radAvgFun (ridgeHermite n v hv) = rho d n := by
  have hint : ∀ α ∈ idxOf d n, Integrable
      (fun U : Od d => ((n ! : ℝ) / (mfact α : ℝ)) * mpow (actMap U⁻¹ v) α)
      (haarOd d) := by
    intro α _
    have hinv_cont : Continuous fun U : Od d => U⁻¹ := continuous_inv
    refine integrable_of_bounded_continuous_haar
      (continuous_const.mul ((continuous_mpow α).comp
        ((continuous_actMap_eval v).comp hinv_cont)))
      (|(n ! : ℝ) / (mfact α : ℝ)|) fun U => ?_
    rw [abs_mul]
    have hb := abs_mpow_le_one (le_of_eq (actMap_unit U⁻¹ hv)) α
    calc |(n ! : ℝ) / (mfact α : ℝ)| * |mpow (actMap U⁻¹ v) α|
        ≤ |(n ! : ℝ) / (mfact α : ℝ)| * 1 := by
          exact mul_le_mul_of_nonneg_left hb (abs_nonneg _)
      _ = |(n ! : ℝ) / (mfact α : ℝ)| := mul_one _
  have hrw : (fun U : Od d => act U (ridgeHermite n v hv))
      = fun U => ∑ α ∈ idxOf d n,
          (((n ! : ℝ) / (mfact α : ℝ)) * mpow (actMap U⁻¹ v) α) • HL2 α := by
    funext U
    rw [act_ridgeHermite, ridgeHermite_eq_sum]
  rw [radAvgFun, hrw, integral_finsetSum _
    (fun α hα => (hint α hα).smul_const (HL2 α))]
  rw [rho]
  refine Finset.sum_congr rfl fun α hα => ?_
  rw [integral_smul_const]
  congr 1
  rw [integral_const_mul]
  congr 1
  have hinv : ∫ U, mpow (actMap U⁻¹ v) α ∂(haarOd d)
      = ∫ U, mpow (actMap U v) α ∂(haarOd d) := by
    have := haarOd_invInvariant d
    exact MeasureTheory.integral_inv_eq_self (fun W => mpow (actMap W v) α) (haarOd d)
  rw [hinv, haar_orbit_moment α hv]

/-! ### Proposition 3.2 -/

/-- `Π_Rad` as a continuous linear map. -/
def radAvgCLM (d : ℕ) : L2 d →L[ℝ] L2 d :=
  LinearMap.mkContinuous
    { toFun := radAvgFun
      map_add' := radAvgFun_add
      map_smul' := radAvgFun_smul }
    1 (fun f => by simpa using radAvgFun_norm_le f)

/- LaTeX — `main.tex`, Proposition 3.2 (Hermite expansion after radial averaging):
"Let $V\sim\mathrm{Unif}(S^{d-1})$, $g\in L^2(\gamma)$, and $v\in S^{d-1}$. Then
$$\Pi_{\mathrm{Rad}}(g^v) = \sum_{n=0}^\infty\sum_{|\alpha|=n}
\frac{\langle g, h_n\rangle_{L^2(\gamma)}}{\alpha!}\mathbb{E}[V^\alpha]\,H_\alpha.$$
The identity holds in $L^2(\gamma^d)$, with the series converging in that norm."
-/
/-- **Proposition 3.2 (Hermite expansion after radial averaging).** -/
theorem radAvg_ridge_expansion {d : ℕ} (v : Vec d) (hv : ‖v‖ = 1) (g : L2R) :
    HasSum
      (fun n : ℕ => ∑ α ∈ idxOf d n,
        ((⟪g, hermiteL2 n⟫ / (mfact α : ℝ)) * sphereMoment d α) • HL2 α)
      (radAvgFun (ridge v hv g)) := by
  have hL := (hermite_hasSum g).mapL
    ((radAvgCLM d).comp (ridge v hv).toContinuousLinearMap)
  have hterm : ∀ n : ℕ,
      ((radAvgCLM d).comp (ridge v hv).toContinuousLinearMap)
          ((⟪g, hermiteL2 n⟫ / (n ! : ℝ)) • hermiteL2 n)
        = ∑ α ∈ idxOf d n,
            ((⟪g, hermiteL2 n⟫ / (mfact α : ℝ)) * sphereMoment d α) • HL2 α := by
    intro n
    rw [map_smul]
    have hcomp : ((radAvgCLM d).comp (ridge v hv).toContinuousLinearMap) (hermiteL2 n)
        = radAvgFun (ridgeHermite n v hv) := rfl
    rw [hcomp, radAvg_ridgeHermite, rho, Finset.smul_sum]
    refine Finset.sum_congr rfl fun α hα => ?_
    rw [smul_smul]
    congr 1
    have hne : (n ! : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
    field_simp
  have hfun : (fun n : ℕ => ∑ α ∈ idxOf d n,
      ((⟪g, hermiteL2 n⟫ / (mfact α : ℝ)) * sphereMoment d α) • HL2 α)
      = fun n => ((radAvgCLM d).comp (ridge v hv).toContinuousLinearMap)
          ((⟪g, hermiteL2 n⟫ / (n ! : ℝ)) • hermiteL2 n) :=
    funext fun n => (hterm n).symm
  rw [hfun]
  have hval : ((radAvgCLM d).comp (ridge v hv).toContinuousLinearMap) g
      = radAvgFun (ridge v hv g) := rfl
  rw [← hval]
  exact hL

end

end GaussianDepthSeparation
