/-
GaussianDepthSeparation §4 — The Ridge Correlation Bound (Proposition 4.1).

Mechanism (all grounded):
- `P_n(g^v) = (⟨g,h_n⟩/n!)·h_n^v`  (1-D Hermite expansion + chaos orthogonality);
- for radial `R`: `⟨R, h_n^v⟩ = ⟨R, ρ_n⟩` where `ρ_n = Π_Rad h_n^v`
  (self-adjointness of `Π_Rad`);
- `‖ρ_n‖² = n!·K_n` via `⟨h_n^v, ρ_n⟩ = n!·𝔼_W[⟨v,W⟩ⁿ] = n!·K_n`
  (multinomial + isometry change of variables in the sphere moments);
- Cauchy–Schwarz.
-/
import GaussianDepthSeparation.Moments

namespace GaussianDepthSeparation

open MeasureTheory ProbabilityTheory Filter
open scoped RealInnerProductSpace ENNReal Nat Topology

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

noncomputable section

/-! ### Chaos orthogonality and the projection of a ridge function -/

lemma ridgeHermite_mem_chaos {d : ℕ} (n : ℕ) (v : Vec d) (hv : ‖v‖ = 1) :
    ridgeHermite n v hv ∈ chaos d n := by
  rw [ridgeHermite_eq_sum]
  exact Submodule.sum_mem _ fun α hα => Submodule.smul_mem _ _
    (Submodule.subset_span ⟨α, by simpa using hα, rfl⟩)

lemma chaos_isOrtho {d : ℕ} {k n : ℕ} (hkn : k ≠ n) :
    chaos d k ⟂ chaos d n := by
  rw [chaos, chaos]
  refine Submodule.isOrtho_span.mpr ?_
  rintro u ⟨β, hβ, rfl⟩ w ⟨α, hα, rfl⟩
  rw [HL2_inner, ite_eq_right]
  intro hcon
  subst hcon
  rw [Finset.mem_coe, mem_idxOf] at hβ hα
  exact hkn (hβ ▸ hα ▸ rfl)

lemma Pn_of_mem {d : ℕ} {n : ℕ} {f : L2 d} (hf : f ∈ chaos d n) :
    Pn d n f = f :=
  Submodule.starProjection_eq_self_iff.mpr hf

lemma Pn_of_mem_ne {d : ℕ} {k n : ℕ} (hkn : k ≠ n) {f : L2 d}
    (hf : f ∈ chaos d k) : Pn d n f = 0 := by
  have hOrtho : f ∈ (chaos d n)ᗮ := (Submodule.isOrtho_iff_le.mp (chaos_isOrtho hkn)) hf
  refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero (Submodule.zero_mem _) ?_
  intro w hw
  rw [sub_zero]
  rw [Submodule.mem_orthogonal] at hOrtho
  rw [real_inner_comm]
  exact hOrtho w hw

/-- `P_n(g^v) = (⟨g,h_n⟩/n!)·h_n^v` (LaTeX — `main.tex` §4: "Write
$P_n(g^v) = \frac{\langle g, h_n\rangle}{n!}h_n(\langle v,x\rangle)$"). -/
theorem Pn_ridge {d : ℕ} (n : ℕ) (v : Vec d) (hv : ‖v‖ = 1) (g : L2R) :
    Pn d n (ridge v hv g)
      = (⟪g, hermiteL2 n⟫ / (n ! : ℝ)) • ridgeHermite n v hv := by
  have hL := (hermite_hasSum g).mapL
    ((Pn d n).comp (ridge v hv).toContinuousLinearMap)
  have hterm : ∀ k : ℕ,
      ((Pn d n).comp (ridge v hv).toContinuousLinearMap)
          ((⟪g, hermiteL2 k⟫ / (k ! : ℝ)) • hermiteL2 k)
        = if k = n then (⟪g, hermiteL2 n⟫ / (n ! : ℝ)) • ridgeHermite n v hv
          else 0 := by
    intro k
    rw [map_smul]
    have hcomp : ((Pn d n).comp (ridge v hv).toContinuousLinearMap) (hermiteL2 k)
        = Pn d n (ridgeHermite k v hv) := rfl
    by_cases hk : k = n
    · subst hk
      rw [ite_eq_left rfl, hcomp, Pn_of_mem (ridgeHermite_mem_chaos k v hv)]
    · rw [ite_eq_right hk, hcomp, Pn_of_mem_ne hk (ridgeHermite_mem_chaos k v hv),
        smul_zero]
  have hsingle : HasSum
      (fun k => if k = n then (⟪g, hermiteL2 n⟫ / (n ! : ℝ)) • ridgeHermite n v hv
        else 0)
      ((⟪g, hermiteL2 n⟫ / (n ! : ℝ)) • ridgeHermite n v hv) := by
    have h := hasSum_single (f := fun k =>
      if k = n then (⟪g, hermiteL2 n⟫ / (n ! : ℝ)) • ridgeHermite n v hv else 0) n
      (fun k hk => ite_eq_right hk)
    simpa using h
  have hfe : (fun k => ((Pn d n).comp (ridge v hv).toContinuousLinearMap)
      ((⟪g, hermiteL2 k⟫ / (k ! : ℝ)) • hermiteL2 k))
      = fun k => if k = n then (⟪g, hermiteL2 n⟫ / (n ! : ℝ)) • ridgeHermite n v hv
        else 0 := funext hterm
  rw [hfe] at hL
  exact hL.unique hsingle

lemma norm_ridgeHermite {d : ℕ} (n : ℕ) (v : Vec d) (hv : ‖v‖ = 1) :
    ‖ridgeHermite n v hv‖ = Real.sqrt (n !) := by
  rw [ridgeHermite, ridge_norm]
  have h : ‖hermiteL2 n‖ ^ 2 = (n ! : ℝ) := by
    rw [← real_inner_self_eq_norm_sq, hermiteL2_inner, ite_eq_left rfl]
  rw [← h, Real.sqrt_sq (norm_nonneg _)]

/-! ### Radial functions pair with `ρ_n` -/

/-- For radial `R`: `⟨R, h_n^v⟩ = ⟨R, ρ_n⟩` (the paper's
"`⟨P_nF, P_n(g^v)⟩ = ⟨P_nF, Π_Rad P_n(g^v)⟩`" step). -/
lemma inner_radial_ridgeHermite {d : ℕ} {R : L2 d} (hR : IsRadial R)
    (n : ℕ) (v : Vec d) (hv : ‖v‖ = 1) :
    ⟪R, ridgeHermite n v hv⟫ = ⟪R, rho d n⟫ := by
  conv_lhs => rw [← radAvgFun_of_isRadial hR]
  rw [inner_radAvgFun, radAvg_ridgeHermite]

/-- `ρ_n = 0` for odd `n`. -/
lemma rho_eq_zero_of_odd {d : ℕ} {n : ℕ} (hn : Odd n) : rho d n = 0 := by
  rw [rho]
  refine Finset.sum_eq_zero fun α hα => ?_
  have hdeg : mdeg α = n := mem_idxOf.mp hα
  have hodd : ∃ i, ¬ Even (α i) := by
    by_contra hcon
    push Not at hcon
    have : Even n := by
      rw [← hdeg, mdeg]
      exact Finset.sum_induction _ Even (fun a b ha hb => ha.add hb) ⟨0, rfl⟩
        (fun i _ => hcon i)
    exact (Nat.not_even_iff_odd.mpr hn) this
  rw [sphereMoment_eq_zero_of_odd hodd, mul_zero, zero_smul]

/-! ### `‖ρ_n‖² = n!·K_n` -/

/-- Pointwise multinomial pairing: the coefficient sum against `v^α` is the
sphere average of `⟨v,·⟩ⁿ`. -/
lemma sum_sphereMoment_mpow {d : ℕ} (hd : 0 < d) (n : ℕ) (v : Vec d) :
    ∑ α ∈ idxOf d n, ((n ! : ℝ) / (mfact α : ℝ)) * sphereMoment d α * mpow v α
      = ∫ w, (⟪v, w⟫ : ℝ) ^ n ∂(sphereUnif d) := by
  have hswap : ∑ α ∈ idxOf d n, ((n ! : ℝ) / (mfact α : ℝ)) * sphereMoment d α * mpow v α
      = ∫ w, ∑ α ∈ idxOf d n, ((n ! : ℝ) / (mfact α : ℝ)) * mpow v α * mpow w α
          ∂(sphereUnif d) := by
    rw [integral_finsetSum]
    · refine Finset.sum_congr rfl fun α hα => ?_
      rw [sphereMoment]
      rw [show ((n ! : ℝ) / (mfact α : ℝ)) * (∫ w, mpow w α ∂(sphereUnif d)) * mpow v α
          = (((n ! : ℝ) / (mfact α : ℝ)) * mpow v α) * ∫ w, mpow w α ∂(sphereUnif d)
        from by ring, ← integral_const_mul]
    · intro α hα
      have hc : Continuous fun w : Vec d => ((n ! : ℝ) / (mfact α : ℝ)) * mpow v α * mpow w α :=
        continuous_const.mul (continuous_mpow α)
      refine integrable_sphere_of_bounded hd hc.measurable
        (|((n ! : ℝ) / (mfact α : ℝ)) * mpow v α|) fun w hw => ?_
      rw [abs_mul]
      calc |((n ! : ℝ) / (mfact α : ℝ)) * mpow v α| * |mpow w α|
          ≤ |((n ! : ℝ) / (mfact α : ℝ)) * mpow v α| * 1 :=
            mul_le_mul_of_nonneg_left (abs_mpow_le_one (le_of_eq hw) α) (abs_nonneg _)
        _ = _ := mul_one _
  rw [hswap]
  refine integral_congr_ae (ae_of_all _ fun w => ?_)
  show ∑ α ∈ idxOf d n, ((n ! : ℝ) / (mfact α : ℝ)) * mpow v α * mpow w α
      = (⟪v, w⟫ : ℝ) ^ n
  have hprod : ∀ α ∈ idxOf d n, ((n ! : ℝ) / (mfact α : ℝ)) * mpow v α * mpow w α
      = ((n ! : ℝ) / (mfact α : ℝ)) * mpow (WithLp.toLp 2 (fun i => v i * w i)) α := by
    intro α _
    rw [mul_assoc]
    congr 1
    rw [mpow, mpow, mpow, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun i _ => by
      rw [show (WithLp.toLp 2 fun j => v j * w j) i = v i * w i from rfl, mul_pow]
  rw [Finset.sum_congr rfl hprod, ← sum_pow_multinomial]
  congr 1
  rw [PiLp.inner_apply]
  exact Finset.sum_congr rfl fun i _ => by
    rw [RCLike.inner_apply, conj_trivial,
      show (WithLp.toLp 2 fun j => v j * w j) i = v i * w i from rfl]
    ring

/-- `𝔼_W[⟨v,W⟩ⁿ] = K_n` for unit `v` (isometry change of variables). -/
lemma integral_inner_pow_sphere {d : ℕ} {v : Vec d} (hv : ‖v‖ = 1) (n : ℕ) :
    ∫ w, (⟪v, w⟫ : ℝ) ^ n ∂(sphereUnif d) = Kmom d n := by
  have hd : 0 < d := dim_pos_of_unit hv
  set e₀ : Vec d := EuclideanSpace.single (⟨0, hd⟩ : Fin d) (1 : ℝ) with he₀
  have he₀u : ‖e₀‖ = 1 := by
    rw [he₀, PiLp.norm_single, norm_one]
  obtain ⟨Q, hQ⟩ := exists_actMap_eq he₀u hv
  -- pass to the Gaussian, substitute x = Q y, land on the first-coordinate moment
  have h1 : ∫ w, (⟪v, w⟫ : ℝ) ^ n ∂(sphereUnif d)
      = ∫ x, (⟪v, ‖x‖⁻¹ • x⟫ : ℝ) ^ n ∂(γ d) := by
    rw [sphereUnif, integral_map (Measurable.aemeasurable (by fun_prop))]
    exact Continuous.aestronglyMeasurable (by fun_prop)
  have h2 : ∀ y : Vec d, (⟪v, ‖actMap Q y‖⁻¹ • actMap Q y⟫ : ℝ) ^ n
      = mpow (‖y‖⁻¹ • y) (fun i : Fin d => if (i : ℕ) = 0 then n else 0) := by
    intro y
    have hxy : (⟪v, ‖actMap Q y‖⁻¹ • actMap Q y⟫ : ℝ) = ⟪e₀, ‖y‖⁻¹ • y⟫ := by
      rw [actMap_norm]
      rw [show (‖y‖⁻¹ • actMap Q y : Vec d) = actMap Q (‖y‖⁻¹ • y) from
        (map_smul ((Q : Vec d →L[ℝ] Vec d)) _ _).symm]
      rw [← hQ]
      exact Unitary.inner_map_map Q e₀ (‖y‖⁻¹ • y)
    rw [hxy]
    -- ⟨e₀, u⟩ = u₀ and u₀ⁿ = mpow u (n·e₀)
    have hcoord : (⟪e₀, ‖y‖⁻¹ • y⟫ : ℝ) = (‖y‖⁻¹ • y : Vec d) ⟨0, hd⟩ := by
      rw [he₀]
      rw [EuclideanSpace.inner_single_left]
      simp
    rw [hcoord, mpow,
      ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ (⟨0, hd⟩ : Fin d))]
    have h0 : ((⟨0, hd⟩ : Fin d) : ℕ) = 0 := rfl
    rw [ite_eq_left h0]
    have hrest : ∏ j ∈ Finset.univ.erase (⟨0, hd⟩ : Fin d),
        (‖y‖⁻¹ • y : Vec d) j ^ (if (j : ℕ) = 0 then n else 0) = 1 :=
      Finset.prod_eq_one fun j hj => by
        have hj0 : (j : ℕ) ≠ 0 := fun hcon =>
          (Finset.ne_of_mem_erase hj) (Fin.ext hcon)
        rw [ite_eq_right hj0, pow_zero]
    rw [hrest, mul_one]
  have h3 : ∫ x, (⟪v, ‖x‖⁻¹ • x⟫ : ℝ) ^ n ∂(γ d)
      = ∫ y, mpow (‖y‖⁻¹ • y) (fun i : Fin d => if (i : ℕ) = 0 then n else 0) ∂(γ d) := by
    have hasm : AEStronglyMeasurable (fun x : Vec d => (⟪v, ‖x‖⁻¹ • x⟫ : ℝ) ^ n)
        (Measure.map (actMap Q) (γ d)) := Measurable.aestronglyMeasurable (by fun_prop)
    have h := integral_map (measurePreserving_actMap Q).aemeasurable hasm
    rw [(measurePreserving_actMap Q).map_eq] at h
    rw [h]
    exact integral_congr_ae (ae_of_all _ fun y => h2 y)
  rw [h1, h3, Kmom, sphereMoment, sphereUnif,
    integral_map (Measurable.aemeasurable (by fun_prop))
      (Continuous.aestronglyMeasurable (continuous_mpow _))]

/-- `‖ρ_n‖² = n!·K_n` for even `n` (LaTeX — `main.tex` §4:
"$\|\Pi_{\mathrm{Rad}}P_n(g^v)\|^2 = c_n^2 n! K_n$", normalized form). -/
lemma norm_rho_sq {d : ℕ} (hd : 0 < d) (n : ℕ) :
    ‖rho d n‖ ^ 2 = (n ! : ℝ) * Kmom d n := by
  set e₀ : Vec d := EuclideanSpace.single (⟨0, hd⟩ : Fin d) (1 : ℝ) with he₀
  have he₀u : ‖e₀‖ = 1 := by
    rw [he₀, PiLp.norm_single, norm_one]
  -- ‖ρ‖² = ⟨h_n^{e₀}, ρ⟩ (projection identity)
  have hproj : ‖rho d n‖ ^ 2 = ⟪ridgeHermite n e₀ he₀u, rho d n⟫ := by
    rw [← radAvg_ridgeHermite n e₀ he₀u, ← real_inner_self_eq_norm_sq]
    rw [inner_radAvgFun,
      radAvgFun_of_isRadial (isRadial_radAvgFun (ridgeHermite n e₀ he₀u))]
  rw [hproj, rho, inner_sum]
  have hterm : ∀ α ∈ idxOf d n,
      ⟪ridgeHermite n e₀ he₀u, (((n ! : ℝ) / (mfact α : ℝ)) * sphereMoment d α) • HL2 α⟫
        = (n ! : ℝ) * (((n ! : ℝ) / (mfact α : ℝ)) * sphereMoment d α * mpow e₀ α) := by
    intro α hα
    rw [real_inner_smul_right, inner_ridgeHermite_HL2 n e₀ he₀u (by simpa using hα)]
    ring
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum,
    sum_sphereMoment_mpow hd n e₀, integral_inner_pow_sphere he₀u]

/-! ### Proposition 4.1 -/

/- LaTeX — `main.tex`, Proposition 4.1: "the inner product
$\langle P_n F, P_n(g^v)\rangle$ vanishes when $n$ is odd." -/
/-- **Proposition 4.1, odd case.** -/
theorem correlation_eq_zero_of_odd {d : ℕ} {n : ℕ} (hn : Odd n)
    (F : L2 d) (hF : IsRadial F) (g : L2R) (v : Vec d) (hv : ‖v‖ = 1) :
    ⟪Pn d n F, Pn d n (ridge v hv g)⟫ = 0 := by
  rw [Pn_ridge, real_inner_smul_right,
    inner_radial_ridgeHermite (isRadial_Pn hF n) n v hv,
    rho_eq_zero_of_odd hn, inner_zero_right, mul_zero]

/- LaTeX — `main.tex`, Proposition 4.1: "When $n$ is even,
$$\left|\langle P_n F, P_n(g^v)\rangle\right| \le \sqrt{K_n}\,
\|P_n F\|\,\|P_n(g^v)\|.$$" -/
/-- **Proposition 4.1, even case.** -/
theorem correlation_bound_of_even {d : ℕ} (hd : 0 < d) {n : ℕ} (hn : Even n)
    (F : L2 d) (hF : IsRadial F) (g : L2R) (v : Vec d) (hv : ‖v‖ = 1) :
    |⟪Pn d n F, Pn d n (ridge v hv g)⟫| ≤
      Real.sqrt (Kmom d n) * ‖Pn d n F‖ * ‖Pn d n (ridge v hv g)‖ := by
  rw [Pn_ridge, real_inner_smul_right, abs_mul,
    inner_radial_ridgeHermite (isRadial_Pn hF n) n v hv]
  have hCS : |⟪Pn d n F, rho d n⟫| ≤ ‖Pn d n F‖ * ‖rho d n‖ :=
    abs_real_inner_le_norm _ _
  have hrho : ‖rho d n‖ = Real.sqrt ((n ! : ℝ) * Kmom d n) := by
    rw [← norm_rho_sq hd n, Real.sqrt_sq (norm_nonneg _)]
  rw [norm_smul, Real.norm_eq_abs, norm_ridgeHermite]
  calc |⟪g, hermiteL2 n⟫ / (n ! : ℝ)| * |⟪Pn d n F, rho d n⟫|
      ≤ |⟪g, hermiteL2 n⟫ / (n ! : ℝ)| * (‖Pn d n F‖ * ‖rho d n‖) :=
        mul_le_mul_of_nonneg_left hCS (abs_nonneg _)
    _ = Real.sqrt (Kmom d n) * ‖Pn d n F‖ *
          (|⟪g, hermiteL2 n⟫ / (n ! : ℝ)| * Real.sqrt (n !)) := by
        rw [hrho, mul_comm ((n ! : ℝ)) (Kmom d n), Real.sqrt_mul
          (Kmom_nonneg hd hn)]
        ring

end

end GaussianDepthSeparation
