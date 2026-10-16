/-
GaussianDepthSeparation §5, Lemma 5.1 — exact radial polynomial distance formula.
-/
import GaussianDepthSeparation.RadialRepresentation
import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed
import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction

namespace GaussianDepthSeparation

open MeasureTheory ProbabilityTheory Real Set Polynomial
open scoped RealInnerProductSpace NNReal

noncomputable section

/-- The normalized chi-square law is the law of `‖X‖²/d` for `X ∼ γ^d`. -/
theorem chiSqMeasure_eq_map {d : ℕ} (hd : 0 < d) :
    chiSqMeasure d = (γ d).map (fun x : Vec d => ‖x‖ ^ 2 / d) := by
  have : NeZero d := ⟨hd.ne'⟩
  have hmeas : Measurable (fun x : Vec d => ‖x‖ ^ 2 / d) := by fun_prop
  refine ext_of_forall_integral_eq_of_IsFiniteMeasure fun f => ?_
  rw [integral_map hmeas.aemeasurable f.continuous.aestronglyMeasurable]
  exact (integral_gaussD_radial_eq_chiSq hd f
    (f.continuous.comp (by fun_prop)).aestronglyMeasurable
    (f.integrable (chiSqMeasure d))).symm

/-- A function of `‖x‖²/d` is radial. -/
theorem isRadial_of_coeFn_eq {d : ℕ} (F : L2 d) (φ : ℝ → ℝ)
    (hF : ⇑F =ᵐ[γ d] fun x => φ (‖x‖ ^ 2 / d)) : IsRadial F := by
  intro U
  apply Lp.ext
  have hcomp : (⇑F) ∘ actMap U
      =ᵐ[γ d] (fun x : Vec d => φ (‖x‖ ^ 2 / d)) ∘ actMap U := by
    refine MeasureTheory.ae_eq_comp (measurePreserving_actMap U).aemeasurable ?_
    rw [(measurePreserving_actMap U).map_eq]
    exact hF
  filter_upwards [act_coeFn U F, hF, hcomp] with x hx1 hx2 hx3
  rw [hx1, show ((⇑F) ∘ actMap U) x = φ (‖actMap U x‖ ^ 2 / d) from hx3, hx2,
    actMap_norm]

/-- The squared distance from `F = φ(‖x‖²/d)` to the radial polynomial
`q(‖x‖²/d)` is the one-dimensional weighted integral of Lemma 5.1. -/
lemma normSq_sub_eq_integral {d : ℕ} (hd : 0 < d) (F : L2 d) (φ : ℝ → ℝ)
    (hφ : Measurable φ) (hF : ⇑F =ᵐ[γ d] fun x => φ (‖x‖ ^ 2 / d))
    (q : Polynomial ℝ) (G : L2 d)
    (hG : ⇑G =ᵐ[γ d] fun x => q.eval (‖x‖ ^ 2 / d)) :
    ‖F - G‖ ^ 2 =
      ∫ t in Ioi (0 : ℝ), (φ t - q.eval t) ^ 2 * chiSqDensity d t := by
  set h : ℝ → ℝ := fun t => (φ t - q.eval t) ^ 2 with hhdef
  have hhm : Measurable h := (hφ.sub (Polynomial.continuous q).measurable).pow_const 2
  have hrad : Measurable (fun x : Vec d => ‖x‖ ^ 2 / d) := by fun_prop
  have hpt : (fun x => ((F - G) x) ^ 2) =ᵐ[γ d] fun x => h (‖x‖ ^ 2 / d) := by
    filter_upwards [Lp.coeFn_sub F G, hF, hG] with x hsub hFx hGx
    rw [hsub, Pi.sub_apply, hFx, hGx]
  have hintγ : Integrable (fun x => h (‖x‖ ^ 2 / d)) (γ d) :=
    (Lp.memLp (F - G)).integrable_sq.congr hpt
  have hintχ : Integrable h (chiSqMeasure d) := by
    rw [chiSqMeasure_eq_map hd,
      integrable_map_measure hhm.aestronglyMeasurable hrad.aemeasurable]
    exact hintγ
  rw [norm_sq_eq_integral, integral_congr_ae hpt,
    integral_gaussD_radial_eq_chiSq hd h (hhm.comp hrad).aestronglyMeasurable hintχ,
    integral_chiSq_eq_density hd h hintχ]

/-- **Lemma 5.1 (radial polynomial distance).** For any measurable radial
profile, the high-chaos energy is the best weighted squared approximation by
polynomials of degree `< n₀/2`. The identity for `F` is almost everywhere,
as appropriate for `L²`. A profile on `[0, ∞)` may be extended measurably
to `ℝ`; the negative values never enter the formula. See also
`radial_polynomial_distance_nonneg` for the nonnegative-domain version. -/
theorem radial_polynomial_distance (d : ℕ) (hd : 0 < d) (n₀ : ℕ)
    (hn₀e : Even n₀) (hn₀ : 2 ≤ n₀) (F : L2 d) (φ : ℝ → ℝ)
    (hφ : Measurable φ) (hF : ⇑F =ᵐ[γ d] fun x => φ (‖x‖ ^ 2 / d)) :
    ‖Pge d n₀ F‖ ^ 2 =
      ⨅ q : Polynomial.degreeLT ℝ (n₀ / 2),
        ∫ t in Ioi (0 : ℝ), (φ t - (q : Polynomial ℝ).eval t) ^ 2 * chiSqDensity d t := by
  rw [normSq_Pge_eq_iInf_radialChaosLt _ (isRadial_of_coeFn_eq F φ hF)]
  let A : radialChaosLt d n₀ → ℝ := fun G =>
    ‖F - (G : L2 d)‖ ^ 2
  let B : Polynomial.degreeLT ℝ (n₀ / 2) → ℝ := fun q =>
    ∫ t in Ioi (0 : ℝ), (φ t - (q : Polynomial ℝ).eval t) ^ 2 * chiSqDensity d t
  have hAbdd : BddBelow (Set.range A) := by
    refine ⟨0, Set.forall_mem_range.mpr fun G => ?_⟩
    exact sq_nonneg _
  have hBbdd : BddBelow (Set.range B) := by
    refine ⟨0, Set.forall_mem_range.mpr fun q => ?_⟩
    exact integral_nonneg fun t =>
      mul_nonneg (sq_nonneg _) (chiSqDensity_nonneg hd t)
  change (⨅ G : radialChaosLt d n₀, A G) = ⨅ q, B q
  apply le_antisymm
  · refine le_ciInf fun q => ?_
    have hqdeg : (q : Polynomial ℝ).natDegree < n₀ / 2 := by
      by_cases hzero : (q : Polynomial ℝ) = 0
      · simp [hzero]
        omega
      · exact (Polynomial.natDegree_lt_iff_degree_lt hzero).mpr
          (Polynomial.mem_degreeLT.mp q.2)
    obtain ⟨G, hG⟩ := polynomial_exists_radial_chaosLt hd (by omega) hn₀e q hqdeg
    refine ciInf_le_of_le hAbdd G ?_
    exact le_of_eq (normSq_sub_eq_integral hd F φ hφ hF q G hG)
  · refine le_ciInf fun G => ?_
    obtain ⟨q, hqdeg, hGq⟩ :=
      radial_chaosLt_exists_polynomial hd (by omega) hn₀e G.2.1 G.2.2
    let q' : Polynomial.degreeLT ℝ (n₀ / 2) :=
      ⟨q, by
        rw [Polynomial.mem_degreeLT]
        by_cases hzero : q = 0
        · simp [hzero]
        · exact (Polynomial.natDegree_lt_iff_degree_lt hzero).mp
            hqdeg⟩
    refine ciInf_le_of_le hBbdd q' ?_
    exact le_of_eq (normSq_sub_eq_integral hd F φ hφ hF q G hGq).symm

/-- Lemma 5.1 with the profile defined on `[0, ∞)`, represented by `ℝ≥0`.
The measurable extension `t ↦ φ (Real.toNNReal t)` agrees with `φ` on the
nonnegative half-line, which contains the normalized squared radius. -/
theorem radial_polynomial_distance_nonneg (d : ℕ) (hd : 0 < d) (n₀ : ℕ)
    (hn₀e : Even n₀) (hn₀ : 2 ≤ n₀) (F : L2 d) (φ : ℝ≥0 → ℝ)
    (hφ : Measurable φ)
    (hF : ⇑F =ᵐ[γ d] fun x => φ (Real.toNNReal (‖x‖ ^ 2 / d))) :
    ‖Pge d n₀ F‖ ^ 2 =
      ⨅ q : Polynomial.degreeLT ℝ (n₀ / 2),
        ∫ t in Ioi (0 : ℝ),
          (φ (Real.toNNReal t) - (q : Polynomial ℝ).eval t) ^ 2 * chiSqDensity d t :=
  radial_polynomial_distance d hd n₀ hn₀e hn₀ F (fun t => φ (Real.toNNReal t))
    (hφ.comp measurable_real_toNNReal) hF

/-- The one-dimensional squared approximation error for the sine family in §5. -/
def radialError (m : ℝ) (q : Polynomial ℝ) (t : ℝ) : ℝ :=
  (sin (π * m * t) - q.eval t) ^ 2

/-- The radial sine target is invariant under orthogonal transformations. -/
theorem isRadial_radialSine (d : ℕ) (m : ℝ) : IsRadial (radialSine d m) :=
  isRadial_of_coeFn_eq _ (fun t => sin (π * m * t)) (radialSine_coeFn d m)

/-- Lemma 5.1 specialized to the sine target used in Lemma 5.3. -/
theorem radialSine_polynomial_distance (d : ℕ) (hd : 0 < d) (n₀ : ℕ)
    (hn₀e : Even n₀) (hn₀ : 2 ≤ n₀) (m : ℝ) :
    ‖Pge d n₀ (radialSine d m)‖ ^ 2 =
      ⨅ q : Polynomial.degreeLT ℝ (n₀ / 2),
        ∫ t in Ioi (0 : ℝ), radialError m q t * chiSqDensity d t :=
  radial_polynomial_distance d hd n₀ hn₀e hn₀ _ _
    (by fun_prop) (radialSine_coeFn d m)

end

end GaussianDepthSeparation
