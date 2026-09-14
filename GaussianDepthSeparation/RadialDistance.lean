/-
GaussianDepthSeparation §5, Lemma 5.1 — exact radial polynomial distance formula.
-/
import GaussianDepthSeparation.RadialRepresentation

namespace GaussianDepthSeparation

open MeasureTheory ProbabilityTheory Real Set Polynomial
open scoped RealInnerProductSpace ENNReal Nat

noncomputable section

/-- The one-dimensional squared approximation error occurring in §5. -/
def radialError (m : ℝ) (q : Polynomial ℝ) (t : ℝ) : ℝ :=
  (sin (π * m * t) - q.eval t) ^ 2

/-- The radial sine target is invariant under orthogonal transformations. -/
theorem isRadial_radialSine (d : ℕ) (m : ℝ) : IsRadial (radialSine d m) := by
  intro U
  apply Lp.ext
  have hcomp : (⇑(radialSine d m)) ∘ actMap U
      =ᵐ[γ d] (fun x : Vec d => sin (π * m * ‖x‖ ^ 2 / d)) ∘ actMap U := by
    refine MeasureTheory.ae_eq_comp (measurePreserving_actMap U).aemeasurable ?_
    rw [(measurePreserving_actMap U).map_eq]
    exact MemLp.coeFn_toLp (memLp_radialSineFun d m)
  filter_upwards [act_coeFn U (radialSine d m),
    MemLp.coeFn_toLp (memLp_radialSineFun d m), hcomp]
    with x hx1 hx2 hx3
  rw [hx1, show (⇑(radialSine d m) ∘ actMap U) x =
      sin (π * m * ‖actMap U x‖ ^ 2 / d) from hx3,
    show (⇑(radialSine d m) : Vec d → ℝ) x =
      sin (π * m * ‖x‖ ^ 2 / d) from hx2, actMap_norm]

/-- Squared `L²(γᵈ)` distance to a radial polynomial equals the corresponding
one-dimensional chi-square integral. -/
lemma normSq_radialSine_sub_eq_integral {d : ℕ} (hd : 0 < d) (m : ℝ)
    (q : Polynomial ℝ) (G : L2 d)
    (hG : ⇑G =ᵐ[γ d] fun x => q.eval (‖x‖ ^ 2 / d)) :
    ‖radialSine d m - G‖ ^ 2 =
      ∫ t in Ioi (0 : ℝ), radialError m q t * chiSqDensity d t := by
  rw [norm_sq_eq_integral]
  have hpoint : (fun x => ((radialSine d m - G) x) ^ 2) =ᵐ[γ d]
      fun x => radialError m q (‖x‖ ^ 2 / d) := by
    filter_upwards [Lp.coeFn_sub (radialSine d m) G,
      MemLp.coeFn_toLp (memLp_radialSineFun d m), hG]
      with x hsub hsine hpoly
    rw [hsub]
    change ((radialSine d m) x - G x) ^ 2 = _
    have hsine' : (radialSine d m : Vec d → ℝ) x =
        sin (π * m * ‖x‖ ^ 2 / d) := by
      simpa [radialSine] using hsine
    rw [hsine', hpoly]
    unfold radialError
    congr 2
    ring_nf
  rw [integral_congr_ae hpoint]
  have hchi := integrable_radialError_chiSqMeasure hd m q
  have herr : Continuous (radialError m q) := by
    unfold radialError
    fun_prop
  rw [integral_gaussD_radial_eq_chiSq hd (radialError m q)
      (Continuous.aestronglyMeasurable (herr.comp (by fun_prop))) hchi,
    integral_chiSq_eq_density hd (radialError m q) hchi]

/-- **Lemma 5.1 (radial polynomial distance).**  This is the exact statement
in the paper: the high-chaos energy is the best weighted approximation by
polynomials of degree `< n₀/2`. -/
theorem radial_polynomial_distance (d : ℕ) (hd : 0 < d) (n₀ : ℕ)
    (hn₀e : Even n₀) (hn₀ : 2 ≤ n₀) (m : ℝ) :
    ‖Pge d n₀ (radialSine d m)‖ ^ 2 =
      ⨅ q : Polynomial.degreeLT ℝ (n₀ / 2),
        ∫ t in Ioi (0 : ℝ), radialError m q t * chiSqDensity d t := by
  rw [normSq_Pge_eq_iInf_radialChaosLt _ (isRadial_radialSine d m)]
  let A : radialChaosLt d n₀ → ℝ := fun G =>
    ‖radialSine d m - (G : L2 d)‖ ^ 2
  let B : Polynomial.degreeLT ℝ (n₀ / 2) → ℝ := fun q =>
    ∫ t in Ioi (0 : ℝ), radialError m q t * chiSqDensity d t
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
    exact le_of_eq (normSq_radialSine_sub_eq_integral hd m q G hG)
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
    exact le_of_eq (normSq_radialSine_sub_eq_integral hd m q G hGq).symm

end

end GaussianDepthSeparation
