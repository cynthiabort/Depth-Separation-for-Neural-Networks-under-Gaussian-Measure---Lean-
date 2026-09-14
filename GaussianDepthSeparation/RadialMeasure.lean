/-
GaussianDepthSeparation §5 — radial change of variables for the standard Gaussian.
-/
import GaussianDepthSeparation.ChiSquare
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

namespace GaussianDepthSeparation

open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal NNReal Nat

noncomputable section

def gaussianPiDensity (d : ℕ) (x : Fin d → ℝ) : ℝ :=
  ∏ i, gaussianPDFReal 0 1 (x i)

lemma gaussianPiDensity_nonneg (d : ℕ) (x : Fin d → ℝ) :
    0 ≤ gaussianPiDensity d x :=
  Finset.prod_nonneg fun i _ => gaussianPDFReal_nonneg 0 1 (x i)

lemma gaussianPiDensity_measurable (d : ℕ) : Measurable (gaussianPiDensity d) := by
  exact Finset.measurable_prod _ fun i _ =>
    (measurable_gaussianPDFReal 0 1).comp (measurable_pi_apply i)

/-- The finite product of standard real Gaussians has the product density. -/
lemma pi_gaussianReal_eq_withDensity (d : ℕ) :
    Measure.pi (fun _ : Fin d => gaussianReal 0 1) =
      volume.withDensity (fun x => ENNReal.ofReal (gaussianPiDensity d x)) := by
  apply Measure.pi_eq
  intro s hs
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs)]
  let f : Fin d → ℝ → ℝ := fun i x => (s i).indicator (gaussianPDFReal 0 1) x
  have hfint : ∀ i, Integrable (f i) := fun i =>
    (integrable_gaussianPDFReal 0 1).indicator (hs i)
  have hprodint : Integrable (fun x : Fin d → ℝ => ∏ i, f i (x i)) :=
    Integrable.fintype_prod hfint
  have hpoint : ∀ x : Fin d → ℝ,
      (Set.pi Set.univ s).indicator (gaussianPiDensity d) x = ∏ i, f i (x i) := by
    intro x
    by_cases hx : x ∈ Set.pi Set.univ s
    · rw [Set.indicator_of_mem hx]
      simp only [gaussianPiDensity, f]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [Set.indicator_of_mem ((mem_pi.mp hx) i (Set.mem_univ i))]
    · rw [Set.indicator_of_notMem hx]
      rw [mem_pi] at hx
      push Not at hx
      obtain ⟨i, hi⟩ := hx
      rw [Finset.prod_eq_zero (Finset.mem_univ i)]
      simp [f, hi]
  have hrealint : Integrable ((Set.pi Set.univ s).indicator (gaussianPiDensity d)) :=
    hprodint.congr (ae_of_all _ fun x => (hpoint x).symm)
  have hofreal :
      (Set.pi Set.univ s).indicator
          (fun x => ENNReal.ofReal (gaussianPiDensity d x)) =
        fun x => ENNReal.ofReal ((Set.pi Set.univ s).indicator
          (gaussianPiDensity d) x) := by
    funext x
    by_cases hx : x ∈ Set.pi Set.univ s <;> simp [hx]
  rw [← lintegral_indicator (MeasurableSet.univ_pi hs), hofreal]
  rw [← ofReal_integral_eq_lintegral_ofReal hrealint
    (ae_of_all _ fun x => Set.indicator_nonneg (fun _ _ => gaussianPiDensity_nonneg d _) _)]
  rw [integral_congr_ae (ae_of_all _ hpoint), integral_fintype_prod_volume_eq_prod f]
  have hone : ∀ i, 0 ≤ ∫ x, f i x := fun i => integral_nonneg fun _ => by
    exact Set.indicator_nonneg (fun x _ => gaussianPDFReal_nonneg 0 1 x) _
  rw [ENNReal.ofReal_prod_of_nonneg fun i _ => hone i]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [gaussianReal_apply_eq_integral 0 one_ne_zero]
  congr 1
  exact integral_indicator (hs i)

/-- A nondegenerate standard real Gaussian is positive on every nonempty open set. -/
instance gaussianRealZeroOne_isOpenPosMeasure :
    Measure.IsOpenPosMeasure (gaussianReal 0 1) := by
  rw [gaussianReal_of_var_ne_zero 0 one_ne_zero]
  have hac : (volume : Measure ℝ) ≪
      volume.withDensity (gaussianPDF 0 1) := withDensity_absolutelyContinuous'
    (measurable_gaussianPDF 0 1).aemeasurable
    (ae_of_all _ fun x => ENNReal.ofReal_ne_zero_iff.mpr
      (gaussianPDFReal_pos 0 1 x one_ne_zero))
  exact hac.isOpenPosMeasure

/-- The coordinate product Gaussian is positive on every nonempty open set. -/
instance piGaussian_isOpenPosMeasure (d : ℕ) :
    Measure.IsOpenPosMeasure (Measure.pi (fun _ : Fin d => gaussianReal 0 1)) :=
  Measure.pi.isOpenPosMeasure _

/-- The standard Gaussian on `Vec d` has full topological support. -/
instance gaussD_isOpenPosMeasure (d : ℕ) : Measure.IsOpenPosMeasure (γ d) := by
  rw [γ, ← ProbabilityTheory.map_pi_eq_stdGaussian]
  exact (show Continuous (@WithLp.toLp 2 (Fin d → ℝ)) by fun_prop).isOpenPosMeasure_map
    (WithLp.toLp_surjective 2)

/-- Product-density normal form, now written in terms of the Euclidean norm. -/
lemma gaussianPiDensity_eq_norm (d : ℕ) (y : Fin d → ℝ) :
    gaussianPiDensity d y =
      (Real.sqrt (2 * π))⁻¹ ^ d * Real.exp (-‖WithLp.toLp 2 y‖ ^ 2 / 2) := by
  simp only [gaussianPiDensity, gaussianPDFReal_zero_one,
    Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    ← Real.exp_sum]
  congr 2
  rw [EuclideanSpace.real_norm_sq_eq]
  calc
    ∑ i, -y i ^ 2 / 2 = (∑ i, -y i ^ 2) / 2 :=
      (Finset.sum_div Finset.univ (fun i => -y i ^ 2) 2).symm
    _ = (-∑ i, y i ^ 2) / 2 := by rw [Finset.sum_neg_distrib]

/-- Integrating against `γ^d` can be written as an ordinary Euclidean
integral against its radial density. -/
lemma integral_gaussD_eq_volume_density {d : ℕ} (f : Vec d → ℝ)
    (hf : AEStronglyMeasurable f (γ d)) :
    ∫ x, f x ∂(γ d) = ∫ x : Vec d,
      ((Real.sqrt (2 * π))⁻¹ ^ d * Real.exp (-‖x‖ ^ 2 / 2)) * f x := by
  rw [integral_gaussD_eq_pi f hf, pi_gaussianReal_eq_withDensity]
  rw [integral_withDensity_eq_integral_toReal_smul
    (gaussianPiDensity_measurable d).ennreal_ofReal (by simp)]
  simp only [smul_eq_mul, ENNReal.toReal_ofReal (gaussianPiDensity_nonneg d _)]
  rw [← (PiLp.volume_preserving_toLp (Fin d)).integral_comp
    (MeasurableEquiv.toLp 2 _).measurableEmbedding]
  apply integral_congr_ae
  exact ae_of_all _ fun y => by
    change gaussianPiDensity d y * f (WithLp.toLp 2 y) = _
    rw [gaussianPiDensity_eq_norm]

/-- Polar-coordinate form of a radial Gaussian integral. -/
lemma integral_gaussD_radial_polar {d : ℕ} (hd : 0 < d) (h : ℝ → ℝ)
    (hh : AEStronglyMeasurable (fun x : Vec d => h (‖x‖ ^ 2 / d)) (γ d)) :
    ∫ x, h (‖x‖ ^ 2 / d) ∂(γ d) =
      (d : ℝ) * volume.real (Metric.ball (0 : Vec d) 1) *
        ∫ r in Ioi (0 : ℝ), r ^ (d - 1) *
          ((Real.sqrt (2 * π))⁻¹ ^ d * Real.exp (-r ^ 2 / 2) * h (r ^ 2 / d)) := by
  let : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  rw [integral_gaussD_eq_volume_density _ hh]
  let g : ℝ → ℝ := fun r =>
    (Real.sqrt (2 * π))⁻¹ ^ d * Real.exp (-r ^ 2 / 2) * h (r ^ 2 / d)
  change (∫ x : Vec d, g ‖x‖) = _
  rw [integral_fun_norm_addHaar volume g]
  simp only [finrank_euclideanSpace, Fintype.card_fin, nsmul_eq_mul, smul_eq_mul, g]
  ring

/-- The common unnormalized kernel in the normalized chi-square density. -/
def chiSqKernel (d : ℕ) (h : ℝ → ℝ) (t : ℝ) : ℝ :=
  t ^ ((d : ℝ) / 2 - 1) * Real.exp (-(d * t) / 2) * h t

/-- The substitutions `s = r²` and `s = d t` in the radial integral. -/
lemma radial_integral_substitution {d : ℕ} (hd : 0 < d) (h : ℝ → ℝ) :
    ∫ r in Ioi (0 : ℝ), r ^ (d - 1) * Real.exp (-r ^ 2 / 2) * h (r ^ 2 / d) =
      (d : ℝ) ^ ((d : ℝ) / 2) / 2 *
        ∫ t in Ioi (0 : ℝ), chiSqKernel d h t := by
  let g : ℝ → ℝ := fun s =>
    (1 / 2 : ℝ) * s ^ ((d : ℝ) / 2 - 1) * Real.exp (-s / 2) * h (s / d)
  have hsquare :
      (∫ r in Ioi (0 : ℝ), r ^ (d - 1) * Real.exp (-r ^ 2 / 2) * h (r ^ 2 / d)) =
        ∫ s in Ioi (0 : ℝ), g s := by
    rw [← integral_comp_rpow_Ioi_of_pos (g := g) (p := (2 : ℝ)) (by norm_num)]
    refine setIntegral_congr_fun measurableSet_Ioi fun r hr => ?_
    have hr0 : 0 ≤ r := le_of_lt hr
    have hcast : ((d - 1 : ℕ) : ℝ) = (d : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega)]
      norm_num
    have hrpow :
        2 * r * ((1 / 2 : ℝ) * (r ^ (2 : ℝ)) ^ ((d : ℝ) / 2 - 1)) =
          r ^ ((d - 1 : ℕ) : ℝ) := by
      calc
        2 * r * ((1 / 2 : ℝ) * (r ^ (2 : ℝ)) ^ ((d : ℝ) / 2 - 1))
            = r * (r ^ (2 : ℝ)) ^ ((d : ℝ) / 2 - 1) := by ring
        _ = r ^ (1 : ℝ) * (r ^ (2 : ℝ)) ^ ((d : ℝ) / 2 - 1) := by
          rw [Real.rpow_one]
        _ = r ^ ((1 : ℝ) + 2 * ((d : ℝ) / 2 - 1)) := by
          rw [← Real.rpow_mul hr0, ← Real.rpow_add hr]
        _ = r ^ ((d - 1 : ℕ) : ℝ) := by
          congr 1
          rw [hcast]
          ring
    simp only [g, smul_eq_mul]
    have hpone : r ^ ((2 : ℝ) - 1) = r := by norm_num [Real.rpow_one]
    rw [← Real.rpow_natCast r (d - 1), ← Real.rpow_natCast r 2]
    rw [hpone]
    rw [← hrpow]
    simp only [div_eq_mul_inv]
    ac_rfl
  rw [hsquare]
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hscale := integral_comp_mul_left_Ioi g 0 hdR
  simp only [mul_zero, smul_eq_mul] at hscale
  have hrescale :
      (∫ s in Ioi (0 : ℝ), g s) =
        (d : ℝ) * ∫ t in Ioi (0 : ℝ), g (d * t) := by
    calc
      ∫ s in Ioi (0 : ℝ), g s =
          (d : ℝ) * ((d : ℝ)⁻¹ * ∫ s in Ioi (0 : ℝ), g s) := by
            field_simp
      _ = (d : ℝ) * ∫ t in Ioi (0 : ℝ), g (d * t) := by rw [hscale]
  rw [hrescale]
  have hgpoint : ∀ t ∈ Ioi (0 : ℝ),
      g (d * t) = ((1 / 2 : ℝ) * (d : ℝ) ^ ((d : ℝ) / 2 - 1)) *
        chiSqKernel d h t := by
    intro t ht
    have ht0 : 0 ≤ t := le_of_lt ht
    dsimp only [g]
    rw [chiSqKernel, Real.mul_rpow hdR.le ht0]
    have hdiv : (d : ℝ) * t / d = t := by field_simp
    rw [hdiv]
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi hgpoint, integral_const_mul]
  have hpow : (d : ℝ) * (d : ℝ) ^ ((d : ℝ) / 2 - 1) =
      (d : ℝ) ^ ((d : ℝ) / 2) := by
    conv_lhs => lhs; rw [← Real.rpow_one (d : ℝ)]
    rw [← Real.rpow_add hdR]
    congr 1
    ring
  calc
    (d : ℝ) * ((1 / 2 : ℝ) * (d : ℝ) ^ ((d : ℝ) / 2 - 1) *
        ∫ t in Ioi (0 : ℝ), chiSqKernel d h t)
        = ((d : ℝ) * (d : ℝ) ^ ((d : ℝ) / 2 - 1)) / 2 *
          ∫ t in Ioi (0 : ℝ), chiSqKernel d h t := by ring
    _ = (d : ℝ) ^ ((d : ℝ) / 2) / 2 *
          ∫ t in Ioi (0 : ℝ), chiSqKernel d h t := by rw [hpow]

def gaussianRadialConstant (d : ℕ) : ℝ :=
  (d : ℝ) * volume.real (Metric.ball (0 : Vec d) 1) *
    (Real.sqrt (2 * π))⁻¹ ^ d * ((d : ℝ) ^ ((d : ℝ) / 2) / 2)

def chiSqConstant (d : ℕ) : ℝ :=
  ((d : ℝ) / 2) ^ ((d : ℝ) / 2) / Real.Gamma ((d : ℝ) / 2)

lemma integral_gaussD_radial_eq_kernel {d : ℕ} (hd : 0 < d) (h : ℝ → ℝ)
    (hh : AEStronglyMeasurable (fun x : Vec d => h (‖x‖ ^ 2 / d)) (γ d)) :
    ∫ x, h (‖x‖ ^ 2 / d) ∂(γ d) =
      gaussianRadialConstant d * ∫ t in Ioi (0 : ℝ), chiSqKernel d h t := by
  rw [integral_gaussD_radial_polar hd h hh]
  have hpull :
      (∫ r in Ioi (0 : ℝ), r ^ (d - 1) *
        ((Real.sqrt (2 * π))⁻¹ ^ d * Real.exp (-r ^ 2 / 2) * h (r ^ 2 / d))) =
        (Real.sqrt (2 * π))⁻¹ ^ d *
          ∫ r in Ioi (0 : ℝ), r ^ (d - 1) * Real.exp (-r ^ 2 / 2) * h (r ^ 2 / d) := by
    calc
      ∫ r in Ioi (0 : ℝ), r ^ (d - 1) *
          ((Real.sqrt (2 * π))⁻¹ ^ d * Real.exp (-r ^ 2 / 2) * h (r ^ 2 / d)) =
          ∫ r in Ioi (0 : ℝ), (Real.sqrt (2 * π))⁻¹ ^ d *
            (r ^ (d - 1) * Real.exp (-r ^ 2 / 2) * h (r ^ 2 / d)) := by
            refine setIntegral_congr_fun measurableSet_Ioi fun r _ => ?_
            ring
      _ = (Real.sqrt (2 * π))⁻¹ ^ d *
          ∫ r in Ioi (0 : ℝ),
            r ^ (d - 1) * Real.exp (-r ^ 2 / 2) * h (r ^ 2 / d) := by
        rw [integral_const_mul]
  rw [hpull, radial_integral_substitution hd]
  simp only [gaussianRadialConstant]
  ring

lemma integral_chiSq_eq_kernel {d : ℕ} (hd : 0 < d) (h : ℝ → ℝ)
    (hh : Integrable h (chiSqMeasure d)) :
    ∫ t, h t ∂(chiSqMeasure d) =
      chiSqConstant d * ∫ t in Ioi (0 : ℝ), chiSqKernel d h t := by
  have ha : (0 : ℝ) < d / 2 := by positivity
  have hpdf : Measurable (fun t => ENNReal.ofReal (chiSqDensity d t)) :=
    (measurable_gammaPDFReal ((d : ℝ) / 2) ((d : ℝ) / 2)).ennreal_ofReal
  have hprod : Integrable (fun t => chiSqDensity d t * h t) := by
    have hh' := hh
    rw [chiSqMeasure, gammaMeasure] at hh'
    have hm := (integrable_withDensity_iff_integrable_smul' hpdf (by simp)).mp hh'
    simpa only [smul_eq_mul, ENNReal.toReal_ofReal (chiSqDensity_nonneg hd _)] using hm
  rw [chiSqMeasure, gammaMeasure,
    show volume.withDensity (gammaPDF ((d : ℝ) / 2) ((d : ℝ) / 2)) =
      volume.withDensity (fun t => ENNReal.ofReal (chiSqDensity d t)) from rfl,
    integral_withDensity_eq_integral_toReal_smul hpdf (by simp)]
  simp only [smul_eq_mul, ENNReal.toReal_ofReal (chiSqDensity_nonneg hd _)]
  rw [← integral_add_compl measurableSet_Ioi hprod, compl_Ioi]
  have hzero : ∫ t in Iic (0 : ℝ), chiSqDensity d t * h t = 0 := by
    apply integral_eq_zero_of_ae
    filter_upwards [ae_restrict_of_ae (volume.ae_ne (0 : ℝ)),
      ae_restrict_mem measurableSet_Iic] with t ht0 ht
    have htneg : t < 0 := lt_of_le_of_ne ht ht0
    simp [chiSqDensity, gammaPDFReal, not_le.mpr htneg]
  rw [hzero, add_zero]
  rw [← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  have ht0 : 0 ≤ t := le_of_lt ht
  simp only [chiSqDensity, chiSqConstant, chiSqKernel, gammaPDFReal, ite_eq_left ht0]
  ring_nf

/-- The two radial normalizing constants agree because both corresponding
measures are probability measures.  This avoids duplicating a Gamma-function
normalization calculation. -/
lemma gaussianRadialConstant_eq_chiSqConstant {d : ℕ} (hd : 0 < d) :
    gaussianRadialConstant d = chiSqConstant d := by
  let : NeZero d := ⟨Nat.ne_of_gt hd⟩
  let J : ℝ := ∫ t in Ioi (0 : ℝ), chiSqKernel d (fun _ => 1) t
  have hG := integral_gaussD_radial_eq_kernel hd (fun _ => 1)
    (Continuous.aestronglyMeasurable (by fun_prop))
  have hC := integral_chiSq_eq_kernel hd (fun _ => 1) (integrable_const 1)
  simp only [integral_const, probReal_univ, one_smul] at hG hC
  change 1 = gaussianRadialConstant d * J at hG
  change 1 = chiSqConstant d * J at hC
  have hJ : J ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hG
    norm_num at hG
  apply mul_right_cancel₀ hJ
  rw [← hG, ← hC]

/-- Exact normalized-radius law: `‖X‖²/d` under `γ^d` is the gamma law
with shape and rate `d/2`. -/
theorem integral_gaussD_radial_eq_chiSq {d : ℕ} (hd : 0 < d) (h : ℝ → ℝ)
    (hgauss : AEStronglyMeasurable (fun x : Vec d => h (‖x‖ ^ 2 / d)) (γ d))
    (hchi : Integrable h (chiSqMeasure d)) :
    ∫ x, h (‖x‖ ^ 2 / d) ∂(γ d) = ∫ t, h t ∂(chiSqMeasure d) := by
  rw [integral_gaussD_radial_eq_kernel hd h hgauss,
    integral_chiSq_eq_kernel hd h hchi,
    gaussianRadialConstant_eq_chiSqConstant hd]

/-- The normalized chi-square measure written as the density used in the
paper, with the integral restricted to its positive support. -/
lemma integrable_mul_chiSqDensity {d : ℕ} (hd : 0 < d) (h : ℝ → ℝ)
    (hh : Integrable h (chiSqMeasure d)) :
    Integrable (fun t => h t * chiSqDensity d t) := by
  have hpdf : Measurable (fun t => ENNReal.ofReal (chiSqDensity d t)) :=
    (measurable_gammaPDFReal ((d : ℝ) / 2) ((d : ℝ) / 2)).ennreal_ofReal
  have hh' := hh
  rw [chiSqMeasure, gammaMeasure] at hh'
  have hm := (integrable_withDensity_iff_integrable_smul' hpdf (by simp)).mp hh'
  simpa only [smul_eq_mul, ENNReal.toReal_ofReal (chiSqDensity_nonneg hd _),
    mul_comm] using hm

theorem integral_chiSq_eq_density {d : ℕ} (hd : 0 < d) (h : ℝ → ℝ)
    (hh : Integrable h (chiSqMeasure d)) :
    ∫ t, h t ∂(chiSqMeasure d) =
      ∫ t in Ioi (0 : ℝ), h t * chiSqDensity d t := by
  have hpdf : Measurable (fun t => ENNReal.ofReal (chiSqDensity d t)) :=
    (measurable_gammaPDFReal ((d : ℝ) / 2) ((d : ℝ) / 2)).ennreal_ofReal
  have hprod := integrable_mul_chiSqDensity hd h hh
  rw [chiSqMeasure, gammaMeasure]
  change (∫ t, h t ∂volume.withDensity
    (fun t => ENNReal.ofReal (chiSqDensity d t))) = _
  rw [integral_withDensity_eq_integral_toReal_smul hpdf (by simp)]
  simp only [smul_eq_mul, ENNReal.toReal_ofReal (chiSqDensity_nonneg hd _)]
  rw [show (∫ t, chiSqDensity d t * h t) =
      ∫ t, h t * chiSqDensity d t from integral_congr_ae
        (ae_of_all _ fun t => mul_comm _ _)]
  rw [← integral_add_compl measurableSet_Ioi hprod, compl_Ioi]
  have hzero : ∫ t in Iic (0 : ℝ), h t * chiSqDensity d t = 0 := by
    apply integral_eq_zero_of_ae
    filter_upwards [ae_restrict_of_ae (volume.ae_ne (0 : ℝ)),
      ae_restrict_mem measurableSet_Iic] with t ht0 ht
    have htneg : t < 0 := lt_of_le_of_ne ht ht0
    simp [chiSqDensity, gammaPDFReal, not_le.mpr htneg]
  rw [hzero, add_zero]

end

end GaussianDepthSeparation
