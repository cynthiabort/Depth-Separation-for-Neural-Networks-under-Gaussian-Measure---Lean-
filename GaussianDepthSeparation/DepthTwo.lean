/-
GaussianDepthSeparation — specialization of the ridge lower bound to depth-2 ReLU networks.

Each neuron is written as a one-dimensional profile along a unit direction.
The key quantitative statement is the paper's bound
`‖a·relu(‖w‖t+b)‖₂ ≤ |a|(‖w‖+|b|)`.
-/
import GaussianDepthSeparation.DepthSeparation
import GaussianDepthSeparation.Totality
import GaussianDepthSeparation.ReLU

namespace GaussianDepthSeparation

open MeasureTheory Polynomial
open scoped RealInnerProductSpace ENNReal Nat

noncomputable section

/-- A depth-2 ReLU network, with no output bias, exactly as in the paper. -/
structure Net2 (d : ℕ) where
  width : ℕ
  w : Fin width → Vec d
  b : Fin width → ℝ
  a : Fin width → ℝ

def Net2.eval {d : ℕ} (N : Net2 d) (x : Vec d) : ℝ :=
  ∑ i, N.a i * relu (⟪N.w i, x⟫ + N.b i)

/-- Uniform parameter bound for a depth-2 network. -/
def Net2.WeightsLe {d : ℕ} (N : Net2 d) (B : ℝ) : Prop :=
  (∀ i, ‖N.w i‖ ≤ B) ∧ (∀ i, |N.b i| ≤ B) ∧ ∀ i, |N.a i| ≤ B

lemma abs_relu_le_abs (t : ℝ) : |relu t| ≤ |t| := by
  rw [abs_of_nonneg (relu_nonneg t)]
  unfold relu
  exact max_le (le_abs_self t) (abs_nonneg t)

/-- The one-dimensional profile of a neuron whose input weight has norm `s`. -/
def reluProfileFun (a s b t : ℝ) : ℝ := a * relu (s * t + b)

lemma memLp_reluProfileFun (a s b : ℝ) :
    MemLp (reluProfileFun a s b) 2 γ₁ := by
  let P : Polynomial ℝ := Polynomial.C (a * b) + Polynomial.C (a * s) * X
  have hP := memLp_polyEval_gaussian P
  have hcont : Continuous (reluProfileFun a s b) := by
    unfold reluProfileFun
    fun_prop
  refine hP.of_le hcont.aestronglyMeasurable (ae_of_all _ fun t => ?_)
  rw [Real.norm_eq_abs, Real.norm_eq_abs]
  dsimp [reluProfileFun, P]
  simp only [Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_mul,
    Polynomial.eval_X]
  rw [abs_mul]
  have hr := abs_relu_le_abs (s * t + b)
  calc
    |a| * |relu (s * t + b)| ≤ |a| * |s * t + b| :=
      mul_le_mul_of_nonneg_left hr (abs_nonneg a)
    _ = |a * (s * t + b)| := by rw [abs_mul]
    _ = |a * b + a * s * t| := congrArg abs (by ring)

/-- The `L²(γ)` class of a depth-2 neuron profile. -/
def reluProfile (a s b : ℝ) : L2R :=
  (memLp_reluProfileFun a s b).toLp

lemma reluProfile_coeFn (a s b : ℝ) :
    ⇑(reluProfile a s b) =ᵐ[γ₁] reluProfileFun a s b :=
  MemLp.coeFn_toLp (memLp_reluProfileFun a s b)

lemma norm_hermiteL2_zero : ‖hermiteL2 0‖ = 1 := by
  have hsq : ‖hermiteL2 0‖ ^ 2 = 1 := by
    rw [← real_inner_self_eq_norm_sq, hermiteL2_inner, ite_eq_left rfl]
    norm_num
  nlinarith [norm_nonneg (hermiteL2 0)]

lemma norm_hermiteL2_one : ‖hermiteL2 1‖ = 1 := by
  have hsq : ‖hermiteL2 1‖ ^ 2 = 1 := by
    rw [← real_inner_self_eq_norm_sq, hermiteL2_inner, ite_eq_left rfl]
    norm_num
  nlinarith [norm_nonneg (hermiteL2 1)]

/-- The exact profile bound used in the paper's depth-2 specialization. -/
theorem norm_reluProfile_le (a s b : ℝ) (hs : 0 ≤ s) :
    ‖reluProfile a s b‖ ≤ |a| * (s + |b|) := by
  let P : Polynomial ℝ := Polynomial.C (a * b) + Polynomial.C (a * s) * X
  let q : L2R := (memLp_polyEval_gaussian P).toLp
  have hnorm : ‖reluProfile a s b‖ ≤ ‖q‖ := by
    apply Lp.norm_le_norm_of_ae_le
    filter_upwards [reluProfile_coeFn a s b,
      MemLp.coeFn_toLp (memLp_polyEval_gaussian P)] with t h1 h2
    rw [h1, h2, Real.norm_eq_abs, Real.norm_eq_abs]
    dsimp [reluProfileFun, P]
    simp only [Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_mul,
      Polynomial.eval_X]
    rw [abs_mul]
    calc
      |a| * |relu (s * t + b)| ≤ |a| * |s * t + b| :=
        mul_le_mul_of_nonneg_left (abs_relu_le_abs _) (abs_nonneg a)
      _ = |a * b + a * s * t| := by
        rw [← abs_mul]
        congr 1
        ring
  have hq : q = a • (b • hermiteL2 0 + s • hermiteL2 1) := by
    dsimp [q]
    change polyL2 P = _
    have hpoly : P = (a * b) • hR 0 + (a * s) • hR 1 := by
      dsimp [P]
      rw [hR_zero, hR_one, Polynomial.smul_eq_C_mul,
        Polynomial.smul_eq_C_mul, mul_one]
    rw [hpoly, map_add, map_smul, map_smul, polyL2_hR, polyL2_hR]
    module
  calc
    ‖reluProfile a s b‖ ≤ ‖q‖ := hnorm
    _ = |a| * ‖b • hermiteL2 0 + s • hermiteL2 1‖ := by
      rw [hq, norm_smul, Real.norm_eq_abs]
    _ ≤ |a| * (‖b • hermiteL2 0‖ + ‖s • hermiteL2 1‖) := by
      gcongr
      exact norm_add_le _ _
    _ = |a| * (s + |b|) := by
      rw [norm_smul, norm_smul, norm_hermiteL2_zero, norm_hermiteL2_one,
        mul_one, mul_one, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hs]
      ring

/-! ### A depth-2 network as a finite sum of ridges -/

def unitAxis (d : ℕ) (hd : 0 < d) : Vec d :=
  EuclideanSpace.single (⟨0, hd⟩ : Fin d) 1

lemma norm_unitAxis (d : ℕ) (hd : 0 < d) : ‖unitAxis d hd‖ = 1 := by
  rw [unitAxis, PiLp.norm_single, norm_one]

/-- Normalize a nonzero input weight; for a zero weight choose a fixed unit
axis. -/
def Net2.direction {d : ℕ} (N : Net2 d) (hd : 0 < d) (i : Fin N.width) : Vec d :=
  if N.w i = 0 then unitAxis d hd else ‖N.w i‖⁻¹ • N.w i

lemma Net2.norm_direction {d : ℕ} (N : Net2 d) (hd : 0 < d) (i : Fin N.width) :
    ‖N.direction hd i‖ = 1 := by
  rw [Net2.direction]
  split_ifs with hi
  · exact norm_unitAxis d hd
  · exact norm_smul_inv_norm hi

lemma Net2.inner_weight_eq {d : ℕ} (N : Net2 d) (hd : 0 < d)
    (i : Fin N.width) (x : Vec d) :
    ⟪N.w i, x⟫ = ‖N.w i‖ * ⟪N.direction hd i, x⟫ := by
  rw [Net2.direction]
  split_ifs with hi
  · rw [hi, inner_zero_left, norm_zero, zero_mul]
  · rw [real_inner_smul_left]
    have hn : ‖N.w i‖ ≠ 0 := norm_ne_zero_iff.mpr hi
    rw [← mul_assoc, mul_inv_cancel₀ hn, one_mul]

def Net2.profile {d : ℕ} (N : Net2 d) (i : Fin N.width) : L2R :=
  reluProfile (N.a i) ‖N.w i‖ (N.b i)

lemma Net2.norm_profile_le {d : ℕ} (N : Net2 d) (i : Fin N.width) :
    ‖N.profile i‖ ≤ |N.a i| * (‖N.w i‖ + |N.b i|) :=
  norm_reluProfile_le _ _ _ (norm_nonneg _)

/-- The `L²(γ^d)` class represented by a depth-2 network. -/
def Net2.asL2 {d : ℕ} (N : Net2 d) (hd : 0 < d) : L2 d :=
  ∑ i, ridge (N.direction hd i) (N.norm_direction hd i) (N.profile i)

lemma Net2.ridge_profile_coeFn {d : ℕ} (N : Net2 d) (hd : 0 < d)
    (i : Fin N.width) :
    ⇑(ridge (N.direction hd i) (N.norm_direction hd i) (N.profile i))
      =ᵐ[γ d] fun x => N.a i * relu (⟪N.w i, x⟫ + N.b i) := by
  have hp : (⇑(N.profile i)) ∘ ridgeMap (N.direction hd i) =ᵐ[γ d]
      (reluProfileFun (N.a i) ‖N.w i‖ (N.b i)) ∘
        ridgeMap (N.direction hd i) := by
    refine MeasureTheory.ae_eq_comp
      (measurePreserving_ridgeMap (N.norm_direction hd i)).aemeasurable ?_
    rw [(measurePreserving_ridgeMap (N.norm_direction hd i)).map_eq]
    exact reluProfile_coeFn _ _ _
  filter_upwards [ridge_coeFn (N.direction hd i) (N.norm_direction hd i)
    (N.profile i), hp] with x h1 h2
  rw [h1, h2]
  dsimp [reluProfileFun, ridgeMap]
  rw [← N.inner_weight_eq hd i x]

/-- The finite ridge sum agrees almost everywhere with the original network
evaluation. -/
theorem Net2.asL2_coeFn {d : ℕ} (N : Net2 d) (hd : 0 < d) :
    ⇑(N.asL2 hd) =ᵐ[γ d] N.eval := by
  let f : Fin N.width → L2 d := fun i =>
    ridge (N.direction hd i) (N.norm_direction hd i) (N.profile i)
  have hall : ∀ᵐ x ∂(γ d), ∀ i ∈ (Finset.univ : Finset (Fin N.width)),
      f i x = N.a i * relu (⟪N.w i, x⟫ + N.b i) :=
    (Filter.eventually_all_finset Finset.univ).mpr fun i _ =>
      N.ridge_profile_coeFn hd i
  filter_upwards [coeFn_finsetSum_Lp (Finset.univ : Finset (Fin N.width)) f,
    hall] with x hsum hx
  rw [Net2.asL2, Net2.eval]
  simpa [f] using hsum.trans (Finset.sum_congr rfl fun i hi => hx i hi)

/-- Under a uniform parameter bound `B ≥ 1`, every neuron profile has the
paper's bound `2B²`. -/
lemma Net2.norm_profile_le_two_mul_sq {d : ℕ} (N : Net2 d) {B : ℝ}
    (hB : 1 ≤ B) (hwt : N.WeightsLe B) (i : Fin N.width) :
    ‖N.profile i‖ ≤ 2 * B ^ 2 := by
  have hB0 : 0 ≤ B := by linarith
  calc
    ‖N.profile i‖ ≤ |N.a i| * (‖N.w i‖ + |N.b i|) := N.norm_profile_le i
    _ ≤ B * (B + B) := by
      gcongr
      · exact hwt.2.2 i
      · exact hwt.1 i
      · exact hwt.2.1 i
    _ = 2 * B ^ 2 := by ring

/-- Concrete depth-2 ReLU corollary of the exponential lower bound. -/
theorem depth_separation_lower_net2 (d : ℕ) (hde : Even d) (hd : 16 ≤ d)
    (N : Net2 d) {B : ℝ} (hB : 1 ≤ B) (hwt : N.WeightsLe B)
    (happrox : ‖sepTarget d - N.asL2
      (by omega)‖ ^ 2 ≤
        cEnergy ^ 2 / 2) :
    cEnergy * 2 ^ ((d : ℝ) / 4) / (8 * B ^ 2) ≤ (N.width : ℝ) := by
  let hdpos : 0 < d := by omega
  have hlb := depth_separation_lower d hde hd
    (g := fun i => N.profile i)
    (v := fun i => N.direction hdpos i)
    (hv := fun i => N.norm_direction hdpos i)
    (M := 2 * B ^ 2) (by positivity)
    (fun i => N.norm_profile_le_two_mul_sq hB hwt i) happrox
  convert hlb using 1
  all_goals ring

end

end GaussianDepthSeparation
