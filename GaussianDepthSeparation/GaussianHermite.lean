/-
Gaussian polynomial analysis: multi-indices, Hermite functions, Stein's identity,
moments, and tensor orthogonality.
-/
import GaussianDepthSeparation.GaussianSpace
import Mathlib.RingTheory.Polynomial.Hermite.Basic
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Data.Finset.NatAntidiagonal
import Mathlib.Data.Fin.Tuple.NatAntidiagonal
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace GaussianDepthSeparation

open MeasureTheory ProbabilityTheory Polynomial Real
open scoped RealInnerProductSpace ENNReal Nat

noncomputable section

/-! ## Multi-index vocabulary

LaTeX — `paper.tex` §2: "For $\alpha = (\alpha_1, \ldots, \alpha_d) \in
\mathbb{N}^d$, set $H_\alpha(x) = \prod_{i=1}^d h_{\alpha_i}(x_i)$,
$\alpha! = \prod_{i=1}^d \alpha_i!$, $|\alpha| = \sum_{i=1}^d \alpha_i$."
-/

/-- Multi-indices `α ∈ ℕ^d`. -/
abbrev MIdx (d : ℕ) := Fin d → ℕ

/-- `|α| = ∑ᵢ αᵢ`. -/
def mdeg {d : ℕ} (α : MIdx d) : ℕ := ∑ i, α i

/-- `α! = ∏ᵢ αᵢ!`. -/
def mfact {d : ℕ} (α : MIdx d) : ℕ := ∏ i, (α i)!

/-- `v^α = ∏ᵢ vᵢ^{αᵢ}` (for `v ∈ ℝ^d`). -/
def mpow {d : ℕ} (v : Vec d) (α : MIdx d) : ℝ := ∏ i, v i ^ α i

/-- `α/2` (entrywise floor-halves; used only on even multi-indices). -/
def halfIdx {d : ℕ} (α : MIdx d) : MIdx d := fun i => α i / 2

/-- The finite set `{α ∈ ℕ^d : |α| = n}`. -/
def idxOf (d n : ℕ) : Finset (MIdx d) := Finset.Nat.antidiagonalTuple d n

@[simp] lemma mem_idxOf {d n : ℕ} {α : MIdx d} : α ∈ idxOf d n ↔ mdeg α = n := by
  simp [idxOf, Finset.Nat.mem_antidiagonalTuple, mdeg]

/-- The finite set `{α ∈ ℕ^d : |α| < n₀}`. -/
def idxLt (d n₀ : ℕ) : Finset (MIdx d) := (Finset.range n₀).biUnion (idxOf d)

@[simp] lemma mem_idxLt {d n₀ : ℕ} {α : MIdx d} : α ∈ idxLt d n₀ ↔ mdeg α < n₀ := by
  simp [idxLt]

lemma mfact_pos {d : ℕ} (α : MIdx d) : 0 < mfact α :=
  Finset.prod_pos fun i _ => Nat.factorial_pos (α i)

lemma mfact_ne_zero {d : ℕ} (α : MIdx d) : (mfact α : ℝ) ≠ 0 :=
  Nat.cast_ne_zero.mpr (mfact_pos α).ne'

/-! ## Hermite functions

LaTeX — `paper.tex` §2: "We use the probabilists' Hermite polynomials,
normalized by $\langle h_m, h_n\rangle_{L^2(\gamma)} = m!\,\delta_{mn}$."
Grounded in `Polynomial.hermite` (which satisfies
`hermite (n+1) = X * hermite n - derivative (hermite n)`).
-/

/-- The probabilists' Hermite polynomial `h_n` as a real function. -/
def hfun (n : ℕ) (t : ℝ) : ℝ := ((hermite n).map (Int.castRingHom ℝ)).eval t

/-- The tensor Hermite polynomial `H_α(x) = ∏ᵢ h_{αᵢ}(xᵢ)`. -/
def Hfun {d : ℕ} (α : MIdx d) (x : Vec d) : ℝ := ∏ i, hfun (α i) (x i)

/-- `h_n` as a real polynomial (base change of `Polynomial.hermite`). -/
def hR (n : ℕ) : Polynomial ℝ := (hermite n).map (Int.castRingHom ℝ)

lemma hfun_eq_hR_eval (n : ℕ) (t : ℝ) : hfun n t = (hR n).eval t := rfl

@[simp] lemma hfun_zero (t : ℝ) : hfun 0 t = 1 := by simp [hfun, hermite_zero]

@[simp] lemma hfun_one (t : ℝ) : hfun 1 t = t := by simp [hfun]

/-! ### One-dimensional Gaussian analysis (M2): integrability, Stein's identity,
Hermite recurrences, orthogonality -/

section GaussianAnalysis1D

open Filter

/-- The Gaussian density solves `(pdf)' = −t·pdf`. -/
lemma hasDerivAt_gaussianPDFReal (t : ℝ) :
    HasDerivAt (gaussianPDFReal 0 1) (-t * gaussianPDFReal 0 1 t) t := by
  have hfeq : gaussianPDFReal 0 1 = fun s => (Real.sqrt (2 * π))⁻¹ * Real.exp (-s ^ 2 / 2) :=
    funext gaussianPDFReal_zero_one
  rw [hfeq]
  have h1 : HasDerivAt (fun s : ℝ => -s ^ 2 / 2) (-t) t := by
    have h := ((hasDerivAt_pow 2 t).neg).div_const 2
    have he : -(((2 : ℕ) : ℝ) * t ^ (2 - 1)) / 2 = -t := by push_cast; ring_nf
    rwa [he] at h
  have h3 := (h1.exp).const_mul (Real.sqrt (2 * π))⁻¹
  have he : (Real.sqrt (2 * π))⁻¹ * (Real.exp (-t ^ 2 / 2) * -t)
      = -t * ((Real.sqrt (2 * π))⁻¹ * Real.exp (-t ^ 2 / 2)) := by ring
  rwa [he] at h3

/-- `t^k · exp(−bt²)` is Lebesgue-integrable (natural-power form of
`integrable_rpow_mul_exp_neg_mul_sq`). -/
lemma integrable_pow_mul_gaussian_exp {b : ℝ} (hb : 0 < b) (k : ℕ) :
    Integrable fun x : ℝ => x ^ k * Real.exp (-b * x ^ 2) := by
  have h := integrable_rpow_mul_exp_neg_mul_sq hb
    (s := (k : ℝ)) (lt_of_lt_of_le neg_one_lt_zero (Nat.cast_nonneg k))
  refine h.congr (ae_of_all _ fun x => ?_)
  simp only [Real.rpow_natCast]

/-- `|t|^k` × Gaussian density is Lebesgue-integrable. -/
lemma integrable_abs_pow_mul_gaussianPDF (k : ℕ) :
    Integrable (fun t : ℝ => |t| ^ k * gaussianPDFReal 0 1 t) := by
  have h := ((integrable_pow_mul_gaussian_exp (b := 1/2) (by norm_num) k).abs).const_mul
    (Real.sqrt (2 * π))⁻¹
  refine h.congr (ae_of_all _ fun t => ?_)
  simp only [gaussianPDFReal_zero_one]
  rw [abs_mul, abs_pow, abs_of_nonneg (Real.exp_pos _).le]
  have he : -(1/2) * t ^ 2 = -t ^ 2 / 2 := by ring
  rw [he]; ring

/-- Polynomial × Gaussian density is Lebesgue-integrable. -/
lemma integrable_polyMul_gaussianPDF (P : Polynomial ℝ) :
    Integrable (fun t => P.eval t * gaussianPDFReal 0 1 t) := by
  classical
  have hbound : ∀ t : ℝ, ‖P.eval t * gaussianPDFReal 0 1 t‖ ≤
      ∑ k ∈ Finset.range (P.natDegree + 1),
        |P.coeff k| * (|t| ^ k * gaussianPDFReal 0 1 t) := by
    intro t
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (gaussianPDFReal_nonneg 0 1 t)]
    have h1 : |P.eval t| ≤ ∑ k ∈ Finset.range (P.natDegree + 1), |P.coeff k| * |t| ^ k := by
      conv_lhs => rw [Polynomial.eval_eq_sum_range]
      refine (Finset.abs_sum_le_sum_abs _ _).trans_eq ?_
      exact Finset.sum_congr rfl fun k _ => by rw [abs_mul, abs_pow]
    calc |P.eval t| * gaussianPDFReal 0 1 t
        ≤ (∑ k ∈ Finset.range (P.natDegree + 1), |P.coeff k| * |t| ^ k) *
            gaussianPDFReal 0 1 t := by
          exact mul_le_mul_of_nonneg_right h1 (gaussianPDFReal_nonneg 0 1 t)
      _ = ∑ k ∈ Finset.range (P.natDegree + 1),
            |P.coeff k| * (|t| ^ k * gaussianPDFReal 0 1 t) := by
          rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun k _ => by ring
  refine (integrable_finsetSum _ fun k _ =>
      (integrable_abs_pow_mul_gaussianPDF k).const_mul _).mono' ?_ (ae_of_all _ hbound)
  exact (P.continuous.aestronglyMeasurable).mul
    ((stronglyMeasurable_gaussianPDFReal 0 1).aestronglyMeasurable)

/-- Every polynomial is `γ`-integrable. -/
theorem integrable_polyEval_gaussian (P : Polynomial ℝ) :
    Integrable (fun t => P.eval t) γ₁ := by
  rw [γ₁, gaussianReal_of_var_ne_zero _ one_ne_zero,
    integrable_withDensity_iff (measurable_gaussianPDF 0 1)
      (ae_of_all _ fun _ => gaussianPDF_lt_top)]
  have : (fun t => P.eval t * (gaussianPDF 0 1 t).toReal)
      = fun t => P.eval t * gaussianPDFReal 0 1 t := by
    funext t; rw [toReal_gaussianPDF]
  rw [this]
  exact integrable_polyMul_gaussianPDF P

/-- Every real polynomial function is in `L²(γ)` — the Gaussian has all moments. -/
theorem memLp_polyEval_gaussian (P : Polynomial ℝ) :
    MemLp (fun t => P.eval t) 2 γ₁ := by
  rw [memLp_two_iff_integrable_sq (P.continuous.aestronglyMeasurable)]
  have : (fun t => P.eval t ^ 2) = fun t => (P ^ 2).eval t := by
    funext t; simp [pow_two]
  rw [this]
  exact integrable_polyEval_gaussian (P ^ 2)

theorem memLp_hfun (n : ℕ) : MemLp (hfun n) 2 γ₁ :=
  memLp_polyEval_gaussian (hR n)

/-- **Stein's identity** for polynomials: `𝔼[X·P(X)] = 𝔼[P'(X)]` under `γ`. -/
theorem stein_poly (P : Polynomial ℝ) :
    ∫ t, t * P.eval t ∂γ₁ = ∫ t, P.derivative.eval t ∂γ₁ := by
  have hderiv : ∀ t : ℝ, HasDerivAt (fun s => P.eval s * gaussianPDFReal 0 1 s)
      ((P.derivative.eval t - t * P.eval t) * gaussianPDFReal 0 1 t) t := by
    intro t
    have h := (P.hasDerivAt t).mul (hasDerivAt_gaussianPDFReal t)
    have he : P.derivative.eval t * gaussianPDFReal 0 1 t
        + P.eval t * (-t * gaussianPDFReal 0 1 t)
        = (P.derivative.eval t - t * P.eval t) * gaussianPDFReal 0 1 t := by ring
    rwa [he] at h
  have hint : Integrable
      (fun t => (P.derivative.eval t - t * P.eval t) * gaussianPDFReal 0 1 t) := by
    have hrw : (fun t => (P.derivative.eval t - t * P.eval t) * gaussianPDFReal 0 1 t)
        = fun t => (P.derivative - X * P).eval t * gaussianPDFReal 0 1 t := by
      funext t; simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_X]
    rw [hrw]
    exact integrable_polyMul_gaussianPDF _
  have hzero := integral_eq_zero_of_hasDerivAt_of_integrable hderiv hint
    (integrable_polyMul_gaussianPDF P)
  have hXP : Integrable (fun t => t * P.eval t * gaussianPDFReal 0 1 t) := by
    have hrw : (fun t => t * P.eval t * gaussianPDFReal 0 1 t)
        = fun t => (X * P).eval t * gaussianPDFReal 0 1 t := by
      funext t; simp only [Polynomial.eval_mul, Polynomial.eval_X]
    rw [hrw]; exact integrable_polyMul_gaussianPDF _
  have hD : Integrable (fun t => P.derivative.eval t * gaussianPDFReal 0 1 t) :=
    integrable_polyMul_gaussianPDF _
  have hsplit : ∫ t, (P.derivative.eval t - t * P.eval t) * gaussianPDFReal 0 1 t
      = (∫ t, P.derivative.eval t * gaussianPDFReal 0 1 t)
        - ∫ t, t * P.eval t * gaussianPDFReal 0 1 t := by
    rw [← integral_sub hD hXP]
    exact integral_congr_ae (ae_of_all _ fun t => by ring)
  rw [integral_gaussian_eq, integral_gaussian_eq]
  rw [hsplit] at hzero
  have := sub_eq_zero.mp hzero
  linarith [this]

/-- `(hermite n)' = n · hermite (n−1)` (by two-step induction; not in Mathlib). -/
theorem derivative_hermite (n : ℕ) :
    derivative (hermite n) = (n : Polynomial ℤ) * hermite (n - 1) := by
  induction n using Nat.twoStepInduction with
  | zero => simp [hermite_zero]
  | one => simp [hermite_zero]
  | more m ih ih1 =>
    show derivative (hermite (m + 1 + 1)) = ((m + 1 + 1 : ℕ) : Polynomial ℤ) * hermite (m + 1)
    have hs := hermite_succ m
    rw [hermite_succ (m + 1), derivative_sub, derivative_mul, derivative_X, one_mul, ih1,
      Nat.add_sub_cancel, derivative_mul, derivative_natCast, zero_mul, zero_add, hs]
    push_cast
    ring

@[simp] lemma hR_zero : hR 0 = 1 := by simp [hR, hermite_zero]

@[simp] lemma hR_one : hR 1 = X := by simp [hR]

lemma hR_succ (n : ℕ) : hR (n + 1) = X * hR n - derivative (hR n) := by
  rw [hR, hermite_succ, Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_X,
    ← Polynomial.derivative_map]
  rfl

lemma derivative_hR (n : ℕ) : derivative (hR n) = (n : Polynomial ℝ) * hR (n - 1) := by
  rw [hR, Polynomial.derivative_map, derivative_hermite, Polynomial.map_mul,
    Polynomial.map_natCast]
  rfl

/-- Lowering/adjoint identity: `⟨h_{n+1}, Q⟩_{L²(γ)} = ⟨h_n, Q'⟩_{L²(γ)}` for
polynomial `Q` (via Stein's identity). -/
theorem integral_hR_succ_mul (n : ℕ) (Q : Polynomial ℝ) :
    ∫ t, (hR (n + 1) * Q).eval t ∂γ₁ = ∫ t, (hR n * Q.derivative).eval t ∂γ₁ := by
  have h1 : hR (n + 1) * Q = X * (hR n * Q) - (derivative (hR n) * Q) := by
    rw [hR_succ]; ring
  have hstein := stein_poly (hR n * Q)
  have hD : (hR n * Q).derivative = derivative (hR n) * Q + hR n * Q.derivative :=
    Polynomial.derivative_mul
  rw [h1]
  have hsub : ∀ t : ℝ, (X * (hR n * Q) - derivative (hR n) * Q).eval t
      = t * (hR n * Q).eval t - (derivative (hR n) * Q).eval t := by
    intro t; simp [Polynomial.eval_sub, Polynomial.eval_mul]
  rw [integral_congr_ae (ae_of_all _ hsub)]
  have hXint : Integrable (fun t => t * (hR n * Q).eval t) γ₁ := by
    have hrw : (fun t => t * (hR n * Q).eval t) = fun t => (X * (hR n * Q)).eval t := by
      funext t; simp [Polynomial.eval_mul]
    rw [hrw]; exact integrable_polyEval_gaussian _
  rw [integral_sub hXint (integrable_polyEval_gaussian _), hstein, hD]
  have hadd : ∀ t : ℝ, (derivative (hR n) * Q + hR n * Q.derivative).eval t
      = (derivative (hR n) * Q).eval t + (hR n * Q.derivative).eval t := by
    intro t; simp [Polynomial.eval_add]
  rw [integral_congr_ae (ae_of_all _ hadd),
    integral_add (integrable_polyEval_gaussian _) (integrable_polyEval_gaussian _)]
  ring

/-- LaTeX — `paper.tex` §2: "$\langle h_m, h_n\rangle_{L^2(\gamma)} = m!\,\delta_{mn}$"
(as an integral identity). -/
theorem integral_hfun_mul_hfun (m n : ℕ) :
    ∫ t, hfun m t * hfun n t ∂γ₁ = if m = n then (m ! : ℝ) else 0 := by
  induction m generalizing n with
  | zero =>
    cases n with
    | zero => simp
    | succ k =>
      have h : ∫ t, hfun 0 t * hfun (k + 1) t ∂γ₁ = ∫ t, (hR (k + 1) * 1).eval t ∂γ₁ := by
        refine integral_congr_ae (ae_of_all _ fun t => ?_)
        simp [hfun_eq_hR_eval]
      rw [h, integral_hR_succ_mul k 1]
      simp
  | succ m ih =>
    cases n with
    | zero =>
      have h : ∫ t, hfun (m + 1) t * hfun 0 t ∂γ₁ = ∫ t, (hR (m + 1) * 1).eval t ∂γ₁ := by
        refine integral_congr_ae (ae_of_all _ fun t => ?_)
        simp [hfun_eq_hR_eval]
      rw [h, integral_hR_succ_mul m 1]
      simp
    | succ k =>
      have h : ∫ t, hfun (m + 1) t * hfun (k + 1) t ∂γ₁
          = ∫ t, (hR (m + 1) * hR (k + 1)).eval t ∂γ₁ := by
        refine integral_congr_ae (ae_of_all _ fun t => ?_)
        simp [hfun_eq_hR_eval]
      rw [h, integral_hR_succ_mul m (hR (k + 1))]
      have hd : hR m * derivative (hR (k + 1)) = C ((k : ℝ) + 1) * (hR m * hR k) := by
        rw [derivative_hR, Nat.add_sub_cancel, ← Polynomial.C_eq_natCast]
        push_cast
        ring
      rw [hd]
      have hsmul : ∀ t : ℝ, (C ((k : ℝ) + 1) * (hR m * hR k)).eval t
          = ((k : ℝ) + 1) * (hR m * hR k).eval t := by
        intro t; simp
      rw [integral_congr_ae (ae_of_all _ hsmul), integral_const_mul]
      have hmk : ∫ t, (hR m * hR k).eval t ∂γ₁ = if m = k then (m ! : ℝ) else 0 := by
        rw [← ih k]
        refine integral_congr_ae (ae_of_all _ fun t => ?_)
        simp [hfun_eq_hR_eval]
      rw [hmk]
      by_cases hcase : m = k
      · subst hcase
        simp only
        rw [Nat.factorial_succ]
        push_cast
        ring
      · simp [hcase]

/-- Gaussian moments: `∫ t^n dγ = (n−1)!!` for even `n`, `0` for odd `n`. -/
theorem integral_pow_gaussian (n : ℕ) :
    ∫ t, t ^ n ∂γ₁ = if Even n then ((n - 1)‼ : ℝ) else 0 := by
  induction n using Nat.twoStepInduction with
  | zero => simp
  | one =>
    have h := stein_poly (1 : Polynomial ℝ)
    simp only [Polynomial.eval_one, mul_one, Polynomial.derivative_one,
      Polynomial.eval_zero] at h
    have h1 : ∫ t, t ^ 1 ∂γ₁ = ∫ t, t * 1 ∂γ₁ := by
      refine integral_congr_ae (ae_of_all _ fun t => ?_); ring
    rw [h1]
    simpa [Nat.even_iff] using h
  | more n ih _ =>
    have hstein := stein_poly (X ^ (n + 1) : Polynomial ℝ)
    have hL : ∫ t, t ^ (n + 2) ∂γ₁ = ∫ t, t * (X ^ (n + 1) : Polynomial ℝ).eval t ∂γ₁ := by
      refine integral_congr_ae (ae_of_all _ fun t => ?_)
      simp [pow_succ]; ring
    have hR' : (X ^ (n + 1) : Polynomial ℝ).derivative = C ((n : ℝ) + 1) * X ^ n := by
      rw [Polynomial.derivative_X_pow, Nat.add_sub_cancel]
      norm_cast
    rw [hL, hstein, hR']
    have hsmul : ∀ t : ℝ, (C ((n : ℝ) + 1) * (X ^ n : Polynomial ℝ)).eval t
        = ((n : ℝ) + 1) * t ^ n := by intro t; simp
    rw [integral_congr_ae (ae_of_all _ hsmul), integral_const_mul, ih]
    have hpar : Even (n + 2) ↔ Even n := by
      constructor
      · intro h; rcases h with ⟨k, hk⟩; exact ⟨k - 1, by omega⟩
      · intro h; rcases h with ⟨k, hk⟩; exact ⟨k + 1, by omega⟩
    by_cases hcase : Even n
    · rw [ite_eq_left hcase, ite_eq_left (hpar.mpr hcase)]
      have hdf : ((n + 2 - 1)‼ : ℕ) = (n + 1) * (n - 1)‼ := by
        have : n + 2 - 1 = n + 1 := rfl
        rw [this]
        cases n with
        | zero => simp [Nat.doubleFactorial]
        | succ m =>
          have h1 : m + 1 + 1 = (m) + 2 := by omega
          rw [h1, Nat.doubleFactorial_add_two]
          congr 1
      rw [hdf]
      push_cast
      ring
    · rw [ite_eq_right hcase, ite_eq_right (fun hc => hcase (hpar.mp hc)), mul_zero]

end GaussianAnalysis1D

/-! ### Product-measure bridge: `γ^d` as the coordinate product (M2, tensor step) -/

section GaussianAnalysisPi

lemma continuous_Hfun {d : ℕ} (α : MIdx d) : Continuous (Hfun α) := by
  unfold Hfun
  refine continuous_finsetProd _ fun i _ => ?_
  have hcoord : Continuous fun x : Vec d => x i := by fun_prop
  exact ((hR (α i)).continuous).comp hcoord

/-- The tensor Hermite polynomial is in `L²(γ^d)`. -/
theorem memLp_Hfun {d : ℕ} (α : MIdx d) : MemLp (Hfun α) 2 (γ d) := by
  rw [memLp_two_iff_integrable_sq (continuous_Hfun α).aestronglyMeasurable,
    integrable_gaussD_iff_pi (fun x => Hfun α x ^ 2)
      (((continuous_Hfun α).pow 2).aestronglyMeasurable)]
  have hrw : (fun y : Fin d → ℝ => Hfun α (WithLp.toLp 2 y) ^ 2)
      = fun y => ∏ i, ((hR (α i)) ^ 2).eval (y i) := by
    funext y
    rw [Hfun, ← Finset.prod_pow]
    exact Finset.prod_congr rfl fun i _ => by
      simp [hfun_eq_hR_eval, pow_two]
  rw [hrw]
  exact Integrable.fintype_prod fun i => integrable_polyEval_gaussian ((hR (α i)) ^ 2)

/-- `h_n` as an element of `L²(γ)`. -/
def hermiteL2 (n : ℕ) : L2R := (memLp_hfun n).toLp

/-- `H_α` as an element of `L²(γ^d)`. -/
def HL2 {d : ℕ} (α : MIdx d) : L2 d := (memLp_Hfun α).toLp

/-- LaTeX — `paper.tex` §2:
"$\langle h_m, h_n\rangle_{L^2(\gamma)} = m!\,\delta_{mn}$." -/
theorem hermiteL2_inner (m n : ℕ) :
    ⟪hermiteL2 m, hermiteL2 n⟫ = if m = n then (m ! : ℝ) else 0 := by
  rw [← integral_hfun_mul_hfun m n, hermiteL2, hermiteL2, L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [MemLp.coeFn_toLp (memLp_hfun m), MemLp.coeFn_toLp (memLp_hfun n)]
    with t h1 h2
  rw [h1, h2, RCLike.inner_apply, conj_trivial]
  exact mul_comm _ _

/-- The `γ^d` inner product of tensor Hermites factors through coordinates. -/
theorem integral_Hfun_mul_Hfun {d : ℕ} (α β : MIdx d) :
    ∫ x, Hfun α x * Hfun β x ∂(γ d)
      = ∏ i, ∫ t, hfun (α i) t * hfun (β i) t ∂γ₁ := by
  rw [integral_gaussD_eq_pi (fun x => Hfun α x * Hfun β x)
    (((continuous_Hfun α).mul (continuous_Hfun β)).aestronglyMeasurable)]
  have hrw : (fun y : Fin d → ℝ => Hfun α (WithLp.toLp 2 y) * Hfun β (WithLp.toLp 2 y))
      = fun y => ∏ i, (fun t => hfun (α i) t * hfun (β i) t) (y i) := by
    funext y
    rw [Hfun, Hfun, ← Finset.prod_mul_distrib]
  rw [hrw]
  exact MeasureTheory.integral_fintype_prod_eq_prod
    (f := fun i (t : ℝ) => hfun (α i) t * hfun (β i) t)

/-- LaTeX — `paper.tex` §2:
"$\langle H_\alpha, H_\beta\rangle_{L^2(\gamma^d)} = \alpha!\,\delta_{\alpha\beta}$." -/
theorem HL2_inner {d : ℕ} (α β : MIdx d) :
    ⟪HL2 α, HL2 β⟫ = if α = β then (mfact α : ℝ) else 0 := by
  have hI : ⟪HL2 α, HL2 β⟫ = ∫ x, Hfun α x * Hfun β x ∂(γ d) := by
    rw [HL2, HL2, L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [MemLp.coeFn_toLp (memLp_Hfun α), MemLp.coeFn_toLp (memLp_Hfun β)]
      with x h1 h2
    rw [h1, h2, RCLike.inner_apply, conj_trivial]
    exact mul_comm _ _
  rw [hI, integral_Hfun_mul_Hfun]
  by_cases h : α = β
  · subst h
    rw [ite_eq_left rfl, mfact, Nat.cast_prod]
    exact Finset.prod_congr rfl fun i _ => by rw [integral_hfun_mul_hfun, ite_eq_left rfl]
  · rw [ite_eq_right h]
    obtain ⟨i, hi⟩ := Function.ne_iff.mp h
    exact Finset.prod_eq_zero (Finset.mem_univ i)
      (by rw [integral_hfun_mul_hfun, ite_eq_right hi])

end GaussianAnalysisPi

end

end GaussianDepthSeparation
