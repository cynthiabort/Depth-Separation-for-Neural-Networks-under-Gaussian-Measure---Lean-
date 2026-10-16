/-
Formal generating functions for the proof of manuscript Lemma 2.1.
All series below are formal power series: coefficient comparison requires
no analytic convergence assumptions.
-/
import GaussianDepthSeparation.GaussianHermite
import Mathlib.RingTheory.PowerSeries.Exp

namespace GaussianDepthSeparation

noncomputable section

/-- The standard three-term recurrence, used to establish the one-variable
generating function, independently of the ridge identity. -/
lemma hfun_succ_eq (n : ℕ) (z : ℝ) :
    hfun (n + 1) z = z * hfun n z - n * hfun (n - 1) z := by
  rw [hfun_eq_hR_eval, hR_succ, Polynomial.eval_sub, Polynomial.eval_mul,
    Polynomial.eval_X, derivative_hR, Polynomial.eval_mul, Polynomial.eval_natCast,
    hfun_eq_hR_eval, hfun_eq_hR_eval]

namespace HermiteGenerating

open PowerSeries
open scoped PowerSeries Nat

/-- Uniqueness for a formal first-order linear differential equation. -/
lemma ode_unique (a f g : PowerSeries ℝ)
    (hc : constantCoeff f = constantCoeff g)
    (hf : d⁄dX ℝ f = a * f) (hg : d⁄dX ℝ g = a * g) : f = g := by
  ext n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    cases n with
    | zero => simpa using hc
    | succ n =>
      apply mul_right_cancel₀ (by positivity : (n : ℝ) + 1 ≠ 0)
      rw [← coeff_derivative, ← coeff_derivative, hf, hg, coeff_mul, coeff_mul]
      apply Finset.sum_congr rfl
      intro p hp
      rw [ih p.2 (by have := Finset.mem_antidiagonal.mp hp; omega)]

/-- The exponential of a series with zero constant term. -/
def formalExp (p : PowerSeries ℝ) : PowerSeries ℝ := (exp ℝ).subst p

lemma constant_formalExp {p : PowerSeries ℝ} (hp : constantCoeff p = 0) :
    constantCoeff (formalExp p) = 1 := by
  rw [formalExp, ← coeff_zero_eq_constantCoeff,
    coeff_subst' (HasSubst.of_constantCoeff_zero' hp), finsum_eq_single _ 0]
  · simp
  · intro n hn
    rw [coeff_zero_eq_constantCoeff, map_pow, hp, zero_pow hn]
    simp

lemma derivative_formalExp {p : PowerSeries ℝ} (hp : constantCoeff p = 0) :
    d⁄dX ℝ (formalExp p) = (d⁄dX ℝ p) * formalExp p := by
  rw [formalExp, derivative_subst (HasSubst.of_constantCoeff_zero' hp), derivative_exp]
  exact mul_comm _ _

/-- The exponential addition law, hence the product identity used in the paper. -/
lemma formalExp_add {p q : PowerSeries ℝ}
    (hp : constantCoeff p = 0) (hq : constantCoeff q = 0) :
    formalExp (p + q) = formalExp p * formalExp q := by
  have hpq : constantCoeff (p + q) = 0 := by simp [hp, hq]
  apply ode_unique (d⁄dX ℝ (p + q))
  · simp [constant_formalExp hpq, constant_formalExp hp, constant_formalExp hq]
  · exact derivative_formalExp hpq
  · rw [(d⁄dX ℝ).leibniz, derivative_formalExp hp, derivative_formalExp hq, map_add]
    simp only [smul_eq_mul]
    ring

lemma formalExp_zero : formalExp 0 = 1 := by
  simp [formalExp, subst_zero_eq_C_constantCoeff]

lemma formalExp_sum {ι : Type*} (s : Finset ι) (p : ι → PowerSeries ℝ)
    (hp : ∀ i ∈ s, constantCoeff (p i) = 0) :
    formalExp (∑ i ∈ s, p i) = ∏ i ∈ s, formalExp (p i) := by
  classical
  induction s using Finset.induction with
  | empty => simp [formalExp_zero]
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.prod_insert hi, formalExp_add (hp i (by simp))
      (by rw [map_sum]; exact Finset.sum_eq_zero fun j hj => hp j (Finset.mem_insert_of_mem hj)),
      ih (fun j hj => hp j (Finset.mem_insert_of_mem hj))]

/-- `zX - X²/2`, the exponent in the probabilists' Hermite generating function. -/
def exponent (z : ℝ) : PowerSeries ℝ := C z * X - C (1 / 2 : ℝ) * X ^ 2

lemma constant_exponent (z : ℝ) : constantCoeff (exponent z) = 0 := by
  simp [exponent]

lemma derivative_exponent (z : ℝ) : d⁄dX ℝ (exponent z) = C z - X := by
  simp only [exponent, map_sub, (d⁄dX ℝ).leibniz, derivative_C, derivative_X,
    derivative_pow, smul_eq_mul, mul_zero, mul_one]
  norm_num
  rw [show (2 : PowerSeries ℝ) = C (2 : ℝ) from (map_ofNat _ 2).symm]
  rw [← mul_assoc, ← map_mul]
  norm_num

/-- `∑ hₙ(z) Xⁿ/n!`. -/
def series (z : ℝ) : PowerSeries ℝ := mk fun n => hfun n z / (n ! : ℝ)

lemma coeff_series (n : ℕ) (z : ℝ) : coeff n (series z) = hfun n z / (n ! : ℝ) :=
  coeff_mk _ _

lemma derivative_series (z : ℝ) : d⁄dX ℝ (series z) = (C z - X) * series z := by
  ext n
  rw [coeff_derivative, sub_mul, map_sub, coeff_C_mul]
  cases n with
  | zero => simp [series, hfun_succ_eq]
  | succ n =>
    rw [coeff_succ_X_mul]
    simp only [coeff_series, hfun_succ_eq, Nat.add_sub_cancel, Nat.factorial_succ,
      Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    have hn : (n ! : ℝ) ≠ 0 := by positivity
    have hn1 : (n : ℝ) + 1 ≠ 0 := by positivity
    have hn2 : (n : ℝ) + 1 + 1 ≠ 0 := by positivity
    field_simp

/-- The generating-function identity displayed at the start of Lemma 2.1. -/
theorem generating_function (z : ℝ) : formalExp (exponent z) = series z := by
  apply ode_unique (C z - X)
  · simp [constant_formalExp (constant_exponent z), series, constantCoeff_mk]
  · rw [derivative_formalExp (constant_exponent z), derivative_exponent]
  · exact derivative_series z

lemma rescale_formalExp (a : ℝ) {p : PowerSeries ℝ} (hp : constantCoeff p = 0) :
    rescale a (formalExp p) = formalExp (rescale a p) := by
  rw [rescale_eq_subst, formalExp, subst_comp_subst_apply
    (HasSubst.of_constantCoeff_zero' hp)
    (HasSubst.of_constantCoeff_zero' (by simp)), ← rescale_eq_subst]
  rfl

lemma rescale_constant (a b : ℝ) : rescale a (C b) = C b := by
  ext n
  simp only [coeff_rescale, coeff_C]
  split_ifs with hn <;> simp [hn]

lemma rescale_exponent (a z : ℝ) :
    rescale a (exponent z) = C (a * z) * X - C (a ^ 2 / 2) * X ^ 2 := by
  simp only [exponent, map_sub, map_mul, map_pow, rescale_constant, rescale_X]
  rw [mul_pow, ← map_pow]
  have h1 : C z * C a = C (a * z) := by rw [← map_mul, mul_comm]
  have h2 : C (1 / 2 : ℝ) * C (a ^ 2) = C (a ^ 2 / 2) := by
    rw [← map_mul]; congr 1; ring
  rw [← mul_assoc, h1, ← mul_assoc, h2]
  rw [map_mul]

/-- Product expansion followed by comparison of degree-`n` coefficients. -/
lemma coeff_prod_series {d : ℕ} (n : ℕ) (v x : Vec d) :
    coeff n (∏ i, rescale (v i) (series (x i))) =
      ∑ α ∈ idxOf d n, mpow v α * Hfun α x / (mfact α : ℝ) := by
  classical
  rw [coeff_prod]
  apply Finset.sum_nbij' (fun a : Fin d →₀ ℕ => (fun i => a i))
    (fun a : MIdx d => Finsupp.equivFunOnFinite.symm a)
  · intro a ha
    exact mem_idxOf.mpr (Finset.mem_finsuppAntidiag.mp ha).1
  · intro a ha
    exact Finset.mem_finsuppAntidiag.mpr ⟨mem_idxOf.mp ha, Finset.subset_univ _⟩
  · intro a _
    exact Finsupp.equivFunOnFinite.symm_apply_apply a
  · intro a _
    exact Finsupp.equivFunOnFinite.apply_symm_apply a
  · intro a _
    simp only [coeff_rescale, coeff_series, mpow, Hfun, mfact, Nat.cast_prod]
    rw [← Finset.prod_mul_distrib, ← Finset.prod_div_distrib]
    apply Finset.prod_congr rfl
    intro i _
    ring

end HermiteGenerating

end

end GaussianDepthSeparation
