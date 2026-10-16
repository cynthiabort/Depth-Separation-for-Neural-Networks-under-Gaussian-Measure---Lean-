/-
GaussianDepthSeparation — ReLU network formalism (for Theorem 1.3(ii)).

Self-contained, finite-dimensional definitions: `relu`, depth-3 networks
(two hidden ReLU layers, no output bias), evaluation, width and weight bounds.
No measure theory.
-/
import GaussianDepthSeparation.Euclidean
import Mathlib.Tactic.FunProp

namespace GaussianDepthSeparation

open scoped RealInnerProductSpace

noncomputable section

/-- The rectified linear unit `relu(t) = max(t,0)`. -/
def relu (t : ℝ) : ℝ := max t 0

lemma relu_nonneg (t : ℝ) : 0 ≤ relu t := le_max_right _ _

lemma lipschitzWith_relu : LipschitzWith 1 relu :=
  LipschitzWith.id.max_const 0

@[fun_prop]
lemma continuous_relu : Continuous relu :=
  lipschitzWith_relu.continuous

/-- A **depth-3 ReLU network** on `ℝ^d`, exactly as displayed in the paper:
two hidden ReLU layers (`n1`, `n2` units) and no output bias.
`eval x = ∑ₖ aₖ·relu(b2ₖ + ∑ⱼ w2ₖⱼ·relu(⟨w1ⱼ,x⟩ + b1ⱼ))`. -/
structure Net3 (d : ℕ) where
  n1 : ℕ
  n2 : ℕ
  w1 : Fin n1 → Vec d
  b1 : Fin n1 → ℝ
  w2 : Fin n2 → Fin n1 → ℝ
  b2 : Fin n2 → ℝ
  a : Fin n2 → ℝ

/-- Network evaluation. -/
def Net3.eval {d : ℕ} (N : Net3 d) (x : Vec d) : ℝ :=
  ∑ k, N.a k * relu (N.b2 k + ∑ j, N.w2 k j * relu (⟪N.w1 j, x⟫ + N.b1 j))

theorem Net3.continuous_eval {d : ℕ} (N : Net3 d) : Continuous N.eval := by
  unfold Net3.eval
  fun_prop

/-- All parameters of the network are bounded by `B` in absolute value
(first-layer weight vectors in Euclidean norm). -/
def Net3.WeightsLe {d : ℕ} (N : Net3 d) (B : ℝ) : Prop :=
  (∀ j, ‖N.w1 j‖ ≤ B) ∧ (∀ j, |N.b1 j| ≤ B) ∧ (∀ k j, |N.w2 k j| ≤ B) ∧
    (∀ k, |N.b2 k| ≤ B) ∧ ∀ k, |N.a k| ≤ B

/-- Weight bounds are monotone in the bound. -/
lemma Net3.WeightsLe.mono {d : ℕ} {N : Net3 d} {B B' : ℝ} (h : N.WeightsLe B)
    (hB : B ≤ B') : N.WeightsLe B' :=
  ⟨fun j => (h.1 j).trans hB, fun j => (h.2.1 j).trans hB,
    fun k j => (h.2.2.1 k j).trans hB, fun k => (h.2.2.2.1 k).trans hB,
    fun k => (h.2.2.2.2 k).trans hB⟩

end

end GaussianDepthSeparation
