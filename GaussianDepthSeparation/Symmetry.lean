/-
Orthogonal transformations, radial invariance, and isometric ridge embeddings.
-/
import GaussianDepthSeparation.GaussianSpace
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule

namespace GaussianDepthSeparation

open MeasureTheory ProbabilityTheory Real
open scoped RealInnerProductSpace

noncomputable section

/-! ## Rotations: the orthogonal group `O(d)` and its action on `L²(γ^d)` -/

/-- The orthogonal group `O(d)`, realized as the unitary group of the algebra of
continuous linear endomorphisms of `ℝ^d` (star = Hilbert adjoint). -/
instance (d : ℕ) : ContinuousStar (Vec d →L[ℝ] Vec d) where
  continuous_star := ContinuousLinearMap.adjoint.continuous

abbrev Od (d : ℕ) := unitary (Vec d →L[ℝ] Vec d)

/-- The action of `U ∈ O(d)` on `ℝ^d`: `x ↦ Ux`. -/
def actMap {d : ℕ} (U : Od d) : Vec d → Vec d := fun x => (U : Vec d →L[ℝ] Vec d) x

/-- Orthogonal maps preserve the Gaussian: `Ux ∼ γ^d` for `x ∼ γ^d`.
A unitary of `ℝ^d →L ℝ^d` is a linear isometry equivalence
(`Unitary.linearIsometryEquiv`), and `stdGaussian` is invariant under those
(`ProbabilityTheory.stdGaussian_map`). -/
theorem measurePreserving_actMap {d : ℕ} (U : Od d) :
    MeasurePreserving (actMap U) (γ d) (γ d) := by
  refine ⟨(U : Vec d →L[ℝ] Vec d).continuous.measurable, ?_⟩
  have h := stdGaussian_map (Unitary.linearIsometryEquiv (𝕜 := ℝ) U)
  rw [γ]
  convert h using 2
  ext x
  rfl

/-- `T_U f = f(U·)`, the composition operator on `L²(γ^d)`, as a linear isometry
(grounded in `Lp.compMeasurePreservingₗᵢ`; its laws are theorems). -/
def act {d : ℕ} (U : Od d) : L2 d →ₗᵢ[ℝ] L2 d :=
  Lp.compMeasurePreservingₗᵢ (𝕜 := ℝ) (actMap U) (measurePreserving_actMap U)

/-- LaTeX — `main.tex` §2 (inside proof of Lemma 2.2): "The map $T_U f = f\circ U$ is
unitary on $L^2(\gamma^d)$". Norm preservation is definitional for `act`. -/
@[simp] lemma act_norm {d : ℕ} (U : Od d) (f : L2 d) : ‖act U f‖ = ‖f‖ :=
  (act U).norm_map f

/-- A function `f ∈ L²(γ^d)` is **radial** iff it is invariant under every rotation. -/
def IsRadial {d : ℕ} (f : L2 d) : Prop := ∀ U : Od d, act U f = f

/-- The subspace of radial functions. -/
def radialSub (d : ℕ) : Submodule ℝ (L2 d) where
  carrier := {f | IsRadial f}
  add_mem' := fun ha hb U => by rw [map_add, ha U, hb U]
  zero_mem' := fun U => map_zero _
  smul_mem' := fun c f hf U => by rw [map_smul, hf U]

@[simp] lemma mem_radialSub {d : ℕ} {f : L2 d} : f ∈ radialSub d ↔ IsRadial f := Iff.rfl

/-- The radial subspace is closed (an intersection of equalizers of isometries). -/
theorem isClosed_radialSub (d : ℕ) : IsClosed ((radialSub d : Set (L2 d))) := by
  have h : (radialSub d : Set (L2 d)) = ⋂ U : Od d, {f | act U f = f} := by
    ext f; simp only [SetLike.mem_coe, mem_radialSub, Set.mem_iInter, Set.mem_ofPred_eq]; rfl
  rw [h]
  exact isClosed_iInter fun U =>
    isClosed_eq (act U).continuous continuous_id

instance (d : ℕ) : CompleteSpace (radialSub d) :=
  (isClosed_radialSub d).completeSpace_coe

/-! ## Ridge functions

LaTeX — `main.tex` §3: "For $g \in L^2(\gamma)$ and $v \in S^{d-1}$, define
$g^v(x) = g(\langle v, x\rangle)$.  If $X \sim \gamma^d$, then
$\langle v, X\rangle \sim \gamma$, so $\|g^v\|_{L^2(\gamma^d)} = \|g\|_{L^2(\gamma)}$."
-/

/-- The scalar projection `x ↦ ⟨v,x⟩`. -/
def ridgeMap {d : ℕ} (v : Vec d) : Vec d → ℝ := fun x => ⟪v, x⟫

/-- For a unit vector `v`, `⟨v,X⟩ ∼ γ` when `X ∼ γ^d`: `⟨v,·⟩` is a continuous
linear functional of norm 1, and the pushforward of a Gaussian measure by a
functional is the 1-D Gaussian with its mean and variance
(`IsGaussian.map_eq_gaussianReal` + `variance_dual_stdGaussian`). -/
theorem measurePreserving_ridgeMap {d : ℕ} {v : Vec d} (hv : ‖v‖ = 1) :
    MeasurePreserving (ridgeMap v) (γ d) γ₁ := by
  have hfun : ridgeMap v = ⇑(innerSL ℝ v) := rfl
  refine ⟨by rw [hfun]; exact (innerSL ℝ v).continuous.measurable, ?_⟩
  rw [hfun, γ, γ₁, IsGaussian.map_eq_gaussianReal (innerSL ℝ v)]
  have hmean : (stdGaussian (Vec d))[⇑(innerSL ℝ v)] = 0 :=
    integral_strongDual_stdGaussian (innerSL ℝ v)
  have hvar : Var[⇑(innerSL ℝ v); stdGaussian (Vec d)] = 1 := by
    rw [variance_dual_stdGaussian (innerSL ℝ v), innerSL_apply_norm, hv, one_pow]
  rw [hmean, hvar]
  norm_num

/-- `g ↦ g^v = g(⟨v,·⟩)`, the ridge embedding, as a linear isometry
`L²(γ) → L²(γ^d)` (so `‖g^v‖ = ‖g‖` is a theorem). -/
def ridge {d : ℕ} (v : Vec d) (hv : ‖v‖ = 1) : L2R →ₗᵢ[ℝ] L2 d :=
  Lp.compMeasurePreservingₗᵢ (𝕜 := ℝ) (ridgeMap v) (measurePreserving_ridgeMap hv)

@[simp] lemma ridge_norm {d : ℕ} (v : Vec d) (hv : ‖v‖ = 1) (g : L2R) :
    ‖ridge v hv g‖ = ‖g‖ := (ridge v hv).norm_map g

end

end GaussianDepthSeparation
