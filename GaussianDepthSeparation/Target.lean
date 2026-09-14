/-
The radial sine family and the target in the depth-separation theorem.
-/
import GaussianDepthSeparation.GaussianSpace

namespace GaussianDepthSeparation

open MeasureTheory Real
open scoped RealInnerProductSpace

noncomputable section

/-! ## The radial sine target

LaTeX — `paper.tex` §5: "For parameters $d, m > 0$, define the radial function
$F(x) = \sin\!\left(\pi m\,\frac{\|x\|^2}{d}\right)$ … well-defined in
$L^2(\gamma^d)$ since $|F| \le 1$."
-/

theorem memLp_radialSineFun (d : ℕ) (m : ℝ) :
    MemLp (fun x : Vec d => Real.sin (π * m * ‖x‖ ^ 2 / d)) 2 (γ d) := by
  refine MemLp.of_bound ?_ 1 (Filter.Eventually.of_forall fun x => ?_)
  · exact (Real.continuous_sin.comp (by fun_prop)).aestronglyMeasurable
  · simpa [Real.norm_eq_abs] using Real.abs_sin_le_one _

/-- `F(x) = sin(π m ‖x‖²/d)` as an element of `L²(γ^d)`. -/
def radialSine (d : ℕ) (m : ℝ) : L2 d := (memLp_radialSineFun d m).toLp

/-- LaTeX — `paper.tex`, Theorem 1.2: "$F(x) = \sin\!\bigl(4\pi d^{1/2}\|x\|^2\bigr)$",
i.e. `radialSine` with `m = 4d^{3/2}`. -/
def sepTarget (d : ℕ) : L2 d := radialSine d (4 * d * Real.sqrt d)

/-- The target from Theorem 1.2 in its displayed pointwise form. -/
theorem sepTarget_coeFn (d : ℕ) (hd : 0 < d) :
    (sepTarget d : Vec d → ℝ) =ᵐ[γ d]
      fun x => Real.sin (4 * π * Real.sqrt d * ‖x‖ ^ 2) := by
  have hdne : (d : ℝ) ≠ 0 := by positivity
  filter_upwards [MemLp.coeFn_toLp
    (memLp_radialSineFun d (4 * d * Real.sqrt d))] with x hx
  rw [show (sepTarget d : Vec d → ℝ) x =
      Real.sin (π * (4 * d * Real.sqrt d) * ‖x‖ ^ 2 / d) from hx]
  congr 1
  field_simp

end

end GaussianDepthSeparation
