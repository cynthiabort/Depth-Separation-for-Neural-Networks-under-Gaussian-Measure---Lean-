/-
GaussianDepthSeparation — Corollary 1.2 of `main.tex` (polynomial criterion for the ridge lower
bound).
-/
import GaussianDepthSeparation.LowerBound
import GaussianDepthSeparation.RadialDistance

namespace GaussianDepthSeparation

open MeasureTheory ProbabilityTheory Real Set Polynomial
open scoped RealInnerProductSpace

noncomputable section

/- LaTeX — `main.tex`, Corollary 1.2:
"Let $d\ge2$ and let $n_0\ge2$ be even. Let $F\in L^2(\gamma^d)$ be such
that $F(x)=\phi(\|x\|^2/d)$ for some $\phi$ and suppose that
$\inf_{q\in\mathbb R[t],\ \deg q<n_0/2}\int_0^\infty(\phi(t)-q(t))^2\rho_d(t)\,dt
\ge a^2>0$.
Let $M>0$, and let $g_1,\ldots,g_r\in L^2(\gamma)$ and $v_1,\ldots,v_r\in S^{d-1}$
satisfy $\|g_j\|_{L^2(\gamma)}\le M$. If
$\|F-\sum_j g_j(\langle v_j,\cdot\rangle)\|^2\le a^2/2$, then
$r\ge\frac{a}{4M\sqrt{K_{n_0}}}$."

In Lean, `φ` is taken measurable (so that the integral is meaningful) and the
identity `F(x) = φ(‖x‖²/d)` holds `γ^d`-almost everywhere, as for any element
of `L²`.  Polynomials of degree `< n₀/2` are `Polynomial.degreeLT ℝ (n₀/2)`.
-/
/-- **Corollary 1.2 (Polynomial criterion).** -/
theorem polynomial_criterion {d : ℕ} (hd : 2 ≤ d) {n₀ : ℕ} (hn₀e : Even n₀)
    (hn₀ : 2 ≤ n₀) (F : L2 d) (φ : ℝ → ℝ) (hφ : Measurable φ)
    (hF : ⇑F =ᵐ[γ d] fun x => φ (‖x‖ ^ 2 / d)) {a : ℝ} (ha : 0 < a)
    (hinf : a ^ 2 ≤ ⨅ q : Polynomial.degreeLT ℝ (n₀ / 2),
      ∫ t in Ioi (0 : ℝ), (φ t - (q : Polynomial ℝ).eval t) ^ 2 * chiSqDensity d t)
    {M : ℝ} (hM : 0 < M) {r : ℕ} (g : Fin r → L2R) (v : Fin r → Vec d)
    (hv : ∀ j, ‖v j‖ = 1) (hgM : ∀ j, ‖g j‖ ≤ M)
    (happrox : ‖F - ∑ j, ridge (v j) (hv j) (g j)‖ ^ 2 ≤ a ^ 2 / 2) :
    a / (4 * M * Real.sqrt (Kmom d n₀)) ≤ (r : ℝ) := by
  have hd0 : 0 < d := by omega
  have hrad : IsRadial F := isRadial_of_coeFn_eq F φ hF
  -- the hypothesis says exactly that `A = ‖P_{≥n₀}F‖ ≥ a` (Lemma 5.1)
  have hA : a ^ 2 ≤ ‖Pge d n₀ F‖ ^ 2 := by
    rw [radial_polynomial_distance d hd0 n₀ hn₀e hn₀ F φ hφ hF]
    exact hinf
  have haA : a ≤ ‖Pge d n₀ F‖ :=
    (pow_le_pow_iff_left₀ ha.le (norm_nonneg _) two_ne_zero).mp hA
  -- Theorem 1.1
  have happrox' : ‖F - ∑ j, ridge (v j) (hv j) (g j)‖ ^ 2 ≤ ‖Pge d n₀ F‖ ^ 2 / 2 :=
    happrox.trans (by linarith)
  have hlb := ridge_lower_bound hd0 hn₀e F hrad g v hv hM hgM happrox'
  exact (div_le_div_of_nonneg_right haA (by positivity)).trans hlb

end

end GaussianDepthSeparation
