/-
GaussianDepthSeparation §2 — chaos-space structure: the L² form of Lemma 2.1, the ridge-Hermite
span of the chaos spaces, and Lemma 2.2 (rotation invariance of the chaos
projections).

Span argument (paper's proof of Lemma 2.2): a residual `r ∈ ℋ_n` orthogonal to
every ridge Hermite has coefficients `c_α` with `∑ c_α v^α = 0` on the unit
sphere; homogeneity extends this to all of `ℝ^d`, and `MvPolynomial.funext`
extracts `c_α = 0`.
-/
import GaussianDepthSeparation.Hermite
import Mathlib.Algebra.MvPolynomial.Funext

namespace GaussianDepthSeparation

open MeasureTheory Polynomial
open scoped RealInnerProductSpace Nat ENNReal

noncomputable section

/-! ### `Lp` coeFn plumbing -/

/-- coeFn of a finite `Lp` sum. -/
lemma coeFn_finsetSum_Lp {ι α' E' : Type*} [NormedAddCommGroup E']
    {m : MeasurableSpace α'} {μ : Measure α'} {p : ℝ≥0∞}
    (s : Finset ι) (f : ι → Lp E' p μ) :
    ⇑(∑ i ∈ s, f i) =ᵐ[μ] fun x => ∑ i ∈ s, f i x := by
  induction s using Finset.cons_induction with
  | empty =>
    filter_upwards [Lp.coeFn_zero E' p μ] with x hx
    simpa using hx
  | cons i s hi ih =>
    rw [Finset.sum_cons]
    filter_upwards [Lp.coeFn_add (f i) (∑ j ∈ s, f j), ih] with x hx1 hx2
    rw [hx1]
    simp only [Pi.add_apply, hx2, Finset.sum_cons]

/-! ### Ridge Hermites in L² and the L² form of Lemma 2.1 -/

/-- The ridge Hermite `h_n(⟨v,·⟩)` as an element of `L²(γ^d)`. -/
def ridgeHermite {d : ℕ} (n : ℕ) (v : Vec d) (hv : ‖v‖ = 1) : L2 d :=
  ridge v hv (hermiteL2 n)

lemma ridgeHermite_congr {d : ℕ} (n : ℕ) {v w : Vec d} (hv : ‖v‖ = 1)
    (hw : ‖w‖ = 1) (h : v = w) : ridgeHermite n v hv = ridgeHermite n w hw := by
  subst h; rfl

lemma ridge_coeFn {d : ℕ} (v : Vec d) (hv : ‖v‖ = 1) (g : L2R) :
    ⇑(ridge v hv g) =ᵐ[γ d] ⇑g ∘ ridgeMap v :=
  Lp.coeFn_compMeasurePreserving g (measurePreserving_ridgeMap hv)

lemma act_coeFn {d : ℕ} (U : Od d) (f : L2 d) :
    ⇑(act U f) =ᵐ[γ d] ⇑f ∘ actMap U :=
  Lp.coeFn_compMeasurePreserving f (measurePreserving_actMap U)

lemma ridgeHermite_coeFn {d : ℕ} (n : ℕ) (v : Vec d) (hv : ‖v‖ = 1) :
    ⇑(ridgeHermite n v hv) =ᵐ[γ d] fun x => hfun n (ridgeMap v x) := by
  have h2 : (⇑(hermiteL2 n)) ∘ (ridgeMap v) =ᵐ[γ d] (hfun n) ∘ (ridgeMap v) := by
    refine MeasureTheory.ae_eq_comp (measurePreserving_ridgeMap hv).aemeasurable ?_
    rw [(measurePreserving_ridgeMap hv).map_eq]
    exact MemLp.coeFn_toLp (memLp_hfun n)
  filter_upwards [ridge_coeFn v hv (hermiteL2 n), h2] with x hx1 hx2
  rw [ridgeHermite, hx1]
  exact hx2

/-- **Lemma 2.1 in `L²(γ^d)`**: the ridge Hermite is the finite chaos combination. -/
theorem ridgeHermite_eq_sum {d : ℕ} (n : ℕ) (v : Vec d) (hv : ‖v‖ = 1) :
    ridgeHermite n v hv
      = ∑ α ∈ idxOf d n, (((n ! : ℝ) / (mfact α : ℝ)) * mpow v α) • HL2 α := by
  apply Lp.ext
  have hterm : ∀ α ∈ idxOf d n,
      ⇑((((n ! : ℝ) / (mfact α : ℝ)) * mpow v α) • HL2 α)
        =ᵐ[γ d] fun x => ((n ! : ℝ) / (mfact α : ℝ)) * mpow v α * Hfun α x := by
    intro α _
    filter_upwards [Lp.coeFn_smul (((n ! : ℝ) / (mfact α : ℝ)) * mpow v α) (HL2 α),
      MemLp.coeFn_toLp (memLp_Hfun α)] with x hx1 hx2
    rw [hx1]
    simp only [Pi.smul_apply, smul_eq_mul]
    exact congrArg (fun t => ((n ! : ℝ) / (mfact α : ℝ) * mpow v α) * t) hx2
  have hall : ∀ᵐ x ∂(γ d), ∀ α ∈ idxOf d n,
      ((((n ! : ℝ) / (mfact α : ℝ)) * mpow v α) • HL2 α : L2 d) x
        = ((n ! : ℝ) / (mfact α : ℝ)) * mpow v α * Hfun α x :=
    (Filter.eventually_all_finset (idxOf d n)).mpr fun α hα => hterm α hα
  filter_upwards [ridgeHermite_coeFn n v hv,
    coeFn_finsetSum_Lp (idxOf d n)
      (fun α => (((n ! : ℝ) / (mfact α : ℝ)) * mpow v α) • HL2 α), hall]
    with x hx1 hx2 hx3
  rw [hx1, hx2]
  rw [show ridgeMap v x = ⟪v, x⟫ from rfl, hermite_ridge_identity n v hv x]
  exact Finset.sum_congr rfl fun α hα => (hx3 α hα).symm

/-- `⟨h_n^v, H_α⟩ = n!·v^α` for `|α| = n`. -/
lemma inner_ridgeHermite_HL2 {d : ℕ} (n : ℕ) (v : Vec d) (hv : ‖v‖ = 1)
    {α : MIdx d} (hα : α ∈ idxOf d n) :
    ⟪ridgeHermite n v hv, HL2 α⟫ = (n ! : ℝ) * mpow v α := by
  rw [ridgeHermite_eq_sum, sum_inner]
  rw [Finset.sum_eq_single α]
  · rw [real_inner_smul_left, HL2_inner, ite_eq_left rfl,
      mul_comm ((n ! : ℝ) / (mfact α : ℝ)) (mpow v α), mul_assoc,
      div_mul_cancel₀ _ (mfact_ne_zero α)]
    ring
  · intro β _ hne
    rw [real_inner_smul_left, HL2_inner, ite_eq_right hne, mul_zero]
  · intro h; exact absurd hα h

/-! ### Scaling and the coefficient-extraction lemma -/

lemma mpow_smul {d : ℕ} (t : ℝ) (u : Vec d) (α : MIdx d) :
    mpow (t • u) α = t ^ mdeg α * mpow u α := by
  rw [mpow, mpow, mdeg, ← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun i _ => by
    rw [PiLp.smul_apply, smul_eq_mul, mul_pow]

/-- A family of level-`n` coefficients whose homogeneous polynomial vanishes on
the unit sphere vanishes identically. -/
lemma coeff_eq_zero_of_vanish_on_sphere {d : ℕ} (hd : 0 < d) {n : ℕ}
    (c : MIdx d → ℝ)
    (h : ∀ (v : Vec d), ‖v‖ = 1 → ∑ α ∈ idxOf d n, c α * mpow v α = 0)
    {α : MIdx d} (hα : α ∈ idxOf d n) : c α = 0 := by
  classical
  -- Step 1: vanishing on all of ℝ^d.
  have hall : ∀ w : Vec d, ∑ β ∈ idxOf d n, c β * mpow w β = 0 := by
    intro w
    by_cases hw : w = 0
    · subst hw
      rcases Nat.eq_zero_or_pos n with hn | hn
      · subst hn
        -- idxOf d 0 = {0}: the sum is c 0, and evaluating h at e₁ also gives c 0
        have he : ‖(EuclideanSpace.single (⟨0, hd⟩ : Fin d) (1 : ℝ) : Vec d)‖ = 1 := by
          rw [PiLp.norm_single, norm_one]
        have h1 := h _ he
        rw [idxOf, Finset.Nat.antidiagonalTuple_zero_right, Finset.sum_singleton] at h1 ⊢
        simpa [mpow] using h1
      · refine Finset.sum_eq_zero fun β hβ => ?_
        have hβd : mdeg β = n := mem_idxOf.mp hβ
        have hex : ∃ i, β i ≠ 0 := by
          by_contra hcon
          push Not at hcon
          have : mdeg β = 0 := Finset.sum_eq_zero fun i _ => hcon i
          omega
        obtain ⟨i, hi⟩ := hex
        rw [mpow, Finset.prod_eq_zero (Finset.mem_univ i)]
        · ring
        · exact zero_pow hi
    · have hnorm : ‖w‖ ≠ 0 := norm_ne_zero_iff.mpr hw
      have hw1 : ‖(‖w‖⁻¹ • w : Vec d)‖ = 1 := norm_smul_inv_norm hw
      have hw2 : w = ‖w‖ • (‖w‖⁻¹ • w) := by
        rw [smul_smul, mul_inv_cancel₀ hnorm, one_smul]
      calc ∑ β ∈ idxOf d n, c β * mpow w β
          = ∑ β ∈ idxOf d n, c β * (‖w‖ ^ n * mpow (‖w‖⁻¹ • w) β) := by
            refine Finset.sum_congr rfl fun β hβ => ?_
            conv_lhs => rw [hw2]
            rw [mpow_smul, mem_idxOf.mp hβ]
        _ = ‖w‖ ^ n * ∑ β ∈ idxOf d n, c β * mpow (‖w‖⁻¹ • w) β := by
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun β _ => by ring
        _ = 0 := by rw [h _ hw1, mul_zero]
  -- Step 2: MvPolynomial coefficient extraction.
  set q : MvPolynomial (Fin d) ℝ :=
    ∑ β ∈ idxOf d n, MvPolynomial.monomial (Finsupp.equivFunOnFinite.symm β) (c β)
    with hq
  have heval : ∀ w : Vec d, MvPolynomial.eval (fun i => w i) q
      = ∑ β ∈ idxOf d n, c β * mpow w β := by
    intro w
    rw [hq, map_sum]
    refine Finset.sum_congr rfl fun β _ => ?_
    rw [MvPolynomial.eval_monomial, mpow]
    congr 1
    rw [Finsupp.prod_pow]
    exact Finset.prod_congr rfl fun i _ => rfl
  have hq0 : q = 0 := by
    apply MvPolynomial.funext
    intro w
    rw [map_zero]
    have := heval (WithLp.toLp 2 w)
    simpa [hall (WithLp.toLp 2 w)] using this
  have hcoeff := congrArg (MvPolynomial.coeff (Finsupp.equivFunOnFinite.symm α)) hq0
  rw [hq, MvPolynomial.coeff_sum, MvPolynomial.coeff_zero] at hcoeff
  rw [Finset.sum_eq_single α] at hcoeff
  · rwa [MvPolynomial.coeff_monomial, ite_eq_left rfl] at hcoeff
  · intro β _ hne
    rw [MvPolynomial.coeff_monomial,
      ite_eq_right fun hcon => hne (Finsupp.equivFunOnFinite.symm.injective hcon)]
  · intro hcon; exact absurd hα hcon

/-! ### The ridge span equals the chaos space -/

/-- The span of the level-`n` ridge Hermites. -/
def ridgeSpan (d n : ℕ) : Submodule ℝ (L2 d) :=
  Submodule.span ℝ {f | ∃ v : Vec d, ∃ hv : ‖v‖ = 1, f = ridgeHermite n v hv}

theorem ridgeSpan_le_chaos (d n : ℕ) : ridgeSpan d n ≤ chaos d n := by
  rw [ridgeSpan, Submodule.span_le]
  rintro f ⟨v, hv, rfl⟩
  rw [ridgeHermite_eq_sum]
  exact Submodule.sum_mem _ fun α hα => Submodule.smul_mem _ _
    (Submodule.subset_span ⟨α, by simpa using hα, rfl⟩)

instance (d n : ℕ) : FiniteDimensional ℝ (ridgeSpan d n) :=
  Submodule.finiteDimensional_of_le (ridgeSpan_le_chaos d n)

/-- A chaos representation over the standard generators. -/
lemma chaos_mem_repr {d n : ℕ} {r : L2 d} (hr : r ∈ chaos d n) :
    ∃ c : MIdx d → ℝ, r = ∑ α ∈ idxOf d n, c α • HL2 α := by
  classical
  have hspan : chaos d n
      = Submodule.span ℝ (Set.range fun α : ↥(idxOf d n) => HL2 (α : MIdx d)) := by
    rw [chaos]
    congr 1
    ext f
    simp only [Set.mem_image, Finset.mem_coe, Set.mem_range]
    constructor
    · rintro ⟨α, hα, rfl⟩; exact ⟨⟨α, hα⟩, rfl⟩
    · rintro ⟨⟨α, hα⟩, rfl⟩; exact ⟨α, hα, rfl⟩
  rw [hspan, Submodule.mem_span_range_iff_exists_fun] at hr
  obtain ⟨c, hc⟩ := hr

  refine ⟨fun α => if hα : α ∈ idxOf d n then c ⟨α, hα⟩ else 0, ?_⟩
  rw [← hc, ← Finset.sum_attach (idxOf d n)
    (fun α => (if hα : α ∈ idxOf d n then c ⟨α, hα⟩ else 0) • HL2 α),
    ← Finset.univ_eq_attach]
  exact (Finset.sum_congr rfl fun i _ => by rw [dite_eq_left i.2]).symm

/-- **Chaos = ridge span**: the paper's spanning claim inside Lemma 2.2
("the ridge Hermites span `ℋ_n`"). -/
theorem chaos_le_ridgeSpan {d : ℕ} (hd : 0 < d) (n : ℕ) :
    chaos d n ≤ ridgeSpan d n := by
  intro f hf
  set W := ridgeSpan d n with hW
  set r := f - W.starProjection f with hr
  have hPmem : W.starProjection f ∈ W := W.starProjection_apply_mem f
  have hrchaos : r ∈ chaos d n :=
    Submodule.sub_mem _ hf (ridgeSpan_le_chaos d n hPmem)
  have hrorth : ∀ w ∈ W, ⟪r, w⟫ = 0 := by
    intro w hw
    have hmem := Submodule.sub_starProjection_mem_orthogonal (K := W) f
    rw [Submodule.mem_orthogonal] at hmem
    rw [real_inner_comm]
    exact hmem w hw
  obtain ⟨c, hc⟩ := chaos_mem_repr hrchaos
  have hcoef : ∀ (v : Vec d), ‖v‖ = 1 →
      ∑ α ∈ idxOf d n, c α * mpow v α = 0 := by
    intro v hv
    have h0 : ⟪r, ridgeHermite n v hv⟫ = 0 :=
      hrorth _ (Submodule.subset_span ⟨v, hv, rfl⟩)
    rw [hc, sum_inner] at h0
    have hterm : ∀ α ∈ idxOf d n,
        ⟪c α • HL2 α, ridgeHermite n v hv⟫ = (n ! : ℝ) * (c α * mpow v α) := by
      intro α hα
      rw [real_inner_smul_left, real_inner_comm, inner_ridgeHermite_HL2 n v hv hα]
      ring
    rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum] at h0
    have hfact : (n ! : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
    exact (mul_eq_zero.mp h0).resolve_left hfact
  have hr0 : r = 0 := by
    rw [hc]
    exact Finset.sum_eq_zero fun α hα => by
      rw [coeff_eq_zero_of_vanish_on_sphere hd c hcoef hα, zero_smul]
  have hfP : f = W.starProjection f := by
    have h := hr0
    rw [hr] at h
    exact sub_eq_zero.mp h
  rw [hfP]
  exact hPmem

/-! ### Rotations permute the ridge Hermites; Lemma 2.2 -/

@[simp] lemma actMap_actMap {d : ℕ} (U V : Od d) (x : Vec d) :
    actMap U (actMap V x) = actMap (U * V) x := rfl

@[simp] lemma actMap_one {d : ℕ} (x : Vec d) : actMap (1 : Od d) x = x := rfl

lemma actMap_norm {d : ℕ} (U : Od d) (v : Vec d) : ‖actMap U v‖ = ‖v‖ :=
  Unitary.norm_map U v

lemma actMap_unit {d : ℕ} (U : Od d) {v : Vec d} (hv : ‖v‖ = 1) :
    ‖actMap U v‖ = 1 := by rw [actMap_norm, hv]

/-- `⟨v, Ux⟩ = ⟨U⁻¹v, x⟩` (the adjoint of a unitary is its inverse). -/
lemma ridgeMap_comp_actMap {d : ℕ} (U : Od d) (v : Vec d) (x : Vec d) :
    ridgeMap v (actMap U x) = ridgeMap (actMap U⁻¹ v) x := by
  have hadj : actMap U⁻¹ v
      = ContinuousLinearMap.adjoint ((U : Vec d →L[ℝ] Vec d)) v := by
    rw [actMap, ← ContinuousLinearMap.star_eq_adjoint, ← Unitary.star_eq_inv]
    rfl
  rw [hadj]
  show ⟪v, (U : Vec d →L[ℝ] Vec d) x⟫
      = ⟪ContinuousLinearMap.adjoint ((U : Vec d →L[ℝ] Vec d)) v, x⟫
  exact (ContinuousLinearMap.adjoint_inner_left _ _ _).symm

/-- Rotations permute ridge embeddings: `T_U ∘ (·)^v = (·)^{U⁻¹v}`. -/
lemma act_ridge {d : ℕ} (U : Od d) (v : Vec d) (hv : ‖v‖ = 1) (g : L2R) :
    act U (ridge v hv g) = ridge (actMap U⁻¹ v) (actMap_unit U⁻¹ hv) g := by
  apply Lp.ext
  have hcomp : (⇑(ridge v hv g)) ∘ actMap U =ᵐ[γ d] (⇑g ∘ ridgeMap v) ∘ actMap U := by
    refine MeasureTheory.ae_eq_comp (measurePreserving_actMap U).aemeasurable ?_
    rw [(measurePreserving_actMap U).map_eq]
    exact ridge_coeFn v hv g
  filter_upwards [act_coeFn U (ridge v hv g), hcomp,
    ridge_coeFn (actMap U⁻¹ v) (actMap_unit U⁻¹ hv) g] with x hx1 hx2 hx3
  rw [hx1, hx2, hx3]
  simp only [Function.comp_apply]
  rw [ridgeMap_comp_actMap]

lemma act_ridgeHermite {d : ℕ} (n : ℕ) (U : Od d) (v : Vec d) (hv : ‖v‖ = 1) :
    act U (ridgeHermite n v hv)
      = ridgeHermite n (actMap U⁻¹ v) (actMap_unit U⁻¹ hv) :=
  act_ridge U v hv (hermiteL2 n)

/-- `T_U` maps the ridge span onto itself. -/
lemma map_act_ridgeSpan {d : ℕ} (n : ℕ) (U : Od d) :
    Submodule.map (act U).toLinearMap (ridgeSpan d n) = ridgeSpan d n := by
  rw [ridgeSpan, Submodule.map_span]
  congr 1
  ext f
  simp only [Set.mem_image, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨g, ⟨v, hv, rfl⟩, rfl⟩
    refine ⟨actMap U⁻¹ v, actMap_unit U⁻¹ hv, ?_⟩
    exact act_ridgeHermite n U v hv
  · rintro ⟨v, hv, rfl⟩
    refine ⟨ridgeHermite n (actMap U v) (actMap_unit U hv),
      ⟨actMap U v, actMap_unit U hv, rfl⟩, ?_⟩
    show act U (ridgeHermite n (actMap U v) (actMap_unit U hv)) = ridgeHermite n v hv
    rw [act_ridgeHermite]
    refine ridgeHermite_congr n _ hv ?_
    rw [actMap_actMap, inv_mul_cancel, actMap_one]

/-- For `d = 0` every rotation acts as the identity on `L²`. -/
lemma act_eq_id_of_dim_zero (U : Od 0) (f : L2 0) : act U f = f := by
  apply Lp.ext
  filter_upwards [act_coeFn U f] with x hx
  rw [hx]
  simp only [Function.comp_apply]
  congr 1
  exact Subsingleton.elim _ _

/-- `T_U` maps each chaos space onto itself. -/
lemma map_act_chaos {d : ℕ} (n : ℕ) (U : Od d) :
    Submodule.map (act U).toLinearMap (chaos d n) = chaos d n := by
  rcases Nat.eq_zero_or_pos d with hd | hd
  · subst hd
    ext f
    simp only [Submodule.mem_map]
    constructor
    · rintro ⟨g, hg, rfl⟩
      rw [show (act U).toLinearMap g = act U g from rfl, act_eq_id_of_dim_zero]
      exact hg
    · intro hf
      exact ⟨f, hf, act_eq_id_of_dim_zero U f⟩
  · have heq : chaos d n = ridgeSpan d n :=
      le_antisymm (chaos_le_ridgeSpan hd n) (ridgeSpan_le_chaos d n)
    rw [heq, map_act_ridgeSpan]

/-- An inner-product-preserving linear map fixing a subspace (with orthogonal
projection) commutes with the orthogonal projection. -/
lemma starProjection_comm_isometry {d : ℕ} (K : Submodule ℝ (L2 d))
    [K.HasOrthogonalProjection] (T : L2 d →ₗᵢ[ℝ] L2 d)
    (hT : Submodule.map T.toLinearMap K = K) (f : L2 d) :
    K.starProjection (T f) = T (K.starProjection f) := by
  refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero ?_ ?_
  · have hmem : T (K.starProjection f) ∈ Submodule.map T.toLinearMap K :=
      Submodule.mem_map_of_mem (K.starProjection_apply_mem f)
    rwa [hT] at hmem
  · intro w hw
    rw [← hT] at hw
    obtain ⟨w', hw', rfl⟩ := hw
    rw [show (T.toLinearMap w' : L2 d) = T w' from rfl,
      show T f - T (K.starProjection f) = T (f - K.starProjection f) by rw [map_sub],
      T.inner_map_map]
    have hmem := Submodule.sub_starProjection_mem_orthogonal (K := K) f
    rw [Submodule.mem_orthogonal] at hmem
    rw [real_inner_comm]
    exact hmem w' hw'

/- LaTeX — `main.tex`, Lemma 2.2 (Rotation invariance of the chaos projections):
"For every $U \in O(d)$ and every $f \in L^2(\gamma^d)$,
$$P_n(f\circ U) = (P_n f)\circ U.$$"
-/
/-- **Lemma 2.2 (Rotation invariance of the chaos projections).** -/
theorem Pn_comp_rotation {d : ℕ} (n : ℕ) (U : Od d) (f : L2 d) :
    Pn d n (act U f) = act U (Pn d n f) :=
  starProjection_comm_isometry (chaos d n) (act U) (map_act_chaos n U) f

end

end GaussianDepthSeparation
