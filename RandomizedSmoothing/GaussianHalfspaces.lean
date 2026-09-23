import RandomizedSmoothing.Lemma4
import Mathlib.Probability.CDF
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Probability.Distributions.Gaussian.CharFun
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Topology.Order.LeftRightLim

/-!
# Gaussian half-spaces

Probability calculations connecting the explicit isotropic Gaussian density
from Lemma 4 to Mathlib's multivariate Gaussian, standard normal CDF/quantile,
and the half-space probabilities used by Theorem 1.

This file is the computational heart of Appendix A of Cohen–Rosenfeld–Kolter
("Certified Adversarial Robustness via Randomized Smoothing"). Lemma 4
(`RandomizedSmoothing/Lemma4.lean`) tells us *which* sets are optimal in the
Neyman–Pearson sense for isotropic Gaussian noise: they are Euclidean
half-spaces cut out by the direction of the perturbation `δ`. What that
lemma does *not* tell us is the actual numerical *probability* those
half-spaces carry under the base noise `N(x, σ² I)` and under the
mean-shifted noise `N(x + δ, σ² I)`. Supplying those probabilities is the
entire content of this file, and they are the ingredients Theorem 1
needs to turn a certified base-class probability `p_A` into a certified
robustness radius.
-/

/-!
## Results from this file used by Theorem 1

`Theorem1.lean` directly uses the following definitions and theorems from this
file.

### Half-space definitions

* `acceptanceHalfspace x δ σ pA`

      A = {z | ⟨δ, z - x⟩ ≤ σ ‖δ‖ Φ⁻¹(pA)}.

  This is the Neyman–Pearson lower half-space associated with the proposed
  winning class `cA`.

* `competitorHalfspace x δ σ pB`

      B = {z | σ ‖δ‖ Φ⁻¹(1 - pB) ≤ ⟨δ, z - x⟩}.

  This is the corresponding upper half-space associated with one competing
  class `cB`.

### Probabilities under the original Gaussian

Let

    X ∼ N(x, σ²I).

* `prob_X_acceptanceHalfspace` proves

      P(X ∈ A) = pA.

* `prob_X_competitorHalfspace` proves

      P(X ∈ B) = pB.

These identities allow the original class-score assumptions

    P(f(X) = cA) ≥ pA
    P(f(X) = cB) ≤ pB

to be rewritten as the half-space hypotheses required by `lemma4_lower` and
`lemma4_upper`.

### Probabilities under the shifted Gaussian

Let

    Y ∼ N(x + δ, σ²I).

* `prob_Y_acceptanceHalfspace` proves

      P(Y ∈ A) =
        Φ(Φ⁻¹(pA) - ‖δ‖ / σ).

* `prob_Y_competitorHalfspace` proves

      P(Y ∈ B) =
        Φ(Φ⁻¹(pB) + ‖δ‖ / σ).

These calculate the two half-space integrals appearing after Lemma 4 has
transferred the class-score bounds from `X` to `Y`.

### Radius comparison

* `shifted_halfspace_probability_lt` proves that

      ‖δ‖ < (σ / 2) * (Φ⁻¹(pA) - Φ⁻¹(pB))

  implies

      Φ(Φ⁻¹(pB) + ‖δ‖ / σ)
        <
      Φ(Φ⁻¹(pA) - ‖δ‖ / σ).

Equivalently,

      P(Y ∈ B) < P(Y ∈ A).

Combining these results with `lemma4_upper` and `lemma4_lower` gives the main
Theorem 1 chain

    P(f(Y) = cB)
      ≤ P(Y ∈ B)
      < P(Y ∈ A)
      ≤ P(f(Y) = cA).

Theorem 1 therefore uses eight declarations from this file directly:

1. `acceptanceHalfspace`;
2. `competitorHalfspace`;
3. `prob_X_acceptanceHalfspace`;
4. `prob_X_competitorHalfspace`;
5. `prob_Y_acceptanceHalfspace`;
6. `prob_Y_competitorHalfspace`;
7. `shifted_halfspace_probability_lt`;
8. the imported notation/functions `standardNormalCDF`,
   `standardNormalQuantile`, and `oneSubProbability` appearing in its
   statements and intermediate half-space thresholds.

Most other declarations in this file are supporting results used internally
to prove these exported Gaussian half-space formulas. In particular, the
multivariate-Gaussian representation, projection, standardisation, CDF,
quantile, and symmetry lemmas are indirect dependencies rather than the
results invoked explicitly inside `theorem1_pairwise`.
-/

namespace RandomizedSmoothing

open Filter MeasureTheory ProbabilityTheory WithLp Complex Matrix Function Set
open scoped BigOperators ENNReal NNReal Topology

noncomputable section


/-! ## Standard normal CDF and quantile -/

/-- The CDF of a standard real normal random variable. -/
def standardNormalCDF (r : Real) : Real :=
  cdf (gaussianReal 0 1) r

theorem standardNormalCDF_monotone : Monotone standardNormalCDF := by
  change Monotone (cdf (gaussianReal 0 1))
  exact monotone_cdf (gaussianReal 0 1)

theorem tendsto_standardNormalCDF_atBot :
    Tendsto standardNormalCDF atBot (nhds 0) := by
  change Tendsto (cdf (gaussianReal 0 1)) atBot (nhds 0)
  exact tendsto_cdf_atBot (gaussianReal 0 1)

theorem tendsto_standardNormalCDF_atTop :
    Tendsto standardNormalCDF atTop (nhds 1) := by
  change Tendsto (cdf (gaussianReal 0 1)) atTop (nhds 1)
  exact tendsto_cdf_atTop (gaussianReal 0 1)

/-- Φ(r) = P(Z ≤ r) as a real integral against the standard normal density. -/
theorem standardNormalCDF_eq_integral (r : Real) :
    standardNormalCDF r = ∫ x in Set.Iic r, gaussianPDFReal 0 1 x := by
  have hv : (1 : NNReal) ≠ 0 := one_ne_zero
  simp only [standardNormalCDF, cdf_eq_real, measureReal_def]
  rw [gaussianReal_apply_eq_integral 0 hv (Set.Iic r), ENNReal.toReal_ofReal]
  exact integral_nonneg fun _ => gaussianPDFReal_nonneg _ _ _

/-- Continuity of Φ: atomless Gaussian + Stieltjes right-continuity. -/
theorem standardNormalCDF_continuous : Continuous standardNormalCDF := by
  -- Work with Mathlib's `cdf` and transport at the end.
  change Continuous (cdf (gaussianReal 0 1))
  have hmono : Monotone (cdf (gaussianReal 0 1)) := monotone_cdf _
  refine continuous_iff_continuousAt.2 fun x =>
    (hmono.continuousAt_iff_leftLim_eq_rightLim).2 ?_
  have hright :
      rightLim (cdf (gaussianReal 0 1)) x = cdf (gaussianReal 0 1) x :=
    ContinuousWithinAt.rightLim_eq ((cdf (gaussianReal 0 1)).right_continuous x)
  haveI := nullSingletonClass_gaussianReal (μ := (0 : Real)) (v := 1) one_ne_zero
  have hsing : (gaussianReal 0 1) ({x} : Set Real) = 0 := measure_singleton x
  have hmeas := measure_cdf (gaussianReal 0 1)
  have hform := StieltjesFunction.measure_singleton (cdf (gaussianReal 0 1)) x
  have hzero :
      ENNReal.ofReal
          (cdf (gaussianReal 0 1) x - leftLim (cdf (gaussianReal 0 1)) x) = 0 := by
    rw [← hform, hmeas, hsing]
  have hnn :
      0 ≤ cdf (gaussianReal 0 1) x - leftLim (cdf (gaussianReal 0 1)) x :=
    sub_nonneg.mpr (hmono.leftLim_le le_rfl)
  have hsub :
      cdf (gaussianReal 0 1) x - leftLim (cdf (gaussianReal 0 1)) x = 0 :=
    le_antisymm (ENNReal.ofReal_eq_zero.mp hzero) hnn
  have hleft :
      leftLim (cdf (gaussianReal 0 1)) x = cdf (gaussianReal 0 1) x := by linarith
  exact hleft.trans hright.symm

/-- The lower generalized inverse of the standard normal CDF. -/
def standardNormalQuantile (p : Set.Ioo (0 : Real) 1) : Real :=
  sInf {r | p.1 ≤ standardNormalCDF r}

def oneSubProbability (p : Set.Ioo (0 : Real) 1) : Set.Ioo (0 : Real) 1 :=
  ⟨1 - p.1, sub_pos.mpr p.2.2, by linarith [p.2.1]⟩

def acceptanceHalfspace {d : Nat} (x δ : Input d) (σ : Real)
    (pA : Set.Ioo (0 : Real) 1) : Set (Input d) :=
  {z | inner Real δ (z - x) ≤ σ * ‖δ‖ * standardNormalQuantile pA}

def competitorHalfspace {d : Nat} (x δ : Input d) (σ : Real)
    (pB : Set.Ioo (0 : Real) 1) : Set (Input d) :=
  {z | σ * ‖δ‖ * standardNormalQuantile (oneSubProbability pB) ≤
    inner Real δ (z - x)}

/-! ## Bridge: explicit PDF ↔ multivariateGaussian -/

/-- The withDensity of the isotropic PDF is a probability measure. -/
theorem isProbabilityMeasure_isotropicGaussian
    {d : Nat} (m : Input d) (σ : Real) (hσ : 0 < σ) :
    IsProbabilityMeasure
      ((volume : Measure (Input d)).withDensity
        (fun z => ENNReal.ofReal (isotropicGaussianPDF m σ z))) := by
  constructor
  rw [withDensity_apply _ MeasurableSet.univ]
  simp only [Measure.restrict_univ]
  have hint := integrable_isotropicGaussianPDF m σ
  have hnn := isotropicGaussianPDF_nonneg m σ
  have h1 := integral_isotropicGaussianPDF_eq_one m σ hσ
  rw [← ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall hnn), h1,
    ENNReal.ofReal_one]

/-- Bridge step 1: explicit density measure equals the mapped product of 1D Gaussians. -/
theorem isotropicGaussian_measure_eq_map_pi
    {d : Nat} (m : Input d) (σ : Real) (hσ : 0 < σ) :
    (volume : Measure (Input d)).withDensity
        (fun z => ENNReal.ofReal (isotropicGaussianPDF m σ z))
      =
    (Measure.pi (fun i : Fin d => gaussianReal (m i) (gaussianVariance σ))).map
      (toLp 2) := by
  have hv := gaussianVariance_ne_zero hσ
  haveI : IsProbabilityMeasure
      ((volume : Measure (Input d)).withDensity
        (fun z => ENNReal.ofReal (isotropicGaussianPDF m σ z))) :=
    isProbabilityMeasure_isotropicGaussian m σ hσ
  haveI : IsProbabilityMeasure
      ((Measure.pi (fun i : Fin d => gaussianReal (m i) (gaussianVariance σ))).map
        (toLp 2)) :=
    Measure.isProbabilityMeasure_map (Measurable.aemeasurable (by fun_prop))
  apply Measure.ext_of_charFun (E := Input d)
  ext t
  -- RHS via Mathlib's product characteristic function.
  rw [charFun_pi]
  simp_rw [charFun_gaussianReal]
  -- LHS as an integral against the density.
  simp only [charFun_apply]
  have hmeas :
      Measurable (fun z => ENNReal.ofReal (isotropicGaussianPDF m σ z)) :=
    Measurable.ennreal_ofReal (measurable_isotropicGaussianPDF m σ)
  have hlt : ∀ᵐ z ∂volume, ENNReal.ofReal (isotropicGaussianPDF m σ z) < ∞ :=
    Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top
  rw [integral_withDensity_eq_integral_toReal_smul hmeas hlt]
  -- `toReal (ofReal (PDF z)) • cexp (...) = PDF z * cexp (...)`.
  have hintegrand :
      (fun z : Input d =>
          (ENNReal.ofReal (isotropicGaussianPDF m σ z)).toReal •
            cexp (inner Real z t * I))
        =
      fun z =>
        (isotropicGaussianPDF m σ z : ℂ) * cexp (inner Real z t * I) := by
    funext z
    rw [ENNReal.toReal_ofReal (isotropicGaussianPDF_nonneg m σ z), real_smul]
  rw [hintegrand]
  -- Transfer to the product space along the volume-preserving map `toLp`.
  have hpres := PiLp.volume_preserving_toLp (Fin d)
  have hme := (MeasurableEquiv.toLp 2 (Fin d → Real)).measurableEmbedding
  rw [← hpres.integral_comp hme]
  -- Factor the integrand into a product over coordinates.
  -- charFun uses `inner x t`, so after substitution: `inner (toLp y) t`.
  have hfun :
      (fun y : Fin d → Real =>
          (isotropicGaussianPDF m σ (toLp 2 y) : ℂ) *
            cexp (inner Real (toLp 2 y) t * I))
        =
      fun y =>
        ∏ i : Fin d,
          (gaussianPDFReal (m i) (gaussianVariance σ) (y i) : ℂ) *
            cexp ((y i : ℂ) * (t i : ℂ) * I) := by
    funext y
    have hinter : inner Real (toLp 2 y) t = ∑ i : Fin d, y i * t i := by
      simp [inner, PiLp.inner_apply, RCLike.inner_apply, mul_comm]
    have hpdf :
        isotropicGaussianPDF m σ (toLp 2 y) =
          ∏ i, gaussianPDFReal (m i) (gaussianVariance σ) (y i) := by
      simp [isotropicGaussianPDF]
    have hexp :
        cexp ((∑ i : Fin d, y i * t i : Real) * I)
          =
        ∏ i : Fin d, cexp ((y i : ℂ) * (t i : ℂ) * I) := by
      rw [← Complex.exp_sum]
      congr 1
      -- ↑(∑ y_i t_i) * I = ∑ ↑y_i * ↑t_i * I
      calc
        (((∑ i : Fin d, y i * t i : Real) : ℂ) * I)
            = (∑ i : Fin d, ((y i * t i : Real) : ℂ)) * I := by
              rw [ofReal_sum]
        _ = ∑ i : Fin d, ((y i * t i : Real) : ℂ) * I := by
              rw [Finset.sum_mul]
        _ = ∑ i : Fin d, (y i : ℂ) * (t i : ℂ) * I := by
              refine Finset.sum_congr rfl fun i _ => ?_
              simp [ofReal_mul, mul_assoc]
    rw [hinter, hpdf, Complex.ofReal_prod, hexp, ← Finset.prod_mul_distrib]
  have hvol : (volume : Measure (Fin d → Real)) = Measure.pi fun _ => volume := volume_pi
  rw [hfun, hvol]
  -- Fubini for a finite product of ℂ-valued coordinate functions.
  rw [integral_fintype_prod_eq_prod
    (f := fun i (x : Real) =>
      (gaussianPDFReal (m i) (gaussianVariance σ) x : ℂ) *
        cexp ((x : ℂ) * (t i : ℂ) * I))]
  -- Goal: product of 1D integrals equals product of closed-form charFuns.
  refine Finset.prod_congr rfl fun i _ => ?_
  have hgi :
      gaussianReal (m i) (gaussianVariance σ) =
        volume.withDensity (gaussianPDF (m i) (gaussianVariance σ)) :=
    gaussianReal_of_var_ne_zero _ hv
  calc
    (∫ x : Real,
        (gaussianPDFReal (m i) (gaussianVariance σ) x : ℂ) *
          cexp ((x : ℂ) * (t i : ℂ) * I))
        =
      ∫ x : Real, cexp ((x : ℂ) * (t i : ℂ) * I)
        ∂gaussianReal (m i) (gaussianVariance σ) := by
          rw [hgi]
          have hm : Measurable (gaussianPDF (m i) (gaussianVariance σ)) :=
            measurable_gaussianPDF _ _
          have hlt' : ∀ᵐ x ∂volume, gaussianPDF (m i) (gaussianVariance σ) x < ∞ :=
            Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top
          rw [integral_withDensity_eq_integral_toReal_smul hm hlt']
          refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
          simp [gaussianPDF, ENNReal.toReal_ofReal (gaussianPDFReal_nonneg _ _ _),
            real_smul, mul_comm]
    _ = charFun (gaussianReal (m i) (gaussianVariance σ)) (t i) := by
          simp only [charFun_apply]
          -- `charFun` uses `cexp (↑(x * t) * I)`; commute the real factors.
          refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
          simp [mul_comm]
    _ = cexp ((t i : ℂ) * (m i : ℂ) * I
          - ((gaussianVariance σ : Real) : ℂ) * (t i : ℂ) ^ 2 / 2) := by
          simpa [mul_comm] using
            (charFun_gaussianReal (μ := m i) (v := gaussianVariance σ) (t i))
/-- Covariance matrix `σ² I` is positive semidefinite. -/
theorem posSemidef_variance_matrix {d : Nat} (σ : Real) :
    ((σ ^ 2) • (1 : Matrix (Fin d) (Fin d) Real)).PosSemidef :=
  Matrix.PosSemidef.smul Matrix.PosSemidef.one (sq_nonneg σ)

/-- Algebraic identity for the isotropic covariance quadratic form. -/
theorem quadratic_form_variance_matrix {d : Nat} (σ : Real) (t : Input d) :
    t ⬝ᵥ ((σ ^ 2) • (1 : Matrix (Fin d) (Fin d) Real)) *ᵥ t
      = σ ^ 2 * ∑ i : Fin d, (t i) ^ 2 := by
  have hmul :
      (((σ ^ 2) • (1 : Matrix (Fin d) (Fin d) Real)) *ᵥ (ofLp t))
        = fun i => σ ^ 2 * ofLp t i := by
    funext i
    simp [mulVec, dotProduct, one_apply, mul_ite, mul_zero]
  change (ofLp t) ⬝ᵥ (((σ ^ 2) • (1 : Matrix (Fin d) (Fin d) Real)) *ᵥ (ofLp t))
    = σ ^ 2 * ∑ i : Fin d, (t i) ^ 2
  rw [hmul]
  simp [dotProduct, Finset.mul_sum, mul_left_comm, mul_assoc, sq]

/-- The withDensity of the isotropic PDF equals Mathlib's multivariate Gaussian. -/
theorem isotropicGaussian_measure_eq
    {d : Nat} (m : Input d) (σ : Real) (hσ : 0 < σ) :
    (volume : Measure (Input d)).withDensity
        (fun z => ENNReal.ofReal (isotropicGaussianPDF m σ z))
      =
    multivariateGaussian m ((σ ^ 2) • (1 : Matrix (Fin d) (Fin d) Real)) := by
  rw [isotropicGaussian_measure_eq_map_pi m σ hσ]
  have hS : ((σ ^ 2) • (1 : Matrix (Fin d) (Fin d) Real)).PosSemidef :=
    posSemidef_variance_matrix σ
  haveI : IsProbabilityMeasure
      ((Measure.pi (fun i : Fin d => gaussianReal (m i) (gaussianVariance σ))).map
        (toLp 2)) :=
    Measure.isProbabilityMeasure_map (Measurable.aemeasurable (by fun_prop))
  haveI : IsProbabilityMeasure
      (multivariateGaussian m ((σ ^ 2) • (1 : Matrix (Fin d) (Fin d) Real))) :=
    inferInstance
  apply Measure.ext_of_charFun (E := Input d)
  ext t
  have hrhs :=
    charFun_multivariateGaussian (μ := m)
      (S := (σ ^ 2) • (1 : Matrix (Fin d) (Fin d) Real)) hS t
  rw [charFun_pi, hrhs]
  simp_rw [charFun_gaussianReal]
  -- Collapse product of exponentials to one exponential of a sum.
  rw [← Complex.exp_sum]
  congr 1
  -- ∑ (tᵢ mᵢ I - σ² tᵢ² / 2) = ⟨t,m⟩ I - (t · σ²I t)/2
  have hvσ : (gaussianVariance σ : Real) = σ ^ 2 := rfl
  simp_rw [hvσ, Finset.sum_sub_distrib]
  have hmean :
      (∑ i : Fin d, (t i : Complex) * (m i : Complex) * I)
        = ((inner Real t m : Real) : Complex) * I := by
    have hinter :
        ((inner Real t m : Real) : Complex)
          = ∑ i : Fin d, (t i : Complex) * (m i : Complex) := by
      simp [inner, Complex.ofReal_sum, Complex.ofReal_mul, mul_comm]
    rw [← Finset.sum_mul, hinter]
  have hquad :
      (∑ i : Fin d, ((σ ^ 2 : Real) : Complex) * (t i : Complex) ^ 2 / 2)
        =
      (((t ⬝ᵥ ((σ ^ 2) • (1 : Matrix (Fin d) (Fin d) Real)) *ᵥ t) : Real) : Complex) / 2 := by
    have hq :
        (((t ⬝ᵥ ((σ ^ 2) • (1 : Matrix (Fin d) (Fin d) Real)) *ᵥ t) : Real) : Complex)
          =
        ∑ i : Fin d, ((σ ^ 2 : Real) : Complex) * (t i : Complex) ^ 2 := by
      rw [quadratic_form_variance_matrix, Complex.ofReal_mul, Complex.ofReal_sum]
      -- ↑(σ²) * ∑ ↑(tᵢ²) = ∑ ↑(σ²) * ↑(tᵢ)²
      simp [Complex.ofReal_pow, Finset.mul_sum]
    rw [← Finset.sum_div, hq]
  rw [hmean, hquad]

theorem sum_sq_eq_norm_sq {d : Nat} (t : Input d) :
    ∑ i : Fin d, (t i) ^ 2 = ‖t‖ ^ 2 := by
  simpa [Real.norm_eq_abs, sq_abs] using
    (PiLp.norm_sq_eq_of_L2 (fun _ : Fin d => Real) t).symm

theorem map_inner_multivariateGaussian
    {d : Nat} (m δ : Input d) (σ : Real) (_hσ : 0 < σ) :
    (multivariateGaussian m ((σ ^ 2) • (1 : Matrix (Fin d) (Fin d) Real))).map
        (fun z => inner Real δ z)
      =
    gaussianReal (inner Real δ m)
      ⟨σ ^ 2 * ‖δ‖ ^ 2, mul_nonneg (sq_nonneg σ) (sq_nonneg ‖δ‖)⟩ := by
  have hS := posSemidef_variance_matrix (d := d) σ
  -- Rewrite the map as that of the continuous linear functional `innerSL δ`.
  have hfun : (fun z : Input d => inner Real δ z) = innerSL Real δ :=
    funext fun z => (innerSL_apply_apply (𝕜 := Real) δ z).symm
  rw [hfun, IsGaussian.map_eq_gaussianReal (innerSL Real δ)]
  -- Mean: E[⟨δ, Z⟩] = ⟨δ, m⟩.
  have hmean :
      (∫ z, (innerSL Real δ) z
        ∂multivariateGaussian m ((σ ^ 2) • (1 : Matrix (Fin d) (Fin d) Real)))
        = inner Real δ m := by
    rw [ContinuousLinearMap.integral_comp_id_comm IsGaussian.integrable_id]
    simp [integral_id_multivariateGaussian, innerSL_apply_apply]
  -- Variance: Var[⟨δ, ·⟩] = δᵀ (σ² I) δ = σ² ‖δ‖².
  have hvar :
      Var[innerSL Real δ;
          multivariateGaussian m ((σ ^ 2) • (1 : Matrix (Fin d) (Fin d) Real))]
        = σ ^ 2 * ‖δ‖ ^ 2 := by
    have hmem :
        MemLp (id : Input d → Input d) 2
          (multivariateGaussian m ((σ ^ 2) • (1 : Matrix (Fin d) (Fin d) Real))) :=
      IsGaussian.memLp_two_id
    have hself :=
      covarianceBilin_self
        (μ := multivariateGaussian m ((σ ^ 2) • (1 : Matrix (Fin d) (Fin d) Real)))
        hmem δ
    -- `covarianceBilin_self` uses `⟪δ, ·⟫`, which is `innerSL δ` on reals.
    simp only [innerSL_apply_apply] at hself ⊢
    have hcov :=
      covarianceBilin_multivariateGaussian (μ := m)
        (S := (σ ^ 2) • (1 : Matrix (Fin d) (Fin d) Real)) hS δ δ
    calc
      Var[fun u : Input d => inner Real δ u;
          multivariateGaussian m ((σ ^ 2) • (1 : Matrix (Fin d) (Fin d) Real))]
          = covarianceBilin
              (multivariateGaussian m ((σ ^ 2) • (1 : Matrix (Fin d) (Fin d) Real)))
              δ δ := hself.symm
      _ = δ ⬝ᵥ ((σ ^ 2) • (1 : Matrix (Fin d) (Fin d) Real)) *ᵥ δ := hcov
      _ = σ ^ 2 * ∑ i : Fin d, (δ i) ^ 2 := quadratic_form_variance_matrix σ δ
      _ = σ ^ 2 * ‖δ‖ ^ 2 := by rw [sum_sq_eq_norm_sq]
  -- Pack mean and variance into `gaussianReal`.
  have hv0 :
      0 ≤
        Var[innerSL Real δ;
            multivariateGaussian m ((σ ^ 2) • (1 : Matrix (Fin d) (Fin d) Real))] :=
    variance_nonneg _ _
  have hvNN :
      Var[innerSL Real δ;
          multivariateGaussian m ((σ ^ 2) • (1 : Matrix (Fin d) (Fin d) Real))].toNNReal
        =
      ⟨σ ^ 2 * ‖δ‖ ^ 2, mul_nonneg (sq_nonneg σ) (sq_nonneg ‖δ‖)⟩ := by
    apply NNReal.coe_injective
    change
      (Var[innerSL Real δ;
          multivariateGaussian m ((σ ^ 2) • (1 : Matrix (Fin d) (Fin d) Real))].toNNReal : Real)
        = σ ^ 2 * ‖δ‖ ^ 2
    rw [Real.coe_toNNReal _ hv0, hvar]
  exact congrArg₂ gaussianReal hmean hvNN



/-! ## Strict monotonicity, symmetry, and quantiles of Φ -/

theorem standardNormalCDF_strictMono : StrictMono standardNormalCDF := by
  intro a b hab
  have hv : (1 : NNReal) ≠ 0 := one_ne_zero
  have hle : (gaussianReal 0 1) (Iic a) ≤ (gaussianReal 0 1) (Iic b) :=
    measure_mono (Iic_subset_Iic.mpr hab.le)
  have hdiff :
      standardNormalCDF b - standardNormalCDF a
        = (gaussianReal 0 1).real (Ioc a b) := by
    simp only [standardNormalCDF, cdf_eq_real, measureReal_def]
    rw [← ENNReal.toReal_sub_of_le hle (measure_ne_top _ _)]
    congr 1
    have hset : Iic b \ Iic a = Ioc a b := by
      ext z
      simp only [Set.mem_sdiff, mem_Iic, mem_Ioc]
      constructor
      · intro ⟨hzb, hna⟩
        exact ⟨lt_of_not_ge hna, hzb⟩
      · intro ⟨hza, hzb⟩
        exact ⟨hzb, not_le.mpr hza⟩
    rw [← hset, measure_sdiff (Iic_subset_Iic.mpr hab.le)
      measurableSet_Iic.nullMeasurableSet (measure_ne_top _ _)]
  have hvol_pos : 0 < (volume : Measure Real) (Ioc a b) := by
    simp [Real.volume_Ioc, hab]
  have habs := gaussianReal_absolutelyContinuous' (μ := 0) (v := 1) hv
  have hμ_ne : (gaussianReal 0 1) (Ioc a b) ≠ 0 := fun h0 =>
    (ne_of_gt hvol_pos) (habs h0)
  have hμ_pos : 0 < (gaussianReal 0 1).real (Ioc a b) := by
    rw [measureReal_def]
    exact ENNReal.toReal_pos hμ_ne (measure_ne_top _ _)
  linarith [hdiff]

theorem standardNormalCDF_neg (r : Real) :
    standardNormalCDF (-r) = 1 - standardNormalCDF r := by
  haveI := nullSingletonClass_gaussianReal (μ := (0 : Real)) (v := 1) one_ne_zero
  have hmap : (gaussianReal 0 1).map (fun x : Real => -x) = gaussianReal 0 1 := by
    simpa using gaussianReal_map_neg (μ := (0 : Real)) (v := 1)
  have hpre : (fun x : Real => -x) ⁻¹' Iic (-r) = Ici r := by
    ext x; simp
  have hrefl :
      (gaussianReal 0 1).real (Iic (-r)) = (gaussianReal 0 1).real (Ici r) := by
    calc
      (gaussianReal 0 1).real (Iic (-r))
          = ((gaussianReal 0 1).map (fun x : Real => -x)).real (Iic (-r)) := by
            rw [hmap]
      _ = (gaussianReal 0 1).real ((fun x : Real => -x) ⁻¹' Iic (-r)) := by
            rw [measureReal_def, measureReal_def,
              Measure.map_apply measurable_neg measurableSet_Iic]
      _ = (gaussianReal 0 1).real (Ici r) := by rw [hpre]
  have hunion : (Ici r ∪ Iio r : Set Real) = univ := by
    ext x
    simp only [mem_union, mem_Ici, mem_Iio, mem_univ, iff_true]
    exact (le_or_gt r x).elim Or.inl Or.inr
  have hdisj : Disjoint (Ici r) (Iio r) := by
    refine disjoint_left.2 fun x (hx1 : x ∈ Ici r) (hx2 : x ∈ Iio r) => ?_
    exact lt_irrefl x (lt_of_lt_of_le hx2 hx1)
  have hsum :
      (gaussianReal 0 1) (Ici r) + (gaussianReal 0 1) (Iio r) = 1 := by
    rw [← measure_union hdisj measurableSet_Iio, hunion, measure_univ]
  have hadd :
      (gaussianReal 0 1).real (Ici r) + (gaussianReal 0 1).real (Iio r) = 1 := by
    simp only [measureReal_def]
    rw [← ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _), hsum,
      ENNReal.toReal_one]
  have hIio :
      (gaussianReal 0 1).real (Iio r) = (gaussianReal 0 1).real (Iic r) := by
    have hset : (Iic r : Set Real) = Iio r ∪ {r} := by
      ext x
      simp only [mem_union, mem_Iic, mem_Iio, mem_singleton_iff]
      constructor
      · intro hx; exact (lt_or_eq_of_le hx).elim Or.inl (fun h => Or.inr h)
      · intro hx; exact hx.elim le_of_lt (fun h => h ▸ le_rfl)
    have hdisj' : Disjoint (Iio r) ({r} : Set Real) := by
      refine disjoint_left.2 fun x hx1 hx2 => ?_
      simp only [mem_Iio, mem_singleton_iff] at hx1 hx2
      exact absurd hx2 (ne_of_lt hx1)
    simp only [measureReal_def]
    rw [hset, measure_union hdisj' (measurableSet_singleton r), measure_singleton,
      add_zero]
  simp only [standardNormalCDF, cdf_eq_real]
  linarith [hrefl, hadd, hIio]

/-- Existence of a real with Φ(q) = p for p ∈ (0,1). -/
theorem exists_standardNormalCDF_eq (p : Set.Ioo (0 : Real) 1) :
    ∃ q : Real, standardNormalCDF q = p.1 := by
  -- Pick a with Φ(a) < p and b with p < Φ(b), then apply IVT.
  have hbot := tendsto_standardNormalCDF_atBot
  have htop := tendsto_standardNormalCDF_atTop
  have ha : ∃ a, standardNormalCDF a < p.1 := by
    have := (tendsto_order.1 hbot).2 p.1 p.2.1
    simp only [eventually_atBot] at this
    obtain ⟨a, ha⟩ := this
    exact ⟨a, ha a le_rfl⟩
  have hb : ∃ b, p.1 < standardNormalCDF b := by
    have := (tendsto_order.1 htop).1 p.1 p.2.2
    simp only [eventually_atTop] at this
    obtain ⟨b, hb⟩ := this
    exact ⟨b, hb b le_rfl⟩
  obtain ⟨a, ha⟩ := ha
  obtain ⟨b, hb⟩ := hb
  have hab : a ≤ b := by
    by_contra h
    have : b < a := lt_of_not_ge h
    have := standardNormalCDF_strictMono this
    linarith
  -- Intermediate value on [a,b]
  have hcont := standardNormalCDF_continuous.continuousOn (s := Icc a b)
  have hex := intermediate_value_Icc hab hcont ⟨ha.le, hb.le⟩
  obtain ⟨x, -, hx⟩ := hex
  exact ⟨x, hx⟩

theorem standardNormalCDF_quantile (p : Set.Ioo (0 : Real) 1) :
    standardNormalCDF (standardNormalQuantile p) = p.1 := by
  -- Let q be the unique point with Φ(q)=p; show sInf equals q.
  obtain ⟨q, hq⟩ := exists_standardNormalCDF_eq p
  -- Show standardNormalQuantile p = q
  have hS : standardNormalQuantile p = q := by
    unfold standardNormalQuantile
    set S := {r : Real | p.1 ≤ standardNormalCDF r}
    have hqS : q ∈ S := by simp [S, hq]
    have hlower : ∀ r ∈ S, q ≤ r := by
      intro r hr
      simp [S] at hr
      by_contra h
      have hlt : r < q := lt_of_not_ge h
      have := standardNormalCDF_strictMono hlt
      linarith [hq]
    -- S is nonempty and bounded below, and q is its least element.
    have hne : S.Nonempty := ⟨q, hqS⟩
    have hbdd : BddBelow S := ⟨q, hlower⟩
    apply le_antisymm
    · exact csInf_le hbdd hqS
    · exact le_csInf hne hlower
  rw [hS, hq]

theorem standardNormalQuantile_strictMono :
    StrictMono standardNormalQuantile := by
  intro p q hpq
  -- Φ⁻¹(p) < Φ⁻¹(q) because Φ is strict mono and Φ(Φ⁻¹ p)=p < q = Φ(Φ⁻¹ q)
  have hp := standardNormalCDF_quantile p
  have hq := standardNormalCDF_quantile q
  have : standardNormalCDF (standardNormalQuantile p)
      < standardNormalCDF (standardNormalQuantile q) := by
    rw [hp, hq]; exact hpq
  exact standardNormalCDF_strictMono.lt_iff_lt.1 this

theorem standardNormalQuantile_one_sub (p : Set.Ioo (0 : Real) 1) :
    standardNormalQuantile (oneSubProbability p)
      = - standardNormalQuantile p := by
  -- Φ(Φ⁻¹(1-p)) = 1-p and Φ(-Φ⁻¹(p)) = 1 - Φ(Φ⁻¹(p)) = 1-p
  have h1 := standardNormalCDF_quantile (oneSubProbability p)
  have h2 := standardNormalCDF_neg (standardNormalQuantile p)
  have h3 := standardNormalCDF_quantile p
  -- So Φ(Φ⁻¹(1-p)) = Φ(-Φ⁻¹(p)), injectivity ⇒ equality
  have : standardNormalCDF (standardNormalQuantile (oneSubProbability p))
      = standardNormalCDF (-standardNormalQuantile p) := by
    rw [h1, h2, h3]
    rfl
  exact standardNormalCDF_strictMono.injective this


/-! ## Integral form of the Gaussian bridge -/

/-- Densities integrate over measurable sets to multivariateGaussian probabilities. -/
theorem integral_isotropicGaussian_eq_multivariateGaussian_apply
    {d : Nat} (m : Input d) (σ : Real) (hσ : 0 < σ)
    (S : Set (Input d)) (hS : MeasurableSet S) :
    (∫ z in S, isotropicGaussianPDF m σ z ∂volume)
      =
    (multivariateGaussian m ((σ ^ 2) • (1 : Matrix (Fin d) (Fin d) Real))).real S := by
  have hbridge := isotropicGaussian_measure_eq m σ hσ
  have hnn : ∀ z, 0 ≤ isotropicGaussianPDF m σ z := isotropicGaussianPDF_nonneg m σ
  have hint : IntegrableOn (isotropicGaussianPDF m σ) S volume :=
    (integrable_isotropicGaussianPDF m σ).integrableOn
  -- Rewrite the multivariateGaussian probability via the density bridge.
  rw [measureReal_def, ← hbridge, withDensity_apply _ hS]
  -- Convert the set integral of a nonnegative function to an ENNReal lintegral.
  have hlin :
      ENNReal.ofReal (∫ z in S, isotropicGaussianPDF m σ z ∂volume)
        =
      ∫⁻ z in S, ENNReal.ofReal (isotropicGaussianPDF m σ z) ∂volume :=
    ofReal_integral_eq_lintegral_ofReal hint
      (ae_restrict_of_forall_mem hS fun _ _ => hnn _)
  -- Take `toReal` of both sides.
  have hnn_int : 0 ≤ ∫ z in S, isotropicGaussianPDF m σ z ∂volume :=
    setIntegral_nonneg hS fun _ _ => hnn _
  rw [← hlin, ENNReal.toReal_ofReal hnn_int]

/-- Centered projection: ⟨δ, X - x⟩ ~ N(0, σ²‖δ‖²) for X ~ N(x, σ² I). -/
theorem isotropicGaussian_inner_projection
    {d : Nat} (x δ : Input d) (σ : Real) (hσ : 0 < σ) :
    (multivariateGaussian x ((σ ^ 2) • (1 : Matrix (Fin d) (Fin d) Real))).map
        (fun z => inner Real δ (z - x))
      =
    gaussianReal 0 ⟨σ ^ 2 * ‖δ‖ ^ 2, mul_nonneg (sq_nonneg σ) (sq_nonneg ‖δ‖)⟩ := by
  -- Package the variance as an `NNReal` to avoid subtype-transparency issues.
  let v : NNReal := ⟨σ ^ 2 * ‖δ‖ ^ 2, mul_nonneg (sq_nonneg σ) (sq_nonneg ‖δ‖)⟩
  -- ⟨δ, z - x⟩ = ⟨δ, z⟩ - ⟨δ, x⟩
  have hfun :
      (fun z : Input d => inner Real δ (z - x))
        =
      (fun t : Real => t - inner Real δ x) ∘ fun z => inner Real δ z := by
    funext z
    simp [inner_sub_right]
  rw [hfun, ← Measure.map_map (by fun_prop) (by fun_prop)]
  have hmap := map_inner_multivariateGaussian x δ σ hσ
  -- Identify the packed variance with `v`.
  have hv : (⟨σ ^ 2 * ‖δ‖ ^ 2, mul_nonneg (sq_nonneg σ) (sq_nonneg ‖δ‖)⟩ : NNReal) = v := rfl
  rw [hv] at hmap ⊢
  rw [hmap, gaussianReal_map_sub_const]
  simp


/-! ## One-dimensional scaling and half-space probabilities -/

/-- If `Z ~ N(0, τ²)` and `τ > 0`, then `Z/τ ~ N(0,1)`. -/
theorem gaussianReal_map_div_scale
    (τ : Real) (hτ : 0 < τ) :
    (gaussianReal 0 (τ ^ 2).toNNReal).map (fun z => z / τ)
      = gaussianReal 0 1 := by
  have hτ0 : τ ≠ 0 := ne_of_gt hτ
  have hpos : 0 ≤ τ ^ 2 := sq_nonneg τ
  have hfun : (fun z : Real => z / τ) = fun z => τ⁻¹ * z := by
    funext z; field_simp [hτ0]
  rw [hfun, gaussianReal_map_const_mul]
  refine congrArg₂ gaussianReal (by ring) ?_
  apply NNReal.coe_injective
  have hpos' : 0 ≤ τ⁻¹ ^ 2 := sq_nonneg _
  simp [Real.coe_toNNReal, hpos, hpos', NNReal.coe_mul]
  field_simp [hτ0]

theorem acceptanceHalfspace_eq_preimage
    {d : Nat} (x δ : Input d) (σ : Real)
    (pA : Set.Ioo (0 : Real) 1) :
    acceptanceHalfspace x δ σ pA
      =
    (fun z => inner Real δ (z - x)) ⁻¹'
      (Iic (σ * ‖δ‖ * standardNormalQuantile pA)) := rfl

theorem measurableSet_acceptanceHalfspace
    {d : Nat} (x δ : Input d) (σ : Real)
    (pA : Set.Ioo (0 : Real) 1) :
    MeasurableSet (acceptanceHalfspace x δ σ pA) := by
  rw [acceptanceHalfspace_eq_preimage]
  exact measurableSet_Iic.preimage (by fun_prop)

theorem measurableSet_competitorHalfspace
    {d : Nat} (x δ : Input d) (σ : Real)
    (pB : Set.Ioo (0 : Real) 1) :
    MeasurableSet (competitorHalfspace x δ σ pB) := by
  change MeasurableSet
    ((fun z => inner Real δ (z - x)) ⁻¹'
      (Ici (σ * ‖δ‖ * standardNormalQuantile (oneSubProbability pB))))
  exact measurableSet_Ici.preimage (by fun_prop)

/-- Identify the packed variance used by the projection with `toNNReal`. -/
theorem variance_toNNReal_eq
    (σ : Real) (δnorm : Real) :
    (⟨σ ^ 2 * δnorm ^ 2, mul_nonneg (sq_nonneg σ) (sq_nonneg δnorm)⟩ : NNReal)
      = ((σ * δnorm) ^ 2).toNNReal := by
  apply NNReal.coe_injective
  have hnn : 0 ≤ (σ * δnorm) ^ 2 := sq_nonneg _
  rw [Real.coe_toNNReal _ hnn]
  -- Both sides are σ² δnorm² after unfolding the subtype coercion.
  change σ ^ 2 * δnorm ^ 2 = (σ * δnorm) ^ 2
  ring

/-- Helper: for standard normal W, P(W ≥ -q) = Φ(q). -/
theorem standardNormal_real_Ici_neg (q : Real) :
    (gaussianReal 0 1).real (Ici (-q)) = standardNormalCDF q := by
  haveI := nullSingletonClass_gaussianReal (μ := (0 : Real)) (v := 1) one_ne_zero
  -- P(Ici (-q)) + P(Iio (-q)) = 1 and P(Iio (-q)) = P(Iic (-q)) = Φ(-q)
  have hIio :
      (gaussianReal 0 1).real (Iio (-q)) = (gaussianReal 0 1).real (Iic (-q)) := by
    have hset : (Iic (-q) : Set Real) = Iio (-q) ∪ {-q} := by
      ext t
      simp only [mem_union, mem_Iic, mem_Iio, mem_singleton_iff]
      constructor
      · intro ht; exact (lt_or_eq_of_le ht).elim Or.inl Or.inr
      · intro ht; exact ht.elim le_of_lt (fun h => h ▸ le_rfl)
    have hdisj : Disjoint (Iio (-q)) ({-q} : Set Real) := by
      refine disjoint_left.2 fun t ht1 ht2 => ?_
      simp only [mem_Iio, mem_singleton_iff] at ht1 ht2
      exact absurd ht2 (ne_of_lt ht1)
    simp only [measureReal_def]
    rw [hset, measure_union hdisj (measurableSet_singleton _), measure_singleton, add_zero]
  have hunion : (Ici (-q) ∪ Iio (-q) : Set Real) = univ := by
    ext t
    simp only [mem_union, mem_Ici, mem_Iio, mem_univ, iff_true]
    exact (le_or_gt (-q) t).elim Or.inl Or.inr
  have hdisj : Disjoint (Ici (-q)) (Iio (-q)) := by
    refine disjoint_left.2 fun t (ht1 : t ∈ Ici (-q)) (ht2 : t ∈ Iio (-q)) => ?_
    exact lt_irrefl t (lt_of_lt_of_le ht2 ht1)
  have hadd :
      (gaussianReal 0 1).real (Ici (-q)) + (gaussianReal 0 1).real (Iio (-q)) = 1 := by
    simp only [measureReal_def]
    have hsum :
        (gaussianReal 0 1) (Ici (-q)) + (gaussianReal 0 1) (Iio (-q)) = 1 := by
      rw [← measure_union hdisj measurableSet_Iio, hunion, measure_univ]
    rw [← ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _), hsum,
      ENNReal.toReal_one]
  have hΦ : (gaussianReal 0 1).real (Iic (-q)) = standardNormalCDF (-q) := by
    simp [standardNormalCDF, cdf_eq_real]
  have hsym := standardNormalCDF_neg q
  linarith [hadd, hIio, hΦ, hsym]

/-- Base probability of the acceptance half-space under `N(x, σ² I)`. -/
theorem prob_X_acceptanceHalfspace
    {d : Nat} (x δ : Input d) (σ : Real) (hσ : 0 < σ)
    (hδ : δ ≠ 0) (pA : Set.Ioo (0 : Real) 1) :
    (∫ z in acceptanceHalfspace x δ σ pA,
        isotropicGaussianPDF x σ z ∂volume)
      = pA.1 := by
  have hnorm : 0 < ‖δ‖ := norm_pos_iff.mpr hδ
  have hS := measurableSet_acceptanceHalfspace x δ σ pA
  rw [integral_isotropicGaussian_eq_multivariateGaussian_apply x σ hσ _ hS,
    acceptanceHalfspace_eq_preimage]
  have hmap := isotropicGaussian_inner_projection x δ σ hσ
  have ht : MeasurableSet (Iic (σ * ‖δ‖ * standardNormalQuantile pA)) :=
    measurableSet_Iic
  have hprob :
      (multivariateGaussian x ((σ ^ 2) • (1 : Matrix (Fin d) (Fin d) Real))).real
          ((fun z => inner Real δ (z - x)) ⁻¹'
            (Iic (σ * ‖δ‖ * standardNormalQuantile pA)))
        =
      (gaussianReal 0 ⟨σ ^ 2 * ‖δ‖ ^ 2,
          mul_nonneg (sq_nonneg σ) (sq_nonneg ‖δ‖)⟩).real
        (Iic (σ * ‖δ‖ * standardNormalQuantile pA)) := by
    rw [measureReal_def, measureReal_def,
      ← Measure.map_apply (by fun_prop) ht, hmap]
  rw [hprob]
  set τ : Real := σ * ‖δ‖
  have hτ : 0 < τ := mul_pos hσ hnorm
  have hv := variance_toNNReal_eq σ ‖δ‖
  -- Align variance packaging with the scaling lemma.
  have hprob' :
      (gaussianReal 0 ⟨σ ^ 2 * ‖δ‖ ^ 2,
          mul_nonneg (sq_nonneg σ) (sq_nonneg ‖δ‖)⟩).real
        (Iic (τ * standardNormalQuantile pA))
        =
      (gaussianReal 0 (τ ^ 2).toNNReal).real
        (Iic (τ * standardNormalQuantile pA)) := by
    simp [hv, τ]
  have hthresh :
      σ * ‖δ‖ * standardNormalQuantile pA = τ * standardNormalQuantile pA := by
    simp [τ]
  rw [hthresh, hprob']
  -- Standardise by dividing by τ.
  have hscale := gaussianReal_map_div_scale τ hτ
  have hqset :
      (fun z : Real => z / τ) ⁻¹' Iic (standardNormalQuantile pA)
        = Iic (τ * standardNormalQuantile pA) := by
    ext z
    simp [div_le_iff₀ hτ, mul_comm]
  have hstd :
      (gaussianReal 0 (τ ^ 2).toNNReal).real (Iic (τ * standardNormalQuantile pA))
        =
      (gaussianReal 0 1).real (Iic (standardNormalQuantile pA)) := by
    rw [measureReal_def, measureReal_def, ← hscale,
      Measure.map_apply (by fun_prop) measurableSet_Iic, hqset]
  rw [hstd, ← cdf_eq_real, ← standardNormalCDF, standardNormalCDF_quantile]

/-- Base probability of the competitor half-space under `N(x, σ² I)`. -/
theorem prob_X_competitorHalfspace
    {d : Nat} (x δ : Input d) (σ : Real) (hσ : 0 < σ)
    (hδ : δ ≠ 0) (pB : Set.Ioo (0 : Real) 1) :
    (∫ z in competitorHalfspace x δ σ pB,
        isotropicGaussianPDF x σ z ∂volume)
      = pB.1 := by
  have hnorm : 0 < ‖δ‖ := norm_pos_iff.mpr hδ
  have hS := measurableSet_competitorHalfspace x δ σ pB
  rw [integral_isotropicGaussian_eq_multivariateGaussian_apply x σ hσ _ hS]
  -- Competitor = {⟨δ,z-x⟩ ≥ σ‖δ‖ Φ⁻¹(1-pB)} = {⟨δ,z-x⟩ ≥ -σ‖δ‖ Φ⁻¹(pB)}
  have hqs := standardNormalQuantile_one_sub pB
  set τ : Real := σ * ‖δ‖
  have hτ : 0 < τ := mul_pos hσ hnorm
  have hmap := isotropicGaussian_inner_projection x δ σ hσ
  have ht : MeasurableSet
      (Ici (σ * ‖δ‖ * standardNormalQuantile (oneSubProbability pB))) :=
    measurableSet_Ici
  have hprob :
      (multivariateGaussian x ((σ ^ 2) • (1 : Matrix (Fin d) (Fin d) Real))).real
          (competitorHalfspace x δ σ pB)
        =
      (gaussianReal 0 ⟨σ ^ 2 * ‖δ‖ ^ 2,
          mul_nonneg (sq_nonneg σ) (sq_nonneg ‖δ‖)⟩).real
        (Ici (σ * ‖δ‖ * standardNormalQuantile (oneSubProbability pB))) := by
    change
      (multivariateGaussian x ((σ ^ 2) • (1 : Matrix (Fin d) (Fin d) Real))).real
          ((fun z => inner Real δ (z - x)) ⁻¹'
            (Ici (σ * ‖δ‖ * standardNormalQuantile (oneSubProbability pB))))
        =
      _
    rw [measureReal_def, measureReal_def,
      ← Measure.map_apply (by fun_prop) ht, hmap]
  rw [hprob, hqs]
  -- Threshold is τ * (-Φ⁻¹(pB)) = -τ Φ⁻¹(pB)
  have hthresh :
      σ * ‖δ‖ * (-standardNormalQuantile pB) = - (τ * standardNormalQuantile pB) := by
    simp [τ]
  rw [hthresh]
  have hv := variance_toNNReal_eq σ ‖δ‖
  have hprob' :
      (gaussianReal 0 ⟨σ ^ 2 * ‖δ‖ ^ 2,
          mul_nonneg (sq_nonneg σ) (sq_nonneg ‖δ‖)⟩).real
        (Ici (-(τ * standardNormalQuantile pB)))
        =
      (gaussianReal 0 (τ ^ 2).toNNReal).real
        (Ici (-(τ * standardNormalQuantile pB))) := by
    simp [hv, τ]
  rw [hprob']
  -- P(Z ≥ -τ q) = P(Z/τ ≥ -q) = P(W ≥ -q) = P(W ≤ q) = Φ(q) = pB
  -- since W ~ N(0,1) and by symmetry P(W ≥ -q) = P(W ≤ q)
  have hscale := gaussianReal_map_div_scale τ hτ
  have hqset :
      (fun z : Real => z / τ) ⁻¹' Ici (-standardNormalQuantile pB)
        = Ici (-(τ * standardNormalQuantile pB)) := by
    ext z
    simp [le_div_iff₀ hτ]
    constructor <;> intro h <;> linarith
  have hstd :
      (gaussianReal 0 (τ ^ 2).toNNReal).real
          (Ici (-(τ * standardNormalQuantile pB)))
        =
      (gaussianReal 0 1).real (Ici (-standardNormalQuantile pB)) := by
    rw [measureReal_def, measureReal_def, ← hscale,
      Measure.map_apply (by fun_prop) measurableSet_Ici, hqset]
  rw [hstd, standardNormal_real_Ici_neg, standardNormalCDF_quantile]


/-! ## Shifted projections and Y-halfspace probabilities -/

theorem isotropicGaussian_inner_projection_shifted
    {d : Nat} (x δ : Input d) (σ : Real) (hσ : 0 < σ) :
    (multivariateGaussian (x + δ) ((σ ^ 2) • (1 : Matrix (Fin d) (Fin d) Real))).map
        (fun z => inner Real δ (z - x))
      =
    gaussianReal (‖δ‖ ^ 2)
      ⟨σ ^ 2 * ‖δ‖ ^ 2, mul_nonneg (sq_nonneg σ) (sq_nonneg ‖δ‖)⟩ := by
  have hfun :
      (fun z : Input d => inner Real δ (z - x))
        =
      (fun t : Real => ‖δ‖ ^ 2 + t) ∘ fun z => inner Real δ (z - (x + δ)) := by
    funext z
    have hlin : z - x = z - (x + δ) + δ := by abel
    calc
      inner Real δ (z - x)
          = inner Real δ (z - (x + δ) + δ) := by rw [hlin]
      _ = inner Real δ (z - (x + δ)) + inner Real δ δ := inner_add_right _ _ _
      _ = inner Real δ (z - (x + δ)) + ‖δ‖ ^ 2 := by rw [real_inner_self_eq_norm_sq]
      _ = ‖δ‖ ^ 2 + inner Real δ (z - (x + δ)) := add_comm _ _
  rw [hfun, ← Measure.map_map (by fun_prop) (by fun_prop)]
  let v : NNReal := ⟨σ ^ 2 * ‖δ‖ ^ 2, mul_nonneg (sq_nonneg σ) (sq_nonneg ‖δ‖)⟩
  have hmap := isotropicGaussian_inner_projection (x + δ) δ σ hσ
  have hv : (⟨σ ^ 2 * ‖δ‖ ^ 2, mul_nonneg (sq_nonneg σ) (sq_nonneg ‖δ‖)⟩ : NNReal) = v := rfl
  rw [hv] at hmap ⊢
  rw [hmap, gaussianReal_map_const_add]
  simp

theorem gaussianReal_center (μ : Real) (v : NNReal) :
    (gaussianReal μ v).map (fun z => z - μ) = gaussianReal 0 v := by
  rw [gaussianReal_map_sub_const]; simp

theorem gaussianReal_cdf_standardize
    (m t τ : Real) (hτ : 0 < τ) :
    (gaussianReal m (τ ^ 2).toNNReal).real (Iic t)
      = standardNormalCDF ((t - m) / τ) := by
  have hcenter := gaussianReal_center m (τ ^ 2).toNNReal
  have hpre : (fun z : Real => z - m) ⁻¹' Iic (t - m) = Iic t := by
    ext z
    simp only [mem_preimage, mem_Iic]
    constructor <;> intro h <;> linarith
  have h1 :
      (gaussianReal m (τ ^ 2).toNNReal).real (Iic t)
        = (gaussianReal 0 (τ ^ 2).toNNReal).real (Iic (t - m)) := by
    rw [measureReal_def, measureReal_def, ← hcenter,
      Measure.map_apply (by fun_prop) measurableSet_Iic, hpre]
  rw [h1]
  have hscale := gaussianReal_map_div_scale τ hτ
  have hpre2 :
      (fun z : Real => z / τ) ⁻¹' Iic ((t - m) / τ) = Iic (t - m) := by
    ext z
    simp only [mem_preimage, mem_Iic]
    constructor
    · intro h
      -- z/τ ≤ (t-m)/τ
      have := (div_le_div_iff_of_pos_right hτ).1 h
      simpa using this
    · intro h
      exact (div_le_div_iff_of_pos_right hτ).2 (by simpa using h)
  have hstd :
      (gaussianReal 0 (τ ^ 2).toNNReal).real (Iic (t - m))
        = (gaussianReal 0 1).real (Iic ((t - m) / τ)) := by
    rw [measureReal_def, measureReal_def, ← hscale,
      Measure.map_apply (by fun_prop) measurableSet_Iic, hpre2]
  rw [hstd, ← cdf_eq_real, ← standardNormalCDF]

theorem prob_Y_acceptanceHalfspace
    {d : Nat} (x δ : Input d) (σ : Real) (hσ : 0 < σ)
    (hδ : δ ≠ 0) (pA : Set.Ioo (0 : Real) 1) :
    (∫ z in acceptanceHalfspace x δ σ pA,
        isotropicGaussianPDF (x + δ) σ z ∂volume)
      =
    standardNormalCDF (standardNormalQuantile pA - ‖δ‖ / σ) := by
  have hnorm : 0 < ‖δ‖ := norm_pos_iff.mpr hδ
  have hS := measurableSet_acceptanceHalfspace x δ σ pA
  rw [integral_isotropicGaussian_eq_multivariateGaussian_apply (x + δ) σ hσ _ hS,
    acceptanceHalfspace_eq_preimage]
  have hmap := isotropicGaussian_inner_projection_shifted x δ σ hσ
  have ht : MeasurableSet (Iic (σ * ‖δ‖ * standardNormalQuantile pA)) :=
    measurableSet_Iic
  have hprob :
      (multivariateGaussian (x + δ) ((σ ^ 2) • (1 : Matrix (Fin d) (Fin d) Real))).real
          ((fun z => inner Real δ (z - x)) ⁻¹'
            (Iic (σ * ‖δ‖ * standardNormalQuantile pA)))
        =
      (gaussianReal (‖δ‖ ^ 2) ⟨σ ^ 2 * ‖δ‖ ^ 2,
          mul_nonneg (sq_nonneg σ) (sq_nonneg ‖δ‖)⟩).real
        (Iic (σ * ‖δ‖ * standardNormalQuantile pA)) := by
    rw [measureReal_def, measureReal_def,
      ← Measure.map_apply (by fun_prop) ht, hmap]
  rw [hprob]
  set τ : Real := σ * ‖δ‖
  have hτ : 0 < τ := mul_pos hσ hnorm
  have hv := variance_toNNReal_eq σ ‖δ‖
  have hthresh :
      σ * ‖δ‖ * standardNormalQuantile pA = τ * standardNormalQuantile pA := rfl
  have hpack :
      (gaussianReal (‖δ‖ ^ 2) ⟨σ ^ 2 * ‖δ‖ ^ 2,
          mul_nonneg (sq_nonneg σ) (sq_nonneg ‖δ‖)⟩).real
        (Iic (τ * standardNormalQuantile pA))
        =
      (gaussianReal (‖δ‖ ^ 2) (τ ^ 2).toNNReal).real
        (Iic (τ * standardNormalQuantile pA)) := by
    simp only [hv, τ]
  rw [hthresh, hpack, gaussianReal_cdf_standardize _ _ _ hτ]
  have hσ0 : σ ≠ 0 := ne_of_gt hσ
  have hn0 : ‖δ‖ ≠ 0 := ne_of_gt hnorm
  have hτ0 : τ ≠ 0 := ne_of_gt hτ
  have harg :
      (τ * standardNormalQuantile pA - ‖δ‖ ^ 2) / τ
        = standardNormalQuantile pA - ‖δ‖ / σ := by
    calc
      (τ * standardNormalQuantile pA - ‖δ‖ ^ 2) / τ
          = standardNormalQuantile pA - ‖δ‖ ^ 2 / τ := by
            field_simp [hτ0]
      _ = standardNormalQuantile pA - ‖δ‖ / σ := by
            change standardNormalQuantile pA - ‖δ‖ ^ 2 / (σ * ‖δ‖)
              = standardNormalQuantile pA - ‖δ‖ / σ
            field_simp [hσ0, hn0]
  rw [harg]

theorem shifted_halfspace_probability_lt
    (σ : Real) (hσ : 0 < σ) (δnorm : Real)
    (pA pB : Set.Ioo (0 : Real) 1)
    (hRadius :
      δnorm < (σ / 2) * (standardNormalQuantile pA - standardNormalQuantile pB)) :
    standardNormalCDF (standardNormalQuantile pB + δnorm / σ)
      <
    standardNormalCDF (standardNormalQuantile pA - δnorm / σ) := by
  have hσ0 : σ ≠ 0 := ne_of_gt hσ
  have hq :
      standardNormalQuantile pB + δnorm / σ
        <
      standardNormalQuantile pA - δnorm / σ := by
    -- From δnorm < (σ/2)(qA - qB), divide by σ > 0:
    -- δnorm/σ < (1/2)(qA - qB), hence qB + δnorm/σ < qA - δnorm/σ.
    have hdiv := div_lt_div_of_pos_right hRadius hσ
    -- hdiv: δnorm/σ < ((σ/2)*(qA-qB))/σ
    have hrhs :
        ((σ / 2) * (standardNormalQuantile pA - standardNormalQuantile pB)) / σ
          =
        (1 / 2) * (standardNormalQuantile pA - standardNormalQuantile pB) := by
      calc
        ((σ / 2) * (standardNormalQuantile pA - standardNormalQuantile pB)) / σ
            = (σ / 2) / σ * (standardNormalQuantile pA - standardNormalQuantile pB) := by
              ring
        _ = (1 / 2) * (standardNormalQuantile pA - standardNormalQuantile pB) := by
              field_simp [hσ0]
    have hhalf :
        δnorm / σ
          <
        (1 / 2) * (standardNormalQuantile pA - standardNormalQuantile pB) := by
      rwa [← hrhs]
    linarith
  exact standardNormalCDF_strictMono hq


/-- Shifted competitor probability: P_Y(B) = Φ(Φ⁻¹(p_B) + ‖δ‖/σ). -/
theorem prob_Y_competitorHalfspace
    {d : Nat} (x δ : Input d) (σ : Real) (hσ : 0 < σ)
    (hδ : δ ≠ 0) (pB : Set.Ioo (0 : Real) 1) :
    (∫ z in competitorHalfspace x δ σ pB,
        isotropicGaussianPDF (x + δ) σ z ∂volume)
      =
    standardNormalCDF (standardNormalQuantile pB + ‖δ‖ / σ) := by
  have hnorm : 0 < ‖δ‖ := norm_pos_iff.mpr hδ
  have hS := measurableSet_competitorHalfspace x δ σ pB
  rw [integral_isotropicGaussian_eq_multivariateGaussian_apply (x + δ) σ hσ _ hS]
  have hqs := standardNormalQuantile_one_sub pB
  set τ : Real := σ * ‖δ‖
  have hτ : 0 < τ := mul_pos hσ hnorm
  have hmap := isotropicGaussian_inner_projection_shifted x δ σ hσ
  have ht : MeasurableSet
      (Ici (σ * ‖δ‖ * standardNormalQuantile (oneSubProbability pB))) :=
    measurableSet_Ici
  have hprob :
      (multivariateGaussian (x + δ) ((σ ^ 2) • (1 : Matrix (Fin d) (Fin d) Real))).real
          (competitorHalfspace x δ σ pB)
        =
      (gaussianReal (‖δ‖ ^ 2) ⟨σ ^ 2 * ‖δ‖ ^ 2,
          mul_nonneg (sq_nonneg σ) (sq_nonneg ‖δ‖)⟩).real
        (Ici (σ * ‖δ‖ * standardNormalQuantile (oneSubProbability pB))) := by
    change
      (multivariateGaussian (x + δ) ((σ ^ 2) • (1 : Matrix (Fin d) (Fin d) Real))).real
          ((fun z => inner Real δ (z - x)) ⁻¹'
            (Ici (σ * ‖δ‖ * standardNormalQuantile (oneSubProbability pB))))
        = _
    rw [measureReal_def, measureReal_def,
      ← Measure.map_apply (by fun_prop) ht, hmap]
  rw [hprob, hqs]
  have hthresh :
      σ * ‖δ‖ * (-standardNormalQuantile pB) = -(τ * standardNormalQuantile pB) := by
    simp [τ]
  rw [hthresh]
  have hv := variance_toNNReal_eq σ ‖δ‖
  have hpack :
      (gaussianReal (‖δ‖ ^ 2) ⟨σ ^ 2 * ‖δ‖ ^ 2,
          mul_nonneg (sq_nonneg σ) (sq_nonneg ‖δ‖)⟩).real
        (Ici (-(τ * standardNormalQuantile pB)))
        =
      (gaussianReal (‖δ‖ ^ 2) (τ ^ 2).toNNReal).real
        (Ici (-(τ * standardNormalQuantile pB))) := by
    simp only [hv, τ]
  rw [hpack]
  -- P(Z ≥ -τ q) = 1 - P(Z < -τ q) = 1 - P(Z ≤ -τ q) = 1 - Φ((-τ q - ‖δ‖²)/τ)
  --             = 1 - Φ(-q - ‖δ‖/σ) = Φ(q + ‖δ‖/σ)
  set a : Real := τ * standardNormalQuantile pB
  haveI : NullSingletonClass (gaussianReal (‖δ‖ ^ 2) (τ ^ 2).toNNReal) := by
    have hvne : (τ ^ 2).toNNReal ≠ 0 := by
      apply Subtype.coe_ne_coe.mp
      have : 0 < τ ^ 2 := sq_pos_of_pos hτ
      simp [Real.coe_toNNReal _ (le_of_lt this), this.ne']
    exact nullSingletonClass_gaussianReal hvne
  have hIio :
      (gaussianReal (‖δ‖ ^ 2) (τ ^ 2).toNNReal).real (Iio (-a))
        =
      (gaussianReal (‖δ‖ ^ 2) (τ ^ 2).toNNReal).real (Iic (-a)) := by
    have hset : (Iic (-a) : Set Real) = Iio (-a) ∪ {-a} := by
      ext t
      simp only [mem_union, mem_Iic, mem_Iio, mem_singleton_iff]
      constructor
      · intro ht; exact (lt_or_eq_of_le ht).elim Or.inl Or.inr
      · intro ht; exact ht.elim le_of_lt (fun h => h ▸ le_rfl)
    have hdisj : Disjoint (Iio (-a)) ({-a} : Set Real) := by
      refine disjoint_left.2 fun t ht1 ht2 => ?_
      simp only [mem_Iio, mem_singleton_iff] at ht1 ht2
      exact absurd ht2 (ne_of_lt ht1)
    simp only [measureReal_def]
    rw [hset, measure_union hdisj (measurableSet_singleton _), measure_singleton, add_zero]
  have hunion : (Ici (-a) ∪ Iio (-a) : Set Real) = univ := by
    ext t
    simp only [mem_union, mem_Ici, mem_Iio, mem_univ, iff_true]
    exact (le_or_gt (-a) t).elim Or.inl Or.inr
  have hdisj : Disjoint (Ici (-a)) (Iio (-a)) := by
    refine disjoint_left.2 fun t (ht1 : t ∈ Ici (-a)) (ht2 : t ∈ Iio (-a)) => ?_
    exact lt_irrefl t (lt_of_lt_of_le ht2 ht1)
  have hadd :
      (gaussianReal (‖δ‖ ^ 2) (τ ^ 2).toNNReal).real (Ici (-a))
        +
      (gaussianReal (‖δ‖ ^ 2) (τ ^ 2).toNNReal).real (Iio (-a))
        = 1 := by
    simp only [measureReal_def]
    have hsum :
        (gaussianReal (‖δ‖ ^ 2) (τ ^ 2).toNNReal) (Ici (-a))
          +
        (gaussianReal (‖δ‖ ^ 2) (τ ^ 2).toNNReal) (Iio (-a))
          = 1 := by
      rw [← measure_union hdisj measurableSet_Iio, hunion, measure_univ]
    rw [← ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _), hsum,
      ENNReal.toReal_one]
  have hcdf := gaussianReal_cdf_standardize (‖δ‖ ^ 2) (-a) τ hτ
  -- Φ((-a - ‖δ‖²)/τ) = standardNormalCDF ...
  have harg :
      (-a - ‖δ‖ ^ 2) / τ = -(standardNormalQuantile pB + ‖δ‖ / σ) := by
    simp only [a, τ]
    have hσ0 : σ ≠ 0 := ne_of_gt hσ
    have hn0 : ‖δ‖ ≠ 0 := ne_of_gt hnorm
    have hτ0 : τ ≠ 0 := ne_of_gt hτ
    field_simp [hσ0, hn0, hτ0]
    ring
  -- Goal uses a = τ q
  have ha_def : a = τ * standardNormalQuantile pB := rfl
  -- Assemble
  have hΦneg :
      (gaussianReal (‖δ‖ ^ 2) (τ ^ 2).toNNReal).real (Iic (-a))
        =
      standardNormalCDF (-(standardNormalQuantile pB + ‖δ‖ / σ)) := by
    rw [hcdf, harg]
  have hsym :=
    standardNormalCDF_neg (standardNormalQuantile pB + ‖δ‖ / σ)
  -- P(Ici) = 1 - P(Iio) = 1 - P(Iic) = 1 - Φ(-(...)) = Φ(...)
  -- Need to unfold a in the goal
  change
    (gaussianReal (‖δ‖ ^ 2) (τ ^ 2).toNNReal).real
        (Ici (-(τ * standardNormalQuantile pB)))
      =
    standardNormalCDF (standardNormalQuantile pB + ‖δ‖ / σ)
  -- a = τ q, so -a = -(τ q)
  have haeq : -a = -(τ * standardNormalQuantile pB) := by simp [a]
  rw [← haeq]
  linarith [hadd, hIio, hΦneg, hsym]

/-- **Hyperplanes are Lebesgue-null under any (non-degenerate) isotropic
Gaussian.** For `δ ≠ 0` and `σ > 0`, the affine hyperplane
`{z | ⟨δ, z⟩ = β}` has measure zero under `N(m, σ² I)`.

Intuitively, `N(m, σ² I)` has a genuine `d`-dimensional density, so any
`(d−1)`-dimensional affine subspace — including every hyperplane — is a null
set for it. The formal proof avoids Hausdorff-measure/dimension arguments
entirely and instead reuses the projection machinery: the hyperplane is the
preimage `{z | ⟨δ,z⟩ = β}` of the single point `{β}` under the linear
functional `z ↦ ⟨δ,z⟩`, and that functional pushes `N(m,σ²I)` forward to the
1D law `N(⟨δ,m⟩, σ²‖δ‖²)` (`map_inner_multivariateGaussian`). Since `δ ≠ 0`
and `σ > 0` make this variance `σ²‖δ‖²` strictly positive, the pushed-forward
law is a genuine (non-degenerate) Gaussian, which — like every 1D Gaussian —
assigns zero mass to every single point (`nullSingletonClass_gaussianReal`).
Pulling that back along the (measure-preserving, in distribution) projection
gives measure zero for the hyperplane itself.

This lemma is what justifies treating the closed half-spaces
`acceptanceHalfspace`/`competitorHalfspace` (defined with `≤`/`≥`) and their
open variants (`<`/`>`) as probabilistically interchangeable elsewhere in the
development: they differ only by the boundary hyperplane
`{z | ⟨δ, z − x⟩ = threshold}`, which this lemma shows is invisible to any
isotropic Gaussian probability. -/
theorem gaussian_hyperplane_measure_zero
    {d : Nat} (m δ : Input d) (σ : Real) (hσ : 0 < σ)
    (hδ : δ ≠ 0) (β : Real) :
    (multivariateGaussian m ((σ ^ 2) • (1 : Matrix (Fin d) (Fin d) Real)))
        {z | inner Real δ z = β}
      = 0 := by
  have hnorm : 0 < ‖δ‖ := norm_pos_iff.mpr hδ
  -- The hyperplane is the preimage of the single point {β} under z ↦ ⟨δ,z⟩.
  change (multivariateGaussian m ((σ ^ 2) • (1 : Matrix (Fin d) (Fin d) Real)))
      ((fun z => inner Real δ z) ⁻¹' {β}) = 0
  have hmap := map_inner_multivariateGaussian m δ σ hσ
  have hvne :
      (⟨σ ^ 2 * ‖δ‖ ^ 2, mul_nonneg (sq_nonneg σ) (sq_nonneg ‖δ‖)⟩ : NNReal) ≠ 0 := by
    apply Subtype.coe_ne_coe.mp
    exact (mul_pos (sq_pos_of_pos hσ) (sq_pos_of_pos hnorm)).ne'
  haveI := nullSingletonClass_gaussianReal
    (μ := inner Real δ m)
    (v := ⟨σ ^ 2 * ‖δ‖ ^ 2, mul_nonneg (sq_nonneg σ) (sq_nonneg ‖δ‖)⟩) hvne
  rw [← Measure.map_apply (by fun_prop) (measurableSet_singleton β), hmap,
    measure_singleton]


end

end RandomizedSmoothing
