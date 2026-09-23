import RandomizedSmoothing.Lemma3
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
-- import ProofTreeWidget

/-!
# Lemma 4: Neyman-Pearson for isotropic Gaussians

This file specialises Lemma 3 to isotropic Gaussian noise on Euclidean space.

Mathematically (Appendix A of Cohen-Rosenfeld-Kolter):

* the isotropic Gaussian density is a product of one-dimensional Gaussian PDFs;
* its likelihood-ratio regions against a mean-shifted copy are Euclidean half-spaces;
* therefore Lemma 3 specialises to the half-space forms of Lemma 4.
-/

namespace RandomizedSmoothing

open MeasureTheory ProbabilityTheory WithLp
open scoped BigOperators

noncomputable section

-- show_panel_widgets [ProofTreeWidget]

/-! ## Input space -/

/-- The input space `R^d`. -/
abbrev Input (d : Nat) :=
  EuclideanSpace Real (Fin d)

/-- Per-coordinate variance `σ^2` as an `NNReal`, for Mathlib's `gaussianPDFReal`. -/
def gaussianVariance (σ : Real) : NNReal :=
  ⟨σ ^ 2, sq_nonneg σ⟩

theorem gaussianVariance_ne_zero {σ : Real} (hσ : 0 < σ) :
    gaussianVariance σ ≠ 0 := by
  apply Subtype.coe_ne_coe.mp
  exact (sq_pos_of_pos hσ).ne'

/-! ## Explicit isotropic Gaussian PDF

We use the product of one-dimensional Gaussians:

```
mu_{m,σ}(z) = ∏ i, gaussianPDFReal (m i) σ^2 (z i)
```

Normalisation then follows from Fubini and `integral_gaussianPDFReal_eq_one`.
-/

/-- Isotropic Gaussian PDF on `R^d` with mean `m` and variance `σ^2` per coordinate. -/
def isotropicGaussianPDF {d : Nat} (m : Input d) (σ : Real) (z : Input d) : Real :=
  ∏ i : Fin d, gaussianPDFReal (m i) (gaussianVariance σ) (z i)

theorem measurable_isotropicGaussianPDF {d : Nat} (m : Input d) (σ : Real) :
    Measurable (isotropicGaussianPDF m σ) := by
  unfold isotropicGaussianPDF
  refine Finset.measurable_prod _ fun i _ => ?_
  -- Evaluation on `EuclideanSpace` is continuous, hence measurable.
  exact (measurable_gaussianPDFReal (m i) (gaussianVariance σ)).comp
    (PiLp.continuous_apply (p := 2) (β := fun _ : Fin d => Real) i).measurable

theorem isotropicGaussianPDF_nonneg {d : Nat} (m : Input d) (σ : Real) (z : Input d) :
    0 ≤ isotropicGaussianPDF m σ z := by
  unfold isotropicGaussianPDF
  exact Finset.prod_nonneg fun i _ => gaussianPDFReal_nonneg _ _ _

/-- Strict positivity: used to cancel the base density in likelihood comparisons. -/
theorem isotropicGaussianPDF_pos {d : Nat} (m : Input d) (σ : Real) (hσ : 0 < σ)
    (z : Input d) :
    0 < isotropicGaussianPDF m σ z := by
  unfold isotropicGaussianPDF
  exact Finset.prod_pos fun i _ =>
    gaussianPDFReal_pos _ _ _ (gaussianVariance_ne_zero hσ)

theorem integrable_isotropicGaussianPDF {d : Nat} (m : Input d) (σ : Real) :
    Integrable (isotropicGaussianPDF m σ) volume := by
  -- Transfer to the product space along the volume-preserving map `toLp`.
  rw [← (PiLp.volume_preserving_toLp (Fin d)).integrable_comp_emb
      (MeasurableEquiv.toLp 2 (Fin d → Real)).measurableEmbedding]
  simp only [Function.comp_def]
  have hfun :
      (fun x : Fin d → Real => isotropicGaussianPDF m σ (toLp 2 x)) =
        fun x => ∏ i, gaussianPDFReal (m i) (gaussianVariance σ) (x i) := by
    funext x
    simp [isotropicGaussianPDF]
  rw [hfun, volume_pi]
  exact Integrable.fintype_prod
    (fun i => integrable_gaussianPDFReal (m i) (gaussianVariance σ))

theorem integral_isotropicGaussianPDF_eq_one {d : Nat} (m : Input d) (σ : Real)
    (hσ : 0 < σ) :
    ∫ z, isotropicGaussianPDF m σ z ∂volume = 1 := by
  have hv := gaussianVariance_ne_zero hσ
  have h1 :
      (∫ z : Input d, isotropicGaussianPDF m σ z ∂volume) =
        ∫ x : Fin d → Real, isotropicGaussianPDF m σ (toLp 2 x) := by
    simpa using
      ((PiLp.volume_preserving_toLp (Fin d)).integral_comp
          (MeasurableEquiv.toLp 2 (Fin d → Real)).measurableEmbedding
          (isotropicGaussianPDF m σ)).symm
  have h2 :
      (fun x : Fin d → Real => isotropicGaussianPDF m σ (toLp 2 x)) =
        fun x => ∏ i : Fin d, gaussianPDFReal (m i) (gaussianVariance σ) (x i) := by
    funext x
    simp [isotropicGaussianPDF]
  rw [h1, h2, integral_fintype_prod_volume_eq_prod]
  simp_rw [integral_gaussianPDFReal_eq_one _ hv]
  simp

/-! ## Packaging as a `ProbabilityDensity` -/

def isotropicGaussianDensity {d : Nat} (m : Input d) (σ : Real) (hσ : 0 < σ) :
    ProbabilityDensity (Input d) volume where
  density := isotropicGaussianPDF m σ
  measurable_density := measurable_isotropicGaussianPDF m σ
  density_nonneg := isotropicGaussianPDF_nonneg m σ
  integrable_density := integrable_isotropicGaussianPDF m σ
  integral_density_eq_one := integral_isotropicGaussianPDF_eq_one m σ hσ

/-! ## Half-spaces -/

def lowerHalfspace {d : Nat} (δ : Input d) (β : Real) : Set (Input d) :=
  {z | inner Real δ z ≤ β}

def upperHalfspace {d : Nat} (δ : Input d) (β : Real) : Set (Input d) :=
  {z | β ≤ inner Real δ z}

theorem measurableSet_lowerHalfspace {d : Nat} (δ : Input d) (β : Real) :
    MeasurableSet (lowerHalfspace δ β) := by
  unfold lowerHalfspace
  exact measurableSet_le (innerSL Real δ).continuous.measurable measurable_const

theorem measurableSet_upperHalfspace {d : Nat} (δ : Input d) (β : Real) :
    MeasurableSet (upperHalfspace δ β) := by
  unfold upperHalfspace
  exact measurableSet_le measurable_const (innerSL Real δ).continuous.measurable

/-! ## Squared-norm expansion -/

theorem norm_sub_shift_sq {d : Nat} (x δ z : Input d) :
    ‖z - (x + δ)‖ ^ 2 =
      ‖z - x‖ ^ 2 - 2 * inner Real δ z + 2 * inner Real δ x + ‖δ‖ ^ 2 := by
  have hrew : z - (x + δ) = (z - x) - δ := by abel
  rw [hrew, norm_sub_sq_real]
  have hinter : inner Real (z - x) δ = inner Real δ z - inner Real δ x := by
    rw [real_inner_comm, inner_sub_right]
  rw [hinter]
  ring

/-! ## Shifted Gaussian identity

We prove the multiplicative form

```
mu_{x+δ,σ}(z) = exp(<δ,z>/σ^2 - (2<δ,x>+|δ|^2)/(2σ^2)) * mu_{x,σ}(z)
```

directly from the product-of-1D definition.
-/

private theorem gaussian_factor_ratio (a b v : Real) (hv : v ≠ 0) :
    Real.exp (-(a - b) ^ 2 / (2 * v)) =
      Real.exp ((2 * a * b - b ^ 2) / (2 * v)) * Real.exp (-a ^ 2 / (2 * v)) := by
  rw [← Real.exp_add]
  congr 1
  field_simp [hv]
  ring

theorem shiftedGaussian_eq_exp_mul {d : Nat} (x δ z : Input d) (σ : Real)
    (hσ : 0 < σ) :
    isotropicGaussianPDF (x + δ) σ z =
      Real.exp
          ((inner Real δ z / σ ^ 2) -
            ((2 * inner Real δ x + ‖δ‖ ^ 2) / (2 * σ ^ 2))) *
        isotropicGaussianPDF x σ z := by
  have hσ2 : 0 < σ ^ 2 := sq_pos_of_pos hσ
  -- The NNReal variance coerces to `σ^2`.
  have hvR : ((gaussianVariance σ : NNReal) : Real) = σ ^ 2 := rfl
  -- Unfold the product definition.
  unfold isotropicGaussianPDF
  -- Expand each 1D Gaussian PDF, rewriting the variance coercion to `σ^2`.
  -- `gaussianPDFReal μ v x = (√(2π v))⁻¹ * exp(-(x-μ)^2/(2v))`.
  have hPDF (m : Input d) (i : Fin d) :
      gaussianPDFReal (m i) (gaussianVariance σ) (z i) =
        (√(2 * Real.pi * σ ^ 2))⁻¹ *
          Real.exp (-(z i - m i) ^ 2 / (2 * σ ^ 2)) := by
    simp [gaussianPDFReal, hvR]
  simp_rw [hPDF]
  -- Factor each product into (common prefactor) * (product of exps).
  have hsplit (m : Input d) :
      (∏ i : Fin d,
          (√(2 * Real.pi * σ ^ 2))⁻¹ *
            Real.exp (-(z i - m i) ^ 2 / (2 * σ ^ 2))) =
        (∏ i : Fin d, (√(2 * Real.pi * σ ^ 2))⁻¹) *
          (∏ i : Fin d, Real.exp (-(z i - m i) ^ 2 / (2 * σ ^ 2))) :=
    Finset.prod_mul_distrib
  -- After `simp_rw [hPDF]`, both sides of the goal are products of expanded factors.
  -- Identify them with `hsplit`.
  rw [hsplit (x + δ), hsplit x]
  -- Relate the exponential products.
  have hexp :
      (∏ i : Fin d, Real.exp (-(z i - (x + δ) i) ^ 2 / (2 * σ ^ 2))) =
        Real.exp
            ((inner Real δ z / σ ^ 2) -
              ((2 * inner Real δ x + ‖δ‖ ^ 2) / (2 * σ ^ 2))) *
          (∏ i : Fin d, Real.exp (-(z i - x i) ^ 2 / (2 * σ ^ 2))) := by
    have hpoint (i : Fin d) :
        Real.exp (-(z i - (x + δ) i) ^ 2 / (2 * σ ^ 2)) =
          Real.exp ((2 * (z i - x i) * δ i - δ i ^ 2) / (2 * σ ^ 2)) *
            Real.exp (-(z i - x i) ^ 2 / (2 * σ ^ 2)) := by
      have : z i - (x + δ) i = (z i - x i) - δ i := by
        simp
        ring
      rw [this]
      exact gaussian_factor_ratio (z i - x i) (δ i) (σ ^ 2) hσ2.ne'
    calc
      (∏ i, Real.exp (-(z i - (x + δ) i) ^ 2 / (2 * σ ^ 2)))
          = ∏ i, Real.exp ((2 * (z i - x i) * δ i - δ i ^ 2) / (2 * σ ^ 2)) *
              Real.exp (-(z i - x i) ^ 2 / (2 * σ ^ 2)) := by
            exact Finset.prod_congr rfl fun i _ => hpoint i
      _ = (∏ i, Real.exp ((2 * (z i - x i) * δ i - δ i ^ 2) / (2 * σ ^ 2))) *
            (∏ i, Real.exp (-(z i - x i) ^ 2 / (2 * σ ^ 2))) := by
              rw [Finset.prod_mul_distrib]
      _ = Real.exp (∑ i, (2 * (z i - x i) * δ i - δ i ^ 2) / (2 * σ ^ 2)) *
            (∏ i, Real.exp (-(z i - x i) ^ 2 / (2 * σ ^ 2))) := by
              rw [← Real.exp_sum]
      _ = Real.exp
              ((inner Real δ z / σ ^ 2) -
                ((2 * inner Real δ x + ‖δ‖ ^ 2) / (2 * σ ^ 2))) *
            (∏ i, Real.exp (-(z i - x i) ^ 2 / (2 * σ ^ 2))) := by
              -- Identify the summed exponent with the claimed threshold.
              have hexp_eq :
                  (∑ i : Fin d, (2 * (z i - x i) * δ i - δ i ^ 2) / (2 * σ ^ 2)) =
                    (inner Real δ z / σ ^ 2) -
                      ((2 * inner Real δ x + ‖δ‖ ^ 2) / (2 * σ ^ 2)) := by
                -- Pull out the common denominator.
                have hsum :
                    (∑ i : Fin d, (2 * (z i - x i) * δ i - δ i ^ 2) / (2 * σ ^ 2)) =
                      (∑ i : Fin d, (2 * (z i - x i) * δ i - δ i ^ 2)) / (2 * σ ^ 2) := by
                  simp_rw [div_eq_mul_inv, ← Finset.sum_mul]
                -- Expand the numerator into an inner product.
                have hnum :
                    (∑ i : Fin d, (2 * (z i - x i) * δ i - δ i ^ 2)) =
                      2 * inner Real δ (z - x) - ‖δ‖ ^ 2 := by
                  have hA :
                      (∑ i : Fin d, 2 * (z i - x i) * δ i) =
                        2 * ∑ i : Fin d, (z i - x i) * δ i := by
                    simp [Finset.mul_sum, mul_assoc]
                  have hB : (∑ i : Fin d, δ i ^ 2) = ‖δ‖ ^ 2 := by
                    simp [EuclideanSpace.norm_sq_eq, Real.norm_eq_abs, sq_abs]
                  have hC :
                      (∑ i : Fin d, (z i - x i) * δ i) = inner Real δ (z - x) := by
                    -- `inner δ (z - x) = ∑ δ_i * (z_i - x_i)`, and multiplication commutes.
                    simp [inner, mul_comm]
                  rw [Finset.sum_sub_distrib, hA, hB, hC]
                have hinter :
                    inner Real δ (z - x) = inner Real δ z - inner Real δ x :=
                  inner_sub_right _ _ _
                rw [hsum, hnum, hinter]
                field_simp [hσ2.ne']
                ring
              rw [hexp_eq]
  rw [hexp]
  ring

/-! ## Gaussian likelihood regions are half-spaces -/

theorem lowerLikelihoodRegion_gaussian_eq {d : Nat} (x δ : Input d) (σ : Real)
    (hσ : 0 < σ) (β : Real) :
    lowerLikelihoodRegion
        (isotropicGaussianDensity x σ hσ)
        (isotropicGaussianDensity (x + δ) σ hσ)
        (Real.exp
          ((β / σ ^ 2) -
            ((2 * inner Real δ x + ‖δ‖ ^ 2) / (2 * σ ^ 2)))) =
      lowerHalfspace δ β := by
  let t :=
    Real.exp
      ((β / σ ^ 2) -
        ((2 * inner Real δ x + ‖δ‖ ^ 2) / (2 * σ ^ 2)))
  have hσ2 : 0 < σ ^ 2 := sq_pos_of_pos hσ
  ext z
  change
      isotropicGaussianPDF (x + δ) σ z ≤ t * isotropicGaussianPDF x σ z ↔
        inner Real δ z ≤ β
  rw [shiftedGaussian_eq_exp_mul x δ z σ hσ]
  have hp : 0 < isotropicGaussianPDF x σ z := isotropicGaussianPDF_pos x σ hσ z
  constructor
  · intro h
    -- Cancel the positive density factor.
    have h' :
        Real.exp
            ((inner Real δ z / σ ^ 2) -
              ((2 * inner Real δ x + ‖δ‖ ^ 2) / (2 * σ ^ 2))) ≤ t := by
      have := (mul_le_mul_iff_of_pos_right hp).1 h
      simpa [t, mul_comm] using this
    have hmono := (Real.exp_le_exp).1 h'
    have hβ : inner Real δ z / σ ^ 2 ≤ β / σ ^ 2 := by linarith [hmono]
    exact (div_le_div_iff_of_pos_right hσ2).1 hβ
  · intro h
    have hβ : inner Real δ z / σ ^ 2 ≤ β / σ ^ 2 :=
      (div_le_div_iff_of_pos_right hσ2).2 h
    have hmono :
        Real.exp
            ((inner Real δ z / σ ^ 2) -
              ((2 * inner Real δ x + ‖δ‖ ^ 2) / (2 * σ ^ 2))) ≤ t :=
      (Real.exp_le_exp).2 (by linarith [hβ])
    have := (mul_le_mul_iff_of_pos_right hp).2 hmono
    simpa [t, mul_comm] using this

theorem upperLikelihoodRegion_gaussian_eq {d : Nat} (x δ : Input d) (σ : Real)
    (hσ : 0 < σ) (β : Real) : -- reuse lower one to prove this one, just replace
    upperLikelihoodRegion
        (isotropicGaussianDensity x σ hσ)
        (isotropicGaussianDensity (x + δ) σ hσ)
        (Real.exp
          ((β / σ ^ 2) -
            ((2 * inner Real δ x + ‖δ‖ ^ 2) / (2 * σ ^ 2)))) =
      upperHalfspace δ β := by
  let t :=
    Real.exp
      ((β / σ ^ 2) -
        ((2 * inner Real δ x + ‖δ‖ ^ 2) / (2 * σ ^ 2)))
  have hσ2 : 0 < σ ^ 2 := sq_pos_of_pos hσ
  ext z
  change
      t * isotropicGaussianPDF x σ z ≤ isotropicGaussianPDF (x + δ) σ z ↔
        β ≤ inner Real δ z
  rw [shiftedGaussian_eq_exp_mul x δ z σ hσ]
  have hp : 0 < isotropicGaussianPDF x σ z := isotropicGaussianPDF_pos x σ hσ z
  constructor
  · intro h
    have h' :
        t ≤
          Real.exp
            ((inner Real δ z / σ ^ 2) -
              ((2 * inner Real δ x + ‖δ‖ ^ 2) / (2 * σ ^ 2))) := by
      have := (mul_le_mul_iff_of_pos_right hp).1 h
      simpa [t, mul_comm] using this
    have hmono := (Real.exp_le_exp).1 h'
    have hβ : β / σ ^ 2 ≤ inner Real δ z / σ ^ 2 := by linarith [hmono]
    exact (div_le_div_iff_of_pos_right hσ2).1 hβ
  · intro h
    have hβ : β / σ ^ 2 ≤ inner Real δ z / σ ^ 2 :=
      (div_le_div_iff_of_pos_right hσ2).2 h
    have hmono :
        t ≤
          Real.exp
            ((inner Real δ z / σ ^ 2) -
              ((2 * inner Real δ x + ‖δ‖ ^ 2) / (2 * σ ^ 2))) :=
      (Real.exp_le_exp).2 (by linarith [hβ])
    have := (mul_le_mul_iff_of_pos_right hp).2 hmono
    simpa [t, mul_comm] using this

/-! ## Lemma 4 (lower form)

Specialise `neymanPearson_lower` using the exponential threshold whose
likelihood region is exactly the lower half-space.
-/

theorem lemma4_lower {d : Nat} (x δ : Input d) (σ : Real) (hσ : 0 < σ)
    (h : RandomizedTest (Input d)) (β : Real)
    (hBase :
      (∫ z,
          h.probOne z *
            isotropicGaussianDensity x σ hσ z
          ∂volume) ≥
        ∫ z in lowerHalfspace δ β,
          isotropicGaussianDensity x σ hσ z
          ∂volume) :
    (∫ z,
        h.probOne z *
          isotropicGaussianDensity (x + δ) σ hσ z
        ∂volume) ≥
      ∫ z in lowerHalfspace δ β,
        isotropicGaussianDensity (x + δ) σ hσ z
        ∂volume := by
  let t :=
    Real.exp
      ((β / σ ^ 2) -
        ((2 * inner Real δ x + ‖δ‖ ^ 2) / (2 * σ ^ 2)))
  have ht : 0 ≤ t := le_of_lt (Real.exp_pos _)
  have hNP :=
    neymanPearson_lower volume
      (isotropicGaussianDensity x σ hσ)
      (isotropicGaussianDensity (x + δ) σ hσ)
      h t ht
  simpa [t, lowerLikelihoodRegion_gaussian_eq x δ σ hσ β] using hNP (by
    simpa [t, lowerLikelihoodRegion_gaussian_eq x δ σ hσ β] using hBase)

/-! ## Lemma 4 (upper form) -/

theorem lemma4_upper {d : Nat} (x δ : Input d) (σ : Real) (hσ : 0 < σ)
    (h : RandomizedTest (Input d)) (β : Real)
    (hBase :
      (∫ z,
          h.probOne z *
            isotropicGaussianDensity x σ hσ z
          ∂volume) ≤
        ∫ z in upperHalfspace δ β,
          isotropicGaussianDensity x σ hσ z
          ∂volume) :
    (∫ z,
        h.probOne z *
          isotropicGaussianDensity (x + δ) σ hσ z
        ∂volume) ≤
      ∫ z in upperHalfspace δ β,
        isotropicGaussianDensity (x + δ) σ hσ z
        ∂volume := by
  let t :=
    Real.exp
      ((β / σ ^ 2) -
        ((2 * inner Real δ x + ‖δ‖ ^ 2) / (2 * σ ^ 2)))
  have ht : 0 ≤ t := le_of_lt (Real.exp_pos _)
  have hNP :=
    neymanPearson_upper volume
      (isotropicGaussianDensity x σ hσ)
      (isotropicGaussianDensity (x + δ) σ hσ)
      h t ht
  simpa [t, upperLikelihoodRegion_gaussian_eq x δ σ hσ β] using hNP (by
    simpa [t, upperLikelihoodRegion_gaussian_eq x δ σ hσ β] using hBase)

end

end RandomizedSmoothing
