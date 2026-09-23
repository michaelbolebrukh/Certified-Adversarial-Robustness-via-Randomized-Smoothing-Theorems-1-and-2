import RandomizedSmoothing.Definitions
-- import ProofTreeWidget

namespace RandomizedSmoothing

open MeasureTheory
open scoped BigOperators

noncomputable section

-- show_panel_widgets [ProofTreeWidget]


/-!
This file proves the six Neyman–Pearson results.  They come in three layers:

1. **Pointwise** (`neymanPearson_lower_pointwise`, `neymanPearson_upper_pointwise`):
   a pure inequality between real numbers at a single point `x`.  These use only
   order arithmetic and the sign of the gap, so the densities can be *arbitrary*
   real functions `p q : α → ℝ`.

2. **Gap integrals** (`neymanPearson_lower_gap`, `neymanPearson_upper_gap`):
   integrate the pointwise inequality to compare `∫ npGap · q` with `∫ npGap · p`.
   Here `p q` are genuine `ProbabilityDensity` objects, so all the integrability
   facts are supplied automatically by the machinery in `Definitions.lean`.

3. **Exact forms** (`neymanPearson_lower`, `neymanPearson_upper`): rewrite the gap
   integrals into the exact probability statement from the paper, comparing
   `∫ h.probOne · q` with `∫_S q`.
-/

/-- **Pointwise lower inequality.**  Under the "likelihood-ratio" hypotheses
`h_on`/`h_off`, at every point `x` we have `t · (npGap · p) ≤ npGap · q`.

This only needs the *sign* of the gap (nonpositive inside `S`, nonnegative
outside `S`) together with the ordering hypotheses, so `p` and `q` are arbitrary
real functions here. -/

theorem neymanPearson_lower_pointwise
    {α : Type*}
    [MeasurableSpace α]
    (p q : α → ℝ)
    (h : RandomizedTest α)
    (S : Set α)
    (t : ℝ)
    (h_on :
      ∀ x, x ∈ S → q x ≤ t * p x)
    (h_off :
      ∀ x, x ∉ S → t * p x ≤ q x)
    (x : α) :
    t * (npGap h S x * p x)
      ≤ npGap h S x * q x := by
  classical
  by_cases hx : x ∈ S
  · have r_nonpos : npGap h S x ≤ 0 := npGap_nonpos_of_mem h hx
    have hq_le : q x ≤ t * p x := h_on x hx
    have key : npGap h S x * (t * p x) ≤ npGap h S x * q x :=
      mul_le_mul_of_nonpos_left hq_le r_nonpos
    simpa [mul_left_comm, mul_assoc, mul_comm] using key
  · have r_nonneg : 0 ≤ npGap h S x := npGap_nonneg_of_not_mem h hx
    have ht_le : t * p x ≤ q x := h_off x hx
    have key : npGap h S x * (t * p x) ≤ npGap h S x * q x :=
      mul_le_mul_of_nonneg_left ht_le r_nonneg
    simpa [mul_left_comm, mul_assoc, mul_comm] using key

theorem neymanPearson_upper_pointwise
    {α : Type*}
    [MeasurableSpace α]
    (p q : α → ℝ)
    (h : RandomizedTest α)
    (S : Set α)
    (t : ℝ)
    (h_on :
      ∀ x, x ∈ S → t * p x ≤ q x)
    (h_off :
      ∀ x, x ∉ S → q x ≤ t * p x)
    (x : α) :
    npGap h S x * q x
      ≤ t * (npGap h S x * p x) := by
  classical
  by_cases hx : x ∈ S
  · have r_nonpos : npGap h S x ≤ 0 := npGap_nonpos_of_mem h hx
    have ht_le : t * p x ≤ q x := h_on x hx
    have key : npGap h S x * q x ≤ npGap h S x * (t * p x) :=
      mul_le_mul_of_nonpos_left ht_le r_nonpos
    simpa [mul_left_comm, mul_assoc, mul_comm] using key
  · have r_nonneg : 0 ≤ npGap h S x := npGap_nonneg_of_not_mem h hx
    have hq_le : q x ≤ t * p x := h_off x hx
    have key : npGap h S x * q x ≤ npGap h S x * (t * p x) :=
      mul_le_mul_of_nonneg_left hq_le r_nonneg
    simpa [mul_left_comm, mul_assoc, mul_comm] using key

theorem neymanPearson_lower_gap
    {α : Type*}
    [MeasurableSpace α]
    (ν : Measure α)
    (p q : ProbabilityDensity α ν)
    (h : RandomizedTest α)
    (t : ℝ)
    (ht : 0 ≤ t)
    (hBase :
      0 ≤
        ∫ x,
          npGap h (lowerLikelihoodRegion p q t) x * p x
        ∂ν) :
    0 ≤
      ∫ x,
        npGap h (lowerLikelihoodRegion p q t) x * q x
      ∂ν := by
  let S : Set α := lowerLikelihoodRegion p q t
  have hS : MeasurableSet S := measurableSet_lowerLikelihoodRegion p q t
  have h_on : ∀ x, x ∈ S → q x ≤ t * p x :=
    fun x hx => lowerLikelihoodRegion_on p q t hx
  have h_off : ∀ x, x ∉ S → t * p x ≤ q x :=
    fun x hx => lowerLikelihoodRegion_off p q t hx
  have hIntP :
      Integrable
        (fun x => npGap h S x * p x)
        ν :=
    integrable_npGap_mul ν p h S hS
  have hIntQ :
      Integrable
        (fun x => npGap h S x * q x)
        ν :=
    integrable_npGap_mul ν q h S hS
  have h_pointwise :
      ∀ x, t * (npGap h S x * p x) ≤ npGap h S x * q x :=
    fun x =>
      neymanPearson_lower_pointwise (fun x => p x) (fun x => q x)
        h S t h_on h_off x
  have h_ae :
      (fun x => t * (npGap h S x * p x))
        ≤ᵐ[ν]
      (fun x => npGap h S x * q x) :=
    Filter.Eventually.of_forall h_pointwise
  have hIntScaled :
      Integrable (fun x => t * (npGap h S x * p x)) ν :=
    hIntP.const_mul t
  have h_int_le :
      (∫ x, t * (npGap h S x * p x) ∂ν)
        ≤
      (∫ x, npGap h S x * q x ∂ν) :=
    integral_mono_ae hIntScaled hIntQ h_ae
  calc
    (0 : ℝ)
        ≤ t * ∫ x, npGap h S x * p x ∂ν :=
          mul_nonneg ht hBase
    _ = ∫ x, t * (npGap h S x * p x) ∂ν := by
          simpa using (integral_const_mul (μ := ν) t
            (fun x => npGap h S x * p x)).symm
    _ ≤ ∫ x, npGap h S x * q x ∂ν :=
          h_int_le

theorem neymanPearson_upper_gap
    {α : Type*}
    [MeasurableSpace α]
    (ν : Measure α)
    (p q : ProbabilityDensity α ν)
    (h : RandomizedTest α)
    (t : ℝ)
    (ht : 0 ≤ t)
    (hBase :
      (∫ x,
          npGap h (upperLikelihoodRegion p q t) x * p x
        ∂ν)
        ≤ 0) :
    (∫ x,
        npGap h (upperLikelihoodRegion p q t) x * q x
      ∂ν)
      ≤ 0 := by
  let S : Set α := upperLikelihoodRegion p q t
  have hS : MeasurableSet S := measurableSet_upperLikelihoodRegion p q t
  have h_on : ∀ x, x ∈ S → t * p x ≤ q x :=
    fun x hx => upperLikelihoodRegion_on p q t hx
  have h_off : ∀ x, x ∉ S → q x ≤ t * p x :=
    fun x hx => upperLikelihoodRegion_off p q t hx
  have hIntP :
      Integrable
        (fun x => npGap h S x * p x)
        ν :=
    integrable_npGap_mul ν p h S hS
  have hIntQ :
      Integrable
        (fun x => npGap h S x * q x)
        ν :=
    integrable_npGap_mul ν q h S hS
  have h_pointwise :
      ∀ x, npGap h S x * q x ≤ t * (npGap h S x * p x) :=
    fun x =>
      neymanPearson_upper_pointwise (fun x => p x) (fun x => q x)
        h S t h_on h_off x
  have h_ae :
      (fun x => npGap h S x * q x)
        ≤ᵐ[ν]
      (fun x => t * (npGap h S x * p x)) :=
    Filter.Eventually.of_forall h_pointwise
  have hIntScaled :
      Integrable (fun x => t * (npGap h S x * p x)) ν :=
    hIntP.const_mul t
  have h_int_le :
      (∫ x, npGap h S x * q x ∂ν)
        ≤
      (∫ x, t * (npGap h S x * p x) ∂ν) :=
    integral_mono_ae hIntQ hIntScaled h_ae
  calc
    (∫ x, npGap h S x * q x ∂ν)
        ≤ ∫ x, t * (npGap h S x * p x) ∂ν :=
          h_int_le
    _ = t * ∫ x, npGap h S x * p x ∂ν := by
          simpa using integral_const_mul (μ := ν) t
            (fun x => npGap h S x * p x)
    _ ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos ht hBase

theorem neymanPearson_lower
    {α : Type*}
    [MeasurableSpace α]
    (ν : Measure α)
    (p q : ProbabilityDensity α ν)
    (h : RandomizedTest α)
    (t : ℝ)
    (ht : 0 ≤ t)
    (hBase :
      (∫ x, h.probOne x * p x ∂ν)
        ≥
      ∫ x in lowerLikelihoodRegion p q t, p x ∂ν) :
    (∫ x, h.probOne x * q x ∂ν)
      ≥
    ∫ x in lowerLikelihoodRegion p q t, q x ∂ν := by
  let S : Set α := lowerLikelihoodRegion p q t
  have hS : MeasurableSet S := measurableSet_lowerLikelihoodRegion p q t
  have hGapP := integral_npGap_mul ν p h S hS
  have hGapQ := integral_npGap_mul ν q h S hS
  have hBaseGap : 0 ≤ ∫ x, npGap h S x * p x ∂ν := by
    have : 0 ≤ (∫ x, h.probOne x * p x ∂ν) - ∫ x in S, p x ∂ν := by
      linarith [hBase]
    rw [hGapP]
    exact this
  have hConclGap : 0 ≤ ∫ x, npGap h S x * q x ∂ν :=
    neymanPearson_lower_gap ν p q h t ht hBaseGap
  have : 0 ≤ (∫ x, h.probOne x * q x ∂ν) - ∫ x in S, q x ∂ν := by
    rw [← hGapQ]
    exact hConclGap
  linarith

theorem neymanPearson_upper
    {α : Type*}
    [MeasurableSpace α]
    (ν : Measure α)
    (p q : ProbabilityDensity α ν)
    (h : RandomizedTest α)
    (t : ℝ)
    (ht : 0 ≤ t)
    (hBase :
      (∫ x, h.probOne x * p x ∂ν)
        ≤
      ∫ x in upperLikelihoodRegion p q t, p x ∂ν) :
    (∫ x, h.probOne x * q x ∂ν)
      ≤
    ∫ x in upperLikelihoodRegion p q t, q x ∂ν := by
  let S : Set α := upperLikelihoodRegion p q t
  have hS : MeasurableSet S := measurableSet_upperLikelihoodRegion p q t
  have hGapP := integral_npGap_mul ν p h S hS
  have hGapQ := integral_npGap_mul ν q h S hS
  have hBaseGap : (∫ x, npGap h S x * p x ∂ν) ≤ 0 := by
    have : (∫ x, h.probOne x * p x ∂ν) - ∫ x in S, p x ∂ν ≤ 0 := by
      linarith [hBase]
    rw [hGapP]
    exact this
  have hConclGap : (∫ x, npGap h S x * q x ∂ν) ≤ 0 :=
    neymanPearson_upper_gap ν p q h t ht hBaseGap
  have : (∫ x, h.probOne x * q x ∂ν) - ∫ x in S, q x ∂ν ≤ 0 := by
    rw [← hGapQ]
    exact hConclGap
  linarith

end

end RandomizedSmoothing
