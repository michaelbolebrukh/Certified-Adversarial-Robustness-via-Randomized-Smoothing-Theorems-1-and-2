import Mathlib

namespace RandomizedSmoothing

open MeasureTheory
open scoped BigOperators

noncomputable section

set_option linter.unusedSectionVars false

variable {α : Type*} [MeasurableSpace α]


/-! ## Randomized Test structure-/

structure RandomizedTest (α : Type*) [MeasurableSpace α] where
  probOne : α → ℝ
  measurable_probOne : Measurable probOne
  probOne_nonneg : ∀ x, 0 ≤ probOne x
  probOne_le_one : ∀ x, probOne x ≤ 1

theorem RandomizedTest.probOne_mem_Icc (h : RandomizedTest α) (x : α) :
    h.probOne x ∈ Set.Icc (0 : ℝ) 1 := by
  exact ⟨h.probOne_nonneg x, h.probOne_le_one x⟩

theorem RandomizedTest.probOne_sub_one_nonpos (h : RandomizedTest α) (x : α) :
    h.probOne x - 1 ≤ 0 := by
  linarith [h.probOne_le_one x]

/-! ## Probability Density structure -/
structure ProbabilityDensity
    (α : Type*)
    [MeasurableSpace α]
    (ν : Measure α) where

  density : α → ℝ
  measurable_density : Measurable density -- use integrablility to prove measurability
  density_nonneg : ∀ x, 0 ≤ density x
  integrable_density : Integrable density ν
  integral_density_eq_one :
    ∫ x, density x ∂ν = 1

instance {ν : Measure α} :
    CoeFun (ProbabilityDensity α ν) (fun _ => α → ℝ) where
  coe p := p.density

theorem ProbabilityDensity.integrable
    {ν : Measure α}
    (p : ProbabilityDensity α ν) :
    Integrable (fun x => p x) ν :=
  p.integrable_density

theorem ProbabilityDensity.integrableOn
    {ν : Measure α}
    (p : ProbabilityDensity α ν)
    (S : Set α) :
    IntegrableOn (fun x => p x) S ν :=
  p.integrable_density.integrableOn

def lowerLikelihoodRegion
    {ν : Measure α}
    (p q : ProbabilityDensity α ν)
    (t : ℝ) :
    Set α :=
  {x | q x ≤ t * p x}

def upperLikelihoodRegion
    {ν : Measure α}
    (p q : ProbabilityDensity α ν )
    (t : ℝ) :
    Set α :=
  {x | t * p x ≤ q x}

theorem measurableSet_lowerLikelihoodRegion
    {ν : Measure α}
    (p q : ProbabilityDensity α ν)
    (t : ℝ) :
    MeasurableSet (lowerLikelihoodRegion p q t) := by
  unfold lowerLikelihoodRegion
  exact measurableSet_le q.measurable_density (p.measurable_density.const_mul t)

theorem measurableSet_upperLikelihoodRegion
    {ν : Measure α}
    (p q : ProbabilityDensity α ν)
    (t : ℝ) :
    MeasurableSet (upperLikelihoodRegion p q t) := by
  unfold upperLikelihoodRegion
  exact measurableSet_le (p.measurable_density.const_mul t) q.measurable_density

theorem lowerLikelihoodRegion_on
    {ν : Measure α}
    (p q : ProbabilityDensity α ν)
    (t : ℝ)
    {x : α}
    (hx : x ∈ lowerLikelihoodRegion p q t) :
    q x ≤ t * p x := by
  simpa [lowerLikelihoodRegion] using hx

theorem lowerLikelihoodRegion_off
    {ν : Measure α}
    (p q : ProbabilityDensity α ν)
    (t : ℝ)
    {x : α}
    (hx : x ∉ lowerLikelihoodRegion p q t) :
    t * p x ≤ q x := by
  have hx' : ¬ q x ≤ t * p x := by
    simpa [lowerLikelihoodRegion] using hx
  exact le_of_lt (not_le.mp hx')

theorem upperLikelihoodRegion_on
    {ν : Measure α}
    (p q : ProbabilityDensity α ν)
    (t : ℝ)
    {x : α}
    (hx : x ∈ upperLikelihoodRegion p q t) :
    t * p x ≤ q x := by
  simpa [upperLikelihoodRegion] using hx

theorem upperLikelihoodRegion_off
    {ν : Measure α}
    (p q : ProbabilityDensity α ν)
    (t : ℝ)
    {x : α}
    (hx : x ∉ upperLikelihoodRegion p q t) :
    q x ≤ t * p x := by
  have hx' : ¬ t * p x ≤ q x := by
    simpa [upperLikelihoodRegion] using hx
  exact le_of_lt (not_le.mp hx')

def indicatorOne (S : Set α) (x : α) : ℝ :=
  S.indicator (fun _ => (1 : ℝ)) x

theorem indicatorOne_of_mem {S : Set α} {x : α} (hx : x ∈ S):
    indicatorOne S x = 1 := by
  simp [indicatorOne, Set.indicator_of_mem hx]


theorem indicatorOne_of_not_mem {S : Set α} {x : α} (hx : x ∉ S):
    indicatorOne S x = 0 := by
  simp [indicatorOne, Set.indicator_of_notMem hx]

theorem measurable_indicatorOne
    {S : Set α}
    (hS : MeasurableSet S) :
    Measurable (indicatorOne S) := by
  unfold indicatorOne
  exact measurable_const.indicator hS

def npGap (h : RandomizedTest α) (S : Set α) (x : α) : ℝ :=
  h.probOne x - indicatorOne S x

theorem npGap_of_mem (h : RandomizedTest α) {S : Set α} {x : α} (hx : x ∈ S) :
    npGap h S x = h.probOne x - 1 := by
  simp [npGap, indicatorOne_of_mem hx]

theorem npGap_of_not_mem (h : RandomizedTest α) {S : Set α} {x : α} (hx : x ∉ S) :
    npGap h S x = h.probOne x := by
  simp [npGap, indicatorOne_of_not_mem hx]

theorem npGap_nonpos_of_mem (h : RandomizedTest α) {S : Set α} {x : α} (hx : x ∈ S) :
    npGap h S x ≤ 0 := by
  rw [npGap_of_mem h hx]
  exact h.probOne_sub_one_nonpos x

theorem npGap_nonneg_of_not_mem (h : RandomizedTest α) {S : Set α} {x : α}
    (hx : x ∉ S) :
    0 ≤ npGap h S x := by
  rw [npGap_of_not_mem h hx]
  exact h.probOne_nonneg x

theorem measurable_npGap
    (h : RandomizedTest α)
    {S : Set α}
    (hS : MeasurableSet S) :
    Measurable (npGap h S) := by
  unfold npGap
  exact h.measurable_probOne.sub (measurable_indicatorOne hS)

theorem abs_npGap_le_one
    (h : RandomizedTest α)
    (S : Set α)
    (x : α) :
    |npGap h S x| ≤ 1 := by
  classical
  by_cases hx : x ∈ S
  · rw [npGap_of_mem h hx, abs_le]
    constructor
    · linarith [h.probOne_nonneg x]
    · linarith [h.probOne_le_one x]
  · rw [npGap_of_not_mem h hx, abs_le]
    constructor
    · linarith [h.probOne_nonneg x]
    · exact h.probOne_le_one x

theorem norm_npGap_le_one
    (h : RandomizedTest α)
    (S : Set α)
    (x : α) :
    ‖npGap h S x‖ ≤ 1 := by
  rw [Real.norm_eq_abs]
  exact abs_npGap_le_one h S x

theorem integrable_probOne_mul
    (ν : Measure α)
    (p : ProbabilityDensity α ν)
    (h : RandomizedTest α) :
    Integrable
      (fun x => h.probOne x * p x)
      ν := by
  have hbound : ∀ᵐ x ∂ν, ‖h.probOne x‖ ≤ (1 : ℝ) :=
    Filter.Eventually.of_forall <| fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (h.probOne_nonneg x)]
      exact h.probOne_le_one x
  exact p.integrable_density.bdd_mul
    h.measurable_probOne.aestronglyMeasurable hbound

theorem npGap_mul_eq_sub
    (p : α → ℝ)
    (h : RandomizedTest α)
    (S : Set α)
    (x : α) :
    npGap h S x * p x = h.probOne x * p x - S.indicator p x := by
  simp only [npGap, sub_mul]
  classical
  by_cases hx : x ∈ S
  · simp [indicatorOne_of_mem hx, Set.indicator_of_mem hx]
  · simp [indicatorOne_of_not_mem hx, Set.indicator_of_notMem hx]

theorem integrable_npGap_mul
    (ν : Measure α)
    (p : ProbabilityDensity α ν)
    (h : RandomizedTest α)
    (S : Set α)
    (hS : MeasurableSet S) :
    Integrable
      (fun x => npGap h S x * p x)
      ν := by
  have hIntTest :
      Integrable (fun x => h.probOne x * p x) ν :=
    integrable_probOne_mul ν p h
  have hIntSet :
      IntegrableOn (fun x => p x) S ν :=
    p.integrableOn S
  have h_eq :
      (fun x => npGap h S x * p x)
        =
      (fun x => h.probOne x * p x - S.indicator (fun x => p x) x) := by
    ext x
    exact npGap_mul_eq_sub (fun x => p x) h S x
  rw [h_eq]
  exact hIntTest.sub (hIntSet.integrable_indicator hS)

theorem integral_npGap_mul
    (ν : Measure α)
    (p : ProbabilityDensity α ν)
    (h : RandomizedTest α)
    (S : Set α)
    (hS : MeasurableSet S) :
    (∫ x, npGap h S x * p x ∂ν)
      =
    (∫ x, h.probOne x * p x ∂ν)
      -
    ∫ x in S, p x ∂ν := by
  have hIntTest :
      Integrable (fun x => h.probOne x * p x) ν :=
    integrable_probOne_mul ν p h
  have hIntSet :
      IntegrableOn (fun x => p x) S ν :=
    p.integrableOn S
  have hIntIndicator :
      Integrable (S.indicator (fun x => p x)) ν :=
    hIntSet.integrable_indicator hS
  have h_expand :
      (fun x => npGap h S x * p x)
        =
      (fun x => h.probOne x * p x - S.indicator (fun x => p x) x) := by
    ext x
    exact npGap_mul_eq_sub (fun x => p x) h S x
  rw [h_expand]
  have h_split :
      (∫ x, h.probOne x * p x - S.indicator (fun x => p x) x ∂ν)
        =
      (∫ x, h.probOne x * p x ∂ν) - ∫ x, S.indicator (fun x => p x) x ∂ν :=
    integral_sub hIntTest hIntIndicator
  have h_restrict :
      (∫ x, S.indicator (fun x => p x) x ∂ν) = ∫ x in S, p x ∂ν :=
    integral_indicator (μ := ν) hS
  rw [h_split, h_restrict]

end

end RandomizedSmoothing
