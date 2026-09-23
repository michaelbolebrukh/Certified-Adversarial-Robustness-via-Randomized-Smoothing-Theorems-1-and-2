import RandomizedSmoothing.GaussianHalfspaces

/-!
# Theorem 1

Certified adversarial robustness for Gaussian randomized smoothing
(Cohen–Rosenfeld–Kolter, Appendix A), built on Lemmas 3–4 and the
Gaussian half-space probability calculations.
-/

namespace RandomizedSmoothing

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators

noncomputable section

/-! ## Minimal randomized multiclass classifier -/

/-- A measurable randomized multiclass classifier: at each input the class
probabilities are nonnegative and sum to one.

Instead of a hard label `f : α → C`, `classProb x c` directly records the
probability that the classifier outputs class `c` on input `x` (think of it
as `P[ f(x) = c ]` for some underlying randomized/soft predictor `f`, or
simply as a vector of confidence scores that behave like probabilities). The
fields are commented below.
-/

structure RandomizedClassifier
    (α : Type*)
    [MeasurableSpace α]
    (C : Type*) -- define the structure representing distributions over `C`
    [Fintype C] where
  classProb : α → C → Real

  -- each coordinate `x ↦ classProb x c` is measurable, so we can integrate it against noise density
  measurable_classProb :
    ∀ c, Measurable (fun x => classProb x c)

  -- probabilities are nonnegative
  classProb_nonneg :
    ∀ x c, 0 ≤ classProb x c

  -- for fixed `x`, the vector `(classProb x c)_{c : C}` sums to `1` over the finite class set `C`.
  sum_classProb_eq_one :
    ∀ x, ∑ c, classProb x c = 1


/-- A single class probability is at most `1`, since it is one nonnegative
summand of a sum that totals `1`. Lets us view `classProb x c` as a genuine `[0,1]`-valued probability
(used immediately below to build a `RandomizedTest`). -/
theorem RandomizedClassifier.classProb_le_one
    {α : Type*} [MeasurableSpace α] {C : Type*} [Fintype C]
    (f : RandomizedClassifier α C) (x : α) (c : C) :
    f.classProb x c ≤ 1 := by
  -- Each probability is ≤ the sum of all (nonnegative) class probabilities.
  have hsum := f.sum_classProb_eq_one x
  have hnn : ∀ c', 0 ≤ f.classProb x c' := fun c' => f.classProb_nonneg x c'
  calc
    f.classProb x c ≤ ∑ c', f.classProb x c' := by
      exact Finset.single_le_sum (fun c' _ => hnn c') (Finset.mem_univ c)
    _ = 1 := hsum


/-- View the class-`c` coordinate of a `RandomizedClassifier` as a binary
Neyman–Pearson test `RandomizedTest α`. A `RandomizedTest` is precisely a
measurable function into `[0,1]` (the probability of "accepting"/predicting
class `c`); `classProb_nonneg`, `classProb_le_one`, and
`measurable_classProb` supply exactly the three fields such a test needs.
Forgetting the other coordinates like this is what lets Lemma 3/4 (proved for
one binary test at a time) be applied class-by-class inside
`theorem1_pairwise`. -/
def RandomizedClassifier.classTest
    {α : Type*} [MeasurableSpace α] {C : Type*} [Fintype C]
    (f : RandomizedClassifier α C) (c : C) :
    RandomizedTest α where
  probOne := fun x => f.classProb x c
  measurable_probOne := f.measurable_classProb c
  probOne_nonneg := fun x => f.classProb_nonneg x c
  probOne_le_one := fun x => f.classProb_le_one x c


/-- The *smoothed class score* `s_p(c)` of class `c` under noise density `p`:
the expectation, over a random draw with density `p` (e.g. `X ∼ N(x, σ²I)` or
`Y ∼ N(x+δ, σ²I)`), of the classifier's probability of predicting `c`,

  `smoothedClassProb p f c = E_{z ∼ p} [ f.classProb z c ] = ∫ classProb(z,c) · p(z) dν`. -/
def smoothedClassProb
    {α : Type*} [MeasurableSpace α] {C : Type*} [Fintype C]
    {ν : Measure α}
    (p : ProbabilityDensity α ν)
    (f : RandomizedClassifier α C)
    (c : C) : Real :=
  ∫ x, f.classProb x c * p x ∂ν

/-- `smoothedClassProb` unfolds definitionally to an integral of the
`classTest c` acceptance probability against the density `p`; this
lets us feed a smoothed class score directly into the
Neyman–Pearson lemmas (`lemma4_lower`, `lemma4_upper`), which are stated in
terms of `RandomizedTest.probOne`. -/
theorem smoothedClassProb_eq_testIntegral
    {α : Type*} [MeasurableSpace α] {C : Type*} [Fintype C]
    {ν : Measure α}
    (p : ProbabilityDensity α ν)
    (f : RandomizedClassifier α C)
    (c : C) :
    smoothedClassProb p f c
      = ∫ x, (f.classTest c).probOne x * p x ∂ν := rfl

/-- `cA` is the *unique winner* of a scoring function `score : C → Real` if
every other class strictly scores lower: `∀ c ≠ cA, score c < score cA`. This
is the formal target of Theorem 1 (`cA` stays the unique winner after
perturbation). -/
def IsUniqueWinner {C : Type*} (score : C → Real) (cA : C) : Prop :=
  ∀ c, c ≠ cA → score c < score cA


/-! ## Relating acceptance/competitor half-spaces to Lemma 4 half-spaces

`GaussianHalfspaces.lean` defines two families of half-spaces centred at `x`:

* `acceptanceHalfspace x δ σ pA = {z | ⟨δ, z − x⟩ ≤ σ‖δ‖·Φ⁻¹(pA)}`, and
* `competitorHalfspace x δ σ pB = {z | σ‖δ‖·Φ⁻¹(1 − pB) ≤ ⟨δ, z − x⟩}`,

whose `N(x, σ²I)`-probabilities are already computed there to be exactly `pA`
and `pB` (`prob_X_acceptanceHalfspace`, `prob_X_competitorHalfspace`). Lemma 4
(`lemma4_lower`, `lemma4_upper`), on the other hand, is phrased in terms of
the *centreless* half-spaces `lowerHalfspace δ β = {z | ⟨δ,z⟩ ≤ β}` and
`upperHalfspace δ β = {z | β ≤ ⟨δ,z⟩}`. The two theorems below expand
`⟨δ, z − x⟩ = ⟨δ,z⟩ − ⟨δ,x⟩` and move `⟨δ,x⟩` to the threshold, showing the
two families coincide once the threshold `β` absorbs the `⟨δ,x⟩` term. This
identification is what lets `theorem1_pairwise` invoke Lemma 4 directly on
`acceptanceHalfspace`/`competitorHalfspace`. -/

/-
The centred and uncentred descriptions define the same half-space because
the inner product is linear in its second argument:

    `⟨δ, z - x⟩ = ⟨δ, z⟩ - ⟨δ, x⟩.`

For the acceptance region,

    `⟨δ, z - x⟩ ≤ σ‖δ‖Φ⁻¹(pA)`

is therefore equivalent to

    `⟨δ, z⟩ ≤ σ‖δ‖Φ⁻¹(pA) + ⟨δ, x⟩.`

Thus the effect of centring at `x` can be moved into the scalar threshold
`βA`; the geometric half-space itself is unchanged. The competitor
half-space is converted in exactly the same way, producing `βB`.
-/

/-- Acceptance half-space is a lower Euclidean half-space, with threshold
`βA = σ‖δ‖·Φ⁻¹(pA) + ⟨δ,x⟩`. -/

theorem acceptanceHalfspace_eq_lowerHalfspace
    {d : Nat} (x δ : Input d) (σ : Real)
    (pA : Set.Ioo (0 : Real) 1) :
    acceptanceHalfspace x δ σ pA
      =
    lowerHalfspace δ
      (σ * ‖δ‖ * standardNormalQuantile pA + inner Real δ x) := by
  ext z -- chnges the goal, making it to show that arbitrary point `z` sattisfies the proposition.
  simp only [acceptanceHalfspace, lowerHalfspace, mem_setOf_eq, inner_sub_right]
  -- Prove equality of the two sets pointwise. `constructor` splits the
  -- equivalence into the forward and reverse implications; `intro h`
  -- assumes the inequality on each side, and `linarith` rearranges the
  -- resulting linear inequality involving ⟪δ, z⟫ and ⟪δ, x⟫.
  constructor <;> intro h <;> linarith -- `<;>` - apply the next tactic to every current goal.\

/-- Competitor half-space is an upper Euclidean half-space. -/
theorem competitorHalfspace_eq_upperHalfspace
    {d : Nat} (x δ : Input d) (σ : Real)
    (pB : Set.Ioo (0 : Real) 1) :
    competitorHalfspace x δ σ pB
      =
    upperHalfspace δ
      (inner Real δ x
        + σ * ‖δ‖ * standardNormalQuantile (oneSubProbability pB)) := by
  ext z
  -- Symmetric rearrangement to the acceptance case, now for the `≥`-shaped half-space.
  simp only [competitorHalfspace, upperHalfspace, mem_setOf_eq, inner_sub_right]
  constructor <;> intro h <;> linarith

/-! ## Theorem 1: pairwise form

Instead of comparing `cA` against *every* other class at once, we compare it
against a single fixed competitor `cB`; `theorem1_uniqueWinner` then applies
this pairwise statement to each competitor in turn.

We are given, at the base point `x`:

* `hA : pA ≤ s_X(cA)` — `cA` scores at least `pA` on the clean point;
* `hB : s_X(cB) ≤ pB` — the competitor `cB` scores at most `pB`;
* `hRadius : ‖δ‖ < (σ/2)(Φ⁻¹(pA) − Φ⁻¹(pB))` — a bound on the adversarial
  perturbation size.

The proof:

1. Introduces two auxiliary half-spaces `A` (the *acceptance* region for
   `cA`) and `B` (the *competitor* region for `cB`), each carrying exactly
   probability `pA`/`pB` under `N(x, σ²I)` (`prob_X_acceptanceHalfspace`,
   `prob_X_competitorHalfspace` from `GaussianHalfspaces.lean`).
2. Identifies `A`/`B` with Lemma 4's `lowerHalfspace`/`upperHalfspace` at
   explicit thresholds `βA`, `βB`
   (`acceptanceHalfspace_eq_lowerHalfspace`, `competitorHalfspace_eq_upperHalfspace`).
3. Uses the hypotheses `hA`, `hB` together with the equal base probabilities
   to rewrite them as the Neyman–Pearson hypotheses `hBaseA`, `hBaseB` that
   `lemma4_lower`/`lemma4_upper` require (a smoothed class score dominating —
   resp. being dominated by — the corresponding half-space integral, under
   the *base* density `N(x, σ²I)`).
4. Applies `lemma4_lower`/`lemma4_upper` to transport these inequalities from
   the base density `N(x, σ²I)` to the *shifted* density `N(x+δ, σ²I)`,
   obtaining `s_Y(cA) ≥ P_Y(A)` and `s_Y(cB) ≤ P_Y(B)`.
5. Evaluates `P_Y(A)` and `P_Y(B)` explicitly as `Φ`-expressions using
   `prob_Y_acceptanceHalfspace`/`prob_Y_competitorHalfspace`, and compares
   them using `hRadius` via `shifted_halfspace_probability_lt`.
6. Chains everything together:
   `s_Y(cB) ≤ P_Y(B) < P_Y(A) ≤ s_Y(cA)`. -/

/-- Pairwise Theorem 1: under the radius condition, the smoothed score of `cA`
strictly exceeds that of a competitor `cB` at the shifted point `x+δ`. -/
theorem theorem1_pairwise
    {d : Nat} {C : Type*} [Fintype C]
    (x δ : Input d) (σ : Real) (hσ : 0 < σ)
    (f : RandomizedClassifier (Input d) C)
    (cA cB : C) (_hc : cB ≠ cA)
    (pA pB : Set.Ioo (0 : Real) 1)
    (hδ : δ ≠ 0)
    (hA :
      pA.1 ≤ smoothedClassProb (isotropicGaussianDensity x σ hσ) f cA)
    (hB :
      smoothedClassProb (isotropicGaussianDensity x σ hσ) f cB ≤ pB.1)
    (hRadius :
      ‖δ‖
        <
      (σ / 2) *
        (standardNormalQuantile pA - standardNormalQuantile pB)) :
    smoothedClassProb (isotropicGaussianDensity (x + δ) σ hσ) f cB
      <
    smoothedClassProb (isotropicGaussianDensity (x + δ) σ hσ) f cA := by
  -- Half-spaces used by the Neyman–Pearson specialisation.
  set A := acceptanceHalfspace x δ σ pA
  set B := competitorHalfspace x δ σ pB
  set βA : Real :=
    σ * ‖δ‖ * standardNormalQuantile pA + inner Real δ x
  set βB : Real :=
    inner Real δ x
      + σ * ‖δ‖ * standardNormalQuantile (oneSubProbability pB)
  -- Package A, B as centreless Lemma-4 half-spaces via the bridge theorems above.
  have hAeq : A = lowerHalfspace δ βA := by
    simpa [A, βA] using acceptanceHalfspace_eq_lowerHalfspace x δ σ pA
  have hBeq : B = upperHalfspace δ βB := by
    simpa [B, βB] using competitorHalfspace_eq_upperHalfspace x δ σ pB
  -- Base probabilities of A and B under X.
  have hXA := prob_X_acceptanceHalfspace x δ σ hσ hδ pA
  have hXB := prob_X_competitorHalfspace x δ σ hσ hδ pB
  -- Lemma 4 lower for class cA: score_Y(cA) ≥ P_Y(A)
  have hBaseA :
      (∫ z,
          (f.classTest cA).probOne z *
            isotropicGaussianDensity x σ hσ z
          ∂volume)
        ≥
      ∫ z in lowerHalfspace δ βA,
        isotropicGaussianDensity x σ hσ z
        ∂volume := by
    -- LHS = smoothedClassProb X f cA ≥ pA = P_X(A)
    have hL :
        smoothedClassProb (isotropicGaussianDensity x σ hσ) f cA
          ≥ pA.1 := hA
    have hR :
        ∫ z in A, isotropicGaussianPDF x σ z ∂volume = pA.1 := hXA
    -- Rewrite through density coercion and halfspace equality.
    -- isotropicGaussianDensity coerces to isotropicGaussianPDF
    have hden : (isotropicGaussianDensity x σ hσ : Input d → Real)
        = isotropicGaussianPDF x σ := rfl
    simpa [smoothedClassProb_eq_testIntegral, hden, hAeq, A, ← hR] using hL
  have hYA :=
    lemma4_lower x δ σ hσ (f.classTest cA) βA hBaseA
  -- Lemma 4 upper for class cB: score_Y(cB) ≤ P_Y(B)
  have hBaseB :
      (∫ z,
          (f.classTest cB).probOne z *
            isotropicGaussianDensity x σ hσ z
          ∂volume)
        ≤
      ∫ z in upperHalfspace δ βB,
        isotropicGaussianDensity x σ hσ z
        ∂volume := by
    have hL :
        smoothedClassProb (isotropicGaussianDensity x σ hσ) f cB
          ≤ pB.1 := hB
    have hR :
        ∫ z in B, isotropicGaussianPDF x σ z ∂volume = pB.1 := hXB
    have hden : (isotropicGaussianDensity x σ hσ : Input d → Real)
        = isotropicGaussianPDF x σ := rfl
    simpa [smoothedClassProb_eq_testIntegral, hden, hBeq, B, ← hR] using hL
  have hYB :=
    lemma4_upper x δ σ hσ (f.classTest cB) βB hBaseB
  -- Shifted probabilities.
  have hYAp := prob_Y_acceptanceHalfspace x δ σ hσ hδ pA
  have hYBp := prob_Y_competitorHalfspace x δ σ hσ hδ pB
  have hlt :=
    shifted_halfspace_probability_lt σ hσ ‖δ‖ pA pB hRadius
  -- Chain:
  -- score_Y(cB) ≤ P_Y(B) = Φ(qB + ‖δ‖/σ) < Φ(qA - ‖δ‖/σ) = P_Y(A) ≤ score_Y(cA)
  have hdenY : (isotropicGaussianDensity (x + δ) σ hσ : Input d → Real)
      = isotropicGaussianPDF (x + δ) σ := rfl
  have hscoreA :
      ∫ z in A, isotropicGaussianPDF (x + δ) σ z ∂volume
        ≤
      smoothedClassProb (isotropicGaussianDensity (x + δ) σ hσ) f cA := by
    -- From hYA after rewriting halfspace and density
    have : ∫ z in lowerHalfspace δ βA,
        isotropicGaussianDensity (x + δ) σ hσ z ∂volume
        ≤
      ∫ z, (f.classTest cA).probOne z *
          isotropicGaussianDensity (x + δ) σ hσ z ∂volume := hYA
    simpa [smoothedClassProb_eq_testIntegral, hdenY, hAeq, A] using this
  have hscoreB :
      smoothedClassProb (isotropicGaussianDensity (x + δ) σ hσ) f cB
        ≤
      ∫ z in B, isotropicGaussianPDF (x + δ) σ z ∂volume := by
    have : ∫ z, (f.classTest cB).probOne z *
          isotropicGaussianDensity (x + δ) σ hσ z ∂volume
        ≤
      ∫ z in upperHalfspace δ βB,
        isotropicGaussianDensity (x + δ) σ hσ z ∂volume := hYB
    simpa [smoothedClassProb_eq_testIntegral, hdenY, hBeq, B] using this
  -- Rewrite the halfspace integrals as Φ expressions.
  have hPA : ∫ z in A, isotropicGaussianPDF (x + δ) σ z ∂volume
      = standardNormalCDF (standardNormalQuantile pA - ‖δ‖ / σ) := by
    simpa [A] using hYAp
  have hPB : ∫ z in B, isotropicGaussianPDF (x + δ) σ z ∂volume
      = standardNormalCDF (standardNormalQuantile pB + ‖δ‖ / σ) := by
    simpa [B] using hYBp
  calc
    smoothedClassProb (isotropicGaussianDensity (x + δ) σ hσ) f cB
        ≤ ∫ z in B, isotropicGaussianPDF (x + δ) σ z ∂volume := hscoreB
    _ = standardNormalCDF (standardNormalQuantile pB + ‖δ‖ / σ) := hPB
    _ < standardNormalCDF (standardNormalQuantile pA - ‖δ‖ / σ) := hlt
    _ = ∫ z in A, isotropicGaussianPDF (x + δ) σ z ∂volume := hPA.symm
    _ ≤ smoothedClassProb (isotropicGaussianDensity (x + δ) σ hσ) f cA := hscoreA

/-! ## Theorem 1: unique-winner form

To get the full statement of Theorem 1 — `cA` is the *unique* arg-max, i.e. `IsUniqueWinner`
holds — we simply note that the hypothesis `hOther : ∀ c ≠ cA, s_X(c) ≤ pB`
supplies, for *every* competing class `c`, exactly the bound `hB` that
`theorem1_pairwise` needs with `cB := c`. So Theorem 1 in unique-winner form
follows by instantiating the pairwise theorem once per competitor `c`; no new
mathematics is needed, only universally quantifying over `c`.

-/

theorem theorem1_uniqueWinner
    {d : Nat} {C : Type*} [Fintype C]
    (x δ : Input d) (σ : Real) (hσ : 0 < σ)
    (f : RandomizedClassifier (Input d) C)
    (cA : C)
    (pA pB : Set.Ioo (0 : Real) 1)
    (hδ : δ ≠ 0)
    (hA :
      pA.1 ≤ smoothedClassProb (isotropicGaussianDensity x σ hσ) f cA)
    (hOther :
      ∀ c, c ≠ cA →
        smoothedClassProb (isotropicGaussianDensity x σ hσ) f c ≤ pB.1)
    (hRadius :
      ‖δ‖
        <
      (σ / 2) *
        (standardNormalQuantile pA - standardNormalQuantile pB)) :
    IsUniqueWinner
      (fun c => smoothedClassProb (isotropicGaussianDensity (x + δ) σ hσ) f c)
      cA := by
  intro c hc
  exact theorem1_pairwise x δ σ hσ f cA c hc pA pB hδ hA (hOther c hc) hRadius

/-! ## Theorem 2 helpers: reversed radius and null boundary

Theorem 2 needs the *opposite* inequality from Theorem 1: instead of `‖δ‖`
being small (radius condition), we now assume `‖δ‖` is at least as large as
the certified radius, and we must show `P_Y(A) < P_Y(B)` — i.e. the
competitor's shifted probability now exceeds the acceptance region's. In
addition, since the witness classifier below partitions `Rᵈ` using both `A`
and `B` simultaneously, we need `A` and `B` to be (essentially) disjoint;
this holds precisely because the paper's Theorem 2 hypothesis is `pA + pB ≤
1` rather than `pA > pB` alone. -/

/-- Reversed radius inequality: swapping the strict inequality direction of
`hRadius` (now `‖δ‖` *exceeds* the critical radius rather than falling below
it) flips which shifted half-space probability is larger: `P_Y(A) < P_Y(B)`
in `Φ`-form. This is the exact mirror image of
`shifted_halfspace_probability_lt` used in `theorem1_pairwise`, and
lets `cB` overtake `cA` in `theorem2_not_uniqueWinner`. -/
theorem shifted_halfspace_probability_gt
    (σ : Real) (hσ : 0 < σ) (δnorm : Real)
    (pA pB : Set.Ioo (0 : Real) 1)
    (hRadius :
      (σ / 2) * (standardNormalQuantile pA - standardNormalQuantile pB)
        <
      δnorm) :
    standardNormalCDF (standardNormalQuantile pA - δnorm / σ)
      <
    standardNormalCDF (standardNormalQuantile pB + δnorm / σ) := by
  have hσ0 : σ ≠ 0 := ne_of_gt hσ
  have hq :
      standardNormalQuantile pA - δnorm / σ
        <
      standardNormalQuantile pB + δnorm / σ := by
    have hdiv := div_lt_div_of_pos_right hRadius hσ
    -- ((σ/2)(qA-qB))/σ = (1/2)(qA-qB)
    have hsimp :
        ((σ / 2) * (standardNormalQuantile pA - standardNormalQuantile pB)) / σ
          =
        (1 / 2) * (standardNormalQuantile pA - standardNormalQuantile pB) := by
      field_simp [hσ0]
    nlinarith [hdiv, hsimp]
  exact standardNormalCDF_strictMono hq

/-- Under `pA + pB ≤ 1`, acceptance and competitor half-spaces meet at most on a
hyperplane.

`A = {z | ⟨δ,z-x⟩ ≤ σ‖δ‖Φ⁻¹(pA)}` and
`B = {z | σ‖δ‖Φ⁻¹(1-pB) ≤ ⟨δ,z-x⟩}` are half-spaces cut by parallel
hyperplanes orthogonal to `δ`, at signed distances `σ‖δ‖Φ⁻¹(pA)` and
`σ‖δ‖Φ⁻¹(1-pB)` respectively. Since `pA + pB ≤ 1` gives `pA ≤ 1 - pB`, and
`Φ⁻¹` is monotone, we get `Φ⁻¹(pA) ≤ Φ⁻¹(1-pB)`, so `A`'s cutting hyperplane
lies at or before `B`'s. Consequently `A ∩ B` can only be the sliver where both boundary inequalities are tight
simultaneously — i.e. a single hyperplane. This is what makes `B \ A` and `B` "the same set" up to a
null set (`acceptance_competitor_inter_gaussian_null`,
`integral_competitor_diff_acceptance`), used for the witness
classifier's class probabilities to add up correctly. -/
theorem acceptance_competitor_inter_subset_hyperplane
    {d : Nat} (x δ : Input d) (σ : Real) (hσ : 0 < σ)
    (pA pB : Set.Ioo (0 : Real) 1)
    (hsum : pA.1 + pB.1 ≤ 1) :
    acceptanceHalfspace x δ σ pA ∩ competitorHalfspace x δ σ pB
      ⊆
    {z | inner Real δ z =
      σ * ‖δ‖ * standardNormalQuantile pA + inner Real δ x} := by
  intro z hz
  simp only [mem_setOf_eq]
  have hzA : inner Real δ (z - x) ≤ σ * ‖δ‖ * standardNormalQuantile pA := hz.1
  have hzB :
      σ * ‖δ‖ * standardNormalQuantile (oneSubProbability pB)
        ≤
      inner Real δ (z - x) := hz.2
  have hp : (pA : Real) ≤ (oneSubProbability pB : Real) := by
    simp only [oneSubProbability]
    linarith
  have hq :
      standardNormalQuantile pA
        ≤
      standardNormalQuantile (oneSubProbability pB) :=
    standardNormalQuantile_strictMono.monotone hp
  have hτle :
      σ * ‖δ‖ * standardNormalQuantile pA
        ≤
      σ * ‖δ‖ * standardNormalQuantile (oneSubProbability pB) :=
    mul_le_mul_of_nonneg_left hq (mul_nonneg (le_of_lt hσ) (norm_nonneg _))
  have hge :
      σ * ‖δ‖ * standardNormalQuantile pA ≤ inner Real δ (z - x) :=
    le_trans hτle hzB
  have heq' :
      inner Real δ (z - x) = σ * ‖δ‖ * standardNormalQuantile pA :=
    le_antisymm hzA hge
  -- ⟨δ, z - x⟩ = ⟨δ, z⟩ - ⟨δ, x⟩
  rw [inner_sub_right] at heq'
  exact sub_eq_iff_eq_add.mp heq'

/-- The intersection `A ∩ B` is null for `N(x, σ² I)` when `pA + pB ≤ 1`.

Combines `acceptance_competitor_inter_subset_hyperplane` (`A ∩ B` sits inside
a single hyperplane orthogonal to `δ`) with `gaussian_hyperplane_measure_zero`
(any such hyperplane has Gaussian measure zero — a hyperplane is a
codimension-1, hence Lebesgue/Gaussian-null, subset of `Rᵈ`) via `measure_mono_null`: a subset of a null set is null. -/
theorem acceptance_competitor_inter_gaussian_null
    {d : Nat} (x δ : Input d) (σ : Real) (hσ : 0 < σ)
    (hδ : δ ≠ 0)
    (pA pB : Set.Ioo (0 : Real) 1)
    (hsum : pA.1 + pB.1 ≤ 1) :
    (multivariateGaussian x ((σ ^ 2) • (1 : Matrix (Fin d) (Fin d) Real)))
        (acceptanceHalfspace x δ σ pA ∩ competitorHalfspace x δ σ pB)
      = 0 := by
  set β : Real :=
    σ * ‖δ‖ * standardNormalQuantile pA + inner Real δ x
  exact measure_mono_null
    (acceptance_competitor_inter_subset_hyperplane x δ σ hσ pA pB hsum)
    (gaussian_hyperplane_measure_zero (m := x) (δ := δ) σ hσ hδ β)

/-- The intersection `A ∩ B` is null for `N(x+δ, σ² I)` when `pA + pB ≤ 1`.

Identical argument to `acceptance_competitor_inter_gaussian_null`, but for
the *shifted* Gaussian `N(x+δ, σ²I)`: a hyperplane is null under every non-degenerate Gaussian on `Rᵈ`, regardless of its mean,
so the same hyperplane containment bound applies with `m := x + δ`. This second copy is
needed because `theorem2_not_uniqueWinner` computes class probabilities at
the shifted point `x + δ`, not at `x`. -/
theorem acceptance_competitor_inter_gaussian_null_shifted
    {d : Nat} (x δ : Input d) (σ : Real) (hσ : 0 < σ)
    (hδ : δ ≠ 0)
    (pA pB : Set.Ioo (0 : Real) 1)
    (hsum : pA.1 + pB.1 ≤ 1) :
    (multivariateGaussian (x + δ) ((σ ^ 2) • (1 : Matrix (Fin d) (Fin d) Real)))
        (acceptanceHalfspace x δ σ pA ∩ competitorHalfspace x δ σ pB)
      = 0 := by
  set β : Real :=
    σ * ‖δ‖ * standardNormalQuantile pA + inner Real δ x
  exact measure_mono_null
    (acceptance_competitor_inter_subset_hyperplane x δ σ hσ pA pB hsum)
    (gaussian_hyperplane_measure_zero (m := x + δ) (δ := δ) σ hσ hδ β)

/-- Integrating the isotropic PDF over `B \ A` equals integrating over `B`.

Since `A ∩ B` is Gaussian-null (`hnull`), removing it from `B` does not
change the integral: `∫_{B\A} = ∫_{B \ (A∩B)} = ∫_B − ∫_{A∩B} = ∫_B − 0 = ∫_B`.
 In probabilistic terms, `P(B \ A) = P(B)` whenever `P(A ∩ B) = 0`. Used to show that the witness classifier's `cB`-region
`B \ A` (which must be disjoint from the `cA`-region `A` by construction)
still carries the *full* probability mass `pB` that `B` alone would carry. -/
theorem integral_competitor_diff_acceptance
    {d : Nat} (m x δ : Input d) (σ : Real) (hσ : 0 < σ)
    (pA pB : Set.Ioo (0 : Real) 1)
    (hnull :
      (multivariateGaussian m ((σ ^ 2) • (1 : Matrix (Fin d) (Fin d) Real)))
          (acceptanceHalfspace x δ σ pA ∩ competitorHalfspace x δ σ pB)
        = 0) :
    (∫ z in competitorHalfspace x δ σ pB \ acceptanceHalfspace x δ σ pA,
        isotropicGaussianPDF m σ z ∂volume)
      =
    (∫ z in competitorHalfspace x δ σ pB,
        isotropicGaussianPDF m σ z ∂volume) := by
  set A := acceptanceHalfspace x δ σ pA
  set B := competitorHalfspace x δ σ pB
  have hA : MeasurableSet A := measurableSet_acceptanceHalfspace x δ σ pA
  have hB : MeasurableSet B := measurableSet_competitorHalfspace x δ σ pB
  have hBA : MeasurableSet (B \ A) := hB.diff hA
  rw [integral_isotropicGaussian_eq_multivariateGaussian_apply m σ hσ _ hBA,
    integral_isotropicGaussian_eq_multivariateGaussian_apply m σ hσ _ hB]
  -- B \ A = B \ (A ∩ B)
  have hset : B \ A = B \ (A ∩ B) := by
    rw [inter_comm A B, sdiff_self_inter]
  rw [hset, measureReal_def, measureReal_def, measure_sdiff_null hnull]

/-- `indicatorOne S x` is always nonnegative, hence usable as one coordinate of
a `RandomizedClassifier`'s `classProb_nonneg` field. -/
theorem indicatorOne_nonneg {α : Type*} (S : Set α) (x : α) :
    0 ≤ indicatorOne S x := by
  unfold indicatorOne
  exact Set.indicator_nonneg (fun _ _ => by norm_num) x

/-- Integrating `indicatorOne S · * pdf` over all of `Rᵈ` is the same as
integrating the plain `pdf` restricted to `S`.

Used repeatedly below to compute `smoothedClassProb` for the (deterministic, indicator-valued) witness
classifier as a plain half-space probability. -/
theorem integral_indicatorOne_mul_pdf
    {d : Nat} (m : Input d) (σ : Real)
    (S : Set (Input d)) (hS : MeasurableSet S) :
    (∫ z, indicatorOne S z * isotropicGaussianPDF m σ z ∂volume)
      =
    ∫ z in S, isotropicGaussianPDF m σ z ∂volume := by
  have hcongr :
      (fun z => indicatorOne S z * isotropicGaussianPDF m σ z)
        =
      S.indicator (isotropicGaussianPDF m σ) := by
    funext z
    by_cases hz : z ∈ S
    · simp [indicatorOne_of_mem hz, Set.indicator_of_mem hz]
    · simp [indicatorOne_of_not_mem hz, Set.indicator_of_notMem hz]
  rw [hcongr, integral_indicator hS]

/-! ## Theorem 2: witness classifier

To show the certified radius of Theorem 1 is tight, we exhibit an explicit
*deterministic* (0/1-valued) classifier that saturates every inequality used
in `theorem1_pairwise`. It uses **three** distinct classes:

* `cA` — wins exactly on the acceptance half-space `A`;
* `cB` — wins exactly on `B \ A` (the competitor half-space, minus the sliver
  possibly shared with `A`);
* `cOther` — a "catch-all" class winning on the complement `(A ∪ B)ᶜ`.

A third class `cOther` is required (rather than only `cA`, `cB`) because `A`
and `B` need not cover all of `Rᵈ`: `A ∪ B` may be a strict subset (e.g. when
`pA + pB < 1` there is genuine room left over), and every point of `Rᵈ` must
be assigned to *some* class with total probability `1`, so the leftover
region `(A ∪ B)ᶜ` needs its own class. Using `B \ A` rather than `B` for
`cB`'s region additionally keeps the three regions `A`, `B \ A`, `(A ∪ B)ᶜ`
pairwise disjoint by construction (so `theorem2WitnessClassProb_sum` is a clean case split),
while `integral_competitor_diff_acceptance` shows this costs `cB` no probability mass, because `A ∩ B` is Gaussian-null. -/

/-- Class-probability function of the Theorem 2 witness classifier: a
deterministic one-hot assignment of each point `z` to
`cA`, `cB`, or `cOther` according to which of the three disjoint regions `A`,
`B \ A`, `(A ∪ B)ᶜ` it falls in. -/
def theorem2WitnessClassProb
    {d : Nat} {C : Type*} [DecidableEq C]
    (x δ : Input d) (σ : Real)
    (pA pB : Set.Ioo (0 : Real) 1)
    (cA cB cOther : C)
    (z : Input d) (c : C) : Real :=
  if c = cA then
    indicatorOne (acceptanceHalfspace x δ σ pA) z
  else if c = cB then
    indicatorOne
      (competitorHalfspace x δ σ pB \ acceptanceHalfspace x δ σ pA) z
  else if c = cOther then
    indicatorOne
      ((acceptanceHalfspace x δ σ pA ∪ competitorHalfspace x δ σ pB)ᶜ) z
  else
    0

/-- Each coordinate `z ↦ theorem2WitnessClassProb` is measurable -/
theorem measurable_theorem2WitnessClassProb
    {d : Nat} {C : Type*} [DecidableEq C]
    (x δ : Input d) (σ : Real)
    (pA pB : Set.Ioo (0 : Real) 1)
    (cA cB cOther : C) (c : C) :
    Measurable (theorem2WitnessClassProb x δ σ pA pB cA cB cOther · c) := by
  set A := acceptanceHalfspace x δ σ pA
  set B := competitorHalfspace x δ σ pB
  have hA : MeasurableSet A := measurableSet_acceptanceHalfspace x δ σ pA
  have hB : MeasurableSet B := measurableSet_competitorHalfspace x δ σ pB
  have hBA : MeasurableSet (B \ A) := hB.diff hA
  have hUc : MeasurableSet (A ∪ B)ᶜ := (hA.union hB).compl
  classical
  -- Nest three constant-predicate `ite`s; each branch is an indicator (or zero).
  unfold theorem2WitnessClassProb
  refine Measurable.ite (p := fun _ => c = cA) (MeasurableSet.const _)
    (by simpa [A] using measurable_indicatorOne hA) ?_
  refine Measurable.ite (p := fun _ => c = cB) (MeasurableSet.const _)
    (by simpa [A, B] using measurable_indicatorOne hBA) ?_
  refine Measurable.ite (p := fun _ => c = cOther) (MeasurableSet.const _)
    (by simpa [A, B] using measurable_indicatorOne hUc) measurable_const

/-- Every branch of `theorem2WitnessClassProb` is either `indicatorOne S z` or the literal `0`, so the whole
function is nonnegative — one of the three fields required for a `RandomizedClassifier`. -/
theorem theorem2WitnessClassProb_nonneg
    {d : Nat} {C : Type*} [DecidableEq C]
    (x δ : Input d) (σ : Real)
    (pA pB : Set.Ioo (0 : Real) 1)
    (cA cB cOther : C) (z : Input d) (c : C) :
    0 ≤ theorem2WitnessClassProb x δ σ pA pB cA cB cOther z c := by
  unfold theorem2WitnessClassProb
  split_ifs <;> first | exact indicatorOne_nonneg _ z | exact le_rfl

/-- The class probabilities at any fixed `z` sum to `1`: since `A`, `B \ A`,
`(A ∪ B)ᶜ` partition `Rᵈ` (every point lies in exactly one of the three), `z`
is a "one-hot" point putting weight `1` on whichever of `cA`, `cB`, `cOther`
owns its region and `0` on every other class (including any fourth class,
where the function is identically `0` by the `else` branch of
`theorem2WitnessClassProb`). The three-way `by_cases` below is exactly this
case split on which region `z` belongs to. -/
theorem theorem2WitnessClassProb_sum
    {d : Nat} {C : Type*} [Fintype C] [DecidableEq C]
    (x δ : Input d) (σ : Real)
    (pA pB : Set.Ioo (0 : Real) 1)
    (cA cB cOther : C)
    (hAB : cA ≠ cB) (hAO : cA ≠ cOther) (hBO : cB ≠ cOther)
    (z : Input d) :
    ∑ c, theorem2WitnessClassProb x δ σ pA pB cA cB cOther z c = 1 := by
  set A := acceptanceHalfspace x δ σ pA with hAdef
  set B := competitorHalfspace x δ σ pB with hBdef
  classical
  -- Case split on the partition {A, B\A, (A∪B)ᶜ}.
  by_cases hzA : z ∈ A
  · -- On A the witness is the one-hot vector at cA.
    have hzBA : z ∉ B \ A := fun h => h.2 hzA
    have hnotUc : z ∉ (A ∪ B)ᶜ := by
      intro h; exact (mem_compl_iff _ _).1 h (Or.inl hzA)
    have hfun :
        ∀ c, theorem2WitnessClassProb x δ σ pA pB cA cB cOther z c
          = if c = cA then (1 : Real) else 0 := by
      intro c
      unfold theorem2WitnessClassProb
      by_cases hca : c = cA
      · subst hca
        rw [if_pos rfl, indicatorOne_of_mem (hAdef ▸ hzA)]
        simp
      · rw [if_neg hca]
        by_cases hcb : c = cB
        · subst hcb
          rw [if_pos rfl, indicatorOne_of_not_mem (by simpa [hAdef, hBdef] using hzBA)]
          simp [hca]
        · rw [if_neg hcb]
          by_cases hco : c = cOther
          · subst hco
            rw [if_pos rfl,
              indicatorOne_of_not_mem (by simpa [hAdef, hBdef] using hnotUc)]
            simp [hca]
          · rw [if_neg hco]
            simp [hca]
    simp_rw [hfun, Finset.sum_ite_eq']
    simp
  · by_cases hzB : z ∈ B
    · -- On B \ A the witness is the one-hot vector at cB.
      have hzBA : z ∈ B \ A := ⟨hzB, hzA⟩
      have hnotUc : z ∉ (A ∪ B)ᶜ := by
        intro h; exact (mem_compl_iff _ _).1 h (Or.inr hzB)
      have hfun :
          ∀ c, theorem2WitnessClassProb x δ σ pA pB cA cB cOther z c
            = if c = cB then (1 : Real) else 0 := by
        intro c
        unfold theorem2WitnessClassProb
        by_cases hca : c = cA
        · subst hca
          rw [if_pos rfl, indicatorOne_of_not_mem (hAdef ▸ hzA)]
          simp [hAB]
        · rw [if_neg hca]
          by_cases hcb : c = cB
          · subst hcb
            rw [if_pos rfl, indicatorOne_of_mem (by simpa [hAdef, hBdef] using hzBA)]
            simp
          · rw [if_neg hcb]
            by_cases hco : c = cOther
            · subst hco
              rw [if_pos rfl,
                indicatorOne_of_not_mem (by simpa [hAdef, hBdef] using hnotUc)]
              simp [hcb]
            · rw [if_neg hco]
              simp [hcb]
      simp_rw [hfun, Finset.sum_ite_eq']
      simp
    · -- Off A ∪ B the witness is the one-hot vector at cOther.
      have hzUc : z ∈ (A ∪ B)ᶜ := by
        rw [mem_compl_iff]
        intro hzU; exact Or.elim hzU hzA hzB
      have hzBA : z ∉ B \ A := fun h => hzB h.1
      have hfun :
          ∀ c, theorem2WitnessClassProb x δ σ pA pB cA cB cOther z c
            = if c = cOther then (1 : Real) else 0 := by
        intro c
        unfold theorem2WitnessClassProb
        by_cases hca : c = cA
        · subst hca
          rw [if_pos rfl, indicatorOne_of_not_mem (hAdef ▸ hzA)]
          simp [hAO]
        · rw [if_neg hca]
          by_cases hcb : c = cB
          · subst hcb
            rw [if_pos rfl, indicatorOne_of_not_mem (by simpa [hAdef, hBdef] using hzBA)]
            simp [hBO]
          · rw [if_neg hcb]
            by_cases hco : c = cOther
            · subst hco
              rw [if_pos rfl, indicatorOne_of_mem (by simpa [hAdef, hBdef] using hzUc)]
              simp
            · rw [if_neg hco]
              simp [hco]
      simp_rw [hfun, Finset.sum_ite_eq']
      simp

/-- Deterministic witness used in Theorem 2: packages
`theorem2WitnessClassProb` together with the three structural lemmas above
(`measurable_theorem2WitnessClassProb`, `theorem2WitnessClassProb_nonneg`,
`theorem2WitnessClassProb_sum`) into a bona fide `RandomizedClassifier`. Note
it is deterministic in the sense that `classProb` only ever takes values `0`
or `1` — it is a hard classifier, merely presented through the
`RandomizedClassifier` interface, which is exactly what is needed to show the
Theorem 1 radius bound cannot be improved even for ordinary (non-randomized)
classifiers. -/
noncomputable def theorem2Witness
    {d : Nat} {C : Type*} [Fintype C] [DecidableEq C]
    (x δ : Input d) (σ : Real)
    (pA pB : Set.Ioo (0 : Real) 1)
    (cA cB cOther : C)
    (hAB : cA ≠ cB) (hAO : cA ≠ cOther) (hBO : cB ≠ cOther) :
    RandomizedClassifier (Input d) C where
  classProb := theorem2WitnessClassProb x δ σ pA pB cA cB cOther
  measurable_classProb := fun c =>
    measurable_theorem2WitnessClassProb x δ σ pA pB cA cB cOther c
  classProb_nonneg := fun z c =>
    theorem2WitnessClassProb_nonneg x δ σ pA pB cA cB cOther z c
  sum_classProb_eq_one := fun z =>
    theorem2WitnessClassProb_sum x δ σ pA pB cA cB cOther hAB hAO hBO z

/-- The witness's `cA`-coordinate is literally the indicator of the
acceptance half-space `A` — a direct unfolding of the `if c = cA then ...`
branch of `theorem2WitnessClassProb` (the `cA` branch does not depend on the
disjointness/naming hypotheses `hAB, hAO, hBO`, only on `c = cA`). -/
theorem theorem2Witness_classProb_cA
    {d : Nat} {C : Type*} [Fintype C] [DecidableEq C]
    (x δ : Input d) (σ : Real)
    (pA pB : Set.Ioo (0 : Real) 1)
    (cA cB cOther : C)
    (hAB : cA ≠ cB) (hAO : cA ≠ cOther) (hBO : cB ≠ cOther) :
    (fun z =>
        (theorem2Witness x δ σ pA pB cA cB cOther hAB hAO hBO).classProb z cA)
      =
    indicatorOne (acceptanceHalfspace x δ σ pA) := by
  funext z -- apply the `funext` lemma untill the goal target is not reducible to `((fun x => ...) = (fun x => ...))`
  simp [theorem2Witness, theorem2WitnessClassProb]

/-- The witness's `cB`-coordinate is the indicator of `B \ A`: since `cB ≠
cA` (`hAB`), unfolding `theorem2WitnessClassProb` skips the `cA` branch and
lands on the `c = cB` branch, `indicatorOne (B \ A)`. -/
theorem theorem2Witness_classProb_cB
    {d : Nat} {C : Type*} [Fintype C] [DecidableEq C]
    (x δ : Input d) (σ : Real)
    (pA pB : Set.Ioo (0 : Real) 1)
    (cA cB cOther : C)
    (hAB : cA ≠ cB) (hAO : cA ≠ cOther) (hBO : cB ≠ cOther) :
    (fun z =>
        (theorem2Witness x δ σ pA pB cA cB cOther hAB hAO hBO).classProb z cB)
      =
    indicatorOne
      (competitorHalfspace x δ σ pB \ acceptanceHalfspace x δ σ pA) := by
  funext z
  simp [theorem2Witness, theorem2WitnessClassProb, hAB.symm]

/-- Theorem 2 (base probabilities): the witness attains the prescribed smoothed
scores at the original point `x`, i.e. `s_X(cA) = pA` and `s_X(cB) = pB`
exactly. This shows the witness genuinely satisfies Theorem 1's premises
with equality, so any radius improvement claimed for Theorem 1 would have to
apply to this witness too — setting up the contradiction proved next in
`theorem2_not_uniqueWinner`.

* `s_X(cA) = P_X(A)`: `cA`'s region is exactly `A`
  (`theorem2Witness_classProb_cA`), and `P_X(A) = pA` by
  `prob_X_acceptanceHalfspace`.
* `s_X(cB) = P_X(B)`: `cB`'s region is `B \ A`
  (`theorem2Witness_classProb_cB`), which by
  `integral_competitor_diff_acceptance` (using the null intersection
  `acceptance_competitor_inter_gaussian_null`) has the *same* `X`-probability
  as `B` itself, namely `pB` (`prob_X_competitorHalfspace`). -/
theorem theorem2_witness
    {d : Nat} {C : Type*} [Fintype C] [DecidableEq C]
    (x δ : Input d) (σ : Real) (hσ : 0 < σ)
    (pA pB : Set.Ioo (0 : Real) 1)
    (cA cB cOther : C)
    (hAB : cA ≠ cB) (hAO : cA ≠ cOther) (hBO : cB ≠ cOther)
    (hδ : δ ≠ 0)
    (hsum : pA.1 + pB.1 ≤ 1) :
    let f := theorem2Witness x δ σ pA pB cA cB cOther hAB hAO hBO
    smoothedClassProb (isotropicGaussianDensity x σ hσ) f cA = pA.1
      ∧
    smoothedClassProb (isotropicGaussianDensity x σ hσ) f cB = pB.1 := by
  intro f
  set A := acceptanceHalfspace x δ σ pA
  set B := competitorHalfspace x δ σ pB
  have hA : MeasurableSet A := measurableSet_acceptanceHalfspace x δ σ pA
  have hB : MeasurableSet B := measurableSet_competitorHalfspace x δ σ pB
  have hBA : MeasurableSet (B \ A) := hB.diff hA
  have hden : (isotropicGaussianDensity x σ hσ : Input d → Real)
      = isotropicGaussianPDF x σ := rfl
  -- s_X(cA) = ∫ [z ∈ A] · pdf(z) dz = ∫_A pdf = P_X(A) = pA.
  have hscoreA :
      smoothedClassProb (isotropicGaussianDensity x σ hσ) f cA = pA.1 := by
    have hfun :
        (fun z => f.classProb z cA) = indicatorOne A := by
      simpa [f, A] using
        theorem2Witness_classProb_cA x δ σ pA pB cA cB cOther hAB hAO hBO
    have hXA := prob_X_acceptanceHalfspace x δ σ hσ hδ pA
    calc
      smoothedClassProb (isotropicGaussianDensity x σ hσ) f cA
          = ∫ z, f.classProb z cA * isotropicGaussianPDF x σ z ∂volume := by
            simp [smoothedClassProb, hden]
      _ = ∫ z, indicatorOne A z * isotropicGaussianPDF x σ z ∂volume :=
        congrArg (fun g : Input d → Real =>
          ∫ z, g z * isotropicGaussianPDF x σ z ∂volume) hfun
      _ = ∫ z in A, isotropicGaussianPDF x σ z ∂volume :=
        integral_indicatorOne_mul_pdf x σ A hA
      _ = pA.1 := by simpa [A] using hXA
  -- s_X(cB) = ∫_{B\A} pdf = ∫_B pdf (null intersection) = P_X(B) = pB.
  have hscoreB :
      smoothedClassProb (isotropicGaussianDensity x σ hσ) f cB = pB.1 := by
    have hfun :
        (fun z => f.classProb z cB) = indicatorOne (B \ A) := by
      simpa [f, A, B] using
        theorem2Witness_classProb_cB x δ σ pA pB cA cB cOther hAB hAO hBO
    have hnull :=
      acceptance_competitor_inter_gaussian_null x δ σ hσ hδ pA pB hsum
    have hdiff :=
      integral_competitor_diff_acceptance (m := x) x δ σ hσ pA pB hnull
    have hXB := prob_X_competitorHalfspace x δ σ hσ hδ pB
    calc
      smoothedClassProb (isotropicGaussianDensity x σ hσ) f cB
          = ∫ z, f.classProb z cB * isotropicGaussianPDF x σ z ∂volume := by
            simp [smoothedClassProb, hden]
      _ = ∫ z, indicatorOne (B \ A) z * isotropicGaussianPDF x σ z ∂volume :=
        congrArg (fun g : Input d → Real =>
          ∫ z, g z * isotropicGaussianPDF x σ z ∂volume) hfun
      _ = ∫ z in B \ A, isotropicGaussianPDF x σ z ∂volume :=
        integral_indicatorOne_mul_pdf x σ (B \ A) hBA
      _ = ∫ z in B, isotropicGaussianPDF x σ z ∂volume := by
          simpa [A, B] using hdiff
      _ = pB.1 := by simpa [B] using hXB
  exact ⟨hscoreA, hscoreB⟩

/-- Theorem 2 (tightness): under the reversed radius condition the witness has
strictly larger smoothed score for `cB` than for `cA` at `x+δ`, so `cA` is not
the unique winner.

### Proof strategy

We argue by contradiction: assume `huniq : IsUniqueWinner (...) cA`, i.e.
`cA` *is* still the unique winner at `x + δ`. The proof then:

1. Computes `s_Y(cA) = P_Y(A) = Φ(Φ⁻¹(pA) − ‖δ‖/σ)` exactly (`hYA`), by the
   same indicator/half-space bookkeeping as in `theorem2_witness`, now at the
   shifted point `x + δ` (using `prob_Y_acceptanceHalfspace`).
2. Computes `s_Y(cB) = P_Y(B \ A) = P_Y(B) = Φ(Φ⁻¹(pB) + ‖δ‖/σ)` exactly
   (`hYB`), using the *shifted* null-intersection fact
   `acceptance_competitor_inter_gaussian_null_shifted` and
   `prob_Y_competitorHalfspace`.
3. Uses the reversed radius hypothesis `hRadius`
   together with `shifted_halfspace_probability_gt` to conclude `s_Y(cA) < s_Y(cB)`
   (`hcmp`) — i.e. the reversed inequality on `δ` makes `cB` strictly
   *defeat* `cA` at the perturbed point, the opposite of what `huniq` claims.
4. Derives the contradiction: `huniq cB hAB.symm` states `s_Y(cB) < s_Y(cA)`
   (unique-winner applied to the competitor `cB ≠ cA`), while `hcmp` states
   the reverse `s_Y(cA) < s_Y(cB)`. Two real numbers cannot be strictly less
   than each other in both directions, which is exactly the statement of
   `lt_asymm : a < b → ¬ (b < a)`; applying it to `hcmp` and feeding it
   `huniq cB hAB.symm` (of type `s_Y(cB) < s_Y(cA)`) yields `False`. -/
theorem theorem2_not_uniqueWinner
    {d : Nat} {C : Type*} [Fintype C] [DecidableEq C]
    (x δ : Input d) (σ : Real) (hσ : 0 < σ)
    (pA pB : Set.Ioo (0 : Real) 1)
    (cA cB cOther : C)
    (hAB : cA ≠ cB) (hAO : cA ≠ cOther) (hBO : cB ≠ cOther)
    (hδ : δ ≠ 0)
    (hsum : pA.1 + pB.1 ≤ 1)
    (hRadius :
      (σ / 2) * (standardNormalQuantile pA - standardNormalQuantile pB)
        <
      ‖δ‖) :
    let f := theorem2Witness x δ σ pA pB cA cB cOther hAB hAO hBO
    ¬ IsUniqueWinner
        (fun c =>
          smoothedClassProb (isotropicGaussianDensity (x + δ) σ hσ) f c)
        cA := by
  -- Assume for contradiction that cA is (still) the unique winner at x + δ.
  intro f huniq
  set A := acceptanceHalfspace x δ σ pA
  set B := competitorHalfspace x δ σ pB
  have hA : MeasurableSet A := measurableSet_acceptanceHalfspace x δ σ pA
  have hB : MeasurableSet B := measurableSet_competitorHalfspace x δ σ pB
  have hBA : MeasurableSet (B \ A) := hB.diff hA
  have hden : (isotropicGaussianDensity (x + δ) σ hσ : Input d → Real)
      = isotropicGaussianPDF (x + δ) σ := rfl
  have hYA :
      smoothedClassProb (isotropicGaussianDensity (x + δ) σ hσ) f cA
        =
      standardNormalCDF (standardNormalQuantile pA - ‖δ‖ / σ) := by
    have hfun :
        (fun z => f.classProb z cA) = indicatorOne A := by
      simpa [f, A] using
        theorem2Witness_classProb_cA x δ σ pA pB cA cB cOther hAB hAO hBO
    have hYAp := prob_Y_acceptanceHalfspace x δ σ hσ hδ pA
    calc
      smoothedClassProb (isotropicGaussianDensity (x + δ) σ hσ) f cA
          = ∫ z, f.classProb z cA * isotropicGaussianPDF (x + δ) σ z ∂volume := by
            simp [smoothedClassProb, hden]
      _ = ∫ z, indicatorOne A z * isotropicGaussianPDF (x + δ) σ z ∂volume :=
        congrArg (fun g : Input d → Real =>
          ∫ z, g z * isotropicGaussianPDF (x + δ) σ z ∂volume) hfun
      _ = ∫ z in A, isotropicGaussianPDF (x + δ) σ z ∂volume :=
        integral_indicatorOne_mul_pdf (x + δ) σ A hA
      _ = standardNormalCDF (standardNormalQuantile pA - ‖δ‖ / σ) := by
          simpa [A] using hYAp
  have hYB :
      smoothedClassProb (isotropicGaussianDensity (x + δ) σ hσ) f cB
        =
      standardNormalCDF (standardNormalQuantile pB + ‖δ‖ / σ) := by
    have hfun :
        (fun z => f.classProb z cB) = indicatorOne (B \ A) := by
      simpa [f, A, B] using
        theorem2Witness_classProb_cB x δ σ pA pB cA cB cOther hAB hAO hBO
    have hnull :=
      acceptance_competitor_inter_gaussian_null_shifted x δ σ hσ hδ pA pB hsum
    have hdiff :=
      integral_competitor_diff_acceptance (m := x + δ) x δ σ hσ pA pB hnull
    have hYBp := prob_Y_competitorHalfspace x δ σ hσ hδ pB
    calc
      smoothedClassProb (isotropicGaussianDensity (x + δ) σ hσ) f cB
          = ∫ z, f.classProb z cB *
              isotropicGaussianPDF (x + δ) σ z ∂volume := by
            simp [smoothedClassProb, hden]
      _ = ∫ z, indicatorOne (B \ A) z *
              isotropicGaussianPDF (x + δ) σ z ∂volume :=
        congrArg (fun g : Input d → Real =>
          ∫ z, g z * isotropicGaussianPDF (x + δ) σ z ∂volume) hfun
      _ = ∫ z in B \ A, isotropicGaussianPDF (x + δ) σ z ∂volume :=
        integral_indicatorOne_mul_pdf (x + δ) σ (B \ A) hBA
      _ = ∫ z in B, isotropicGaussianPDF (x + δ) σ z ∂volume := by
          simpa [A, B] using hdiff
      _ = standardNormalCDF (standardNormalQuantile pB + ‖δ‖ / σ) := by
          simpa [B] using hYBp
  -- Reversed radius ⇒ reversed Φ-comparison: Φ(Φ⁻¹(pA) - ‖δ‖/σ) < Φ(Φ⁻¹(pB) + ‖δ‖/σ).
  have hlt := shifted_halfspace_probability_gt σ hσ ‖δ‖ pA pB hRadius
  -- Combine with hYA, hYB: s_Y(cA) < s_Y(cB), i.e. cB actually defeats cA.
  have hcmp :
      smoothedClassProb (isotropicGaussianDensity (x + δ) σ hσ) f cA
        <
      smoothedClassProb (isotropicGaussianDensity (x + δ) σ hσ) f cB := by
    rw [hYA, hYB]; exact hlt
  -- `huniq cB hAB.symm : s_Y(cB) < s_Y(cA)` (cB is a competitor, cB ≠ cA)
  -- directly contradicts `hcmp : s_Y(cA) < s_Y(cB)`, since `<` cannot hold in
  -- both directions between the same two reals (`lt_asymm`).
  exact lt_asymm hcmp (huniq cB hAB.symm)

end

end RandomizedSmoothing
