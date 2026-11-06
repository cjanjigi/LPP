/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Martin2004.Frozen.Martin.Shape
public import LPP_Foundations.Model.LastPassage.FirstPassage
public import Martin2004.Probability.MartinWeakContinuity
public import Martin2004.Probability.NegatedLaw

/-!
# First-passage shapes by the sign change

Martin (2004), the remark after Theorem 2.4: replacing the maximum by a minimum and each weight
`X(z)` by `-X(z)` only changes the sign of the passage time and so of the shape. Here the
first-passage time of the canonical environment with law `μ` is minus the last-passage time of the
negated environment, whose law is the canonical environment of `μ.map Neg.neg`. The last-passage
shape theorems for the negated law therefore give the first-passage shapes of Corollary 2.5(i) and
the uniform first-passage shape that Corollary 2.5(ii) and the growth models use.
-/

public section

open MeasureTheory Filter Set
open scoped Topology ENNReal NNReal

namespace LPPDifferentiability

/-- Negating every site weight, as a measurable bijection of the space of environments. -/
private def negateEnvironment : Environment ≃ᵐ Environment where
  toFun ω := fun z => -ω z
  invFun ω := fun z => -ω z
  left_inv ω := funext fun z => neg_neg (ω z)
  right_inv ω := funext fun z => neg_neg (ω z)
  measurable_toFun := Measurable.of_eval fun z => (measurable_pi_apply z).neg
  measurable_invFun := Measurable.of_eval fun z => (measurable_pi_apply z).neg

/-- An event holds almost surely for the canonical environment of the negated law exactly when its
preimage under negation of the environment holds almost surely for the original canonical
environment. Meaning: negating all weights carries null sets to null sets. See Martin (2004),
Section 2 (the weights are i.i.d.) and the remark after Theorem 2.4 (the sign change). -/
theorem ae_environmentLaw_negated_iff (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (p : Environment → Prop) :
    (∀ᵐ ω ∂environmentLaw (μ.map Neg.neg), p ω) ↔ ∀ᵐ ω ∂environmentLaw μ, p (-ω) := by
  rw [← environmentLaw_negated_eq μ]
  exact negateEnvironment.measurableEmbedding.ae_map_iff

/-- The expected first-passage time for the law `μ` is minus the expected last-passage time for the
negated law. Meaning: the sign change described after Theorem 2.4 of Martin (2004), at the level of
expectations, for any base point and displacement; see (2.9). -/
theorem integral_firstPassage_eq_neg_integral_lastPassage_negated
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (u : Lattice) (d : ℕ × ℕ) :
    ∫ ω : Environment, firstPassage ω u d ∂environmentLaw μ =
      -∫ ω : Environment, lastPassage ω u d ∂environmentLaw (μ.map Neg.neg) := by
  -- The expectation under the negated law is the expectation of the passage time of the
  -- negated environment under the original law.
  have hmap : ∫ ω : Environment, lastPassage ω u d ∂environmentLaw (μ.map Neg.neg) =
      ∫ ω : Environment, lastPassage (-ω) u d ∂environmentLaw μ := by
    rw [← environmentLaw_negated_eq μ]
    exact integral_map_equiv negateEnvironment (fun ω => lastPassage ω u d)
  -- The sign identity holds for every environment, hence under the integral.
  rw [hmap, ← integral_neg]
  exact integral_congr_ae
    (Filter.Eventually.of_forall fun ω => firstPassage_eq_neg_lastPassage ω u d)

/-- The uniform first-passage approximation by `h` for the law `μ` is the uniform last-passage
approximation by `g` for the negated law, when `h = -g`. Meaning: the almost-sure statement of the
sign change; the absolute error of the first-passage time against `h` equals the absolute error of
the negated last-passage time against `g`. See Martin (2004), the remark after Theorem 2.4 and
Corollary 2.5(ii). -/
private theorem ae_firstPassage_approx_iff (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (h g : Quadrant → ℝ) (hgh : ∀ x : Quadrant, h x = -g x) :
    (∀ᵐ ω ∂environmentLaw μ,
      ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ z : ℕ × ℕ,
        N ≤ z.1 + z.2 →
        |firstPassage ω (0, 0) z - h ((z.1 : ℝ≥0), (z.2 : ℝ≥0))| ≤
          ε * ((z.1 + z.2 : ℕ) : ℝ)) ↔
    (∀ᵐ ω ∂environmentLaw (μ.map Neg.neg),
      ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ z : ℕ × ℕ,
        N ≤ z.1 + z.2 →
        |lastPassage ω (0, 0) z - g ((z.1 : ℝ≥0), (z.2 : ℝ≥0))| ≤
          ε * ((z.1 + z.2 : ℕ) : ℝ)) := by
  rw [ae_environmentLaw_negated_iff μ]
  refine Filter.eventually_congr (Filter.Eventually.of_forall fun ω => ?_)
  -- The two absolute errors are equal, because first passage is minus last passage of `-ω`.
  have key : ∀ z : ℕ × ℕ,
      |lastPassage (-ω) (0, 0) z - g ((z.1 : ℝ≥0), (z.2 : ℝ≥0))| =
        |firstPassage ω (0, 0) z - h ((z.1 : ℝ≥0), (z.2 : ℝ≥0))| := by
    intro z
    rw [hgh, firstPassage_eq_neg_lastPassage ω (0, 0) z]
    exact abs_eq_abs.2 (Or.inr (by ring))
  constructor
  · intro H ε hε
    obtain ⟨N, hN⟩ := H ε hε
    exact ⟨N, fun z hz => by rw [key z]; exact hN z hz⟩
  · intro H ε hε
    obtain ⟨N, hN⟩ := H ε hε
    exact ⟨N, fun z hz => by have := hN z hz; rwa [key z] at this⟩

/-- Martin (2004), Corollary 2.5(i), for `d = 2`. Meaning: if the weight has a finite
mean and the lower integrated square-root tail is finite, there is exactly one real function `h` on
the closed quadrant such that the expected first-passage rate `E S(⌊n x⌋) / n` tends to `h x` in
every real direction, and this `h` is homogeneous, symmetric, subadditive and continuous on the
whole closed quadrant. Proof: the sign change turns the hypotheses into those of the
last-passage theorem for the negated law, and `h` is minus its shape. -/
theorem exists_unique_continuous_firstPassage_real_expected_rate_of_integrable_and_negative_tail
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : Integrable (fun t : ℝ => t) μ)
    (hneg : (∫⁻ t in Iio (0 : ℝ), (μ (Iic t)) ^ (1 / 2 : ℝ)) < ∞) :
    ∃! h : Quadrant → ℝ,
      (∀ x : Quadrant, Tendsto (fun n : ℕ =>
        (∫ ω : Environment, firstPassage ω 0
          (⌊(n : ℝ) * (x.1 : ℝ)⌋₊, ⌊(n : ℝ) * (x.2 : ℝ)⌋₊)
          ∂environmentLaw μ) / (n : ℝ)) atTop (𝓝 (h x))) ∧
      (∀ (c : ℝ≥0) (x : Quadrant), h (c * x.1, c * x.2) = (c : ℝ) * h x) ∧
      (∀ x : Quadrant, h (x.2, x.1) = h x) ∧
      (∀ x y : Quadrant, h (x.1 + y.1, x.2 + y.2) ≤ h x + h y) ∧
      Continuous h := by
  -- The negated law has a finite mean and a finite positive square-root tail.
  have hμν : Integrable (fun t : ℝ => t) (μ.map Neg.neg) := (negated_integrable_iff μ).2 hμ
  have hposν : (∫⁻ t in Ioi (0 : ℝ), ((μ.map Neg.neg) (Ioi t)) ^ (1 / 2 : ℝ)) < ∞ :=
    (negated_upper_sqrt_tail_iff μ).2 hneg
  -- The last-passage shape for the negated law.
  obtain ⟨g, hP, -⟩ :=
    exists_unique_continuous_lastPassage_real_expected_rate_of_integrable_and_positive_tail
      (μ.map Neg.neg) hμν hposν
  obtain ⟨⟨⟨hconv, -⟩, hhom, hsup, hswap, -⟩, hcont⟩ := hP
  -- The expected first-passage rates converge to minus the last-passage shape.
  have hfp : ∀ x : Quadrant, Tendsto (fun n : ℕ =>
      (∫ ω : Environment, firstPassage ω 0
        (⌊(n : ℝ) * (x.1 : ℝ)⌋₊, ⌊(n : ℝ) * (x.2 : ℝ)⌋₊)
        ∂environmentLaw μ) / (n : ℝ)) atTop (𝓝 (-g x)) := by
    intro x
    refine (hconv x).neg.congr fun n => ?_
    rw [integral_firstPassage_eq_neg_integral_lastPassage_negated, neg_div]
  refine ⟨fun x => -g x, ⟨hfp, ?_, ?_, ?_, hcont.neg⟩, ?_⟩
  · -- Homogeneity.
    intro c x
    have h2 : g (c * x.1, c * x.2) = (c : ℝ) * g x := hhom c x
    show -g (c * x.1, c * x.2) = (c : ℝ) * -g x
    rw [h2, mul_neg]
  · -- Symmetry.
    intro x
    have h2 : g (x.2, x.1) = g x := hswap x
    show -g (x.2, x.1) = -g x
    rw [h2]
  · -- Subadditivity is superadditivity of `g`, negated.
    intro x y
    have h2 : g x + g y ≤ g (x.1 + y.1, x.2 + y.2) := hsup x y
    linarith only [h2]
  · -- Uniqueness: two limits of the same real sequence are equal.
    intro f hf
    funext x
    exact tendsto_nhds_unique (hf.1 x) (hfp x)

/-- Martin (2004), the uniform first-passage shape (the sign change described after Theorem 2.4
applied to the uniform last-passage shape, as used for Corollary 2.5(ii) and for the growth models
of Section 5). Meaning: under both integrated square-root tails there is exactly one continuous,
homogeneous, convex function `h` on the closed quadrant such that, almost surely, the first-passage
time `S(z)` is within `ε ‖z‖` of `h z` for all long `z`, for every `ε > 0`. This is
`exists_unique_shape_martin` with minimum for maximum, `h = -g` and convex for concave. -/
theorem exists_unique_firstPassage_shape_martin
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hneg : (∫⁻ t in Iio (0 : ℝ), (μ (Iic t)) ^ (1 / 2 : ℝ)) < ∞)
    (hpos : (∫⁻ t in Ioi (0 : ℝ), (μ (Ioi t)) ^ (1 / 2 : ℝ)) < ∞) :
    ∃! h : Quadrant → ℝ,
      Continuous h ∧
      (∀ (c : ℝ≥0) (x : Quadrant),
        h (c * x.1, c * x.2) = (c : ℝ) * h x) ∧
      (∀ (x y : Quadrant) (a b : ℝ≥0), a + b = 1 →
        h (a * x.1 + b * y.1, a * x.2 + b * y.2) ≤
          (a : ℝ) * h x + (b : ℝ) * h y) ∧
      (∀ᵐ ω ∂environmentLaw μ,
        ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ z : ℕ × ℕ,
          N ≤ z.1 + z.2 →
          |firstPassage ω (0, 0) z - h ((z.1 : ℝ≥0), (z.2 : ℝ≥0))| ≤
            ε * ((z.1 + z.2 : ℕ) : ℝ)) := by
  -- The two tails of the negated law are the two tails of `μ`, exchanged.
  have hnegν : (∫⁻ t in Iio (0 : ℝ), ((μ.map Neg.neg) (Iic t)) ^ (1 / 2 : ℝ)) < ∞ :=
    (negated_lower_sqrt_tail_iff μ).2 hpos
  have hposν : (∫⁻ t in Ioi (0 : ℝ), ((μ.map Neg.neg) (Ioi t)) ^ (1 / 2 : ℝ)) < ∞ :=
    (negated_upper_sqrt_tail_iff μ).2 hneg
  -- The uniform last-passage shape for the negated law.
  obtain ⟨g, ⟨hcont, hhom, hconc, hae⟩, hUnique⟩ :=
    exists_unique_shape_martin (μ.map Neg.neg) hnegν hposν
  refine ⟨fun x => -g x, ⟨hcont.neg, ?_, ?_, ?_⟩, ?_⟩
  · -- Homogeneity.
    intro c x
    have h2 : g (c * x.1, c * x.2) = (c : ℝ) * g x := hhom c x
    show -g (c * x.1, c * x.2) = (c : ℝ) * -g x
    rw [h2, mul_neg]
  · -- Convexity is concavity of `g`, negated.
    intro x y a b hab
    have h2 := hconc x y a b hab
    linarith only [h2]
  · -- The almost-sure approximation transfers by the sign change.
    exact (ae_firstPassage_approx_iff μ (fun x => -g x) g fun _ => rfl).2 hae
  · -- Uniqueness: a competitor `f` gives the competitor `-f` for the negated law.
    rintro f ⟨hfc, hfhom, hfconv, hfae⟩
    have hneg_f : (fun x : Quadrant => -f x) = g := by
      refine hUnique (fun x => -f x) ⟨hfc.neg, ?_, ?_, ?_⟩
      · intro c x
        have h2 : f (c * x.1, c * x.2) = (c : ℝ) * f x := hfhom c x
        show -f (c * x.1, c * x.2) = (c : ℝ) * -f x
        rw [h2, mul_neg]
      · intro x y a b hab
        have h2 := hfconv x y a b hab
        show (a : ℝ) * -f x + (b : ℝ) * -f y ≤ -f (a * x.1 + b * y.1, a * x.2 + b * y.2)
        linarith only [h2]
      · exact (ae_firstPassage_approx_iff μ f (fun x => -f x)
          fun x => (neg_neg (f x)).symm).1 hfae
    funext x
    have h3 : -f x = g x := congrFun hneg_f x
    linarith only [h3]

end LPPDifferentiability
