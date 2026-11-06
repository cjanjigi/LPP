/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module
public import Mathlib.MeasureTheory.Integral.Layercake
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# First moments from exponential probability tails

The tail integral gives a first-moment bound used for greedy lattice animal estimates in
Martin (2002), Theorem 2.3. The finite extended moment is established first, followed by
integrability and the bound on the real expectation.
-/

public section
open MeasureTheory Set
open scoped ENNReal
namespace LPPDifferentiability

private theorem exponential_tail_integrable {a : ℝ} (ha : 0 < a) (y : ℝ) :
    IntegrableOn (fun s : ℝ => Real.exp (-a * (s - y))) (Ioi y) := by
  have h := (integrableOn_exp_mul_Ioi (neg_neg_of_pos ha) y).const_mul (Real.exp (a * y))
  have heq : (fun s : ℝ => Real.exp (-a * (s - y))) =
      (fun s : ℝ => Real.exp (a * y) * Real.exp (-a * s)) := by
    funext s
    rw [← Real.exp_add]
    congr 1
    ring
  rw [heq]
  exact h

private theorem exponential_tail_integral {a : ℝ} (ha : 0 < a) (y : ℝ) :
    (∫ s : ℝ in Ioi y, Real.exp (-a * (s - y))) = 1 / a := by
  have heq : (fun s : ℝ => Real.exp (-a * (s - y))) =
      (fun s : ℝ => Real.exp (a * y) * Real.exp (-a * s)) := by
    funext s
    rw [← Real.exp_add]
    congr 1
    ring
  rw [heq, integral_const_mul, integral_exp_mul_Ioi (neg_neg_of_pos ha)]
  rw [div_neg, neg_div, neg_neg, ← mul_div_assoc, ← Real.exp_add]
  have hz : a * y + -a * y = 0 := by ring
  rw [hz, Real.exp_zero]

/-- An exponential bound on the closed tails of a nonnegative random variable gives a finite
first moment, and bounds its expectation. -/
theorem integrable_and_integral_le_of_exponential_tail
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {X : Ω → ℝ} (hX : Measurable X) (hX0 : 0 ≤ᵐ[μ] X)
    {a y : ℝ} (ha : 0 < a) (hy : 0 ≤ y)
    (htail : ∀ s : ℝ, y ≤ s →
      μ {ω | s ≤ X ω} ≤ ENNReal.ofReal (Real.exp (-a * (s - y)))) :
    Integrable X μ ∧ (∫ ω, X ω ∂μ) ≤ y + 1 / a := by
  have hsplit : Ioi (0 : ℝ) = Ioc 0 y ∪ Ioi y := by
    ext s
    simp only [mem_Ioi, mem_union, mem_Ioc]
    constructor
    · intro hs
      by_cases hsy : s ≤ y
      · exact Or.inl ⟨hs, hsy⟩
      · exact Or.inr (lt_of_not_ge hsy)
    · rintro (⟨hs, _⟩ | hs)
      · exact hs
      · exact lt_of_le_of_lt hy hs
  have hdisj : Disjoint (Ioc (0 : ℝ) y) (Ioi y) := by
    rw [disjoint_left]
    exact fun s hs ht => (not_lt_of_ge hs.2) ht
  have hlow : (∫⁻ s in Ioc (0 : ℝ) y, μ {ω | s ≤ X ω}) ≤ ENNReal.ofReal y := by
    calc
      _ ≤ ∫⁻ _s in Ioc (0 : ℝ) y, (1 : ℝ≥0∞) :=
        lintegral_mono (fun _ => prob_le_one)
      _ = ENNReal.ofReal y := by rw [setLIntegral_one, Real.volume_Ioc, sub_zero]
  have hhigh : (∫⁻ s in Ioi y, μ {ω | s ≤ X ω}) ≤ ENNReal.ofReal (1 / a) := by
    calc
      _ ≤ ∫⁻ s in Ioi y, ENNReal.ofReal (Real.exp (-a * (s - y))) := by
        apply setLIntegral_mono' measurableSet_Ioi
        intro s hs
        exact htail s hs.le
      _ = ENNReal.ofReal (1 / a) := by
        rw [← ofReal_integral_eq_lintegral_ofReal (exponential_tail_integrable ha y)
          (Filter.Eventually.of_forall (fun s => (Real.exp_pos _).le)),
          exponential_tail_integral ha y]
  have hbound : (∫⁻ ω, ENNReal.ofReal (X ω) ∂μ) ≤ ENNReal.ofReal (y + 1 / a) := by
    rw [lintegral_eq_lintegral_meas_le μ hX0 hX.aemeasurable, hsplit,
      lintegral_union measurableSet_Ioi hdisj]
    calc
      _ ≤ ENNReal.ofReal y + ENNReal.ofReal (1 / a) := add_le_add hlow hhigh
      _ = ENNReal.ofReal (y + 1 / a) := (ENNReal.ofReal_add hy (by positivity)).symm
  have hint : Integrable X μ :=
    (lintegral_ofReal_ne_top_iff_integrable hX.aestronglyMeasurable hX0).mp
      (ne_of_lt (lt_of_le_of_lt hbound ENNReal.ofReal_lt_top))
  refine ⟨hint, ?_⟩
  rw [← ofReal_integral_eq_lintegral_ofReal hint hX0] at hbound
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity : 0 ≤ y + 1 / a)).mp hbound

/-- The moment estimate above, for an exponential rate at least one. -/
theorem integrable_and_integral_le_add_one_of_exponential_tail
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {X : Ω → ℝ} (hX : Measurable X) (hX0 : 0 ≤ᵐ[μ] X)
    {a y : ℝ} (ha : 1 ≤ a) (hy : 0 ≤ y)
    (htail : ∀ s : ℝ, y ≤ s →
      μ {ω | s ≤ X ω} ≤ ENNReal.ofReal (Real.exp (-a * (s - y)))) :
    Integrable X μ ∧ (∫ ω, X ω ∂μ) ≤ y + 1 := by
  have ha0 : 0 < a := lt_of_lt_of_le zero_lt_one ha
  obtain ⟨hint, hmean⟩ := integrable_and_integral_le_of_exponential_tail μ hX hX0 ha0 hy htail
  refine ⟨hint, hmean.trans (add_le_add_right ?_ y)⟩
  exact (div_le_one ha0).mpr ha

end LPPDifferentiability
