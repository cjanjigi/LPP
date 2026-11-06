/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module
public import ProbabilityBasics.Probability.ExponentialTailMean
public import Martin2004.Probability.AnimalMaximum
public import Martin2004.Probability.BernoulliNormalizedTail
import Martin2004.Probability.BernoulliAnimalSmall
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-!
# Bernoulli animal first moments

Martin (2002), Proposition 2.2: the actual
small-parameter mean and normalized large-parameter tail give one universal
first-moment bound. Integrability is proved before rescaling the expectation.
-/

public section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace LPPDifferentiability

/-- Rescale the actual normalized exponential tail to an integrable raw
random variable and its first-moment bound. -/
theorem integrable_and_integral_le_mul_of_normalized_exponential_tail
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {N : Ω → ℝ} (hN : Measurable N) (hN0 : 0 ≤ᵐ[μ] N)
    {a y : ℝ} (ha : 1 ≤ a) (hy : 0 ≤ y)
    (htail : ∀ s : ℝ, y ≤ s →
      μ {ω | s ≤ N ω / a} ≤ ENNReal.ofReal (Real.exp (-a * (s - y)))) :
    Integrable N μ ∧ (∫ ω, N ω ∂μ) ≤ a * (y + 1) := by
  have ha0 : 0 < a := lt_of_lt_of_le zero_lt_one ha
  obtain ⟨hint, hmean⟩ := integrable_and_integral_le_add_one_of_exponential_tail
    μ (hN.div_const a) (hN0.mono (fun _ hω => div_nonneg hω ha0.le)) ha hy htail
  have heq : (fun ω => N ω / a * a) = N := by
    funext ω
    exact div_mul_cancel₀ _ (ne_of_gt ha0)
  have hintN := hint.mul_const a
  rw [heq] at hintN
  refine ⟨hintN, ?_⟩
  rw [integral_div] at hmean
  simpa only [mul_comm] using (div_le_iff₀ ha0).mp hmean

/-- Martin's large-parameter animal first moment, with both the actual maximum
and its normalized tail derived from the Bernoulli field. -/
theorem integrable_and_integral_animalMaximum_le_of_one_lt_scale
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Lattice → Ω → ℝ) (hInd : iIndepFun X μ) (hX : ∀ v, Measurable (X v))
    (h01 : ∀ v, ∀ᵐ ω ∂μ, X v ω = 0 ∨ X v ω = 1)
    (p : ℝ) (hp : ∀ v, μ.real {ω | X v ω = 1} = p)
    (hp0 : 0 < p) (hp1 : p ≤ 1) (n : ℕ) (hn : 1 ≤ n)
    (ha : 1 < (n : ℝ) * Real.sqrt p) :
    Integrable (fun ω => animalMaximum n hn (fun v => X v ω)) μ ∧
      (∫ ω, animalMaximum n hn (fun v => X v ω) ∂μ) ≤
        ((n : ℝ) * Real.sqrt p) *
          (2 * Real.log 9 + 243 * (Real.exp 1 - 1) + 1) := by
  have ha0 : 0 < (n : ℝ) * Real.sqrt p := lt_trans zero_lt_one ha
  have hN0 : 0 ≤ᵐ[μ] (fun ω => animalMaximum n hn (fun v => X v ω)) := by
    filter_upwards [ae_all_iff.2 h01] with ω hω
    apply animalMaximum_nonneg_of_forall_nonneg n hn
    intro v
    rcases hω v with hzero | hone
    · rw [hzero]
    · rw [hone]
      exact zero_le_one
  apply integrable_and_integral_le_mul_of_normalized_exponential_tail μ
    (measurable_animalMaximum X hX n hn) hN0 ha.le bernoulli_tail_constant_pos.le
  intro s hs
  have hEvent : {ω | s ≤ animalMaximum n hn (fun v => X v ω) /
        ((n : ℝ) * Real.sqrt p)} =
        {ω | ∃ A : Finset Lattice, IsConnectedAnimal A ∧
          (0 : Lattice) ∈ A ∧ A.card = n ∧
          (n : ℝ) * Real.sqrt p * s ≤ ∑ v ∈ A, X v ω} := by
    ext ω
    rw [Set.mem_ofPred_eq, Set.mem_ofPred_eq, le_div_iff₀ ha0, mul_comm s,
      le_animalMaximum_iff_exists_animalWeight_ge]
    simp only [mem_animalFamily_iff, animalWeight, and_assoc]
  rw [hEvent]
  exact measure_exists_animal_sum_ge_le_normalized μ X hInd hX h01 p hp hp0 hp1 n hn ha s hs

/-- One positive constant works for every actual planar iid Bernoulli field,
parameter in `[0,1]`, and positive animal size. Both integrability and the
actual expectation bound are conclusions. -/
theorem exists_pos_universal_animalMaximum_mean_bound :
    ∃ C : ℝ, 0 < C ∧
      ∀ {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (X : Lattice → Ω → ℝ) (_hInd : iIndepFun X μ) (_hX : ∀ v, Measurable (X v))
        (_h01 : ∀ v, ∀ᵐ ω ∂μ, X v ω = 0 ∨ X v ω = 1)
        (p : ℝ) (_hp : ∀ v, μ.real {ω | X v ω = 1} = p)
        (_hp0 : 0 ≤ p) (_hp1 : p ≤ 1) (n : ℕ) (hn : 1 ≤ n),
        Integrable (fun ω => animalMaximum n hn (fun v => X v ω)) μ ∧
          (∫ ω, animalMaximum n hn (fun v => X v ω) ∂μ) ≤ C * (n : ℝ) * Real.sqrt p := by
  refine ⟨max 4 (2 * Real.log 9 + 243 * (Real.exp 1 - 1) + 1),
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < 4) (le_max_left _ _), ?_⟩
  intro Ω inst μ instP X hInd hX h01 p hp hp0 hp1 n hn
  have ha0 : 0 ≤ (n : ℝ) * Real.sqrt p :=
    mul_nonneg (Nat.cast_nonneg n) (Real.sqrt_nonneg p)
  by_cases ha : (n : ℝ) * Real.sqrt p ≤ 1
  · obtain ⟨hint, hmean⟩ := bernoulli_animal_small_bound μ n hn X p ⟨hp0, hp1⟩ hX h01 hp ha
    refine ⟨hint, hmean.trans ?_⟩
    calc
      4 * (n : ℝ) * Real.sqrt p = 4 * ((n : ℝ) * Real.sqrt p) := by ring
      _ ≤
          max 4 (2 * Real.log 9 + 243 * (Real.exp 1 - 1) + 1) *
            ((n : ℝ) * Real.sqrt p) :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) ha0
      _ = _ := by ring
  · have ha1 : 1 < (n : ℝ) * Real.sqrt p := lt_of_not_ge ha
    have hp_pos : 0 < p := by
      by_contra h
      have hpzero : p = 0 := le_antisymm (le_of_not_gt h) hp0
      have hfalse : (1 : ℝ) < 0 := by
        simpa only [hpzero, Real.sqrt_zero, mul_zero] using ha1
      exact (not_lt_of_ge zero_le_one) hfalse
    obtain ⟨hint, hmean⟩ := integrable_and_integral_animalMaximum_le_of_one_lt_scale
      μ X hInd hX h01 p hp hp_pos hp1 n hn ha1
    refine ⟨hint, hmean.trans ?_⟩
    calc
      ((n : ℝ) * Real.sqrt p) * (2 * Real.log 9 + 243 * (Real.exp 1 - 1) + 1) ≤
          ((n : ℝ) * Real.sqrt p) *
            max 4 (2 * Real.log 9 + 243 * (Real.exp 1 - 1) + 1) :=
        mul_le_mul_of_nonneg_left (le_max_right _ _) ha0
      _ = _ := by ring

end LPPDifferentiability
