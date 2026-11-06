/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Martin2004.Probability.BernoulliCoverTail
public import ProbabilityBasics.Analysis.BernoulliScales
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

import Mathlib.Tactic.Linarith

/-! # The planar normalized Bernoulli animal tail

The scale substitution and exponential simplification in Martin (2002),
Proposition 2.2. The probability event is stated
by existence of an actual rooted animal, without introducing a maximum.
-/

public section

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace LPPDifferentiability

/-- The explicit planar constant in Martin's large-scale tail is positive. -/
theorem bernoulli_tail_constant_pos :
    0 < 2 * Real.log 9 + 243 * (Real.exp 1 - 1) := by
  have hlog : 0 < Real.log 9 := Real.log_pos (by norm_num)
  have hexp : 0 < Real.exp 1 - 1 := by
    have := Real.one_lt_exp_iff.mpr (by norm_num : (0 : ℝ) < 1)
    linarith only [this]
  positivity

/-- The purely numerical simplification of the cover estimate. The final
probabilistic theorem derives these count and size bounds at the actual scale. -/
theorem bernoulli_cover_exponential_le (p a s : ℝ) (r M : ℕ)
    (hp : 0 < p) (hr : (r : ℝ) ≤ 2 * a) (hM : (M : ℝ) ≤ 243 * a / p) :
    (9 ^ r : ℝ) * Real.exp (-a * s + p * (Real.exp 1 - 1) * (M : ℝ)) ≤
      Real.exp (-a * (s - (2 * Real.log 9 + 243 * (Real.exp 1 - 1)))) := by
  have hlog : 0 ≤ Real.log 9 := le_of_lt (Real.log_pos (by norm_num))
  have hexp : 0 ≤ Real.exp 1 - 1 := by
    have := Real.one_le_exp (by norm_num : (0 : ℝ) ≤ 1)
    linarith only [this]
  have hrlog := mul_le_mul_of_nonneg_right hr hlog
  have hMp : p * (M : ℝ) ≤ 243 * a := by
    have := (le_div_iff₀ hp).mp hM
    simpa only [mul_comm] using this
  have hMexp := mul_le_mul_of_nonneg_left hMp hexp
  have hpow : (9 ^ r : ℝ) = Real.exp ((r : ℝ) * Real.log 9) := by
    rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 9)]
  rw [hpow, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  nlinarith only [hrlog, hMexp]

/-- Martin's planar large-scale tail for the actual rooted-animal existence
event, with the ceiling and floor scales derived inside the proof. -/
theorem measureReal_exists_animal_sum_ge_le_normalized {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Lattice → Ω → ℝ)
    (hInd : iIndepFun X μ) (hX : ∀ v, Measurable (X v))
    (h01 : ∀ v, ∀ᵐ ω ∂μ, X v ω = 0 ∨ X v ω = 1)
    (p : ℝ) (hp : ∀ v, μ.real {ω | X v ω = 1} = p)
    (hp0 : 0 < p) (hp1 : p ≤ 1) (n : ℕ) (hn : 1 ≤ n)
    (ha : 1 < (n : ℝ) * Real.sqrt p) (s : ℝ)
    (hs : 2 * Real.log 9 + 243 * (Real.exp 1 - 1) ≤ s) :
    μ.real {ω | ∃ A : Finset Lattice, IsConnectedAnimal A ∧
      (0 : Lattice) ∈ A ∧ A.card = n ∧
        (n : ℝ) * Real.sqrt p * s ≤ ∑ v ∈ A, X v ω} ≤
      Real.exp (-((n : ℝ) * Real.sqrt p) *
        (s - (2 * Real.log 9 + 243 * (Real.exp 1 - 1)))) := by
  let a : ℝ := (n : ℝ) * Real.sqrt p
  let l : ℕ := Nat.ceil (1 / Real.sqrt p)
  let r : ℕ := 2 * n / l
  let M : ℕ := (r + 1) * (4 * l + 1) ^ 2
  have hl : 1 ≤ l := bernoulli_scale_positive p hp0
  have hln : l ≤ n := bernoulli_scale_le_n n p hp0 ha
  have hr : (r : ℝ) ≤ 2 * a := by
    simpa only [mul_assoc] using bernoulli_radius_bound n p hn hp0
  have hM : (M : ℝ) ≤ 243 * a / p := by
    dsimp only [M]
    push_cast
    exact bernoulli_cover_count_bound n p hn hp0 hp1 ha
  have ha0 : 0 < a := lt_trans zero_lt_one ha
  have hs0 : 0 < s := lt_of_lt_of_le bernoulli_tail_constant_pos hs
  have ht : 0 < a * s := mul_pos ha0 hs0
  calc
    μ.real {ω | ∃ A : Finset Lattice, IsConnectedAnimal A ∧
        (0 : Lattice) ∈ A ∧ A.card = n ∧
          (n : ℝ) * Real.sqrt p * s ≤ ∑ v ∈ A, X v ω} ≤
        (9 ^ r : ℝ) * Real.exp (-a * s + p * (Real.exp 1 - 1) * (M : ℝ)) :=
      by
        simpa only [neg_mul] using
          measureReal_exists_animal_sum_ge_le μ X hInd hX h01 p hp hp0.le hp1
            n l hn hl hln (a * s) ht
    _ ≤ Real.exp (-a * (s - (2 * Real.log 9 + 243 * (Real.exp 1 - 1)))) :=
      bernoulli_cover_exponential_le p a s r M hp0 hr hM

/-- The same normalized tail as an ENNReal probability bound. Finiteness of
the actual probability measure justifies conversion from its real probability. -/
theorem measure_exists_animal_sum_ge_le_normalized {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Lattice → Ω → ℝ)
    (hInd : iIndepFun X μ) (hX : ∀ v, Measurable (X v))
    (h01 : ∀ v, ∀ᵐ ω ∂μ, X v ω = 0 ∨ X v ω = 1)
    (p : ℝ) (hp : ∀ v, μ.real {ω | X v ω = 1} = p)
    (hp0 : 0 < p) (hp1 : p ≤ 1) (n : ℕ) (hn : 1 ≤ n)
    (ha : 1 < (n : ℝ) * Real.sqrt p) (s : ℝ)
    (hs : 2 * Real.log 9 + 243 * (Real.exp 1 - 1) ≤ s) :
    μ {ω | ∃ A : Finset Lattice, IsConnectedAnimal A ∧
      (0 : Lattice) ∈ A ∧ A.card = n ∧
        (n : ℝ) * Real.sqrt p * s ≤ ∑ v ∈ A, X v ω} ≤
      ENNReal.ofReal (Real.exp (-((n : ℝ) * Real.sqrt p) *
        (s - (2 * Real.log 9 + 243 * (Real.exp 1 - 1))))) := by
  let E : Set Ω := {ω | ∃ A : Finset Lattice, IsConnectedAnimal A ∧
    (0 : Lattice) ∈ A ∧ A.card = n ∧
      (n : ℝ) * Real.sqrt p * s ≤ ∑ v ∈ A, X v ω}
  have hreal : μ.real E ≤ Real.exp (-((n : ℝ) * Real.sqrt p) *
      (s - (2 * Real.log 9 + 243 * (Real.exp 1 - 1)))) :=
    measureReal_exists_animal_sum_ge_le_normalized μ X hInd hX h01 p hp hp0 hp1 n hn ha s hs
  calc
    μ E = ENNReal.ofReal (μ.real E) := (ofReal_measureReal (measure_ne_top μ E)).symm
    _ ≤ ENNReal.ofReal (Real.exp (-((n : ℝ) * Real.sqrt p) *
        (s - (2 * Real.log 9 + 243 * (Real.exp 1 - 1))))) :=
      ENNReal.ofReal_le_ofReal hreal

end LPPDifferentiability
