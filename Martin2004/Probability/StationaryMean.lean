/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Martin2004.Model.LastPassage.Stationary
public import Martin2004.Probability.ExponentialLaw
public import Martin2004.Probability.StationaryIncrements
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Tactic.Ring

/-!
# The mean and the second moment of the stationary passage time

Under i.i.d. `Exp(1)` weights and `0 < ρ < 1`, the telescoping identity
`stationaryPassage_eq_column_add_row` writes `G(m, n)` as a sum of `1 + n + m` terms: the corner
weight, the `n` weights above it divided by `ρ`, and the `m` horizontal increments of row `n`.
The three groups have laws `Exp(1)`, `Exp(ρ)` and `Exp(1 - ρ)` (the last by
`map_stationaryHorizontalIncrements`). Only the law of each single term is used, never the
independence of different terms.

* The mean is the sum of the means `1`, `1 / ρ` and `1 / (1 - ρ)`.
* The second moment is bounded by `(1 + n + m)` times the sum of the second moments `2`,
  `2 / ρ ^ 2` and `2 / (1 - ρ) ^ 2`, using that the square of a sum of `K` numbers is at most
  `K` times the sum of their squares.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace LPPDifferentiability

/-! ## Moments of a variable with an exponential law -/

/-- A real random variable whose law is `Exp(r)` is integrable with mean `1 / r`, and its square
is integrable with mean `2 / r ^ 2`. -/
private theorem moments_of_map_eq {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {X : Ω → ℝ}
    (hX : AEMeasurable X μ) {r : ℝ} (hr : 0 < r) (h : μ.map X = expMeasure r) :
    Integrable X μ ∧ ∫ ω, X ω ∂μ = 1 / r ∧
      Integrable (fun ω => X ω ^ 2) μ ∧ ∫ ω, X ω ^ 2 ∂μ = 2 / r ^ 2 := by
  obtain ⟨h1, h1'⟩ := integrable_and_integral_id_expMeasure hr
  obtain ⟨h2, h2'⟩ := integrable_and_integral_sq_expMeasure hr
  rw [← h] at h1 h2 h1' h2'
  exact ⟨(integrable_map_measure h1.aestronglyMeasurable hX).1 h1,
    (integral_map hX h1.aestronglyMeasurable).symm.trans h1',
    (integrable_map_measure h2.aestronglyMeasurable hX).1 h2,
    (integral_map hX h2.aestronglyMeasurable).symm.trans h2'⟩

/-! ## The laws of the three kinds of terms -/

/-- The corner weight has law `Exp(1)`. -/
private theorem law_corner :
    (environmentLaw (expMeasure 1)).map (fun ω : Environment => ω 0) = expMeasure 1 :=
  environmentLaw_map_eval (expMeasure 1) 0

/-- A weight on the left column, divided by `ρ`, has law `Exp(ρ)`. -/
private theorem law_column {ρ : ℝ} (hρ : 0 < ρ) (j : ℕ) :
    (environmentLaw (expMeasure 1)).map
        (fun ω : Environment => ω (0, (j : ℤ) + 1) / ρ) = expMeasure ρ := by
  have hcomp : (fun ω : Environment => ω (0, (j : ℤ) + 1) / ρ) =
      (fun t : ℝ => t / ρ) ∘ (fun ω : Environment => ω (0, (j : ℤ) + 1)) := rfl
  rw [hcomp, ← Measure.map_map (by fun_prop : Measurable fun t : ℝ => t / ρ)
    (measurable_environment_eval (0, (j : ℤ) + 1)), environmentLaw_map_eval,
    expMeasure_one_map_div hρ]

/-- A single horizontal increment of row `n` has law `Exp(1 - ρ)`: it is one coordinate of the
vector of increments, whose law is the product of `Exp(1 - ρ)` laws. -/
private theorem law_row {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (n m : ℕ) (i : Fin m) :
    (environmentLaw (expMeasure 1)).map
        (fun ω : Environment => stationaryHorizontalIncrement ρ ω i n) =
      expMeasure (1 - ρ) := by
  have hprob : IsProbabilityMeasure (expMeasure (1 - ρ)) :=
    isProbabilityMeasure_expMeasure (by linarith)
  have hv : Measurable (fun ω : Environment => fun k : Fin m =>
      stationaryHorizontalIncrement ρ ω k n) :=
    measurable_pi_iff.2 fun k => measurable_stationaryHorizontalIncrement ρ k n
  have hcomp : (fun ω : Environment => stationaryHorizontalIncrement ρ ω i n) =
      Function.eval i ∘ (fun ω : Environment => fun k : Fin m =>
        stationaryHorizontalIncrement ρ ω k n) := rfl
  rw [hcomp, ← Measure.map_map (measurable_pi_apply i) hv,
    map_stationaryHorizontalIncrements hρ0 hρ1 n m, Measure.pi_map_eval]
  simp

/-! ## The terms of the telescoping sum -/

/-- The terms of the telescoping sum for `G(m, n)`, indexed by the corner (a one-point type),
the `n` column sites and the `m` row increments. -/
private noncomputable def term (ρ : ℝ) (n m : ℕ) :
    Unit ⊕ (Fin n ⊕ Fin m) → Environment → ℝ
  | Sum.inl _ => fun ω => ω 0
  | Sum.inr (Sum.inl j) => fun ω => ω (0, (j.val : ℤ) + 1) / ρ
  | Sum.inr (Sum.inr i) => fun ω => stationaryHorizontalIncrement ρ ω i n

/-- The rate of the exponential law of each term. -/
private def termRate (ρ : ℝ) (n m : ℕ) : Unit ⊕ (Fin n ⊕ Fin m) → ℝ
  | Sum.inl _ => 1
  | Sum.inr (Sum.inl _) => ρ
  | Sum.inr (Sum.inr _) => 1 - ρ

/-- The telescoping identity written as a sum over the index type of the terms. -/
private theorem stationaryPassage_eq_sum_term (ρ : ℝ) (ω : Environment) (m n : ℕ) :
    stationaryPassage ρ ω m n = ∑ t, term ρ n m t ω := by
  rw [stationaryPassage_eq_column_add_row]
  simp [Fintype.sum_sum_type, term, add_assoc]

/-- Each term has an exponential law, hence a first and a second moment. -/
private theorem term_moments {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (n m : ℕ)
    (t : Unit ⊕ (Fin n ⊕ Fin m)) :
    Integrable (term ρ n m t) (environmentLaw (expMeasure 1)) ∧
      ∫ ω, term ρ n m t ω ∂environmentLaw (expMeasure 1) = 1 / termRate ρ n m t ∧
      Integrable (fun ω => term ρ n m t ω ^ 2) (environmentLaw (expMeasure 1)) ∧
      ∫ ω, term ρ n m t ω ^ 2 ∂environmentLaw (expMeasure 1) = 2 / termRate ρ n m t ^ 2 := by
  rcases t with _ | j | i
  · exact moments_of_map_eq (measurable_environment_eval 0).aemeasurable one_pos law_corner
  · exact moments_of_map_eq
      ((measurable_environment_eval (0, (j.val : ℤ) + 1)).div_const ρ).aemeasurable hρ0
      (law_column hρ0 j.val)
  · exact moments_of_map_eq (measurable_stationaryHorizontalIncrement ρ i n).aemeasurable
      (show (0 : ℝ) < 1 - ρ by linarith) (law_row hρ0 hρ1 n m i)

/-! ## The square of a finite sum -/

/-- If finitely many functions and their squares are integrable, the square of their sum is
integrable and its integral is at most the number of functions times the sum of the integrals of
the squares (the square of a sum of `K` numbers is at most `K` times the sum of squares). -/
private theorem sq_sum_integral_le {Ω ι : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [Fintype ι] (f : ι → Ω → ℝ) (hf : ∀ i, Integrable (f i) μ)
    (hf2 : ∀ i, Integrable (fun ω => f i ω ^ 2) μ) :
    Integrable (fun ω => (∑ i, f i ω) ^ 2) μ ∧
      ∫ ω, (∑ i, f i ω) ^ 2 ∂μ ≤
        (Fintype.card ι : ℝ) * ∑ i, ∫ ω, f i ω ^ 2 ∂μ := by
  have hsum2 : Integrable (fun ω => ∑ i, f i ω ^ 2) μ :=
    integrable_finsetSum _ fun i _ => hf2 i
  have hbound : ∀ ω, (∑ i, f i ω) ^ 2 ≤ (Fintype.card ι : ℝ) * ∑ i, f i ω ^ 2 := fun ω => by
    simpa using sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun i => f i ω)
  have hint : Integrable (fun ω => (Fintype.card ι : ℝ) * ∑ i, f i ω ^ 2) μ :=
    hsum2.const_mul _
  have hsm : AEStronglyMeasurable (fun ω => ∑ i, f i ω) μ :=
    (integrable_finsetSum _ fun i _ => hf i).aestronglyMeasurable
  have hsq : Integrable (fun ω => (∑ i, f i ω) ^ 2) μ :=
    hint.mono' (hsm.pow 2) (Filter.Eventually.of_forall fun ω => by
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      exact hbound ω)
  refine ⟨hsq, ?_⟩
  calc ∫ ω, (∑ i, f i ω) ^ 2 ∂μ
      ≤ ∫ ω, (Fintype.card ι : ℝ) * ∑ i, f i ω ^ 2 ∂μ := integral_mono hsq hint hbound
    _ = (Fintype.card ι : ℝ) * ∑ i, ∫ ω, f i ω ^ 2 ∂μ := by
      rw [integral_const_mul, integral_finsetSum _ fun i _ => hf2 i]

/-! ## The two statements -/

/-- **Mean.** Under i.i.d. `Exp(1)` weights and `0 < ρ < 1`, the stationary passage time
`G(m, n)` is integrable with mean `1 + m / (1 - ρ) + n / ρ`; the `1` is the corner weight, the
`n / ρ` the left column and the `m / (1 - ρ)` the row increments. -/
theorem integrable_and_integral_stationaryPassage {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (m n : ℕ) :
    Integrable (fun ω => stationaryPassage ρ ω m n) (environmentLaw (expMeasure 1)) ∧
    ∫ ω, stationaryPassage ρ ω m n ∂environmentLaw (expMeasure 1) =
      1 + (m : ℝ) / (1 - ρ) + (n : ℝ) / ρ := by
  have hfun : (fun ω => stationaryPassage ρ ω m n) = fun ω => ∑ t, term ρ n m t ω :=
    funext fun ω => stationaryPassage_eq_sum_term ρ ω m n
  rw [hfun]
  refine ⟨integrable_finsetSum _ fun t _ => (term_moments hρ0 hρ1 n m t).1, ?_⟩
  rw [integral_finsetSum _ fun t _ => (term_moments hρ0 hρ1 n m t).1]
  simp only [fun t => (term_moments hρ0 hρ1 n m t).2.1]
  simp [Fintype.sum_sum_type, termRate]
  ring

/-- **Second moment.** Under i.i.d. `Exp(1)` weights and `0 < ρ < 1`, the square of the
stationary passage time `G(m, n)` is integrable and its integral is at most
`(1 + m + n) * (2 + 2 n / ρ ^ 2 + 2 m / (1 - ρ) ^ 2)`: `G(m, n)` is a sum of `1 + m + n`
terms and the square of such a sum is at most `1 + m + n` times the sum of the squares. -/
theorem integrable_and_integral_sq_stationaryPassage_le {ρ : ℝ} (hρ0 : 0 < ρ)
    (hρ1 : ρ < 1) (m n : ℕ) :
    Integrable (fun ω => stationaryPassage ρ ω m n ^ 2) (environmentLaw (expMeasure 1)) ∧
    ∫ ω, stationaryPassage ρ ω m n ^ 2 ∂environmentLaw (expMeasure 1) ≤
      (1 + m + n : ℝ) * (2 + 2 * n / ρ ^ 2 + 2 * m / (1 - ρ) ^ 2) := by
  have hfun : (fun ω => stationaryPassage ρ ω m n ^ 2) =
      fun ω => (∑ t, term ρ n m t ω) ^ 2 :=
    funext fun ω => by rw [stationaryPassage_eq_sum_term ρ ω m n]
  rw [hfun]
  obtain ⟨hint, hle⟩ := sq_sum_integral_le (μ := environmentLaw (expMeasure 1)) (term ρ n m)
    (fun t => (term_moments hρ0 hρ1 n m t).1) fun t => (term_moments hρ0 hρ1 n m t).2.2.1
  refine ⟨hint, hle.trans (le_of_eq ?_)⟩
  simp only [fun t => (term_moments hρ0 hρ1 n m t).2.2.2]
  simp [Fintype.sum_sum_type, Fintype.card_sum, termRate]
  ring

end LPPDifferentiability
