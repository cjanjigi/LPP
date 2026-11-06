/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import LPP_Foundations.Frozen.Model.EnvironmentLaw
public import LPP_Foundations.Frozen.Model.LastPassage
public import LPP_Foundations.Frozen.Model.Quadrant
public import Martin2004.Probability.ColumnLaws
public import Martin2004.Probability.ColumnPassageBound
public import Martin2004.Probability.ShearComparison
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.SpecificLimits.Basic

@[expose] public section

/-!
# The Bernoulli upper bound for the limit shape (Lemma 4.1 of Martin (2004))

Martin (2004), Lemma 4.1 bounds the limit shape of Bernoulli weights at the point
`(1, α)`. His proof compares `E T(n, ⌊αn⌋)` with `E T̃(n + ⌊αn⌋, ⌊αn⌋)` by a shear, and then
quotes a known limit for `E T̃`.

Here the quoted limit is replaced by the finite-size bound of `Probability/ColumnPassageBound.lean`,
which holds at every size. The results of this module are:

* `integral_lastPassage_le_of_zero_one`: for a weight law carried by `{0, 1}` with `P(1) = p`,
  `E T(n, k) ≤ (n + k) p + 2 √((n + k)(k + 1) p (1 - p))`, at every `n` and `k`.
* `integral_lastPassage_le_bernoulli`: the same bound for Mathlib's `bernoulliMeasure 1 0 p`.
* `martin_lemma_4_1`: Lemma 4.1 itself. If `g` is the limit of the expected floor rates, then
  `g(1, α) ≤ (1 + α) p + 2 √α √(1 + α) √(p (1 - p))`.
-/

open MeasureTheory ProbabilityTheory Filter unitInterval
open scoped NNReal Topology

namespace LPPDifferentiability

/-! ## The finite-size bound -/

/-- Martin (2004), proof of Lemma 4.1, at finite size. If the weight law is carried by `{0, 1}`
and gives
`1` the probability `p`, then for all `n` and `k`,
`E T(n, k) ≤ (n + k) p + 2 √((n + k)(k + 1) p (1 - p))`. The shear comparison bounds `E T(n, k)` by
`E T̃(n + k, k)`, and the column passage bound controls the latter. -/
theorem integral_lastPassage_le_of_zero_one (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (h01 : ∀ᵐ t ∂μ, t = 0 ∨ t = 1) (p : ℝ) (hp : μ.real {1} = p) (n k : ℕ) :
    ∫ ω, lastPassage ω 0 (n, k) ∂environmentLaw μ ≤
      ((n + k : ℕ) : ℝ) * p + 2 * Real.sqrt (((n + k : ℕ) : ℝ) * ((k : ℝ) + 1) * (p * (1 - p))) := by
  -- a law carried by `{0, 1}` is a Bernoulli law, hence has a finite mean
  have hint : Integrable (fun t : ℝ => t) μ := by
    obtain ⟨_, hμ⟩ := exists_eq_bernoulliMeasure_of_ae_zero_or_one μ h01 p hp
    rw [hμ]
    exact integrable_bernoulliMeasure (1 : ℝ) 0 _ (fun t : ℝ => t)
  -- shear comparison, then the column passage bound with `m = n + k`
  exact (integral_lastPassage_le_integral_columnPassage μ hint n k).trans
    (integral_columnPassage_le μ h01 p hp (n + k) k)

/-- Mathlib's Bernoulli law with mass `p` on `1` and `1 - p` on `0` is carried by `{0, 1}`. -/
private theorem ae_bernoulliMeasure_zero_or_one (p : unitInterval) :
    ∀ᵐ t ∂bernoulliMeasure (1 : ℝ) 0 p, t = 0 ∨ t = 1 := by
  have hpair : MeasurableSet (({1, 0} : Set ℝ)ᶜ) := (Set.toFinite _).measurableSet.compl
  have hnull : bernoulliMeasure (1 : ℝ) 0 p (({1, 0} : Set ℝ)ᶜ) = 0 :=
    bernoulliMeasure_apply_of_notMem_of_notMem p hpair (by simp) (by simp)
  rw [ae_iff]
  convert hnull using 2
  ext t
  simp [or_comm]

/-- The finite-size bound for `bernoulliMeasure 1 0 p`, `p : unitInterval` (Martin (2004), proof
of Lemma 4.1, at finite size): `E T(n, k) ≤ (n + k) p + 2 √((n + k)(k + 1) p (1 - p))`. -/
theorem integral_lastPassage_le_bernoulli (p : unitInterval) (n k : ℕ) :
    ∫ ω, lastPassage ω 0 (n, k) ∂environmentLaw (bernoulliMeasure (1 : ℝ) 0 p) ≤
      ((n + k : ℕ) : ℝ) * p + 2 * Real.sqrt (((n + k : ℕ) : ℝ) * ((k : ℝ) + 1) * (p * (1 - p))) :=
  integral_lastPassage_le_of_zero_one (bernoulliMeasure (1 : ℝ) 0 p)
    (ae_bernoulliMeasure_zero_or_one p) p
    (bernoulliMeasure_real_apply_of_mem_of_notMem p (measurableSet_singleton _)
      (Set.mem_singleton _) (by simp)) n k

/-! ## Lemma 4.1 -/

/-- **Martin (2004), Lemma 4.1**. For Bernoulli
`p` weights (values `0` and `1`, `P(X = 1) = p`) and any `α > 0`, the shape satisfies
`g(1, α) ≤ (1 + α) p + 2 √α √(1 + α) √(p (1 - p))`. The shape `g` is the limit of the expected
floor rates, as in `hg`. -/
theorem martin_lemma_4_1
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (h01 : ∀ᵐ t ∂μ, t = 0 ∨ t = 1) (p : ℝ) (hp : μ.real {1} = p)
    (g : Quadrant → ℝ)
    (hg : ∀ x : Quadrant, Tendsto (fun n : ℕ =>
        (∫ ω : Environment, lastPassage ω 0
          (⌊(n : ℝ) * (x.1 : ℝ)⌋₊, ⌊(n : ℝ) * (x.2 : ℝ)⌋₊)
          ∂environmentLaw μ) / (n : ℝ)) atTop (𝓝 (g x)))
    (α : ℝ≥0) (hα : 0 < α) :
    g (1, α) ≤ (1 + (α : ℝ)) * p +
      2 * Real.sqrt (α : ℝ) * Real.sqrt (1 + (α : ℝ)) * Real.sqrt (p * (1 - p)) := by
  have ha : 0 ≤ (α : ℝ) := (NNReal.coe_pos.2 hα).le
  -- the floor rate at the point `(1, α)`: `⌊n * 1⌋ = n`
  have hlim : Tendsto (fun n : ℕ =>
      (∫ ω : Environment, lastPassage ω 0 (n, ⌊(n : ℝ) * (α : ℝ)⌋₊) ∂environmentLaw μ) / (n : ℝ))
      atTop (𝓝 (g (1, α))) :=
    (hg (1, α)).congr fun n => by simp
  -- the finite-size bound divided by `n`, with `k = ⌊n α⌋`
  have hrate : ∀ n : ℕ, 1 ≤ n →
      (∫ ω : Environment, lastPassage ω 0 (n, ⌊(n : ℝ) * (α : ℝ)⌋₊) ∂environmentLaw μ) / (n : ℝ) ≤
        (1 + (⌊(n : ℝ) * (α : ℝ)⌋₊ : ℝ) / n) * p +
          2 * Real.sqrt ((1 + (⌊(n : ℝ) * (α : ℝ)⌋₊ : ℝ) / n) *
            ((⌊(n : ℝ) * (α : ℝ)⌋₊ : ℝ) / n + 1 / n) * (p * (1 - p))) := by
    intro n hn
    have hn0 : (0 : ℝ) < n := Nat.cast_pos.2 hn
    set k : ℕ := ⌊(n : ℝ) * (α : ℝ)⌋₊ with hk
    have hfinite := integral_lastPassage_le_of_zero_one μ h01 p hp n k
    -- the square root scales by `n`
    have hinside : ((n + k : ℕ) : ℝ) * ((k : ℝ) + 1) * (p * (1 - p)) =
        (n : ℝ) ^ 2 * ((1 + (k : ℝ) / n) * ((k : ℝ) / n + 1 / n) * (p * (1 - p))) := by
      push_cast
      field_simp
    have hsqrt : Real.sqrt (((n + k : ℕ) : ℝ) * ((k : ℝ) + 1) * (p * (1 - p))) =
        (n : ℝ) * Real.sqrt ((1 + (k : ℝ) / n) * ((k : ℝ) / n + 1 / n) * (p * (1 - p))) := by
      rw [hinside, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hn0.le]
    have hmain : ((n + k : ℕ) : ℝ) * p = (1 + (k : ℝ) / n) * p * n := by
      push_cast
      field_simp
    rw [div_le_iff₀ hn0]
    calc _ ≤ _ := hfinite
      _ = _ := by rw [hsqrt, hmain]; ring
  -- the proportions `k / n → α` and `1 / n → 0`
  have hprop : Tendsto (fun n : ℕ => (⌊(n : ℝ) * (α : ℝ)⌋₊ : ℝ) / n) atTop (𝓝 (α : ℝ)) :=
    ((tendsto_nat_floor_mul_div_atTop ha).comp tendsto_natCast_atTop_atTop).congr fun n => by
      simp [mul_comm]
  have hone : Tendsto (fun n : ℕ => 1 / (n : ℝ)) atTop (𝓝 0) := tendsto_one_div_atTop_nhds_zero_nat
  -- the limit of the right side
  have h1 := hprop.const_add 1
  have h2 := hprop.add hone
  have hbound := (h1.mul_const p).add (((h1.mul h2).mul_const (p * (1 - p))).sqrt.const_mul 2)
  have hle := le_of_tendsto_of_tendsto hlim hbound
    (eventually_atTop.2 ⟨1, fun n hn => hrate n hn⟩)
  -- the end of the proof of Martin (2004), Lemma 4.1: `√((1 + α) α q) = √α √(1 + α) √q`
  have hsqrt : Real.sqrt ((1 + (α : ℝ)) * ((α : ℝ) + 0) * (p * (1 - p))) =
      Real.sqrt (α : ℝ) * Real.sqrt (1 + (α : ℝ)) * Real.sqrt (p * (1 - p)) := by
    rw [add_zero, mul_comm (1 + (α : ℝ)) (α : ℝ),
      Real.sqrt_mul (mul_nonneg ha (by linarith) : 0 ≤ (α : ℝ) * (1 + (α : ℝ))),
      Real.sqrt_mul ha (1 + (α : ℝ))]
  rw [hsqrt] at hle
  linarith

end LPPDifferentiability
