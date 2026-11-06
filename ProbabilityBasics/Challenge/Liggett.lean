/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Mathlib.Dynamics.Ergodic.Ergodic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Probability.IdentDistrib

/-!
# Challenge: Liggett's subadditive ergodic theorem

This file states Liggett (1985), Theorem 1.10, using only Mathlib. It contains the statement, with
its proof left open, and exactly the definitions the statement uses. The solution file proves the
same statement from the library.

## Main results

- `subadditive_ergodic_theorem`: Liggett (1985), Theorem 1.10.

## References

- T. M. Liggett, "An improved subadditive ergodic theorem", Ann. Probab. 13 (1985), 1279-1285.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology

namespace LPPAudit.Liggett

/-- The left shift on sequences: `(seqShift x) n = x (n + 1)`. -/
def seqShift {β : Type*} (x : ℕ → β) : ℕ → β := fun n => x (n + 1)

/-- A process `Y 0, Y 1, Y 2, ...` is stationary when the shifted process `Y 1, Y 2, Y 3, ...` has
the same joint law. -/
def IsStationaryProcess {Ω β : Type*} [MeasurableSpace Ω] [MeasurableSpace β] (μ : Measure Ω)
    (Y : ℕ → Ω → β) : Prop :=
  IdentDistrib (fun ω n => Y (n + 1) ω) (fun ω n => Y n ω) μ μ

/-- A process is ergodic when the left shift is ergodic for its joint law. -/
def IsErgodicProcess {Ω β : Type*} [MeasurableSpace Ω] [MeasurableSpace β] (μ : Measure Ω)
    (Y : ℕ → Ω → β) : Prop :=
  Ergodic (seqShift (β := β)) (μ.map fun ω n => Y n ω)

/-- The block process of (1.9) for block length `k`: `{X_{nk,(n+1)k}, n ≥ 1}`, with process
index `j` standing for `n = j + 1`. -/
def liggettBlockProcess {Ω : Type*} (X : ℕ → ℕ → Ω → ℝ) (k : ℕ) : ℕ → Ω → ℝ :=
  fun j ω => X ((j + 1) * k) ((j + 2) * k) ω

/-- Liggett (1.7): `X_{0,n} ≤ X_{0,m} + X_{m,n}` whenever `0 < m < n`, almost surely. -/
def LiggettSubadditive {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (X : ℕ → ℕ → Ω → ℝ) : Prop :=
  ∀ m n : ℕ, 0 < m → m < n → ∀ᵐ ω ∂μ, X 0 n ω ≤ X 0 m ω + X m n ω

/-- Liggett (1.8): for each `m ≥ 0`, `{X_{m+1,m+k+1}, k ≥ 1}` has the same joint distributions as
`{X_{m,m+k}, k ≥ 1}`. Sequence index `j` stands for `k = j + 1`. -/
def LiggettRowLaws {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (X : ℕ → ℕ → Ω → ℝ) : Prop :=
  ∀ m : ℕ, IdentDistrib (fun ω (j : ℕ) => X (m + 1) (m + 1 + (j + 1)) ω)
    (fun ω (j : ℕ) => X m (m + (j + 1)) ω) μ μ

/-- Liggett (1.9): for each `k ≥ 1` the block process `{X_{nk,(n+1)k}, n ≥ 1}` is stationary. -/
def LiggettBlockStationary {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (X : ℕ → ℕ → Ω → ℝ) : Prop :=
  ∀ k : ℕ, 0 < k → IsStationaryProcess μ (liggettBlockProcess X k)

/-- Liggett (1.3): for each `n ≥ 1`, `E |X_{0,n}| < ∞`, and one constant `c` has
`E X_{0,n} ≥ -c n` for all `n ≥ 1`. -/
def LiggettMomentCondition {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (X : ℕ → ℕ → Ω → ℝ) : Prop :=
  (∀ n : ℕ, 0 < n → Integrable (X 0 n) μ) ∧
    ∃ c : ℝ, ∀ n : ℕ, 0 < n → -(c * n) ≤ ∫ ω, X 0 n ω ∂μ

/-- The four hypotheses (1.7), (1.8), (1.9) and (1.3) of Liggett (1985), Theorem 1.10, for a doubly
indexed family `X m n` of random variables under the measure `μ`. -/
structure LiggettHypotheses {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (X : ℕ → ℕ → Ω → ℝ) : Prop where
  /-- Hypothesis (1.7). -/
  subadditive : LiggettSubadditive μ X
  /-- Hypothesis (1.8). -/
  row_laws : LiggettRowLaws μ X
  /-- Hypothesis (1.9). -/
  block_stationary : LiggettBlockStationary μ X
  /-- Hypothesis (1.3). -/
  moment_condition : LiggettMomentCondition μ X

/-- The mean rate `(1/n) E X_{0,n}`, whose limit and infimum appear in Liggett (1985), (1.4). -/
noncomputable def meanRate {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (X : ℕ → ℕ → Ω → ℝ)
    (n : ℕ) : ℝ :=
  (∫ ω, X 0 n ω ∂μ) / n

/-- Conclusion (1.5), almost surely: `X_{0,n}/n` converges to `Xlim ω` for almost every `ω`. -/
def ConvergesAlmostSurely {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (X : ℕ → ℕ → Ω → ℝ)
    (Xlim : Ω → ℝ) : Prop :=
  ∀ᵐ ω ∂μ, Tendsto (fun n : ℕ => X 0 n ω / n) atTop (𝓝 (Xlim ω))

/-- Conclusion (1.5), in `L¹`: `E |X_{0,n}/n - Xlim|` tends to `0`. -/
def ConvergesInL1 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (X : ℕ → ℕ → Ω → ℝ)
    (Xlim : Ω → ℝ) : Prop :=
  Tendsto (fun n : ℕ => ∫ ω, |X 0 n ω / n - Xlim ω| ∂μ) atTop (𝓝 0)

/-- The ergodicity assumption of the last sentence of the theorem: the block processes of (1.9) are
ergodic for every `k ≥ 1`. -/
def BlocksAreErgodic {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (X : ℕ → ℕ → Ω → ℝ) : Prop :=
  ∀ k : ℕ, 0 < k → IsErgodicProcess μ (liggettBlockProcess X k)

/-- Liggett (1985), Theorem 1.10.

Suppose the family `X m n` of random variables on a probability space satisfies the four hypotheses
(1.7), (1.8), (1.9) and (1.3), bundled as `LiggettHypotheses μ X`. Then the mean rate
`(1/n) E X_{0,n}` converges, and its limit `γ` is also its infimum over `n ≥ 1` (1.4). The sequence
`X_{0,n}/n` converges to a random variable `Xlim`, both almost surely and in `L¹` (1.5), and `Xlim`
has mean `γ` (1.6). If in addition the block processes of (1.9) are ergodic, then `Xlim` equals `γ`
almost surely. -/
theorem subadditive_ergodic_theorem {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (X : ℕ → ℕ → Ω → ℝ) (h : LiggettHypotheses μ X) :
    ∃ γ : ℝ,
      -- (1.4)
      Tendsto (meanRate μ X) atTop (𝓝 γ) ∧ IsGLB (meanRate μ X '' Ioi 0) γ ∧
      ∃ Xlim : Ω → ℝ, Measurable Xlim ∧ Integrable Xlim μ ∧
        -- (1.5)
        ConvergesAlmostSurely μ X Xlim ∧ ConvergesInL1 μ X Xlim ∧
        -- (1.6)
        ∫ ω, Xlim ω ∂μ = γ ∧
        -- final clause
        (BlocksAreErgodic μ X → ∀ᵐ ω ∂μ, Xlim ω = γ) := by
  sorry

end LPPAudit.Liggett
