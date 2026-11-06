/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import ProbabilityBasics.Statements.ProbabilityDefinitions
public import ProbabilityBasics.Frozen.Foundations.Liggett.Theorem110

/-!
# Liggett's subadditive ergodic theorem, in two versions

Theorem 1.10 of Liggett (1985): for a doubly indexed array of random variables that is subadditive
and has stationary block structure, the normalized sums converge almost surely and in `L¹`, with the
limit of the means equal to the infimum.

* Version A, `literal_subadditive_ergodic_theorem`: the statement
  `ProbabilityBasics.Liggett.liggett_subadditive_ergodic` of the `Frozen` folder, copied verbatim as
  a universally quantified proposition, with `literal_subadditive_ergodic_theorem_holds` proved from
  that theorem.
* Version B, `plain_subadditive_ergodic_theorem`: the same mathematics with the four hypotheses
  (1.7), (1.8), (1.9) and (1.3) bundled as `LiggettHypotheses μ X` and the clauses of the conclusion
  written with the named definitions of `ProbabilityDefinitions.lean`. The theorem
  `subadditive_ergodic_theorem` states it and is proved from version A;
  `plain_subadditive_ergodic_theorem_iff_literal` shows the versions are equivalent.

## References

* T. M. Liggett, An improved subadditive ergodic theorem, Ann. Probab. 13 (1985), Theorem 1.10.
-/

@[expose] public section

open MeasureTheory Filter Set ProbabilityBasics ProbabilityBasics.Liggett
open scoped Topology

namespace LPPStatements.Liggett

set_option linter.unusedVariables false in
/-- Version A of Liggett (1985), Theorem 1.10: the statement
`ProbabilityBasics.Liggett.liggett_subadditive_ergodic` of the `Frozen` folder, verbatim. -/
def literal_subadditive_ergodic_theorem.{u} : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → ℕ → Ω → ℝ) (h17 : LiggettSubadditive μ X) (h18 : LiggettRowLaws μ X)
    (h19 : LiggettBlockStationary μ X) (h13 : LiggettMomentCondition μ X),
    ∃ γ : ℝ,
      -- (1.4)
      Tendsto (fun n : ℕ => (∫ ω, X 0 n ω ∂μ) / n) atTop (𝓝 γ) ∧
      IsGLB ((fun n : ℕ => (∫ ω, X 0 n ω ∂μ) / n) '' Ioi 0) γ ∧
      ∃ Xlim : Ω → ℝ, Measurable Xlim ∧ Integrable Xlim μ ∧
        -- (1.5), almost surely
        (∀ᵐ ω ∂μ, Tendsto (fun n : ℕ => X 0 n ω / n) atTop (𝓝 (Xlim ω))) ∧
        -- (1.5), in L¹
        Tendsto (fun n : ℕ => ∫ ω, |X 0 n ω / n - Xlim ω| ∂μ) atTop (𝓝 0) ∧
        -- (1.6)
        ∫ ω, Xlim ω ∂μ = γ ∧
        -- final clause
        ((∀ k : ℕ, 0 < k → IsErgodicProcess μ (liggettBlockProcess X k)) →
          ∀ᵐ ω ∂μ, Xlim ω = γ)

/-- Version A holds: it is `ProbabilityBasics.Liggett.liggett_subadditive_ergodic`. -/
theorem literal_subadditive_ergodic_theorem_holds.{u} : literal_subadditive_ergodic_theorem.{u} := by
  unfold literal_subadditive_ergodic_theorem
  intros
  apply ProbabilityBasics.Liggett.liggett_subadditive_ergodic
  all_goals assumption

set_option linter.unusedVariables false in
/-- Version B of Liggett (1985), Theorem 1.10: under the four hypotheses `LiggettHypotheses μ X`,
there is a constant `γ` which is the limit and the infimum of `(1/n) E X_{0,n}` (1.4), and a random
variable `Xlim`, measurable and integrable, with `X_{0,n}/n → Xlim` almost surely and in `L¹` (1.5)
and `E Xlim = γ` (1.6); if the block processes are ergodic then `Xlim = γ` almost surely. -/
def plain_subadditive_ergodic_theorem.{u} : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → ℕ → Ω → ℝ), LiggettHypotheses μ X →
    ∃ γ : ℝ,
      -- (1.4)
      Tendsto (meanRate μ X) atTop (𝓝 γ) ∧ IsGLB (meanRate μ X '' Ioi 0) γ ∧
      ∃ Xlim : Ω → ℝ, Measurable Xlim ∧ Integrable Xlim μ ∧
        -- (1.5)
        ConvergesAlmostSurely μ X Xlim ∧ ConvergesInL1 μ X Xlim ∧
        -- (1.6)
        ∫ ω, Xlim ω ∂μ = γ ∧
        -- final clause
        (BlocksAreErgodic μ X → ∀ᵐ ω ∂μ, Xlim ω = γ)

/-- Version B is equivalent to version A. -/
theorem plain_subadditive_ergodic_theorem_iff_literal.{u} :
    plain_subadditive_ergodic_theorem.{u} ↔ literal_subadditive_ergodic_theorem.{u} := by
  unfold plain_subadditive_ergodic_theorem literal_subadditive_ergodic_theorem
  constructor
  · intro h Ω _ μ _ X h17 h18 h19 h13
    exact h μ X ⟨h17, h18, h19, h13⟩
  · intro h Ω _ μ _ X hX
    exact h μ X hX.subadditive hX.row_laws hX.block_stationary hX.moment_condition

/-- Liggett (1985), Theorem 1.10.

Suppose (1.7), (1.8), (1.9) and (1.3) (`LiggettHypotheses μ X`). Then there is `γ` with (1.4):
`γ = lim (1/n) E X_{0,n} = inf_{n ≥ 1} (1/n) E X_{0,n}`; the limit `X = lim X_{0,n}/n` exists almost
surely and in `L¹` (1.5), and `E X = γ` (1.6). If the stationary processes in (1.9) are ergodic,
then `X = γ` almost surely. -/
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
        (BlocksAreErgodic μ X → ∀ᵐ ω ∂μ, Xlim ω = γ) :=
  literal_subadditive_ergodic_theorem_holds μ X h.subadditive h.row_laws h.block_stationary
    h.moment_condition

end LPPStatements.Liggett

/-- Label: Liggett (1985), Theorem 1.10. -/
alias Liggett1985.theorem_1_10 := LPPStatements.Liggett.subadditive_ergodic_theorem
