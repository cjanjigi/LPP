-- FROZEN_ANCHOR_PREFIX_BEGIN
module

public import ProbabilityBasics.Full.Foundations.LiggettSubadditiveErgodic
public import ProbabilityBasics.Frozen.Foundations.Liggett.LiggettSubadditive
public import ProbabilityBasics.Frozen.Foundations.Liggett.LiggettRowLaws
public import ProbabilityBasics.Frozen.Foundations.Liggett.LiggettBlockStationary
public import ProbabilityBasics.Frozen.Foundations.Liggett.LiggettMomentCondition
public import ProbabilityBasics.Frozen.Foundations.Liggett.IsErgodicProcess
public import ProbabilityBasics.Frozen.Foundations.Liggett.LiggettBlockProcess
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Order.Bounds.Basic

@[expose] public section

open MeasureTheory Filter Set
open scoped Topology

namespace ProbabilityBasics.Liggett

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **Liggett (1985), Theorem 1.10.** Suppose (1.7), (1.8), (1.9) and (1.3).
Then (1.4): `γ = lim (1/n) E X_{0,n} = inf_{n ≥ 1} (1/n) E X_{0,n}`;
(1.5): `X = lim X_{0,n}/n` exists almost surely and in `L¹`;
(1.6): `E X = γ`. If the stationary processes in (1.9) are ergodic,
then `X = γ` almost surely. -/
theorem liggett_subadditive_ergodic (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → ℕ → Ω → ℝ)
    (h17 : LiggettSubadditive μ X) (h18 : LiggettRowLaws μ X)
    (h19 : LiggettBlockStationary μ X) (h13 : LiggettMomentCondition μ X) :
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
          ∀ᵐ ω ∂μ, Xlim ω = γ) :=
-- FROZEN_ANCHOR_PROOF_BEGIN
by exact ProbabilityBasics.Full.liggett_subadditive_ergodic μ X h17 h18 h19 h13
-- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end ProbabilityBasics.Liggett
-- FROZEN_ANCHOR_SUFFIX_END
