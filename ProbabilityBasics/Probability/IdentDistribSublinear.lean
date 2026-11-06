/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import ProbabilityBasics.Probability.IntegrableTails
public import Mathlib.Probability.IdentDistrib
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Sublinear sequences with identical marginal laws

Integrable real variables with the same law are almost surely sublinear.
The proof uses summable integrable tails and the first Borel–Cantelli lemma.
No independence, joint stationarity, or common transformation is required.
-/

public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal Topology

namespace LPPDifferentiability

/-- A sequence with the law of one integrable real variable is almost surely
sublinear. Almost-everywhere measurability is supplied by `IdentDistrib`. -/
theorem ae_tendsto_identDistrib_div_nat {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X : ℕ → Ω → ℝ} {g : Ω → ℝ}
    (hg : Integrable g μ) (hX : ∀ n, IdentDistrib (X n) g μ μ) :
    ∀ᵐ ω ∂μ, Tendsto (fun n : ℕ => X n ω / (n : ℝ)) atTop (𝓝 0) := by
  have hε (ε : ℝ) (hε : 0 < ε) :
      ∀ᵐ ω ∂μ, ∀ᶠ n : ℕ in atTop, ‖X n ω‖ ≤ ε * (n : ℝ) := by
    have hgε : Integrable (fun ω => ‖g ω‖ / ε) μ := hg.norm.div_const ε
    have htail := integrable_nat_tails hgε (fun ω => div_nonneg (norm_nonneg _) hε.le)
    have heq (n : ℕ) : μ {ω | ε * (n : ℝ) < ‖X n ω‖} =
        μ {ω | (n : ℝ) < ‖g ω‖ / ε} := by
      calc
        _ = μ {ω | ε * (n : ℝ) < ‖g ω‖} :=
          (hX n).norm.measure_mem_eq measurableSet_Ioi
        _ = _ := by
          congr 1
          ext ω
          simp only [mem_ofPred_eq, lt_div_iff₀ hε, mul_comm ε]
    have hsum : (∑' n : ℕ, μ {ω | ε * (n : ℝ) < ‖X n ω‖}) ≠ ∞ := by
      simpa only [heq] using htail
    filter_upwards [ae_eventually_notMem hsum] with ω hω
    exact hω.mono fun n hn => le_of_not_gt hn
  have hall : ∀ᵐ ω ∂μ, ∀ k : ℕ, ∀ᶠ n : ℕ in atTop,
      ‖X n ω‖ ≤ (1 / ((k : ℝ) + 1)) * (n : ℝ) := by
    exact ae_all_iff.mpr fun k => hε _ (by positivity)
  filter_upwards [hall] with ω hω
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨k, hk⟩ := exists_nat_one_div_lt hε
  filter_upwards [hω k, eventually_gt_atTop (0 : ℕ)] with n hn hnpos
  have hnreal : (0 : ℝ) < n := Nat.cast_pos.mpr hnpos
  rw [dist_zero_right, norm_div, Real.norm_natCast]
  exact lt_of_le_of_lt ((div_le_iff₀ hnreal).mpr hn) hk

end LPPDifferentiability
