/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Mathlib.Dynamics.Ergodic.MeasurePreserving
public import ProbabilityBasics.Probability.IntegrableTails
public import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Sublinear boundary terms

An integrable observable along a measure-preserving orbit, divided by time,
converges almost surely to zero. The proof uses summable integrable tails,
measure preservation and the first Borel–Cantelli lemma. Independence and
ergodicity are not required.
-/

public section

open MeasureTheory Filter Set
open scoped ENNReal Topology

namespace LPPDifferentiability

/-- An integrable observable is sublinear along a measure-preserving orbit,
almost surely. No independence or ergodicity assumption is needed. -/
theorem ae_tendsto_iterate_div_nat {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {T : Ω → Ω} {f : Ω → ℝ}
    (hT : MeasurePreserving T μ μ) (hf : Integrable f μ) :
    ∀ᵐ ω ∂μ, Tendsto (fun n : ℕ => f ((T^[n]) ω) / (n : ℝ)) atTop (𝓝 0) := by
  have hε (ε : ℝ) (hε : 0 < ε) :
      ∀ᵐ ω ∂μ, ∀ᶠ n : ℕ in atTop, ‖f ((T^[n]) ω)‖ ≤ ε * (n : ℝ) := by
    have hg : Integrable (fun ω => ‖f ω‖ / ε) μ := hf.norm.div_const ε
    have htail := integrable_nat_tails hg (fun ω => div_nonneg (norm_nonneg _) hε.le)
    have heq (n : ℕ) : μ {ω | ε * (n : ℝ) < ‖f ((T^[n]) ω)‖} =
        μ {ω | (n : ℝ) < ‖f ω‖ / ε} := by
      have hs : NullMeasurableSet {ω | (n : ℝ) < ‖f ω‖ / ε} μ :=
        nullMeasurableSet_lt aemeasurable_const hg.aestronglyMeasurable.aemeasurable
      convert (hT.iterate n).measure_preimage hs using 2
      ext ω
      simp only [mem_ofPred_eq, mem_preimage, lt_div_iff₀ hε, mul_comm ε]
    have hsum : (∑' n : ℕ, μ {ω | ε * (n : ℝ) < ‖f ((T^[n]) ω)‖}) ≠ ∞ := by
      simpa only [heq] using htail
    filter_upwards [ae_eventually_notMem hsum] with ω hω
    exact hω.mono fun n hn => le_of_not_gt hn
  have hall : ∀ᵐ ω ∂μ, ∀ k : ℕ, ∀ᶠ n : ℕ in atTop,
      ‖f ((T^[n]) ω)‖ ≤ (1 / ((k : ℝ) + 1)) * (n : ℝ) := by
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
