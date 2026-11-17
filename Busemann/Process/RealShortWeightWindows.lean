/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Busemann.Frozen.Definitions.ProcessEnvironment
public import Busemann.Frozen.Definitions.FiniteEdgeStep
public import LPP_Foundations.Frozen.Model.EnvironmentLaw
public import Busemann.Probability.RealShortWeightWindows
public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Finset.Prod
public import Mathlib.Data.Int.Interval
public import Mathlib.Order.LiminfLimsup
import Busemann.Process.ShellComparisonBounds
import LPP_Foundations.Probability.ShortSegments
import Mathlib.Data.EReal.Basic
import Mathlib.Tactic

/-! Real signed-window short-weight bounds for a process with the required environment marginal. -/

@[expose] public section

open LPPDifferentiability
open MeasureTheory Filter
open scoped BigOperators ENNReal Topology

namespace LPP.Busemann

/-- The environment bound transfers through the actual marginal and
gives an eventual real bound on every signed short-window maximum. This is the
real-window step preceding JR1810.03580v3, Appendix B, proof of B.3. -/
theorem ae_eventually_small_real_short_weight_windows
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hmoment : ∃ p : ℝ, 2 < p ∧
      (∫⁻ t, ENNReal.ofReal (|t| ^ p) ∂μ) < ∞)
    (P : Measure ProcessSample) [IsProbabilityMeasure P]
    (hMarginal : P.map processEnvironment = environmentLaw μ) :
    let C : ℕ → Finset Lattice := fun n => insert 0
      (((Finset.Icc (-(2 * (n : ℤ))) (2 * (n : ℤ))).product
        (Finset.Icc (-(2 * (n : ℤ))) (2 * (n : ℤ)))).filter
          (fun z => z.1.natAbs + z.2.natAbs ≤ 2 * n))
    ∀ᵐ s ∂P,
      let W : Fin 2 → ℝ → ℕ → ℝ := fun i δ n =>
        (C n).sup' (by dsimp [C]; exact Finset.insert_nonempty _ _)
          (fun z => (∑ k ∈ Finset.range (⌊(n : ℝ) * δ⌋₊ + 1),
            |(processEnvironment s) (z + (k : ℤ) • finiteEdgeStep i)|) / (n : ℝ))
      ∀ η : ℝ, 0 < η → ∃ δ0 : ℝ, 0 < δ0 ∧ δ0 ≤ 1 ∧
        ∀ δ : ℝ, 0 < δ → δ ≤ δ0 → ∀ i : Fin 2,
          ∀ᶠ n : ℕ in atTop, W i δ n < 2 * η := by
  have hWeights : Measurable processEnvironment := by
    change Measurable (fun s : ProcessSample => s.1)
    exact measurable_fst
  exact ae_eventually_small_real_short_weight_windows_of_weight_map
    μ hmoment P processEnvironment hWeights hMarginal

end LPP.Busemann
