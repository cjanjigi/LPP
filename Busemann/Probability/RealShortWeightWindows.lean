/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen.
Released under Apache 2.0 license as described in file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Busemann.Frozen.Definitions.FiniteEdgeStep
public import LPP_Foundations.Frozen.Model.EnvironmentLaw
public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Finset.Prod
public import Mathlib.Data.Int.Interval
import Busemann.Process.ShellComparisonBounds
import LPP_Foundations.Probability.ShortSegments
import Mathlib.Data.EReal.Basic
import Mathlib.Order.LiminfLimsup
import Mathlib.Tactic

/-! Real short-window bounds for arbitrary measurable maps into an iid environment. -/

@[expose] public section

open LPPDifferentiability
open MeasureTheory Filter
open scoped BigOperators ENNReal Topology

namespace LPP.Busemann

private theorem short_window_real_sup_coe_eq_ereal_iSup
    (ω : Environment) (i : Fin 2) (δ : ℝ) (n : ℕ) :
    let C : Finset Lattice := insert 0
      (((Finset.Icc (-(2 * (n : ℤ))) (2 * (n : ℤ))).product
        (Finset.Icc (-(2 * (n : ℤ))) (2 * (n : ℤ)))).filter
          (fun z => z.1.natAbs + z.2.natAbs ≤ 2 * n))
    ((C.sup' (by dsimp [C]; exact Finset.insert_nonempty _ _)
        (fun z => (∑ k ∈ Finset.range (⌊(n : ℝ) * δ⌋₊ + 1),
          |ω (z + (k : ℤ) • finiteEdgeStep i)|) / (n : ℝ)) : ℝ) : EReal) =
      ⨆ x : {x : Lattice // x.1.natAbs + x.2.natAbs ≤ 2 * n},
        (((∑ k ∈ Finset.range (⌊(n : ℝ) * δ⌋₊ + 1),
          |ω (x.1 + (k : ℤ) •
            (if i = 0 then ((1 : ℤ), (0 : ℤ)) else ((0 : ℤ), (1 : ℤ))))|) /
            (n : ℝ) : ℝ) : EReal) := by
  classical
  let C : Finset Lattice := insert 0
    (((Finset.Icc (-(2 * (n : ℤ))) (2 * (n : ℤ))).product
      (Finset.Icc (-(2 * (n : ℤ))) (2 * (n : ℤ)))).filter
        (fun z => z.1.natAbs + z.2.natAbs ≤ 2 * n))
  have hC : C.Nonempty := by
    dsimp [C]
    exact Finset.insert_nonempty _ _
  have hmem (z : Lattice) : z ∈ C ↔ z.1.natAbs + z.2.natAbs ≤ 2 * n := by
    dsimp [C]
    exact signed_ball_mem n z
  have hstep : finiteEdgeStep i =
      (if i = 0 then ((1 : ℤ), (0 : ℤ)) else ((0 : ℤ), (1 : ℤ))) := by
    fin_cases i <;> simp [finiteEdgeStep]
  let f (z : Lattice) : ℝ :=
    (∑ k ∈ Finset.range (⌊(n : ℝ) * δ⌋₊ + 1),
      |ω (z + (k : ℤ) • finiteEdgeStep i)|) / (n : ℝ)
  let g (x : {x : Lattice // x.1.natAbs + x.2.natAbs ≤ 2 * n}) : EReal :=
    (((∑ k ∈ Finset.range (⌊(n : ℝ) * δ⌋₊ + 1),
      |ω (x.1 + (k : ℤ) •
        (if i = 0 then ((1 : ℤ), (0 : ℤ)) else ((0 : ℤ), (1 : ℤ))))|) /
        (n : ℝ) : ℝ) : EReal)
  change ((C.sup' hC f : ℝ) : EReal) = ⨆ x, g x
  apply le_antisymm
  · obtain ⟨z, hz, hmax⟩ := Finset.exists_mem_eq_sup' (s := C) (H := hC) f
    rw [hmax]
    apply le_iSup_of_le ⟨z, (hmem z).1 hz⟩
    have hvalue : (f z : EReal) = g ⟨z, (hmem z).1 hz⟩ := by
      dsimp only [f, g]
      rw [hstep]
    rw [hvalue]
  · apply iSup_le
    rintro ⟨z, hz⟩
    have hzC : z ∈ C := (hmem z).2 hz
    have hvalue : g ⟨z, hz⟩ = (f z : EReal) := by
      dsimp only [f, g]
      rw [← hstep]
    rw [hvalue]
    exact EReal.coe_le_coe_iff.mpr (Finset.le_sup' f hzC)

/-- A measurable weight map with the iid environment marginal obeys the same
real signed short-window bound as the native process coordinate. -/
theorem ae_eventually_small_real_short_weight_windows_of_weight_map
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hmoment : ∃ p : ℝ, 2 < p ∧
      (∫⁻ t, ENNReal.ofReal (|t| ^ p) ∂μ) < ∞)
    (P : Measure Ω) [IsProbabilityMeasure P]
    (weights : Ω → Environment) (hWeights : Measurable weights)
    (hMarginal : P.map weights = environmentLaw μ) :
    let C : ℕ → Finset Lattice := fun n => insert 0
      (((Finset.Icc (-(2 * (n : ℤ))) (2 * (n : ℤ))).product
        (Finset.Icc (-(2 * (n : ℤ))) (2 * (n : ℤ)))).filter
          (fun z => z.1.natAbs + z.2.natAbs ≤ 2 * n))
    ∀ᵐ ω ∂P,
      let W : Fin 2 → ℝ → ℕ → ℝ := fun i δ n =>
        (C n).sup' (by dsimp [C]; exact Finset.insert_nonempty _ _)
          (fun z => (∑ k ∈ Finset.range (⌊(n : ℝ) * δ⌋₊ + 1),
            |(weights ω) (z + (k : ℤ) • finiteEdgeStep i)|) / (n : ℝ))
      ∀ η : ℝ, 0 < η → ∃ δ0 : ℝ, 0 < δ0 ∧ δ0 ≤ 1 ∧
        ∀ δ : ℝ, 0 < δ → δ ≤ δ0 → ∀ i : Fin 2,
          ∀ᶠ n : ℕ in atTop, W i δ n < 2 * η := by
  classical
  have hSource :=
    LPPDifferentiability.ae_uniform_short_weight_segments_of_absolute_moment μ hmoment
  have hMap : ∀ᵐ ω ∂P.map weights,
      let W : Fin 2 → ℝ → ℕ → EReal := fun i δ n =>
        ⨆ x : {x : Lattice // x.1.natAbs + x.2.natAbs ≤ 2 * n},
          (((∑ k ∈ Finset.range (⌊(n : ℝ) * δ⌋₊ + 1),
            |ω (x.1 + (k : ℤ) •
              (if i = 0 then ((1 : ℤ), (0 : ℤ)) else ((0 : ℤ), (1 : ℤ))))|) /
                (n : ℝ) : ℝ) : EReal)
      ∀ η : ℝ, 0 < η → ∃ δ0 : ℝ, 0 < δ0 ∧ δ0 ≤ 1 ∧
        ∀ δ : ℝ, 0 < δ → δ ≤ δ0 → ∀ i : Fin 2,
          limsup (W i δ) atTop ≤ (η : EReal) := by
    rw [hMarginal]
    exact hSource
  have hPulled : ∀ᵐ ω ∂P,
      let W : Fin 2 → ℝ → ℕ → EReal := fun i δ n =>
        ⨆ x : {x : Lattice // x.1.natAbs + x.2.natAbs ≤ 2 * n},
          (((∑ k ∈ Finset.range (⌊(n : ℝ) * δ⌋₊ + 1),
            |(weights ω) (x.1 + (k : ℤ) •
              (if i = 0 then ((1 : ℤ), (0 : ℤ)) else ((0 : ℤ), (1 : ℤ))))|) /
                (n : ℝ) : ℝ) : EReal)
      ∀ η : ℝ, 0 < η → ∃ δ0 : ℝ, 0 < δ0 ∧ δ0 ≤ 1 ∧
        ∀ δ : ℝ, 0 < δ → δ ≤ δ0 → ∀ i : Fin 2,
          limsup (W i δ) atTop ≤ (η : EReal) := by
    exact (Measure.tendsto_ae_map hWeights.aemeasurable).eventually hMap
  dsimp only
  filter_upwards [hPulled] with ω hω
  dsimp only at hω
  intro η hη
  obtain ⟨δ0, hδ0, hδ0le, hlimsup⟩ := hω η hη
  refine ⟨δ0, hδ0, hδ0le, ?_⟩
  intro δ hδ hδ0 i
  let realW : ℕ → ℝ := fun n =>
    (insert 0
      (((Finset.Icc (-(2 * (n : ℤ))) (2 * (n : ℤ))).product
        (Finset.Icc (-(2 * (n : ℤ))) (2 * (n : ℤ)))).filter
          (fun z => z.1.natAbs + z.2.natAbs ≤ 2 * n))).sup'
      (by exact Finset.insert_nonempty _ _)
      (fun z => (∑ k ∈ Finset.range (⌊(n : ℝ) * δ⌋₊ + 1),
        |(weights ω) (z + (k : ℤ) • finiteEdgeStep i)|) / (n : ℝ))
  have hEqSeq : (fun n : ℕ => (realW n : EReal)) = fun n =>
      ⨆ x : {x : Lattice // x.1.natAbs + x.2.natAbs ≤ 2 * n},
        (((∑ k ∈ Finset.range (⌊(n : ℝ) * δ⌋₊ + 1),
          |(weights ω) (x.1 + (k : ℤ) •
            (if i = 0 then ((1 : ℤ), (0 : ℤ)) else ((0 : ℤ), (1 : ℤ))))|) /
              (n : ℝ) : ℝ) : EReal) := by
    funext n
    exact short_window_real_sup_coe_eq_ereal_iSup (weights ω) i δ n
  have hlimsupReal : limsup (fun n : ℕ => (realW n : EReal)) atTop ≤ (η : EReal) := by
    rw [hEqSeq]
    exact hlimsup δ hδ hδ0 i
  have hηcast : (η : EReal) < ((2 * η : ℝ) : EReal) := by
    exact EReal.coe_lt_coe_iff.mpr (by linarith)
  have hstrict : limsup (fun n : ℕ => (realW n : EReal)) atTop <
      ((2 * η : ℝ) : EReal) := hlimsupReal.trans_lt hηcast
  have hEventuallyE : ∀ᶠ n : ℕ in atTop,
      (realW n : EReal) < ((2 * η : ℝ) : EReal) :=
    eventually_lt_of_limsup_lt hstrict (by isBoundedDefault)
  have hEventuallyReal : ∀ᶠ n : ℕ in atTop, realW n < 2 * η := by
    filter_upwards [hEventuallyE] with n hn
    exact EReal.coe_lt_coe_iff.mp hn
  change ∀ᶠ n : ℕ in atTop, realW n < 2 * η
  exact hEventuallyReal

end LPP.Busemann
