/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LPP_Foundations.Statements.ShapeDefinitions
public import LPP_Foundations.Probability.PassageMeasurable
import Busemann.Geometry.EnvironmentUniformPassageBoundsAux
import LPP_Foundations.Probability.TranslationCylinder
import Mathlib.MeasureTheory.Order.Group.Lattice
import Mathlib.Tactic

/-! Measurable common environment events for uniform interior passage bounds. -/

@[expose] public section
open MeasureTheory LPPDifferentiability
open scoped ENNReal

namespace LPP.Busemann

private theorem measurableSet_uniform_neighbor_bounds :
    MeasurableSet {ω : LPPDifferentiability.Environment |
      ∀ x : Lattice, ∀ ε : ℚ, 0 < ε → ε < 1 / 2 →
        ∃ C N : ℕ, 0 < N ∧
          ∀ d : ℕ × ℕ, N ≤ d.1 + d.2 →
            (ε : ℝ) ≤ (d.1 : ℝ) / ((d.1 + d.2 : ℕ) : ℝ) →
            (d.1 : ℝ) / ((d.1 + d.2 : ℕ) : ℝ) ≤ 1 - (ε : ℝ) →
            0 < d.1 ∧ 0 < d.2 ∧
            |lastPassage ω x d -
              lastPassage ω (x + ((1 : ℤ), (0 : ℤ))) (d.1 - 1, d.2)| ≤ (C : ℝ) ∧
            |lastPassage ω x d -
              lastPassage ω (x + ((0 : ℤ), (1 : ℤ))) (d.1, d.2 - 1)| ≤ (C : ℝ)} := by
  classical
  -- All geometric indices and integer bounds are countable.
  rw [Set.ofPred_forall]
  apply MeasurableSet.iInter
  intro x
  rw [Set.ofPred_forall]
  apply MeasurableSet.iInter
  intro ε
  apply (MeasurableSet.const _).imp
  apply (MeasurableSet.const _).imp
  rw [Set.ofPred_exists]
  apply MeasurableSet.iUnion
  intro C
  rw [Set.ofPred_exists]
  apply MeasurableSet.iUnion
  intro N
  -- Keep the nested set builder explicit before forming its intersection.
  have hTail : MeasurableSet {ω : LPPDifferentiability.Environment |
      ∀ d : ℕ × ℕ, N ≤ d.1 + d.2 →
        (ε : ℝ) ≤ (d.1 : ℝ) / ((d.1 + d.2 : ℕ) : ℝ) →
        (d.1 : ℝ) / ((d.1 + d.2 : ℕ) : ℝ) ≤ 1 - (ε : ℝ) →
        0 < d.1 ∧ 0 < d.2 ∧
        |lastPassage ω x d -
          lastPassage ω (x + ((1 : ℤ), (0 : ℤ))) (d.1 - 1, d.2)| ≤ (C : ℝ) ∧
        |lastPassage ω x d -
          lastPassage ω (x + ((0 : ℤ), (1 : ℤ))) (d.1, d.2 - 1)| ≤ (C : ℝ)} := by
    rw [Set.ofPred_forall]
    apply MeasurableSet.iInter
    intro d
    apply (MeasurableSet.const _).imp
    apply (MeasurableSet.const _).imp
    apply (MeasurableSet.const _).imp
    -- Actual neighboring-start passages have the same terminal endpoint.
    have hEast : Measurable (fun ω : LPPDifferentiability.Environment =>
        |lastPassage ω x d -
          lastPassage ω (x + ((1 : ℤ), (0 : ℤ))) (d.1 - 1, d.2)|) :=
      ((measurable_lastPassage x d).sub
        (measurable_lastPassage (x + ((1 : ℤ), (0 : ℤ))) (d.1 - 1, d.2))).abs
    have hNorth : Measurable (fun ω : LPPDifferentiability.Environment =>
        |lastPassage ω x d -
          lastPassage ω (x + ((0 : ℤ), (1 : ℤ))) (d.1, d.2 - 1)|) :=
      ((measurable_lastPassage x d).sub
        (measurable_lastPassage (x + ((0 : ℤ), (1 : ℤ))) (d.1, d.2 - 1))).abs
    exact (MeasurableSet.const _).inter ((MeasurableSet.const _).inter
      ((measurableSet_le hEast measurable_const).inter
        (measurableSet_le hNorth measurable_const)))
  exact (MeasurableSet.const (0 < N)).inter hTail

private theorem exists_shift_closed_full_subset
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (A : Set LPPDifferentiability.Environment) (hA : MeasurableSet A)
    (hFull : environmentLaw μ A = 1) :
    ∃ E : Set LPPDifferentiability.Environment,
      MeasurableSet E ∧ environmentLaw μ E = 1 ∧ E ⊆ A ∧
      ∀ z : Lattice, ∀ ω ∈ E, (fun y : Lattice => ω (z + y)) ∈ E := by
  let E : Set LPPDifferentiability.Environment :=
    ⋂ z : Lattice, (fun ω : LPPDifferentiability.Environment =>
      fun y : Lattice => ω (z + y)) ⁻¹' A
  have hMeas : MeasurableSet E := MeasurableSet.iInter fun z =>
    hA.preimage (measurePreserving_environment_translation μ z).measurable
  have hTranslate (z : Lattice) :
      ∀ᵐ ω : LPPDifferentiability.Environment ∂environmentLaw μ,
        (fun y : Lattice => ω (z + y)) ∈ A := by
    have hm := measurePreserving_environment_translation μ z
    apply (mem_ae_iff_prob_eq_one (hA.preimage hm.measurable)).mpr
    rw [hm.measure_preimage hA.nullMeasurableSet]
    exact hFull
  have hAll : ∀ᵐ ω : LPPDifferentiability.Environment ∂environmentLaw μ,
      ∀ z : Lattice, (fun y : Lattice => ω (z + y)) ∈ A := ae_all_iff.mpr hTranslate
  have hEae : ∀ᵐ ω : LPPDifferentiability.Environment ∂environmentLaw μ, ω ∈ E := by
    filter_upwards [hAll] with ω hω
    exact Set.mem_iInter.mpr hω
  refine ⟨E, hMeas, (mem_ae_iff_prob_eq_one hMeas).mp hEae, ?_, ?_⟩
  · intro ω hω
    have hzero := Set.mem_iInter.mp hω (0 : Lattice)
    simpa only [Set.mem_preimage, zero_add] using hzero
  · intro z ω hω
    apply Set.mem_iInter.mpr
    intro w
    have hzw := Set.mem_iInter.mp hω (z + w)
    change (fun y : Lattice => ω ((z + w) + y)) ∈ A at hzw
    change (fun y : Lattice => ω (z + (w + y))) ∈ A
    simpa only [add_assoc] using hzw

/-- On one measurable full environment event, passage differences from both
neighboring starts are uniformly bounded over every compact interior cone.
The event includes all signed translates. This is the neighboring-start
specialization of Strong Existence, g602, lines 1663–1666. -/
theorem exists_full_environment_event_uniform_interior_neighbor_bounds
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : LPPStatements.NotAPointMass μ)
    (hmoment : ∃ p : ℝ, 2 < p ∧
      (∫⁻ t, ENNReal.ofReal (|t| ^ p) ∂μ) < ∞) :
    ∃ E : Set LPPDifferentiability.Environment,
      MeasurableSet E ∧ environmentLaw μ E = 1 ∧
      (∀ z : Lattice, ∀ ω ∈ E,
        (fun y : Lattice => ω (z + y)) ∈ E) ∧
      ∀ ω ∈ E, ∀ x : Lattice, ∀ ε : ℚ,
        0 < ε → ε < 1 / 2 →
        ∃ C N : ℕ, 0 < N ∧
          ∀ d : ℕ × ℕ, N ≤ d.1 + d.2 →
            (ε : ℝ) ≤ (d.1 : ℝ) / ((d.1 + d.2 : ℕ) : ℝ) →
            (d.1 : ℝ) / ((d.1 + d.2 : ℕ) : ℝ) ≤ 1 - (ε : ℝ) →
            0 < d.1 ∧ 0 < d.2 ∧
            |lastPassage ω x d -
              lastPassage ω (x + ((1 : ℤ), (0 : ℤ))) (d.1 - 1, d.2)| ≤ (C : ℝ) ∧
            |lastPassage ω x d -
              lastPassage ω (x + ((0 : ℤ), (1 : ℤ))) (d.1, d.2 - 1)| ≤ (C : ℝ) := by
  let A : Set LPPDifferentiability.Environment := {ω |
    ∀ x : Lattice, ∀ ε : ℚ, 0 < ε → ε < 1 / 2 →
      ∃ C N : ℕ, 0 < N ∧
        ∀ d : ℕ × ℕ, N ≤ d.1 + d.2 →
          (ε : ℝ) ≤ (d.1 : ℝ) / ((d.1 + d.2 : ℕ) : ℝ) →
          (d.1 : ℝ) / ((d.1 + d.2 : ℕ) : ℝ) ≤ 1 - (ε : ℝ) →
          0 < d.1 ∧ 0 < d.2 ∧
          |lastPassage ω x d -
            lastPassage ω (x + ((1 : ℤ), (0 : ℤ))) (d.1 - 1, d.2)| ≤ (C : ℝ) ∧
          |lastPassage ω x d -
            lastPassage ω (x + ((0 : ℤ), (1 : ℤ))) (d.1, d.2 - 1)| ≤ (C : ℝ)}
  -- The actual original-law native producer supplies the common environment property.
  have hAmeas : MeasurableSet A := measurableSet_uniform_neighbor_bounds
  have hAae : ∀ᵐ ω : LPPDifferentiability.Environment ∂environmentLaw μ, ω ∈ A :=
    ae_uniform_interior_neighbor_bounds μ hμ hmoment
  have hAfull : environmentLaw μ A = 1 :=
    (mem_ae_iff_prob_eq_one hAmeas).mp hAae
  -- One countable signed-shift intersection retains all bounds on the same event.
  obtain ⟨E, hEmeas, hEfull, hSubset, hShift⟩ :=
    exists_shift_closed_full_subset μ A hAmeas hAfull
  exact ⟨E, hEmeas, hEfull, hShift, fun ω hω => hSubset hω⟩

end LPP.Busemann
