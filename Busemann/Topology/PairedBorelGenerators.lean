/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Busemann.Frozen.StrongExistence.Definitions.SkorokhodRealization
public import ProbabilityBasics.Analysis.CountableSidedSampleSet
public import Busemann.Topology.PairedEvaluationMeasurability
public import Busemann.Topology.PairedPathSecondCountability
public import Busemann.Topology.PairedGraphOpenHitMeasurability
public import Busemann.Topology.PairedGraphUpperOpenMeasurability
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

@[expose] public section
open Filter MeasureTheory LPPDifferentiability LPP.Busemann
open scoped ENNReal Topology
namespace LPP.Busemann

/-- A countable set of times, including every time lacking either neighboring
side, generates the Borel structure of the ordered-graph Vietoris
topology through both scalar traces. The topology and Borel definitions are at
`PairedSkorokhodPathTopology.lean:12` and `PairedSkorokhodPathBorel.lean:12`.
-/
theorem exists_countable_sided_eval_generators
    (S : Set ℝ) (J : Type*) [Countable J] (hS : IsClosed S) :
    ∃ D : Set {u : ℝ // u ∈ S},
      D.Countable ∧
      (∀ t : {u : ℝ // u ∈ S}, t ∉ D →
        t ∈ closure (D ∩ Set.Iio t) ∧
        t ∈ closure (D ∩ Set.Ioi t)) ∧
      pairedSkorokhodPathBorel S J =
        MeasurableSpace.generateFrom
          {A : Set (PairedSkorokhodPath S J) |
            ∃ t : {u : ℝ // u ∈ S}, t ∈ D ∧
              ∃ j : J, ∃ U : Set ℝ, IsOpen U ∧
                (A = {f | evalMinus f t j ∈ U} ∨
                 A = {f | evalPlus f t j ∈ U})} := by
  classical
  -- Choose one countable set of sided samples for both inclusions.
  obtain ⟨D, hD, hside⟩ :=
    ProbabilityBasics.exists_countable_sided_sample_set S

  -- Name the exact scalar-generator sigma algebra in the original conclusion.
  let sampledSigma : MeasurableSpace (PairedSkorokhodPath S J) :=
    MeasurableSpace.generateFrom
      {A : Set (PairedSkorokhodPath S J) |
        ∃ t : {u : ℝ // u ∈ S}, t ∈ D ∧
          ∃ j : J, ∃ U : Set ℝ, IsOpen U ∧
            (A = {f | evalMinus f t j ∈ U} ∨
             A = {f | evalPlus f t j ∈ U})}

  -- Pin native measurability to the frozen Borel space for scalar evaluations.
  let : MeasurableSpace (PairedSkorokhodPath S J) :=
    pairedSkorokhodPathBorel S J
  have hSampled_le_borel :
      sampledSigma ≤ pairedSkorokhodPathBorel S J := by
    apply MeasurableSpace.generateFrom_le
    intro A hA
    rcases hA with ⟨t, _, j, U, hU, hBranch⟩
    rcases measurable_evalMinus_evalPlus S J hS t j with
      ⟨hEvalMinus, hEvalPlus⟩
    rcases hBranch with hMinus | hPlus
    · rw [hMinus]
      exact hEvalMinus hU.measurableSet
    · rw [hPlus]
      exact hEvalPlus hU.measurableSet

  -- Install only the second-countability class for the topology.
  let : SecondCountableTopology (PairedSkorokhodPath S J) :=
    pairedSkorokhodPath_secondCountableTopology S J
  have hBorel_eq_vietoris :
      pairedSkorokhodPathBorel S J =
        MeasurableSpace.generateFrom (pairedGraphVietorisGenerators S J) := by
    change @borel (PairedSkorokhodPath S J)
        (pairedSkorokhodPathTopology S J) = _
    exact borel_eq_generateFrom_of_subbasis (by rfl)

  -- Reduce the reverse inclusion to each original upper or lower generator.
  have hBorel_le_sampled :
      pairedSkorokhodPathBorel S J ≤ sampledSigma := by
    rw [hBorel_eq_vietoris]
    apply MeasurableSpace.generateFrom_le
    intro V hV
    change
      (∃ U : Set (SqueezedState J × SqueezedState J), IsOpen U ∧
        V = {f | pairedPathOrderGraph S J f ⊆ U}) ∨
      (∃ U : Set (SqueezedState J × SqueezedState J), IsOpen U ∧
        V = {f | (pairedPathOrderGraph S J f ∩ U).Nonempty}) at hV
    rcases hV with ⟨U, hU, hEq⟩ | ⟨U, hU, hEq⟩
    · rw [hEq]
      exact measurableSet_pairedPathOrderGraph_subset_open_of_sidedSamples
        S J hS D hD hside U hU
    · rw [hEq]
      exact measurableSet_pairedPathOrderGraph_hit_open_of_sidedSamples
        S J hS D hD hside U hU

  -- Both directions concern the exact frozen Borel structure and this same D.
  refine ⟨D, hD, hside, ?_⟩
  exact le_antisymm hBorel_le_sampled hSampled_le_borel

end LPP.Busemann
