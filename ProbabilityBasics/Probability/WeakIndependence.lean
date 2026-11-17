/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Mathlib.Probability.Independence.Basic
public import Mathlib.MeasureTheory.Measure.FiniteMeasureProd

/-!
# Independence under weak limits

If two continuous observations are independent under each law in a weakly
convergent sequence, then they remain independent under the limiting law.
-/

@[expose] public section

open Filter MeasureTheory ProbabilityTheory
open scoped Topology

namespace ProbabilityBasics

/-- Independence of two continuous observations is preserved by weak limits. -/
theorem indepFun_of_weakLimit
    {Ω A B : Type*}
    [MeasurableSpace Ω] [TopologicalSpace Ω] [OpensMeasurableSpace Ω]
    [MeasurableSpace A] [TopologicalSpace A] [BorelSpace A]
    [SecondCountableTopology A] [TopologicalSpace.PseudoMetrizableSpace A]
    [OpensMeasurableSpace A]
    [MeasurableSpace B] [TopologicalSpace B] [BorelSpace B]
    [SecondCountableTopology B] [TopologicalSpace.PseudoMetrizableSpace B]
    [OpensMeasurableSpace B]
    [BorelSpace (A × B)]
    (ν : ℕ → ProbabilityMeasure Ω) (P : ProbabilityMeasure Ω)
    (hweak : Tendsto ν atTop (𝓝 P))
    (f : Ω → A) (g : Ω → B)
    (hf : Continuous f) (hg : Continuous g)
    (hindep : ∀ n, IndepFun f g (ν n : Measure Ω)) :
    IndepFun f g (P : Measure Ω) := by
  have hjoint : Tendsto (fun n => (ν n).map fun ω => (f ω, g ω)) atTop
      (𝓝 (P.map fun ω => (f ω, g ω))) :=
    ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous ν P hweak (hf.prodMk hg)
  have hmarginalA : Tendsto (fun n => (ν n).map f) atTop (𝓝 (P.map f)) :=
    ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous ν P hweak hf
  have hmarginalB : Tendsto (fun n => (ν n).map g) atTop (𝓝 (P.map g)) :=
    ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous ν P hweak hg
  have hproduct : Tendsto (fun n => ((ν n).map f).prod ((ν n).map g)) atTop
      (𝓝 ((P.map f).prod (P.map g))) := by
    exact (ProbabilityMeasure.continuous_prod.continuousAt.tendsto
      (x := (P.map f, P.map g))).comp
      (hmarginalA.prodMk_nhds hmarginalB)
  have hfinite (n : ℕ) : (ν n).map (fun ω => (f ω, g ω)) =
      ((ν n).map f).prod ((ν n).map g) := by
    apply Subtype.ext
    change ((ν n : Measure Ω).map (fun ω => (f ω, g ω))) =
      (((ν n : Measure Ω).map f).prod ((ν n : Measure Ω).map g))
    exact (indepFun_iff_map_prod_eq_prod_map_map
      (μ := (ν n : Measure Ω))
      hf.measurable.aemeasurable hg.measurable.aemeasurable).mp (hindep n)
  have hseq : (fun n => (ν n).map (fun ω => (f ω, g ω))) =
      (fun n => ((ν n).map f).prod ((ν n).map g)) := funext hfinite
  have hjoint' : Tendsto (fun n => ((ν n).map f).prod ((ν n).map g)) atTop
      (𝓝 (P.map fun ω => (f ω, g ω))) := by
    rw [← hseq]
    exact hjoint
  have hlimit : P.map (fun ω => (f ω, g ω)) = (P.map f).prod (P.map g) :=
    tendsto_nhds_unique hjoint' hproduct
  apply (indepFun_iff_map_prod_eq_prod_map_map
    (μ := (P : Measure Ω)) hf.measurable.aemeasurable hg.measurable.aemeasurable).2
  exact congrArg (fun μ : ProbabilityMeasure (A × B) => (μ : Measure (A × B))) hlimit

end ProbabilityBasics
