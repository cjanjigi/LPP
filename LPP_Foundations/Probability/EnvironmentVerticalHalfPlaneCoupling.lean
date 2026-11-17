/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import LPP_Foundations.Probability.EnvironmentHalfPlaneCouplingErgodic
public import LPP_Foundations.Probability.EnvironmentHalfPlaneCouplingSymmetry
public import LPP_Foundations.Probability.EnvironmentSwap
import Mathlib.MeasureTheory.Measure.Prod

/-!
# Coupling across the vertical half-plane

Swapping the lattice coordinates in each weight field carries the horizontal coupling to the literal vertical coupling. The two outputs remain
correlated, and the first input is retained on the boundary.
-/

@[expose] public section
open MeasureTheory
namespace LPPDifferentiability

private def swapPair (p : Environment × Environment) : Environment × Environment :=
  (environmentSwap p.1, environmentSwap p.2)

private def horizontalPair (p : Environment × Environment) : Environment × Environment :=
  (p.1, fun z => if 0 ≤ z.2 then p.1 z else p.2 z)

private def verticalPair (p : Environment × Environment) : Environment × Environment :=
  (p.1, fun z => if 0 ≤ z.1 then p.1 z else p.2 z)

private theorem measurable_swapPair : Measurable swapPair := by
  exact (measurable_environmentSwap.comp measurable_fst).prodMk
    (measurable_environmentSwap.comp measurable_snd)

private theorem measurable_horizontalPair : Measurable horizontalPair := by
  exact measurable_fst.prodMk measurable_horizontal_halfPlane_resample

private theorem swapPair_involutive (p : Environment × Environment) :
    swapPair (swapPair p) = p := by
  apply Prod.ext
  · exact environmentSwap_involutive p.1
  · exact environmentSwap_involutive p.2

private theorem verticalPair_swap_conjugacy (p : Environment × Environment) :
    verticalPair p = swapPair (horizontalPair (swapPair p)) := by
  apply Prod.ext
  · exact (environmentSwap_involutive p.1).symm
  · funext z
    by_cases hz : 0 ≤ z.1
    · simp [verticalPair, horizontalPair, swapPair, environmentSwap, hz]
    · simp [verticalPair, horizontalPair, swapPair, environmentSwap, hz]

private theorem input_law_swapPair
    (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    ((environmentLaw μ).prod (environmentLaw μ)).map swapPair =
      (environmentLaw μ).prod (environmentLaw μ) := by
  change ((environmentLaw μ).prod (environmentLaw μ)).map
    (Prod.map environmentSwap environmentSwap) = _
  rw [← Measure.map_prod_map (environmentLaw μ) (environmentLaw μ)
    measurable_environmentSwap measurable_environmentSwap]
  rw [environmentLaw_map_environmentSwap μ]

private theorem vertical_pair_law_eq_horizontal_map
    (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    ((environmentLaw μ).prod (environmentLaw μ)).map verticalPair =
      (((environmentLaw μ).prod (environmentLaw μ)).map horizontalPair).map swapPair := by
  let P : Measure (Environment × Environment) :=
    (environmentLaw μ).prod (environmentLaw μ)
  have hconjugacy : verticalPair = swapPair ∘ horizontalPair ∘ swapPair := by
    funext p
    exact verticalPair_swap_conjugacy p
  change P.map verticalPair = (P.map horizontalPair).map swapPair
  calc
    P.map verticalPair = P.map (swapPair ∘ horizontalPair ∘ swapPair) := by
      rw [hconjugacy]
    _ = (P.map (horizontalPair ∘ swapPair)).map swapPair :=
      (Measure.map_map measurable_swapPair
        (measurable_horizontalPair.comp measurable_swapPair)).symm
    _ = ((P.map swapPair).map horizontalPair).map swapPair := by
      rw [Measure.map_map measurable_horizontalPair measurable_swapPair]
    _ = (P.map horizontalPair).map swapPair := by
      rw [input_law_swapPair μ]

/-- The literal splice that retains the first input at sites with nonnegative
first coordinate is measurable. This is the coupling at
`Strong Existence_final.tex`, line 999. -/
theorem measurable_vertical_halfPlane_resample :
    Measurable (fun p : Environment × Environment => fun z : Lattice =>
      if 0 ≤ z.1 then p.1 z else p.2 z) := by
  -- Each output weight is a measurable coordinate of one of the two inputs.
  apply Measurable.of_eval
  intro z
  by_cases hz : 0 ≤ z.1
  · simpa only [hz, ite_true, Function.comp_def] using
      (measurable_environment_eval z).comp
        (measurable_fst : Measurable
          (Prod.fst : Environment × Environment → Environment))
  · simpa only [hz, ite_false, Function.comp_def] using
      (measurable_environment_eval z).comp
        (measurable_snd : Measurable
          (Prod.snd : Environment × Environment → Environment))

private theorem measurable_verticalPair : Measurable verticalPair := by
  exact measurable_fst.prodMk measurable_vertical_halfPlane_resample

/-- The first output of the correlated vertical coupling has canonical law.
This is the first marginal in `Strong Existence_final.tex`, line 999. -/
theorem environmentLaw_vertical_halfPlane_coupling_fst
    (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    (((environmentLaw μ).prod (environmentLaw μ)).map
      (fun p : Environment × Environment =>
        (p.1, fun z : Lattice => if 0 ≤ z.1 then p.1 z else p.2 z))).map
      (Prod.fst : Environment × Environment → Environment) =
    environmentLaw μ := by
  -- The first output is literally the first independent input.
  change (((environmentLaw μ).prod (environmentLaw μ)).map verticalPair).map
    (Prod.fst : Environment × Environment → Environment) = environmentLaw μ
  rw [Measure.map_map measurable_fst measurable_verticalPair]
  have hfirst : (Prod.fst : Environment × Environment → Environment) ∘ verticalPair =
      Prod.fst := rfl
  rw [hfirst, Measure.map_fst_prod, measure_univ, one_smul]

/-- The resampled second output also has the canonical full product law.
This is the second marginal in `Strong Existence_final.tex`, line 999. -/
theorem environmentLaw_vertical_halfPlane_coupling_snd
    (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    (((environmentLaw μ).prod (environmentLaw μ)).map
      (fun p : Environment × Environment =>
        (p.1, fun z : Lattice => if 0 ≤ z.1 then p.1 z else p.2 z))).map
      (Prod.snd : Environment × Environment → Environment) =
    environmentLaw μ := by
  -- Project the conjugated horizontal law, then use its proved full marginal law.
  change (((environmentLaw μ).prod (environmentLaw μ)).map verticalPair).map
    (Prod.snd : Environment × Environment → Environment) = environmentLaw μ
  rw [vertical_pair_law_eq_horizontal_map μ]
  rw [Measure.map_map measurable_snd measurable_swapPair]
  have hsecond : (Prod.snd : Environment × Environment → Environment) ∘ swapPair =
      environmentSwap ∘ Prod.snd := rfl
  rw [hsecond, ← Measure.map_map measurable_environmentSwap measurable_snd]
  have hhorizontal :
      (((environmentLaw μ).prod (environmentLaw μ)).map horizontalPair).map
        (Prod.snd : Environment × Environment → Environment) = environmentLaw μ := by
    rw [Measure.map_map measurable_snd measurable_horizontalPair]
    have hproject : (Prod.snd : Environment × Environment → Environment) ∘
        horizontalPair =
        (fun p : Environment × Environment => fun z : Lattice =>
          if 0 ≤ z.2 then p.1 z else p.2 z) := rfl
    rw [hproject]
    exact environmentLaw_map_horizontal_halfPlane_resample μ
  rw [hhorizontal, environmentLaw_map_environmentSwap μ]

/-- The correlated output law is invariant under exchanging its two environments.
This is the exchangeability step in `Strong Existence_final.tex`, line 999. -/
theorem environmentLaw_vertical_halfPlane_coupling_swap
    (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    ((environmentLaw μ).prod (environmentLaw μ)).map
      (fun p : Environment × Environment =>
        (p.1, fun z : Lattice => if 0 ≤ z.1 then p.1 z else p.2 z)) =
    (((environmentLaw μ).prod (environmentLaw μ)).map
      (fun p : Environment × Environment =>
        (p.1, fun z : Lattice => if 0 ≤ z.1 then p.1 z else p.2 z))).map
      Prod.swap := by
  -- Weight-field swap commutes with exchanging the two output fields.
  change ((environmentLaw μ).prod (environmentLaw μ)).map verticalPair =
    (((environmentLaw μ).prod (environmentLaw μ)).map verticalPair).map Prod.swap
  rw [vertical_pair_law_eq_horizontal_map μ]
  have hcommute : Prod.swap ∘ swapPair = swapPair ∘ Prod.swap := by
    funext p
    rfl
  have hHorizontalSwap :
      ((environmentLaw μ).prod (environmentLaw μ)).map horizontalPair =
      (((environmentLaw μ).prod (environmentLaw μ)).map horizontalPair).map
        Prod.swap :=
    environmentLaw_horizontal_halfPlane_coupling_swap μ
  calc
    (((environmentLaw μ).prod (environmentLaw μ)).map horizontalPair).map swapPair =
        ((((environmentLaw μ).prod (environmentLaw μ)).map horizontalPair).map
          Prod.swap).map swapPair :=
            congrArg (fun ν : Measure (Environment × Environment) => ν.map swapPair)
              hHorizontalSwap
    _ = (((environmentLaw μ).prod (environmentLaw μ)).map horizontalPair).map
          (swapPair ∘ Prod.swap) := by
            rw [Measure.map_map measurable_swapPair measurable_swap]
    _ = (((environmentLaw μ).prod (environmentLaw μ)).map horizontalPair).map
          (Prod.swap ∘ swapPair) := by rw [hcommute]
    _ = ((((environmentLaw μ).prod (environmentLaw μ)).map horizontalPair).map
          swapPair).map Prod.swap := by
            rw [Measure.map_map measurable_swap measurable_swapPair]

/-- The correlated output pair is ergodic under simultaneous positive vertical
translation; the first input is retained on the boundary `z.1 = 0`.
This is the shift step in `Strong Existence_final.tex`, line 999. -/
theorem ergodic_environmentLaw_vertical_halfPlane_coupling
    (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    Ergodic
      (fun p : Environment × Environment =>
        (fun z : Lattice => p.1 (((0 : ℤ), (1 : ℤ)) + z),
         fun z : Lattice => p.2 (((0 : ℤ), (1 : ℤ)) + z)))
      (((environmentLaw μ).prod (environmentLaw μ)).map
        (fun p : Environment × Environment =>
          (p.1, fun z : Lattice => if 0 ≤ z.1 then p.1 z else p.2 z))) := by
  let horizontalShift : Environment × Environment → Environment × Environment :=
    fun p =>
      (fun z => p.1 (((1 : ℤ), (0 : ℤ)) + z),
       fun z => p.2 (((1 : ℤ), (0 : ℤ)) + z))
  let verticalShift : Environment × Environment → Environment × Environment :=
    fun p =>
      (fun z => p.1 (((0 : ℤ), (1 : ℤ)) + z),
       fun z => p.2 (((0 : ℤ), (1 : ℤ)) + z))
  let Qh : Measure (Environment × Environment) :=
    ((environmentLaw μ).prod (environmentLaw μ)).map horizontalPair
  let Qv : Measure (Environment × Environment) :=
    ((environmentLaw μ).prod (environmentLaw μ)).map verticalPair
  change Ergodic verticalShift Qv

  -- The actual vertical correlated law is the image of the horizontal one.
  have hLaw : Qh.map swapPair = Qv :=
    (vertical_pair_law_eq_horizontal_map μ).symm
  have hSwapPreserving : MeasurePreserving swapPair Qh Qv :=
    ⟨measurable_swapPair, hLaw⟩
  have hHorizontalErgodic : Ergodic horizontalShift Qh :=
    ergodic_environmentLaw_horizontal_halfPlane_coupling μ
  have hVerticalMeasurable : Measurable verticalShift := by
    apply Measurable.prodMk
    · apply Measurable.of_eval
      intro z
      exact (measurable_pi_apply (((0 : ℤ), (1 : ℤ)) + z)).comp measurable_fst
    · apply Measurable.of_eval
      intro z
      exact (measurable_pi_apply (((0 : ℤ), (1 : ℤ)) + z)).comp measurable_snd

  -- Swapping lattice coordinates turns each horizontal translation into a
  -- vertical translation of the same weight fields.
  have hSemiconj :
      ∀ p : Environment × Environment,
        swapPair (horizontalShift p) = verticalShift (swapPair p) := by
    intro p
    apply Prod.ext
    · funext z
      rfl
    · funext z
      rfl
  exact hSwapPreserving.ergodic_of_ergodic_semiconj
    hHorizontalErgodic hVerticalMeasurable hSemiconj

end LPPDifferentiability
