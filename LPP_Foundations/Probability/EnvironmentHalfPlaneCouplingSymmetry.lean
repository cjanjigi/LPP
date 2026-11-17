/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import LPP_Foundations.Probability.EnvironmentHalfPlaneResample
import Mathlib.MeasureTheory.Constructions.Pi

/-!
# Symmetry of the horizontal half-plane coupling

The two coupled output environments are exchangeable under the canonical iid law.
-/

@[expose] public section

open MeasureTheory

namespace LPPDifferentiability

private def lowerTagSwap : (Fin 2 × Lattice) ≃ (Fin 2 × Lattice) where
  toFun p := (if 0 ≤ p.2.2 then p.1 else (Equiv.swap (0 : Fin 2) 1) p.1, p.2)
  invFun p := (if 0 ≤ p.2.2 then p.1 else (Equiv.swap (0 : Fin 2) 1) p.1, p.2)
  left_inv p := by
    by_cases h : 0 ≤ p.2.2
    · simp [h]
    · simp [h]
  right_inv p := by
    by_cases h : 0 ≤ p.2.2
    · simp [h]
    · simp [h]

private def taggedToPair : ((Fin 2 × Lattice) → ℝ) → Environment × Environment :=
  fun x => (fun z => x (0, z), fun z => x (1, z))

private def lowerInputSwap : Environment × Environment → Environment × Environment :=
  fun p =>
    ((fun z => if 0 ≤ z.2 then p.1 z else p.2 z),
     (fun z => if 0 ≤ z.2 then p.2 z else p.1 z))

private theorem measurable_taggedToPair : Measurable taggedToPair := by
  apply Measurable.prodMk
  · apply Measurable.of_eval
    intro z
    exact measurable_pi_apply (0, z)
  · apply Measurable.of_eval
    intro z
    exact measurable_pi_apply (1, z)

private theorem measurable_lowerInputSwap : Measurable lowerInputSwap := by
  apply Measurable.prodMk
  · exact measurable_horizontal_halfPlane_resample
  · exact measurable_horizontal_halfPlane_resample.comp measurable_swap

private theorem taggedToPair_reindex (x : (Fin 2 × Lattice) → ℝ) :
    taggedToPair (Equiv.piCongrLeft (fun _ : Fin 2 × Lattice => ℝ) lowerTagSwap x) =
      lowerInputSwap (taggedToPair x) := by
  apply Prod.ext
  · funext z
    by_cases h : 0 ≤ z.2
    · simp [taggedToPair, lowerInputSwap, lowerTagSwap, h, Equiv.piCongrLeft_apply]
    · simp [taggedToPair, lowerInputSwap, lowerTagSwap, h, Equiv.piCongrLeft_apply]
  · funext z
    by_cases h : 0 ≤ z.2
    · simp [taggedToPair, lowerInputSwap, lowerTagSwap, h, Equiv.piCongrLeft_apply]
    · simp [taggedToPair, lowerInputSwap, lowerTagSwap, h, Equiv.piCongrLeft_apply]

private theorem tagged_input_representation (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    (Measure.infinitePi (fun _ : Fin 2 × Lattice => μ)).map taggedToPair =
      (environmentLaw μ).prod (environmentLaw μ) := by
  let C := MeasurableEquiv.curry (Fin 2) Lattice ℝ
  let P := MeasurableEquiv.piFinTwo (fun _ : Fin 2 => Environment)
  have hcomp : taggedToPair = P ∘ C := by
    funext x
    apply Prod.ext <;> funext z <;> rfl
  rw [hcomp, ← Measure.map_map P.measurable C.measurable]
  rw [Measure.infinitePi_map_curry (fun _ : Fin 2 => fun _ : Lattice => μ)]
  rw [Measure.infinitePi_eq_pi]
  exact measurePreserving_piFinTwo (fun _ : Fin 2 => environmentLaw μ) |>.map_eq

private theorem lowerInputSwap_preserves_law (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    (((environmentLaw μ).prod (environmentLaw μ)).map lowerInputSwap) =
      (environmentLaw μ).prod (environmentLaw μ) := by
  let ν : Measure ((Fin 2 × Lattice) → ℝ) :=
    Measure.infinitePi (fun _ : Fin 2 × Lattice => μ)
  have hreindex :
      ν.map (Equiv.piCongrLeft (fun _ : Fin 2 × Lattice => ℝ) lowerTagSwap) = ν := by
    simpa only [ν, MeasurableEquiv.coe_piCongrLeft] using
      (Measure.infinitePi_map_piCongrLeft (fun _ : Fin 2 × Lattice => μ) lowerTagSwap)
  have hrep : ν.map taggedToPair =
      (environmentLaw μ).prod (environmentLaw μ) := tagged_input_representation μ
  calc
    ((environmentLaw μ).prod (environmentLaw μ)).map lowerInputSwap =
        (ν.map taggedToPair).map lowerInputSwap := by rw [hrep]
    _ = ν.map (lowerInputSwap ∘ taggedToPair) := by
      rw [Measure.map_map measurable_lowerInputSwap measurable_taggedToPair]
    _ = ν.map (taggedToPair ∘
        Equiv.piCongrLeft (fun _ : Fin 2 × Lattice => ℝ) lowerTagSwap) := by
      congr 1
      funext x
      exact (taggedToPair_reindex x).symm
    _ = (ν.map (Equiv.piCongrLeft (fun _ : Fin 2 × Lattice => ℝ) lowerTagSwap)).map
        taggedToPair := by
      simpa only [MeasurableEquiv.coe_piCongrLeft] using
        (Measure.map_map measurable_taggedToPair
          (MeasurableEquiv.piCongrLeft
            (fun _ : Fin 2 × Lattice => ℝ) lowerTagSwap).measurable).symm
    _ = (environmentLaw μ).prod (environmentLaw μ) := by rw [hreindex, hrep]

private theorem lowerInputSwap_output (p : Environment × Environment) :
    (fun q : Environment × Environment =>
      (q.1, fun z : Lattice => if 0 ≤ z.2 then q.1 z else q.2 z))
        (lowerInputSwap p) =
      Prod.swap ((fun q : Environment × Environment =>
        (q.1, fun z : Lattice => if 0 ≤ z.2 then q.1 z else q.2 z)) p) := by
  apply Prod.ext
  · funext z
    rfl
  · funext z
    by_cases h : 0 ≤ z.2
    · simp [lowerInputSwap, h]
    · simp [lowerInputSwap, h]

/-- The joint law of an environment and its independent resample below the
horizontal axis is invariant under exchanging the two output environments. -/
theorem environmentLaw_horizontal_halfPlane_coupling_swap
    (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    ((environmentLaw μ).prod (environmentLaw μ)).map
      (fun p : Environment × Environment =>
        (p.1, fun z : Lattice => if 0 ≤ z.2 then p.1 z else p.2 z)) =
    (((environmentLaw μ).prod (environmentLaw μ)).map
      (fun p : Environment × Environment =>
        (p.1, fun z : Lattice => if 0 ≤ z.2 then p.1 z else p.2 z))).map
      Prod.swap := by
  let C : Environment × Environment → Environment × Environment :=
    fun p => (p.1, fun z => if 0 ≤ z.2 then p.1 z else p.2 z)
  have hC : Measurable C :=
    measurable_fst.prodMk measurable_horizontal_halfPlane_resample
  have hswap : Measurable (Prod.swap : Environment × Environment → Environment × Environment) :=
    measurable_swap
  have hcommute : C ∘ lowerInputSwap = Prod.swap ∘ C := by
    funext p
    exact lowerInputSwap_output p
  change ((environmentLaw μ).prod (environmentLaw μ)).map C =
    (((environmentLaw μ).prod (environmentLaw μ)).map C).map Prod.swap
  calc
    ((environmentLaw μ).prod (environmentLaw μ)).map C =
        (((environmentLaw μ).prod (environmentLaw μ)).map lowerInputSwap).map C := by
      rw [lowerInputSwap_preserves_law μ]
    _ = ((environmentLaw μ).prod (environmentLaw μ)).map (C ∘ lowerInputSwap) := by
      rw [Measure.map_map hC measurable_lowerInputSwap]
    _ = ((environmentLaw μ).prod (environmentLaw μ)).map (Prod.swap ∘ C) := by
      rw [hcommute]
    _ = (((environmentLaw μ).prod (environmentLaw μ)).map C).map Prod.swap := by
      rw [Measure.map_map hswap hC]

end LPPDifferentiability
