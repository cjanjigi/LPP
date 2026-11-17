/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import LPP_Foundations.Probability.EnvironmentPairTranslationErgodic
public import LPP_Foundations.Probability.EnvironmentHalfPlaneResample

@[expose] public section
open MeasureTheory
namespace LPPDifferentiability

/-- The correlated half-plane output pair is ergodic under simultaneous positive
horizontal translation. This formalizes the coupling step in
`Strong Existence_final.tex:985–993`, with the first input retained at height
zero. -/
theorem ergodic_environmentLaw_horizontal_halfPlane_coupling
    (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    Ergodic
      (fun p : Environment × Environment =>
        (fun z : Lattice => p.1 (((1 : ℤ), (0 : ℤ)) + z),
         fun z : Lattice => p.2 (((1 : ℤ), (0 : ℤ)) + z)))
      (((environmentLaw μ).prod (environmentLaw μ)).map
        (fun p : Environment × Environment =>
          (p.1, fun z : Lattice => if 0 ≤ z.2 then p.1 z else p.2 z))) := by
  -- Name the independent input law, the coupled output map, and their shared shift.
  let inputLaw : Measure (Environment × Environment) :=
    (environmentLaw μ).prod (environmentLaw μ)
  let coupling : Environment × Environment → Environment × Environment :=
    fun p => (p.1, fun z : Lattice => if 0 ≤ z.2 then p.1 z else p.2 z)
  let shift : Environment × Environment → Environment × Environment :=
    fun p =>
      (fun z : Lattice => p.1 (((1 : ℤ), (0 : ℤ)) + z),
       fun z : Lattice => p.2 (((1 : ℤ), (0 : ℤ)) + z))

  -- The target law is exactly the pushforward of the independent inputs by this map.
  change Ergodic shift (inputLaw.map coupling)
  have hCouplingMeasurable : Measurable coupling := by
    change Measurable (fun p : Environment × Environment =>
      (p.1, fun z : Lattice => if 0 ≤ z.2 then p.1 z else p.2 z))
    exact measurable_fst.prodMk measurable_horizontal_halfPlane_resample
  have hCouplingMeasurePreserving :
      MeasurePreserving coupling inputLaw (inputLaw.map coupling) :=
    ⟨hCouplingMeasurable, rfl⟩

  -- The input result supplies ergodicity and measurability of this shift.
  have hInputErgodic : Ergodic shift inputLaw :=
    ergodic_independent_environment_pair_horizontal_translation μ
  have hShiftMeasurable : Measurable shift :=
    hInputErgodic.toMeasurePreserving.measurable

  -- Horizontal translation leaves the height used by the splice unchanged.
  have hHeight (z : Lattice) :
      (((1 : ℤ), (0 : ℤ)) + z).2 = z.2 := by
    change 0 + z.2 = z.2
    exact zero_add _

  -- The coupling commutes pointwise with the simultaneous horizontal shift.
  have hSemiconj :
      ∀ p : Environment × Environment, coupling (shift p) = shift (coupling p) := by
    intro p
    apply Prod.ext
    · rfl
    · funext z
      change
        (if 0 ≤ z.2 then p.1 (((1 : ℤ), (0 : ℤ)) + z)
          else p.2 (((1 : ℤ), (0 : ℤ)) + z)) =
        (if 0 ≤ (((1 : ℤ), (0 : ℤ)) + z).2 then p.1 (((1 : ℤ), (0 : ℤ)) + z)
          else p.2 (((1 : ℤ), (0 : ℤ)) + z))
      rw [hHeight z]

  -- Transfer ergodicity from the independent input pair to its coupled output.
  exact MeasurePreserving.ergodic_of_ergodic_semiconj
    hCouplingMeasurePreserving hInputErgodic hShiftMeasurable hSemiconj

end LPPDifferentiability
