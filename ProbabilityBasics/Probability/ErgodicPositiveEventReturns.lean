/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Mathlib.Dynamics.Ergodic.Conservative
public import Mathlib.Dynamics.Ergodic.Ergodic

@[expose] public section

open MeasureTheory

namespace ProbabilityBasics

/-- In a finite ergodic measure-preserving system, almost every orbit
visits each positive measurable event arbitrarily late. -/
theorem ergodic_ae_frequently_iterate_mem
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P]
    {T : Ω → Ω} (hT : Ergodic T P)
    (E : Set Ω) (hE : MeasurableSet E) (hpos : 0 < P E) :
    ∀ᵐ ω ∂P, ∃ᶠ n in Filter.atTop, T^[n] ω ∈ E := by
  -- Frequent hits are membership in the limsup of the iterated preimages.
  let F : Set Ω := Filter.limsup (fun n : ℕ => T^[n] ⁻¹' E) Filter.atTop

  -- Each iterated preimage is measurable, so its countable limsup is measurable.
  have hFmeas : MeasurableSet F :=
    .measurableSet_limsup fun n => hT.measurable.iterate n hE

  -- Preimage commutes with this limsup of iterates, making F exactly invariant.
  have hFinv : T ⁻¹' F = F := by
    dsimp [F]
    simp only [Set.preimage_iterate_eq]
    exact CompleteLatticeHom.apply_limsup_iterate
      (CompleteLatticeHom.setPreimage T) E

  -- Finite measure preservation gives the recurrence needed for the positive event.
  have hTconservative : Conservative T P := hT.toMeasurePreserving.conservative

  -- Returns to E give a positive-measure subset of the frequent-hit limsup F.
  have hFfrequent : ∃ᵐ ω ∂P, ω ∈ F := by
    have hEreturns :
        ∃ᵐ ω ∂P, ω ∈ E ∧ ∃ᶠ n in Filter.atTop, T^[n] ω ∈ E :=
      hTconservative.frequently_ae_mem_and_frequently_image_mem
        hE.nullMeasurableSet hpos.ne'
    refine hEreturns.mono fun ω hω => ?_
    change ω ∈ Filter.limsup (fun n : ℕ => T^[n] ⁻¹' E) Filter.atTop
    simpa only [Filter.mem_limsup_iff_frequently_mem, Set.mem_preimage] using hω.2

  -- Ergodicity makes the measurable invariant set F null or full; recurrence excludes null.
  have hFae : ∀ᵐ ω ∂P, ω ∈ F := by
    rcases hT.toPreErgodic.ae_mem_or_ae_notMem hFmeas hFinv with hfull | hnull
    · exact hfull
    · exact False.elim (hFfrequent hnull)

  -- Almost-everywhere membership in F is exactly the desired frequent-hit conclusion.
  filter_upwards [hFae] with ω hω
  change ω ∈ Filter.limsup (fun n : ℕ => T^[n] ⁻¹' E) Filter.atTop at hω
  have hωfreq : ∃ᶠ n in Filter.atTop, ω ∈ T^[n] ⁻¹' E :=
    Filter.mem_limsup_iff_frequently_mem.mp hω
  simpa only [Set.mem_preimage] using hωfreq

end ProbabilityBasics
