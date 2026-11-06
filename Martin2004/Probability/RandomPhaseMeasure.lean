/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import LPP_Foundations.Probability.TranslationCylinder
public import Mathlib.MeasureTheory.Function.Floor
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

/-!
# Random phase: translation modulo one and the skew map

Martin (2004), Proposition 2.1 is stated for every real direction `x`. Martin gives no
argument when the fractional parts of `n x` keep changing. Here an independent uniform phase
`θ` in `[0,1)²` is added, together with the skew map that adds `x` to the phase modulo one
and shifts the environment by the integer part of `x + θ`.

This file proves the two measure facts that this construction needs:

* adding a real vector modulo one preserves the uniform law on `[0,1)²`;
* the skew map preserves the product of that uniform law and the environment law.

Mathlib has no ready statement that `t ↦ fract (t + a)` preserves Lebesgue measure
on `[0,1)`. It is proved here through the unit circle with its Haar measure.
The uniform law on `[0,1)` is written `volume.restrict (Set.Ico 0 1)`.
-/

public section

open MeasureTheory Set

namespace LPPDifferentiability

/-- The uniform law on `[0,1)`, that is Lebesgue measure restricted to `[0,1)`, is a
probability measure. -/
instance isProbabilityMeasure_volume_restrict_Ico_zero_one :
    IsProbabilityMeasure (volume.restrict (Ico (0 : ℝ) 1)) :=
  ⟨by simp⟩

/-- Adding `a` and taking the fractional part preserves the uniform law on `[0,1)`.
This is the one-dimensional step of the random phase that fills the gap in Martin (2004),
Proposition 2.1. -/
theorem measurePreserving_fract_add_restrict_Ico (a : ℝ) :
    MeasurePreserving (fun t : ℝ => Int.fract (t + a)) (volume.restrict (Ico (0 : ℝ) 1))
      (volume.restrict (Ico (0 : ℝ) 1)) := by
  have hmeas : Measurable (fun t : ℝ => Int.fract (t + a)) :=
    measurable_fract.comp (measurable_add_const a)
  refine ⟨hmeas, ?_⟩
  have : Fact ((0 : ℝ) < 1) := ⟨one_pos⟩
  -- The quotient map to the circle carries the uniform law to Haar measure. Mathlib states
  -- this for `(0, 1]`, which differs from `[0, 1)` by a null set.
  have hcircle : MeasurePreserving ((↑) : ℝ → AddCircle (1 : ℝ))
      (volume.restrict (Ico (0 : ℝ) 1)) volume := by
    have h := AddCircle.measurePreserving_mk (1 : ℝ) 0
    rwa [zero_add, ← Measure.restrict_congr_set
      (μ := volume) (Ico_ae_eq_Ioc (a := (0 : ℝ)) (b := 1))] at h
  -- The representative of a circle point in `[0, 1)` is the fractional part.
  have hrep : ∀ s : ℝ,
      ((AddCircle.equivIco (1 : ℝ) 0 (s : AddCircle (1 : ℝ)) : Ico (0 : ℝ) (0 + 1)) : ℝ) =
        Int.fract s := by
    intro s
    simp
  ext S hS
  rw [Measure.map_apply hmeas hS]
  -- `U` is the set of circle points whose representative in `[0, 1)` lies in `S`.
  let U : Set (AddCircle (1 : ℝ)) :=
    (fun y => ((AddCircle.equivIco (1 : ℝ) 0 y : Ico (0 : ℝ) (0 + 1)) : ℝ)) ⁻¹' S
  have hU : MeasurableSet U :=
    hS.preimage (measurable_subtype_coe.comp (AddCircle.measurableEquivIco (1 : ℝ) 0).measurable)
  have hpre : (fun t : ℝ => Int.fract (t + a)) ⁻¹' S =
      ((↑) : ℝ → AddCircle (1 : ℝ)) ⁻¹' ((fun y => y + (a : AddCircle (1 : ℝ))) ⁻¹' U) := by
    ext t
    simp only [mem_preimage, U, ← hrep, AddCircle.coe_add]
  have hshift := measurePreserving_add_right (volume : Measure (AddCircle (1 : ℝ)))
    (a : AddCircle (1 : ℝ))
  have hV : MeasurableSet ((fun y => y + (a : AddCircle (1 : ℝ))) ⁻¹' U) :=
    hU.preimage (measurable_add_const _)
  have hUS : ((↑) : ℝ → AddCircle (1 : ℝ)) ⁻¹' U ∩ Ico (0 : ℝ) 1 = S ∩ Ico (0 : ℝ) 1 := by
    ext t
    simp only [mem_inter_iff, mem_preimage, U, hrep, and_congr_left_iff]
    intro ht
    rw [Int.fract_eq_self.mpr ⟨ht.1, ht.2⟩]
  rw [hpre, hcircle.measure_preimage hV.nullMeasurableSet,
    hshift.measure_preimage hU.nullMeasurableSet,
    ← hcircle.measure_preimage hU.nullMeasurableSet,
    Measure.restrict_apply (hU.preimage AddCircle.measurable_mk'), Measure.restrict_apply hS, hUS]

/-- Adding a real vector `a` and taking fractional parts coordinatewise preserves the
uniform law on the unit square `[0,1)²`. This is the phase part of the skew map used for
Martin (2004), Proposition 2.1 in a non-lattice direction `a`. -/
theorem measurePreserving_fract_add_prod_restrict_Ico (a : ℝ × ℝ) :
    MeasurePreserving
      (fun θ : ℝ × ℝ => (Int.fract (θ.1 + a.1), Int.fract (θ.2 + a.2)))
      ((volume.restrict (Ico (0 : ℝ) 1)).prod (volume.restrict (Ico (0 : ℝ) 1)))
      ((volume.restrict (Ico (0 : ℝ) 1)).prod (volume.restrict (Ico (0 : ℝ) 1))) :=
  (measurePreserving_fract_add_restrict_Ico a.1).prod (measurePreserving_fract_add_restrict_Ico a.2)

/-- The skew map is measurable: the integer shift takes countably many values. -/
private theorem measurable_phase_skew (a : ℝ × ℝ) :
    Measurable (fun p : (ℝ × ℝ) × Environment =>
      ((Int.fract (p.1.1 + a.1), Int.fract (p.1.2 + a.2)),
        fun z : Lattice => p.2 ((⌊p.1.1 + a.1⌋, ⌊p.1.2 + a.2⌋) + z))) := by
  have hshift : Measurable (fun θ : ℝ × ℝ => ((⌊θ.1 + a.1⌋, ⌊θ.2 + a.2⌋) : Lattice)) :=
    (Int.measurable_floor.comp (measurable_fst.add_const _)).prodMk
      (Int.measurable_floor.comp (measurable_snd.add_const _))
  have hphase : Measurable (fun θ : ℝ × ℝ => (Int.fract (θ.1 + a.1), Int.fract (θ.2 + a.2))) :=
    (measurable_fract.comp (measurable_fst.add_const _)).prodMk
      (measurable_fract.comp (measurable_snd.add_const _))
  refine (hphase.comp measurable_fst).prodMk (measurable_pi_iff.mpr fun z => ?_)
  have hevaluate : Measurable (fun q : Lattice × Environment => q.2 (q.1 + z)) :=
    measurable_from_prod_countable_right fun v => measurable_environment_eval (v + z)
  exact hevaluate.comp ((hshift.comp measurable_fst).prodMk measurable_snd)

/-- The skew map of the random phase preserves the product of the uniform law on `[0,1)²`
and the environment law. Here `a` is the direction `x`: the phase `θ` moves to
`fract (θ + a)` and the environment is translated by the integer vector `⌊θ + a⌋`.
This is the invariance, for Martin (2004), Proposition 2.1, needed to apply Liggett's
theorem on the product space. -/
theorem measurePreserving_phase_skew (μ : Measure ℝ) [IsProbabilityMeasure μ] (a : ℝ × ℝ) :
    MeasurePreserving
      (fun p : (ℝ × ℝ) × Environment =>
        ((Int.fract (p.1.1 + a.1), Int.fract (p.1.2 + a.2)),
          fun z : Lattice => p.2 ((⌊p.1.1 + a.1⌋, ⌊p.1.2 + a.2⌋) + z)))
      (((volume.restrict (Ico (0 : ℝ) 1)).prod (volume.restrict (Ico (0 : ℝ) 1))).prod
        (environmentLaw μ))
      (((volume.restrict (Ico (0 : ℝ) 1)).prod (volume.restrict (Ico (0 : ℝ) 1))).prod
        (environmentLaw μ)) := by
  have hphase := measurePreserving_fract_add_prod_restrict_Ico a
  refine ⟨measurable_phase_skew a, ?_⟩
  symm
  refine Measure.prod_eq fun A S hA hS => ?_
  have hmeasurable := measurable_phase_skew a
  rw [Measure.map_apply hmeasurable (hA.prod hS),
    Measure.prod_apply (hmeasurable (hA.prod hS))]
  -- For a fixed phase the section of the preimage is either empty or an environment
  -- translate of `S`, whose law is that of `S`.
  have hsection : ∀ θ : ℝ × ℝ,
      environmentLaw μ (Prod.mk θ ⁻¹' ((fun p : (ℝ × ℝ) × Environment =>
        ((Int.fract (p.1.1 + a.1), Int.fract (p.1.2 + a.2)),
          fun z : Lattice => p.2 ((⌊p.1.1 + a.1⌋, ⌊p.1.2 + a.2⌋) + z))) ⁻¹' A ×ˢ S)) =
      ((fun θ : ℝ × ℝ => (Int.fract (θ.1 + a.1), Int.fract (θ.2 + a.2))) ⁻¹' A).indicator
        (fun _ => environmentLaw μ S) θ := by
    intro θ
    by_cases h : (Int.fract (θ.1 + a.1), Int.fract (θ.2 + a.2)) ∈ A
    · have hset : Prod.mk θ ⁻¹' ((fun p : (ℝ × ℝ) × Environment =>
          ((Int.fract (p.1.1 + a.1), Int.fract (p.1.2 + a.2)),
            fun z : Lattice => p.2 ((⌊p.1.1 + a.1⌋, ⌊p.1.2 + a.2⌋) + z))) ⁻¹' A ×ˢ S) =
          (fun ω : Environment => fun z : Lattice => ω ((⌊θ.1 + a.1⌋, ⌊θ.2 + a.2⌋) + z)) ⁻¹' S := by
        ext ω
        simp [h]
      rw [hset, (measurePreserving_environment_translation μ
        ((⌊θ.1 + a.1⌋, ⌊θ.2 + a.2⌋) : Lattice)).measure_preimage hS.nullMeasurableSet,
        indicator_of_mem (show θ ∈ _ from h)]
    · have hset : Prod.mk θ ⁻¹' ((fun p : (ℝ × ℝ) × Environment =>
          ((Int.fract (p.1.1 + a.1), Int.fract (p.1.2 + a.2)),
            fun z : Lattice => p.2 ((⌊p.1.1 + a.1⌋, ⌊p.1.2 + a.2⌋) + z))) ⁻¹' A ×ˢ S) = ∅ := by
        ext ω
        simp [h]
      rw [hset, indicator_of_notMem (show θ ∉ _ from h)]
      simp
  simp_rw [hsection]
  rw [lintegral_indicator_const (hphase.measurable hA),
    hphase.measure_preimage hA.nullMeasurableSet, mul_comm]

end LPPDifferentiability
