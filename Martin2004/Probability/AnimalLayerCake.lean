/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Mathlib.MeasureTheory.Integral.Lebesgue.Add
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Order.Lattice
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

/-!
# Layer cake for finite families of finite site sets

The count at level `t` uses the strict site threshold `t < w v`. For a finite
nonempty family, the maximum of the weights is bounded by the integral of the
maximum threshold count. The maximum remains attached to its nonempty family.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal BigOperators

namespace LPPDifferentiability

/-- The number of sites in `U` whose weight is strictly above `t`, as an `ENNReal`. -/
noncomputable def animalThresholdCount {α : Type*} (U : Finset α) (w : α → ℝ) (t : ℝ) : ℝ≥0∞ :=
  ∑ v ∈ U, (Iio (w v)).indicator (fun _ => (1 : ℝ≥0∞)) t

/-- The largest strict-threshold count in an explicitly nonempty finite family. -/
noncomputable def animalThresholdMaximum {α : Type*} (H : Finset (Finset α))
    (hH : H.Nonempty) (w : α → ℝ) (t : ℝ) : ℝ≥0∞ :=
  H.sup' hH (fun U => animalThresholdCount U w t)

private theorem lintegral_strict_interval (x : ℝ) :
    ∫⁻ t in Ioi (0 : ℝ), (Iio x).indicator (fun _ => (1 : ℝ≥0∞)) t ∂volume =
      ENNReal.ofReal x := by
  rw [setLIntegral_indicator measurableSet_Iio]
  rw [show Iio x ∩ Ioi (0 : ℝ) = Ioo 0 x by
    ext t
    simp only [mem_inter_iff, mem_Iio, mem_Ioi, mem_Ioo]
    constructor <;> intro h <;> exact ⟨h.2, h.1⟩]
  rw [setLIntegral_const, Real.volume_Ioo]
  simp

/-- For a fixed finite set, summing the strict-threshold indicators gives its total weight. -/
theorem animalThresholdCount_lintegral {α : Type*} (U : Finset α) (w : α → ℝ)
    (_hw : ∀ v ∈ U, 0 ≤ w v) :
    (∑ v ∈ U, ENNReal.ofReal (w v)) =
      ∫⁻ t in Ioi (0 : ℝ), animalThresholdCount U w t ∂volume := by
  classical
  unfold animalThresholdCount
  rw [lintegral_finsetSum]
  · apply Finset.sum_congr rfl
    intro v hv
    exact (lintegral_strict_interval (w v)).symm
  · intro v hv
    exact measurable_const.indicator measurableSet_Iio

/-- The maximum total weight over a nonempty finite family is bounded by the
integral of the maximum strict-threshold count. -/
theorem finite_animalThresholdMaximum_lintegral {α : Type*}
    (H : Finset (Finset α)) (hH : H.Nonempty) (w : α → ℝ) (hw : ∀ v, 0 ≤ w v) :
    H.sup' hH (fun U => ∑ v ∈ U, ENNReal.ofReal (w v)) ≤
      ∫⁻ t in Ioi (0 : ℝ), animalThresholdMaximum H hH w t ∂volume := by
  classical
  rw [Finset.sup'_le_iff]
  intro U hU
  calc
    (∑ v ∈ U, ENNReal.ofReal (w v)) =
        ∫⁻ t in Ioi (0 : ℝ), animalThresholdCount U w t ∂volume :=
      animalThresholdCount_lintegral U w (fun v hv => hw v)
    _ ≤ ∫⁻ t in Ioi (0 : ℝ), animalThresholdMaximum H hH w t ∂volume := by
      apply lintegral_mono
      intro t
      unfold animalThresholdMaximum
      exact Finset.le_sup' (f := fun V => animalThresholdCount V w t) hU

/-- The strict-threshold maximum is jointly measurable for measurable random weights. -/
theorem measurable_animalThresholdMaximum {Ω α : Type*} [MeasurableSpace Ω]
    (H : Finset (Finset α)) (hH : H.Nonempty) (w : Ω → α → ℝ)
    (hw : ∀ v, Measurable (fun ω => w ω v)) :
    Measurable (fun p : Ω × ℝ =>
      animalThresholdMaximum H hH (fun v => w p.1 v) p.2) := by
  classical
  unfold animalThresholdMaximum
  let F : Finset α → Ω × ℝ → ℝ≥0∞ := fun U p =>
    animalThresholdCount U (fun v => w p.1 v) p.2
  have hF : (fun p : Ω × ℝ => H.sup' hH (fun U => F U p)) = H.sup' hH F := by
    funext p
    exact (Finset.sup'_apply hH F p).symm
  change Measurable (fun p : Ω × ℝ => H.sup' hH (fun U => F U p))
  rw [hF]
  apply Finset.measurable_sup' hH
  intro U hU
  dsimp [F]
  unfold animalThresholdCount
  apply Finset.measurable_fun_sum
  intro v hv
  have hs : MeasurableSet {p : Ω × ℝ | p.2 < w p.1 v} :=
    measurableSet_lt measurable_snd ((hw v).comp measurable_fst)
  have hfun :
      (fun p : Ω × ℝ => (Iio (w p.1 v)).indicator (fun _ => (1 : ℝ≥0∞)) p.2) =
        ({p : Ω × ℝ | p.2 < w p.1 v}.indicator (fun _ => (1 : ℝ≥0∞))) := by
    funext p
    simp only [indicator_apply, Set.mem_ofPred_eq, mem_Iio]
  rw [hfun]
  exact measurable_const.indicator hs

end LPPDifferentiability
