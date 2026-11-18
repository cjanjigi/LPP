/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Busemann.Frozen.StrongExistence.Definitions.TimeIndex
public import LPP_Foundations.Statements.ShapeDefinitions
public import LPP_Foundations.Statements.WeightMoments
public import Mathlib.Topology.Maps.Basic

import Busemann.Frozen.Variational.OneSidedBound
import Busemann.Process.CoalescingTiltSupport
import Busemann.Geometry.SupportOrder
import LPP_Foundations.Analysis.AbsoluteMomentShape
import Mathlib.Topology.MetricSpace.Antilipschitz
import Mathlib.Topology.MetricSpace.Pseudo.Constructions

/-! The time index has the strict order of the first H coordinate and
is an embedding, using the actual-support and support-order adapters. -/

@[expose] public section

open MeasureTheory LPPDifferentiability
open scoped ENNReal Topology

namespace LPP.Busemann

/-- The existing time index has exactly the strict order of the first tilt
coordinate, on the actual source H subtype. -/
theorem timeIndex_lt_iff_first_coordinate_lt
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : LPPStatements.NotAPointMass μ)
    (hmoment : LPPStatements.HasAbsoluteMomentAbove μ 2)
    (h k : CoalescingTilt μ) :
    (timeIndex μ h).val < (timeIndex μ k).val ↔ h.val.1 < k.val.1 := by
  classical
  obtain ⟨g, hg, _⟩ := exists_expected_rate_shape_le_cocycle_essSup μ hmoment
  have hGeometry := expected_rate_shape_geometry_of_absolute_moment μ g hmoment hg
  have hHomogeneous : ∀ (c : NNReal) (z : Quadrant),
      g (c • z) = (c : ℝ) * g z := by
    intro c z
    change g (c * z.1, c * z.2) = (c : ℝ) * g z
    exact hGeometry.2.1 c z
  let supports : CoalescingTilt μ → SupportTilt g := fun x =>
    Classical.choose (coalescingTilt_to_supportTilt μ hμ hmoment g hg x)
  have hSupportValue (x : CoalescingTilt μ) : (supports x).val = x.val :=
    Classical.choose_spec (coalescingTilt_to_supportTilt μ hμ hmoment g hg x)

  change h.val.1 - h.val.2 < k.val.1 - k.val.2 ↔ h.val.1 < k.val.1
  constructor
  · intro hTime
    by_contra hNotFirst
    have hReverse : k.val.1 ≤ h.val.1 := le_of_not_gt hNotFirst
    rcases lt_or_eq_of_le hReverse with hStrict | hEqual
    · have hStrictSupport : (supports k).val.1 < (supports h).val.1 := by
        rw [hSupportValue k, hSupportValue h]
        exact hStrict
      have hSupportOrder :=
        (supportTilt_coordinate_order g hHomogeneous (supports k) (supports h)).1
          hStrictSupport
      have hReverseTime : k.val.1 - k.val.2 < h.val.1 - h.val.2 := by
        simpa only [hSupportValue k, hSupportValue h] using hSupportOrder.2
      linarith
    · have hSameSupport : supports h = supports k :=
        (supportTilt_coordinate_order g hHomogeneous (supports h) (supports k)).2
          (by rw [hSupportValue h, hSupportValue k]; exact hEqual.symm)
      have hSameTime : h.val.1 - h.val.2 = k.val.1 - k.val.2 := by
        have hTimeEq := congrArg (fun s : SupportTilt g => s.val.1 - s.val.2) hSameSupport
        simpa only [hSupportValue h, hSupportValue k] using hTimeEq
      exact (ne_of_lt hTime) hSameTime
  · intro hFirst
    have hStrictSupport : (supports h).val.1 < (supports k).val.1 := by
      rw [hSupportValue h, hSupportValue k]
      exact hFirst
    have hSupportOrder :=
      (supportTilt_coordinate_order g hHomogeneous (supports h) (supports k)).1
        hStrictSupport
    simpa only [hSupportValue h, hSupportValue k] using hSupportOrder.2

/-- The existing time index is a topological embedding; its range is the
whole time-set subtype by the definition of `timeSet`. -/
theorem timeIndex_isEmbedding
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : LPPStatements.NotAPointMass μ)
    (hmoment : LPPStatements.HasAbsoluteMomentAbove μ 2) :
    Topology.IsEmbedding (timeIndex μ) := by
  classical
  obtain ⟨g, hg, _⟩ := exists_expected_rate_shape_le_cocycle_essSup μ hmoment
  have hGeometry := expected_rate_shape_geometry_of_absolute_moment μ g hmoment hg
  have hHomogeneous : ∀ (c : NNReal) (z : Quadrant),
      g (c • z) = (c : ℝ) * g z := by
    intro c z
    change g (c * z.1, c * z.2) = (c : ℝ) * g z
    exact hGeometry.2.1 c z
  let supports : CoalescingTilt μ → SupportTilt g := fun x =>
    Classical.choose (coalescingTilt_to_supportTilt μ hμ hmoment g hg x)
  have hSupportValue (x : CoalescingTilt μ) : (supports x).val = x.val :=
    Classical.choose_spec (coalescingTilt_to_supportTilt μ hμ hmoment g hg x)
  let τ : CoalescingTilt μ → ℝ := fun x => (timeIndex μ x).val
  let scalarTime : ℝ × ℝ → ℝ := fun x => x.1 - x.2
  have hτSupport (x : CoalescingTilt μ) : τ x = scalarTime (supports x).val := by
    change x.val.1 - x.val.2 = (supports x).val.1 - (supports x).val.2
    rw [← hSupportValue x]

  have hOrderedBound (a b : SupportTilt g) (hab : a.val.1 ≤ b.val.1) :
      |a.val.1 - b.val.1| ≤ |scalarTime b.val - scalarTime a.val| ∧
      |a.val.2 - b.val.2| ≤ |scalarTime b.val - scalarTime a.val| := by
    rcases lt_or_eq_of_le hab with hStrict | hEqual
    · have hSecond : b.val.2 < a.val.2 :=
        (supportTilt_coordinate_order g hHomogeneous a b).1 hStrict |>.1
      have hGap : scalarTime b.val - scalarTime a.val =
          (b.val.1 - a.val.1) + (a.val.2 - b.val.2) := by
        simp only [scalarTime]
        ring
      have hGapNonneg : 0 ≤ scalarTime b.val - scalarTime a.val := by
        rw [hGap]
        exact add_nonneg (sub_nonneg.mpr hStrict.le) (sub_nonneg.mpr hSecond.le)
      constructor
      · calc
          |a.val.1 - b.val.1| = b.val.1 - a.val.1 := by
            rw [abs_of_nonpos (sub_nonpos.mpr hab)]
            ring
          _ ≤ (b.val.1 - a.val.1) + (a.val.2 - b.val.2) :=
            le_add_of_nonneg_right (sub_nonneg.mpr hSecond.le)
          _ = scalarTime b.val - scalarTime a.val := hGap.symm
          _ = |scalarTime b.val - scalarTime a.val| :=
            (abs_of_nonneg hGapNonneg).symm
      · calc
          |a.val.2 - b.val.2| = a.val.2 - b.val.2 :=
            abs_of_nonneg (sub_nonneg.mpr hSecond.le)
          _ ≤ (b.val.1 - a.val.1) + (a.val.2 - b.val.2) :=
            le_add_of_nonneg_left (sub_nonneg.mpr hStrict.le)
          _ = scalarTime b.val - scalarTime a.val := hGap.symm
          _ = |scalarTime b.val - scalarTime a.val| :=
            (abs_of_nonneg hGapNonneg).symm
    · have hSame : a = b :=
        (supportTilt_coordinate_order g hHomogeneous a b).2 hEqual
      rw [hSame]
      simp

  have hCoordinateBounds (x y : CoalescingTilt μ) :
      |x.val.1 - y.val.1| ≤ |τ x - τ y| ∧
      |x.val.2 - y.val.2| ≤ |τ x - τ y| := by
    rcases le_total (supports x).val.1 (supports y).val.1 with hxy | hyx
    · have hbound := hOrderedBound (supports x) (supports y) hxy
      rw [← hτSupport x, ← hτSupport y] at hbound
      rw [hSupportValue x, hSupportValue y] at hbound
      have hAbsTime : |τ y - τ x| = |τ x - τ y| := abs_sub_comm _ _
      exact ⟨hbound.1.trans_eq hAbsTime, hbound.2.trans_eq hAbsTime⟩
    · have hbound := hOrderedBound (supports y) (supports x) hyx
      rw [← hτSupport x, ← hτSupport y] at hbound
      rw [hSupportValue y, hSupportValue x] at hbound
      refine ⟨?_, ?_⟩
      · calc
          |x.val.1 - y.val.1| = |y.val.1 - x.val.1| := abs_sub_comm _ _
          _ ≤ |τ x - τ y| := hbound.1
      · calc
          |x.val.2 - y.val.2| = |y.val.2 - x.val.2| := abs_sub_comm _ _
          _ ≤ |τ x - τ y| := hbound.2

  have hDistance (x y : CoalescingTilt μ) :
      dist x y ≤ dist (timeIndex μ x) (timeIndex μ y) := by
    have hbound := hCoordinateBounds x y
    calc
      dist x y = max (|x.val.1 - y.val.1|) (|x.val.2 - y.val.2|) := by
        rw [Subtype.dist_eq, Prod.dist_eq, Real.dist_eq, Real.dist_eq]
      _ ≤ |τ x - τ y| := max_le_iff.mpr hbound
      _ = dist (timeIndex μ x) (timeIndex μ y) := by
        rw [Subtype.dist_eq, Real.dist_eq]
  have hAntilipschitz : AntilipschitzWith (1 : NNReal) (timeIndex μ) := by
    apply AntilipschitzWith.of_le_mul_dist
    intro x y
    simpa using hDistance x y

  have hScalarContinuous :
      Continuous (fun x : CoalescingTilt μ => x.val.1 - x.val.2) :=
    (continuous_fst.sub continuous_snd).comp continuous_subtype_val
  have hTimeMembership (x : CoalescingTilt μ) :
      x.val.1 - x.val.2 ∈ timeSet μ := ⟨x, rfl⟩
  have hContinuous : Continuous (timeIndex μ) := by
    change Continuous (fun x : CoalescingTilt μ =>
      (⟨x.val.1 - x.val.2, hTimeMembership x⟩ : {t : ℝ // t ∈ timeSet μ}))
    exact Continuous.subtype_mk hScalarContinuous hTimeMembership

  exact hAntilipschitz.isEmbedding hContinuous

end LPP.Busemann
