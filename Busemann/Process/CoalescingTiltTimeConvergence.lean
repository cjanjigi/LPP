/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Busemann.Frozen.Definitions.CoalescingTilt
public import Martin2004.Statements.ShapeFacts
public import Mathlib.Topology.MetricSpace.Cauchy

import Busemann.Frozen.Variational.OneSidedBound
import Busemann.Process.CoalescingTiltSupport
import Busemann.Geometry.SupportOrder
import LPP_Foundations.Analysis.AbsoluteMomentShape

/-! Scalar-time convergence controls both coordinates of actual H tilts. -/

@[expose] public section

open MeasureTheory Filter LPPDifferentiability
open scoped ENNReal NNReal Topology

namespace LPP.Busemann

/-- A convergent sequence of H times has a subsequence whose two tilt
coordinates converge to a finite pair. The support order controls both coordinates through the scalar time. -/
theorem exists_coalescing_tilt_subseq_of_time_tendsto
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : LPPStatements.NotAPointMass μ)
    (hmoment : ∃ p : ℝ, 2 < p ∧
      (∫⁻ t, ENNReal.ofReal (|t| ^ p) ∂μ) < ∞)
    (hs : ℕ → CoalescingTilt μ) (t : ℝ)
    (ht : Tendsto (fun n => (hs n).val.1 - (hs n).val.2) atTop (𝓝 t)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∃ h : ℝ × ℝ,
        Tendsto (fun n => (hs (φ n)).val) atTop (𝓝 h) ∧
          t = h.1 - h.2 := by
  classical
  obtain ⟨g, hg, _⟩ := exists_expected_rate_shape_le_cocycle_essSup μ hmoment
  have hGeometry := expected_rate_shape_geometry_of_absolute_moment μ g hmoment hg
  have hHomogeneous : ∀ (c : ℝ≥0) (z : Quadrant),
      g (c • z) = (c : ℝ) * g z := by
    intro c z
    change g (c * z.1, c * z.2) = (c : ℝ) * g z
    exact hGeometry.2.1 c z

  -- Each H witness gives an actual interior-contact support tilt.
  let supports : ℕ → SupportTilt g := fun n =>
    Classical.choose (coalescingTilt_to_supportTilt μ hμ hmoment g hg (hs n))
  have hSupportValue (n : ℕ) : (supports n).val = (hs n).val :=
    Classical.choose_spec
      (coalescingTilt_to_supportTilt μ hμ hmoment g hg (hs n))
  let scalarTime : ℝ × ℝ → ℝ := fun x => x.1 - x.2
  let τ : ℕ → ℝ := fun n => scalarTime (hs n).val
  have hτSupport (n : ℕ) : τ n = scalarTime (supports n).val := by
    change (hs n).val.1 - (hs n).val.2 =
      (supports n).val.1 - (supports n).val.2
    rw [← hSupportValue n]

  -- Support order bounds both coordinate gaps by the scalar-time gap.
  have hOrderedBound (a b : SupportTilt g) (hab : a.val.1 ≤ b.val.1) :
      |a.val.1 - b.val.1| ≤ |scalarTime b.val - scalarTime a.val| ∧
      |a.val.2 - b.val.2| ≤ |scalarTime b.val - scalarTime a.val| := by
    rcases lt_or_eq_of_le hab with hlt | heq
    · have hSecond : b.val.2 < a.val.2 :=
        (supportTilt_coordinate_order g hHomogeneous a b).1 hlt |>.1
      have hGap : scalarTime b.val - scalarTime a.val =
          (b.val.1 - a.val.1) + (a.val.2 - b.val.2) := by
        simp only [scalarTime]
        ring
      have hGapNonneg : 0 ≤ scalarTime b.val - scalarTime a.val := by
        rw [hGap]
        exact add_nonneg (sub_nonneg.mpr hlt.le) (sub_nonneg.mpr hSecond.le)
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
            le_add_of_nonneg_left (sub_nonneg.mpr hlt.le)
          _ = scalarTime b.val - scalarTime a.val := hGap.symm
          _ = |scalarTime b.val - scalarTime a.val| :=
            (abs_of_nonneg hGapNonneg).symm
    · have hab : a = b :=
        (supportTilt_coordinate_order g hHomogeneous a b).2 heq
      rw [hab]
      simp

  have hCoordinateBound (m n : ℕ) :
      |(hs m).val.1 - (hs n).val.1| ≤ |τ m - τ n| ∧
      |(hs m).val.2 - (hs n).val.2| ≤ |τ m - τ n| := by
    rcases le_total (supports m).val.1 (supports n).val.1 with hmn | hnm
    · have hbound := hOrderedBound (supports m) (supports n) hmn
      rw [← hτSupport m, ← hτSupport n] at hbound
      rw [hSupportValue m, hSupportValue n] at hbound
      have hAbsTime : |τ n - τ m| = |τ m - τ n| := abs_sub_comm _ _
      exact ⟨hbound.1.trans_eq hAbsTime, hbound.2.trans_eq hAbsTime⟩
    · have hbound := hOrderedBound (supports n) (supports m) hnm
      rw [← hτSupport m, ← hτSupport n] at hbound
      rw [hSupportValue n, hSupportValue m] at hbound
      refine ⟨?_, ?_⟩
      · calc
          |(hs m).val.1 - (hs n).val.1| =
              |(hs n).val.1 - (hs m).val.1| := abs_sub_comm _ _
          _ ≤ |τ m - τ n| := hbound.1
      · calc
          |(hs m).val.2 - (hs n).val.2| =
              |(hs n).val.2 - (hs m).val.2| := abs_sub_comm _ _
          _ ≤ |τ m - τ n| := hbound.2

  -- The scalar limit makes the scalar sequence Cauchy, then each coordinate is Cauchy.
  have hτLimit : Tendsto τ atTop (𝓝 t) := ht
  have hτCauchy : CauchySeq τ := hτLimit.cauchySeq
  have hFirstCauchy : CauchySeq (fun n : ℕ => (hs n).val.1) := by
    apply Metric.cauchySeq_iff.mpr
    intro ε hε
    obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hτCauchy ε hε
    refine ⟨N, ?_⟩
    intro m hm n hn
    have hbound := (hCoordinateBound m n).1
    calc
      dist ((hs m).val.1) ((hs n).val.1) =
          |(hs m).val.1 - (hs n).val.1| := Real.dist_eq _ _
      _ ≤ |τ m - τ n| := hbound
      _ = dist (τ m) (τ n) := (Real.dist_eq _ _).symm
      _ < ε := hN m hm n hn
  have hSecondCauchy : CauchySeq (fun n : ℕ => (hs n).val.2) := by
    apply Metric.cauchySeq_iff.mpr
    intro ε hε
    obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hτCauchy ε hε
    refine ⟨N, ?_⟩
    intro m hm n hn
    have hbound := (hCoordinateBound m n).2
    calc
      dist ((hs m).val.2) ((hs n).val.2) =
          |(hs m).val.2 - (hs n).val.2| := Real.dist_eq _ _
      _ ≤ |τ m - τ n| := hbound
      _ = dist (τ m) (τ n) := (Real.dist_eq _ _).symm
      _ < ε := hN m hm n hn

  -- Completeness of the real pair gives a finite limit for the original tilt sequence.
  have hPairCauchy : CauchySeq (fun n : ℕ => (hs n).val) := by
    convert hFirstCauchy.prodMk hSecondCauchy using 1
  obtain ⟨hLimit, hPairLimit⟩ := cauchySeq_tendsto_of_complete hPairCauchy
  have hTimeOfPair : Tendsto τ atTop (𝓝 (scalarTime hLimit)) := by
    exact (continuous_fst.sub continuous_snd).continuousAt.tendsto.comp hPairLimit
  have hTimeIdentity : t = hLimit.1 - hLimit.2 := by
    have hUnique := tendsto_nhds_unique hτLimit hTimeOfPair
    exact hUnique

  -- The identity index is a strictly monotone subsequence of the convergent pair sequence.
  exact ⟨id, strictMono_id, hLimit, hPairLimit, hTimeIdentity⟩

end LPP.Busemann
