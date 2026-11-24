/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Differentiability.FinalDraft.WitnessMultiplicity.Maximum
import Differentiability.Model.Paths.StageDefectTotal
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-! Stage weight bounds with the maximal witness count, for bounded and general weights. -/

public section

open scoped BigOperators

namespace LPPDifferentiability

namespace Path

private theorem stage_weight_le_with_cutoff {d : ℕ × ℕ} (p : Path 0 d) (ω : Environment)
    (a : ℝ) (ha : 0 < a) (ha1 : a < 1) (m : ℕ) (hm : 0 < m) (s : ℝ) (hs : 2 ≤ s)
    (η G0 dl dr K M0 : ℝ) (hη : 0 < η)
    (hstep : |G0| + |(dl + dr) / 2| + M0 ≤ η * s / 2)
    (k l : Fin (d.1 + d.2 + 1)) (hkl : k ≤ l)
    (hmin : ∀ t, k < t → t < l → t.val - k.val < 2 * m ∧
      |latticeTransverseCoordinate a (p.vertex t) - latticeTransverseCoordinate a (p.vertex k)| < s)
    {u : Lattice} {e : ℕ × ℕ} (y : Path u e)
    (hy : p.is_segment_at k.val y) (hyl : k.val + (e.1 + e.2) = l.val) :
    pathWeight ω y ≤ averageSupportingFunctional a G0 dl dr ((e.1 : ℝ), (e.2 : ℝ)) +
      η * s + 2 * η * s *
        (p.stageWitnessMultiplicity ω a m s η G0 dl dr K hm (by linarith) hη k l hkl : ℝ) +
      ∑ z ∈ y.collectedSites, max (ω z - M0) 0 := by
  obtain ⟨M, time, start, disp, q, hmem, hdisj, hbound⟩ :=
    p.stage_split_witnesses ω a ha ha1 m hm s hs η G0 dl dr M0 hη hstep k l hkl hmin
  have hfamily : p.has_stage_witness_family ω a m s η G0 dl dr K k l M := by
    refine ⟨time, start, disp, q, fun j => ?_, hdisj⟩
    exact ⟨(hmem j).1, (hmem j).2.1, (hmem j).2.2.1, Or.inl (hmem j).2.2.2⟩
  have hcount := p.le_stageWitnessMultiplicity_of_has_stage_witness_family hm
    (by linarith) hη hkl hfamily
  have hcast := (Nat.cast_le (α := ℝ)).mpr hcount
  have hcoeff := mul_le_mul_of_nonneg_left hcast (show 0 ≤ 2 * η * s by positivity)
  have hyb := hbound u e y hy hyl
  change _ ≤ averageSupportingFunctional a G0 dl dr ((e.1 : ℝ), (e.2 : ℝ)) -
    pathWeight ω y at hyb
  linarith only [hyb, hcoeff]

/-- Bounded-weight stage inequality in `lem:multiplicity`, including the remainder. -/
theorem stage_weight_le {d : ℕ × ℕ} (p : Path 0 d) (ω : Environment)
    (a : ℝ) (ha : 0 < a) (ha1 : a < 1) (m : ℕ) (hm : 0 < m) (s : ℝ) (hs : 2 ≤ s)
    (η G0 dl dr K M : ℝ) (hη : 0 < η) (hbounded : ∀ z, ω z ≤ M)
    (hstep : |G0| + |(dl + dr) / 2| + M ≤ η * s / 2)
    (k l : Fin (d.1 + d.2 + 1)) (hkl : k ≤ l)
    (hmin : ∀ t, k < t → t < l → t.val - k.val < 2 * m ∧
      |latticeTransverseCoordinate a (p.vertex t) - latticeTransverseCoordinate a (p.vertex k)| < s)
    {u : Lattice} {e : ℕ × ℕ} (y : Path u e)
    (hy : p.is_segment_at k.val y) (hyl : k.val + (e.1 + e.2) = l.val) :
    pathWeight ω y ≤ averageSupportingFunctional a G0 dl dr ((e.1 : ℝ), (e.2 : ℝ)) +
      η * s + 2 * η * s *
        (p.stageWitnessMultiplicity ω a m s η G0 dl dr K hm (by linarith) hη k l hkl : ℝ) := by
  have hexcess (z : Lattice) : max (ω z - M) 0 = 0 := max_eq_right (sub_nonpos.mpr (hbounded z))
  simpa only [hexcess, Finset.sum_const_zero, add_zero] using
    p.stage_weight_le_with_cutoff ω a ha ha1 m hm s hs η G0 dl dr K M hη hstep k l hkl hmin y hy hyl

/-- The stage inequality of `lem:multiplicity-general`, with the source cutoff. -/
theorem stage_weight_le_with_excess {d : ℕ × ℕ} (p : Path 0 d) (ω : Environment)
    (a : ℝ) (ha : 0 < a) (ha1 : a < 1) (m : ℕ) (hm : 0 < m) (s : ℝ) (hs : 2 ≤ s)
    (η G0 dl dr K : ℝ) (hη : 0 < η)
    (hscale : |G0| + |(dl + dr) / 2| ≤ η * s / 4)
    (k l : Fin (d.1 + d.2 + 1)) (hkl : k ≤ l)
    (hmin : ∀ t, k < t → t < l → t.val - k.val < 2 * m ∧
      |latticeTransverseCoordinate a (p.vertex t) - latticeTransverseCoordinate a (p.vertex k)| < s)
    {u : Lattice} {e : ℕ × ℕ} (y : Path u e)
    (hy : p.is_segment_at k.val y) (hyl : k.val + (e.1 + e.2) = l.val) :
    pathWeight ω y ≤ averageSupportingFunctional a G0 dl dr ((e.1 : ℝ), (e.2 : ℝ)) +
      η * s + 2 * η * s *
        (p.stageWitnessMultiplicity ω a m s η G0 dl dr K hm (by linarith) hη k l hkl : ℝ) +
      ∑ z ∈ y.collectedSites, max (ω z - η * s / 4) 0 :=
  p.stage_weight_le_with_cutoff ω a ha ha1 m hm s hs η G0 dl dr K (η * s / 4)
    hη (by linarith only [hscale]) k l hkl hmin y hy hyl

private theorem full_stage_weight_le_with_cutoff {d : ℕ × ℕ} (p : Path 0 d) (ω : Environment)
    (a : ℝ) (ha : 0 < a) (ha1 : a < 1) (m : ℕ) (hm : 0 < m) (s : ℝ) (hs : 2 ≤ s)
    (η G0 dl dr K M0 : ℝ) (hη : 0 < η) (hc : 2 * η ≤ (dl - dr) / 2)
    (hstep : |G0| + |(dl + dr) / 2| + M0 ≤ η * s / 2)
    (hK : 3 * η * s + |(dl + dr) / 2| * (2 * s + 2) < K * s)
    (k l : Fin (d.1 + d.2 + 1)) (hkl : k < l)
    (hcut : 2 * m ≤ l.val - k.val ∨
      s ≤ |latticeTransverseCoordinate a (p.vertex l) - latticeTransverseCoordinate a (p.vertex k)|)
    (hmin : ∀ t, k < t → t < l → t.val - k.val < 2 * m ∧
      |latticeTransverseCoordinate a (p.vertex t) - latticeTransverseCoordinate a (p.vertex k)| < s)
    {u : Lattice} {e : ℕ × ℕ} (y : Path u e)
    (hy : p.is_segment_at k.val y) (hyl : k.val + (e.1 + e.2) = l.val) :
    pathWeight ω y ≤ averageSupportingFunctional a G0 dl dr ((e.1 : ℝ), (e.2 : ℝ)) -
      η * s + 4 * η * s *
        (p.stageWitnessMultiplicity ω a m s η G0 dl dr K hm (by linarith) hη k l hkl.le : ℝ) +
      ∑ z ∈ y.collectedSites, max (ω z - M0) 0 := by
  obtain ⟨M, time, start, disp, q, hmem, hdisj, hbound⟩ :=
    p.full_stage_defect ω a ha ha1 m hm s hs η G0 dl dr K M0 hη hc hstep hK k l hkl hcut hmin
  have hfamily : p.has_stage_witness_family ω a m s η G0 dl dr K k l M :=
    ⟨time, start, disp, q, hmem, hdisj⟩
  have hcount := p.le_stageWitnessMultiplicity_of_has_stage_witness_family hm
    (by linarith) hη hkl.le hfamily
  have hcast := (Nat.cast_le (α := ℝ)).mpr hcount
  have hcoeff := mul_le_mul_of_nonneg_left hcast (show 0 ≤ 4 * η * s by positivity)
  have hyb := hbound u e y hy hyl
  change _ ≤ averageSupportingFunctional a G0 dl dr ((e.1 : ℝ), (e.2 : ℝ)) -
    pathWeight ω y at hyb
  linarith only [hyb, hcoeff]

/-- The bounded full-stage inequality in `lem:fulldefect`. -/
theorem full_stage_weight_le {d : ℕ × ℕ} (p : Path 0 d) (ω : Environment)
    (a : ℝ) (ha : 0 < a) (ha1 : a < 1) (m : ℕ) (hm : 0 < m) (s : ℝ) (hs : 2 ≤ s)
    (η G0 dl dr K M : ℝ) (hη : 0 < η) (hc : 2 * η ≤ (dl - dr) / 2) (hbounded : ∀ z, ω z ≤ M)
    (hstep : |G0| + |(dl + dr) / 2| + M ≤ η * s / 2)
    (hK : 3 * η * s + |(dl + dr) / 2| * (2 * s + 2) < K * s)
    (k l : Fin (d.1 + d.2 + 1)) (hkl : k < l)
    (hcut : 2 * m ≤ l.val - k.val ∨
      s ≤ |latticeTransverseCoordinate a (p.vertex l) - latticeTransverseCoordinate a (p.vertex k)|)
    (hmin : ∀ t, k < t → t < l → t.val - k.val < 2 * m ∧
      |latticeTransverseCoordinate a (p.vertex t) - latticeTransverseCoordinate a (p.vertex k)| < s)
    {u : Lattice} {e : ℕ × ℕ} (y : Path u e)
    (hy : p.is_segment_at k.val y) (hyl : k.val + (e.1 + e.2) = l.val) :
    pathWeight ω y ≤ averageSupportingFunctional a G0 dl dr ((e.1 : ℝ), (e.2 : ℝ)) -
      η * s + 4 * η * s *
        (p.stageWitnessMultiplicity ω a m s η G0 dl dr K hm (by linarith) hη k l hkl.le : ℝ) := by
  have hexcess (z : Lattice) : max (ω z - M) 0 = 0 := max_eq_right (sub_nonpos.mpr (hbounded z))
  simpa only [hexcess, Finset.sum_const_zero, add_zero] using
    p.full_stage_weight_le_with_cutoff ω a ha ha1 m hm s hs η G0 dl dr K M hη hc hstep hK
      k l hkl hcut hmin y hy hyl

/-- The general-weight full-stage inequality in `lem:multiplicity-general`. -/
theorem full_stage_weight_le_with_excess {d : ℕ × ℕ} (p : Path 0 d) (ω : Environment)
    (a : ℝ) (ha : 0 < a) (ha1 : a < 1) (m : ℕ) (hm : 0 < m) (s : ℝ) (hs : 2 ≤ s)
    (η G0 dl dr K : ℝ) (hη : 0 < η) (hc : 2 * η ≤ (dl - dr) / 2)
    (hscale : |G0| + |(dl + dr) / 2| ≤ η * s / 4)
    (hK : 3 * η * s + |(dl + dr) / 2| * (2 * s + 2) < K * s)
    (k l : Fin (d.1 + d.2 + 1)) (hkl : k < l)
    (hcut : 2 * m ≤ l.val - k.val ∨
      s ≤ |latticeTransverseCoordinate a (p.vertex l) - latticeTransverseCoordinate a (p.vertex k)|)
    (hmin : ∀ t, k < t → t < l → t.val - k.val < 2 * m ∧
      |latticeTransverseCoordinate a (p.vertex t) - latticeTransverseCoordinate a (p.vertex k)| < s)
    {u : Lattice} {e : ℕ × ℕ} (y : Path u e)
    (hy : p.is_segment_at k.val y) (hyl : k.val + (e.1 + e.2) = l.val) :
    pathWeight ω y ≤ averageSupportingFunctional a G0 dl dr ((e.1 : ℝ), (e.2 : ℝ)) -
      η * s + 4 * η * s *
        (p.stageWitnessMultiplicity ω a m s η G0 dl dr K hm (by linarith) hη k l hkl.le : ℝ) +
      ∑ z ∈ y.collectedSites, max (ω z - η * s / 4) 0 :=
  p.full_stage_weight_le_with_cutoff ω a ha ha1 m hm s hs η G0 dl dr K (η * s / 4)
    hη hc (by linarith only [hscale]) hK k l hkl hcut hmin y hy hyl

end Path

end LPPDifferentiability
