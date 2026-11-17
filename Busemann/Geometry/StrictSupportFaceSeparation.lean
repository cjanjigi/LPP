/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Busemann.Frozen.Definitions.SupportFacesUnion
import Busemann.Geometry.SupportIdentities
import Busemann.Geometry.SupportOrder
import Busemann.Geometry.SupportFaceIntervals
import Busemann.Geometry.SupportFaceCompactness
import Mathlib.Tactic.Linarith

/-! Strict separation of a compact support face from a ray beyond a maximal face. -/

public section

open LPPDifferentiability
open scoped NNReal

namespace LPP.Busemann

/-- For two ordered interior contact directions, the first coordinate of the
left support tilt does not exceed that of the right support tilt. -/
theorem support_first_coord_le_of_direction_lt
    (g : Quadrant → ℝ)
    (hhom : ∀ (c : ℝ≥0) (z : Quadrant), g (c • z) = (c : ℝ) * g z)
    (q t : InteriorDirection) (h k : SupportTilt g)
    (hqt : (q.1.1 : ℝ) < (t.1.1 : ℝ))
    (hq : SupportsAt g q h.1) (ht : SupportsAt g t k.1) :
    h.1.1 ≤ k.1.1 := by
  by_contra hnot
  have hkfirst : k.1.1 < h.1.1 := lt_of_not_ge hnot
  have hkslope : k.1.1 - k.1.2 < h.1.1 - h.1.2 :=
    ((supportTilt_coordinate_order g hhom k h).1 hkfirst).2
  have hpositive :
      0 < ((h.1.1 - h.1.2) - (k.1.1 - k.1.2)) *
        ((t.1.1 : ℝ) - (q.1.1 : ℝ)) :=
    mul_pos (sub_pos.mpr hkslope) (sub_pos.mpr hqt)
  have hqsecond :
      (q.1.2 : ℝ) - (t.1.2 : ℝ) =
        -((q.1.1 : ℝ) - (t.1.1 : ℝ)) := by
    linarith only [q.2.2.2, t.2.2.2]
  have htsecond :
      (t.1.2 : ℝ) - (q.1.2 : ℝ) =
        -((t.1.1 : ℝ) - (q.1.1 : ℝ)) := by
    linarith only [q.2.2.2, t.2.2.2]
  have hqbound := hq t.1
  have htbound := ht q.1
  rw [hqsecond] at hqbound
  rw [htsecond] at htbound
  nlinarith only [hqbound, htbound, hpositive]

/-- A support at a direction beyond the maximal right face at `q` has a
compact contact face uniformly to the right of `q`. -/
theorem exists_strict_threshold_right_of_maximal_support_face
    (g : Quadrant → ℝ) (hgcont : Continuous g)
    (hconc : ∀ (x y : Quadrant) (a b : ℝ≥0), a + b = 1 →
      (a : ℝ) * g x + (b : ℝ) * g y ≤ g (a • x + b • y))
    (hhom : ∀ (c : ℝ≥0) (z : Quadrant),
      g (c • z) = (c : ℝ) * g z)
    (q right t : InteriorDirection) (hR h : SupportTilt g)
    (hqR : SupportsAt g q hR.1)
    (hRmax : ∀ k : SupportTilt g,
      SupportsAt g q k.1 → k.1.1 ≤ hR.1.1)
    (hRface : ∀ ζ ∈ supportFace g hR,
      (ζ.1.1 : ℝ) ≤ (right.1.1 : ℝ))
    (ht : SupportsAt g t h.1)
    (hrt : (right.1.1 : ℝ) < (t.1.1 : ℝ))
    (hgap₁ : g (1, 0) < -h.1.1)
    (hgap₂ : g (0, 1) < -h.1.2) :
    ∃ θ : ℝ, 0 ≤ θ ∧ θ < 1 ∧
      (q.1.1 : ℝ) < θ ∧
      ∀ ζ ∈ supportFace g h, θ < (ζ.1.1 : ℝ) := by
  have hqr : (q.1.1 : ℝ) ≤ (right.1.1 : ℝ) := hRface q hqR
  have hqt : (q.1.1 : ℝ) < (t.1.1 : ℝ) := lt_of_le_of_lt hqr hrt
  have hstrict : ∀ ζ ∈ supportFace g h, (q.1.1 : ℝ) < (ζ.1.1 : ℝ) := by
    intro ζ hζ
    by_contra hnot
    have hζq : ζ.1.1 ≤ q.1.1 := by exact_mod_cast le_of_not_gt hnot
    have hqt' : q.1.1 ≤ t.1.1 := by exact_mod_cast le_of_lt hqt
    have hq : SupportsAt g q h.1 :=
      supportFace_mem_of_between g hconc hhom h ζ t q hζ ht hζq hqt'
    have hRle : hR.1.1 ≤ h.1.1 :=
      support_first_coord_le_of_direction_lt g hhom q t hR h hqt hqR ht
    have hle : h.1.1 ≤ hR.1.1 := hRmax h hq
    have heq : hR = h :=
      (supportTilt_coordinate_order g hhom hR h).2 (le_antisymm hRle hle)
    have htf0 : t ∈ supportFace g h := ht
    have htf : t ∈ supportFace g hR := by simpa only [heq] using htf0
    exact (not_lt_of_ge (hRface t htf)) hrt
  obtain ⟨u, ⟨hu, hmin⟩, _⟩ :=
    (supportFacesUnion_compact_nonempty_extrema_of_strict_axis_gaps
      g hgcont hhom h h hgap₁ hgap₂ hgap₁ hgap₂).2.2.1
  have hu' : u ∈ supportFace g h := hu.elim id id
  have hqu : (q.1.1 : ℝ) < (u.1.1 : ℝ) := hstrict u hu'
  have hq0 : 0 ≤ (q.1.1 : ℝ) := NNReal.coe_nonneg _
  have hu1 : (u.1.1 : ℝ) < 1 := by
    have hu2 : 0 < (u.1.2 : ℝ) := by exact_mod_cast u.2.2.1
    linarith only [u.2.2.2, hu2]
  refine ⟨((q.1.1 : ℝ) + (u.1.1 : ℝ)) / 2, ?_, ?_, ?_, ?_⟩
  · linarith only [hq0, hqu]
  · linarith only [hqu, hu1]
  · linarith only [hqu]
  · intro ζ hζ
    have huζ : (u.1.1 : ℝ) ≤ (ζ.1.1 : ℝ) := hmin ζ (Or.inl hζ)
    linarith only [hqu, huζ]

/-- A support at a direction beyond the maximal left face at `q` has a
compact contact face uniformly to the left of `q`. -/
theorem exists_strict_threshold_left_of_minimal_support_face
    (g : Quadrant → ℝ) (hgcont : Continuous g)
    (hconc : ∀ (x y : Quadrant) (a b : ℝ≥0), a + b = 1 →
      (a : ℝ) * g x + (b : ℝ) * g y ≤ g (a • x + b • y))
    (hhom : ∀ (c : ℝ≥0) (z : Quadrant),
      g (c • z) = (c : ℝ) * g z)
    (q left t : InteriorDirection) (hL h : SupportTilt g)
    (hqL : SupportsAt g q hL.1)
    (hLmin : ∀ k : SupportTilt g,
      SupportsAt g q k.1 → hL.1.1 ≤ k.1.1)
    (hLface : ∀ ζ ∈ supportFace g hL,
      (left.1.1 : ℝ) ≤ (ζ.1.1 : ℝ))
    (ht : SupportsAt g t h.1)
    (htl : (t.1.1 : ℝ) < (left.1.1 : ℝ))
    (hgap₁ : g (1, 0) < -h.1.1)
    (hgap₂ : g (0, 1) < -h.1.2) :
    ∃ θ : ℝ, 0 ≤ θ ∧ θ < 1 ∧
      θ < (q.1.1 : ℝ) ∧
      ∀ ζ ∈ supportFace g h, (ζ.1.1 : ℝ) < θ := by
  have hlq : (left.1.1 : ℝ) ≤ (q.1.1 : ℝ) := hLface q hqL
  have htq : (t.1.1 : ℝ) < (q.1.1 : ℝ) := lt_of_lt_of_le htl hlq
  have hstrict : ∀ ζ ∈ supportFace g h, (ζ.1.1 : ℝ) < (q.1.1 : ℝ) := by
    intro ζ hζ
    by_contra hnot
    have hqζ : q.1.1 ≤ ζ.1.1 := by exact_mod_cast le_of_not_gt hnot
    have htq' : t.1.1 ≤ q.1.1 := by exact_mod_cast le_of_lt htq
    have hq : SupportsAt g q h.1 :=
      supportFace_mem_of_between g hconc hhom h t ζ q ht hζ htq' hqζ
    have hle : h.1.1 ≤ hL.1.1 :=
      support_first_coord_le_of_direction_lt g hhom t q h hL htq ht hqL
    have hLle : hL.1.1 ≤ h.1.1 := hLmin h hq
    have heq : hL = h :=
      (supportTilt_coordinate_order g hhom hL h).2 (le_antisymm hLle hle)
    have htf0 : t ∈ supportFace g h := ht
    have htf : t ∈ supportFace g hL := by simpa only [heq] using htf0
    exact (not_lt_of_ge (hLface t htf)) htl
  obtain ⟨u, ⟨hu, hmax⟩, _⟩ :=
    (supportFacesUnion_compact_nonempty_extrema_of_strict_axis_gaps
      g hgcont hhom h h hgap₁ hgap₂ hgap₁ hgap₂).2.2.2
  have hu' : u ∈ supportFace g h := hu.elim id id
  have huq : (u.1.1 : ℝ) < (q.1.1 : ℝ) := hstrict u hu'
  have hu0 : 0 ≤ (u.1.1 : ℝ) := NNReal.coe_nonneg _
  have hq1 : (q.1.1 : ℝ) < 1 := by
    have hq2 : 0 < (q.1.2 : ℝ) := by exact_mod_cast q.2.2.1
    linarith only [q.2.2.2, hq2]
  refine ⟨((u.1.1 : ℝ) + (q.1.1 : ℝ)) / 2, ?_, ?_, ?_, ?_⟩
  · linarith only [hu0, huq]
  · linarith only [huq, hq1]
  · linarith only [huq]
  · intro ζ hζ
    have hζu : (ζ.1.1 : ℝ) ≤ (u.1.1 : ℝ) := hmax ζ (Or.inl hζ)
    linarith only [huq, hζu]

end LPP.Busemann
