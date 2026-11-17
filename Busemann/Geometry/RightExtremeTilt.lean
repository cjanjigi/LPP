/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Busemann.Frozen.Definitions.SupportTilt
import Busemann.Geometry.ExtremeCoordinateTilts
import Busemann.Geometry.SupportIdentities

/-! # The negative right coordinate-gradient support -/

public section

open Set LPPDifferentiability
open scoped NNReal

namespace LPP.Busemann.Proof

/-- The negative right coordinate-gradient pair is the unique support with
greatest first tilt coordinate. This proves JR1810.03580v3,
Section 2.3 and Lemma 4.7(c). -/
theorem exists_unique_right_extreme_tilt
    (g : Quadrant → ℝ)
    (hconc : ∀ (x y : Quadrant) (r s : ℝ≥0), r + s = 1 →
      (r : ℝ) * g x + (s : ℝ) * g y ≤ g (r • x + s • y))
    (hhom : ∀ (c : ℝ≥0) (z : Quadrant),
      g (c • z) = (c : ℝ) * g z)
    (ξ : InteriorDirection) :
    ∃! h : SupportTilt g,
      SupportsAt g ξ h.1 ∧
      ∀ k : SupportTilt g,
        SupportsAt g ξ k.1 → k.1.1 ≤ h.1.1 := by
  let a : ℝ := (ξ.1.1 : ℝ)
  let U1 : ℝ → ℝ := fun t => quadrantExtension g (a + t, 1 - a)
  let U2 : ℝ → ℝ := fun t => quadrantExtension g (a, 1 - a + t)
  let pair : ℝ × ℝ :=
    (-derivWithin U1 (Ioi 0) 0, -derivWithin U2 (Iio 0) 0)
  have hpair := coordinate_extreme_tilts_support_and_order g hconc hhom ξ
  -- Package the literal coordinate-gradient pair using its actual contact at ξ.
  let h : SupportTilt g := ⟨pair, ⟨ξ, hpair.2.1⟩⟩
  have hproperty : SupportsAt g ξ h.1 ∧
      ∀ k : SupportTilt g, SupportsAt g ξ k.1 → k.1.1 ≤ h.1.1 := by
    refine ⟨hpair.2.1, ?_⟩
    intro k hk
    exact (hpair.2.2 k.1 hk).2
  refine ⟨h, hproperty, ?_⟩
  -- Extremality fixes the first coordinate; Euler contact fixes the second.
  intro k hk
  apply Subtype.ext
  apply supporting_tilts_eq_of_first_coord_eq g ξ k.1 h.1 hhom hk.1 hproperty.1
  exact le_antisymm (hproperty.2 k hk.1) (hk.2 h hproperty.1)

end LPP.Busemann.Proof
