/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LPP_Foundations.Model.LastPassage.GeodesicSegments
public import Busemann.Geometry.LocallyRightmostGeodesic

/-! Maximizing segments underlying locally rightmost geodesics. -/

@[expose] public section

open LPPDifferentiability

namespace LPP.Busemann

/-- A locally rightmost geodesic has maximizing segments, using the same
finite displacement and path that witness its rightmost segment property. -/
theorem IsLocallyRightmostGeodesic.has_maximizing_segments
    {ω : Environment} {u : Lattice} {γ : ℕ → Lattice}
    (hγ : IsLocallyRightmostGeodesic ω u γ) :
    has_maximizing_segments ω γ := by
  intro m N hN
  rcases hγ.2.2 m N hN with ⟨d, p, hlength, hvertices, hweight, _hrightmost⟩
  exact ⟨d, p, hlength, hvertices, hweight⟩

end LPP.Busemann
