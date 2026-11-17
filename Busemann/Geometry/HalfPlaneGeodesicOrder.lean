/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Busemann.Geometry.GeodesicOrder
public import LPP_Foundations.Model.LastPassage.Locality
import Lean.Elab.Tactic.Omega

/-! Order of locally rightmost rays in environments agreeing above the axis. -/

@[expose] public section

open LPPDifferentiability

namespace LPP.Busemann

private theorem locallyRightmost_nonnegative_height
    {ω : Environment} {γ : ℕ → Lattice}
    (hγ : IsLocallyRightmostGeodesic ω (0, 0) γ) (n : ℕ) :
    0 ≤ (γ n).2 := by
  induction n with
  | zero =>
      rw [hγ.1]
  | succ n ih =>
      rcases hγ.2.1 n with hEast | hNorth
      · rw [hEast]
        simp only [Prod.snd_add, add_zero]
        exact ih
      · rw [hNorth]
        simp only [Prod.snd_add]
        omega

private theorem locallyRightmost_transfer_of_nonnegative_height_agreement
    (ω η : Environment)
    (hagree : ∀ z : Lattice, 0 ≤ z.2 → ω z = η z)
    (δ : ℕ → Lattice)
    (hδ : IsLocallyRightmostGeodesic η (0, 0) δ) :
    IsLocallyRightmostGeodesic ω (0, 0) δ := by
  refine ⟨hδ.1, hδ.2.1, ?_⟩
  intro m N hN
  obtain ⟨d, p, hd, htrace, hmax, hgreatest⟩ := hδ.2.2 m N hN
  have hrectangle :
      Set.EqOn ω η
        (Set.Icc (δ m) (δ m + ((d.1 : ℤ), (d.2 : ℤ)))) := by
    intro z hz
    apply hagree z
    exact (locallyRightmost_nonnegative_height hδ m).trans hz.1.2
  have hpath : pathWeight ω p = pathWeight η p :=
    pathWeight_eq_of_eqOn hrectangle p
  have hpassage : lastPassage ω (δ m) d = lastPassage η (δ m) d :=
    lastPassage_eq_of_eqOn hrectangle
  refine ⟨d, p, hd, htrace, ?_, ?_⟩
  · calc
      pathWeight ω p = pathWeight η p := hpath
      _ = lastPassage η (δ m) d := hmax
      _ = lastPassage ω (δ m) d := hpassage.symm
  · intro q hq i
    have hqη : pathWeight η q = lastPassage η (δ m) d := by
      calc
        pathWeight η q = pathWeight ω q :=
          (pathWeight_eq_of_eqOn hrectangle q).symm
        _ = lastPassage ω (δ m) d := hq
        _ = lastPassage η (δ m) d := hpassage
    exact hgreatest q hqη i

/-- Rightmost rays from zero in environments agreeing at nonnegative heights
are ordered at every shared absolute level. Public Strong existence, line 988. -/
theorem pathSoutheastLE_total_of_nonnegative_height_agreement
    (ω η : Environment)
    (hagree : ∀ z : Lattice, 0 ≤ z.2 → ω z = η z)
    (γ δ : ℕ → Lattice)
    (hγ : IsLocallyRightmostGeodesic ω (0, 0) γ)
    (hδ : IsLocallyRightmostGeodesic η (0, 0) δ) :
    pathSoutheastLE γ δ ∨ pathSoutheastLE δ γ := by
  have hδω := locallyRightmost_transfer_of_nonnegative_height_agreement
    ω η hagree δ hδ
  exact pathSoutheastLE_total_of_isLocallyRightmostGeodesic
    ω (0, 0) γ δ hγ hδω

end LPP.Busemann
