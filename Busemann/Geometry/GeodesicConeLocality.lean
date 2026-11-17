/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Busemann.Geometry.LocallyRightmostGeodesic
public import LPP_Foundations.Model.LastPassage.Locality
import Lean.Elab.Tactic.Omega

/-! Full locally rightmost ray sets depend only on the forward reachable cone. -/

@[expose] public section

open LPPDifferentiability

namespace LPP.Busemann

private theorem locallyRightmost_root_le
    {ω : Environment} {u : Lattice} {γ : ℕ → Lattice}
    (hγ : IsLocallyRightmostGeodesic ω u γ) (n : ℕ) :
    u ≤ γ n := by
  induction n with
  | zero =>
      simpa only [hγ.1] using (le_refl u)
  | succ n ih =>
      rcases hγ.2.1 n with hEast | hNorth
      · rw [hEast]
        rcases Prod.le_def.mp ih with ⟨hfirst, hsecond⟩
        change u.1 ≤ (γ n).1 + 1 ∧ u.2 ≤ (γ n).2 + 0
        exact ⟨by omega, by omega⟩
      · rw [hNorth]
        rcases Prod.le_def.mp ih with ⟨hfirst, hsecond⟩
        change u.1 ≤ (γ n).1 + 0 ∧ u.2 ≤ (γ n).2 + 1
        exact ⟨by omega, by omega⟩

private theorem locallyRightmost_transfer_of_eqOn_Ici
    (ω η : Environment) (u : Lattice)
    (hagree : Set.EqOn ω η (Set.Ici u)) (γ : ℕ → Lattice)
    (hη : IsLocallyRightmostGeodesic η u γ) :
    IsLocallyRightmostGeodesic ω u γ := by
  refine ⟨hη.1, hη.2.1, ?_⟩
  intro m N hN
  obtain ⟨d, p, hd, htrace, hmax, hgreatest⟩ := hη.2.2 m N hN
  have hrectangle :
      Set.EqOn ω η
        (Set.Icc (γ m) (γ m + ((d.1 : ℤ), (d.2 : ℤ)))) := by
    intro z hz
    exact hagree ((locallyRightmost_root_le hη m).trans hz.1)
  have hpath : pathWeight ω p = pathWeight η p :=
    pathWeight_eq_of_eqOn hrectangle p
  have hpassage : lastPassage ω (γ m) d = lastPassage η (γ m) d :=
    lastPassage_eq_of_eqOn hrectangle
  refine ⟨d, p, hd, htrace, ?_, ?_⟩
  · calc
      pathWeight ω p = pathWeight η p := hpath
      _ = lastPassage η (γ m) d := hmax
      _ = lastPassage ω (γ m) d := hpassage.symm
  · intro q hq i
    have hqη : pathWeight η q = lastPassage η (γ m) d := by
      calc
        pathWeight η q = pathWeight ω q :=
          (pathWeight_eq_of_eqOn hrectangle q).symm
        _ = lastPassage ω (γ m) d := hq
        _ = lastPassage η (γ m) d := hpassage
    exact hgreatest q hqη i

/-- Environments agreeing on the forward cone from a signed root have the same
full set of locally rightmost rays from that root. Strong Existence source,
lines 994–999. -/
theorem locallyRightmostGeodesic_set_eq_of_eqOn_Ici
    (ω η : Environment) (u : Lattice)
    (hagree : Set.EqOn ω η (Set.Ici u)) :
    {γ : ℕ → Lattice | IsLocallyRightmostGeodesic ω u γ} =
      {γ : ℕ → Lattice | IsLocallyRightmostGeodesic η u γ} := by
  ext γ
  constructor
  · intro hγ
    exact locallyRightmost_transfer_of_eqOn_Ici η ω u
      (fun {z} hz => (hagree hz).symm) γ hγ
  · intro hγ
    exact locallyRightmost_transfer_of_eqOn_Ici ω η u hagree γ hγ

end LPP.Busemann
