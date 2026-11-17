/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Busemann.Geometry.LocallyRightmostGeodesic
public import LPP_Foundations.Model.LastPassage.Locality
import Lean.Elab.Tactic.Omega

/-! Full locally rightmost ray sets are local to the upper half-plane. -/

@[expose] public section

open LPPDifferentiability

namespace LPP.Busemann

private theorem locallyRightmost_nonnegative_height
    {ω : Environment} {k : ℤ} {γ : ℕ → Lattice}
    (hγ : IsLocallyRightmostGeodesic ω (k, 0) γ) (n : ℕ) :
    0 ≤ (γ n).2 := by
  induction n with
  | zero =>
      simp [hγ.1]
  | succ n ih =>
      rcases hγ.2.1 n with hEast | hNorth
      · rw [hEast]
        simpa only [Prod.snd_add, add_zero] using ih
      · rw [hNorth]
        simp only [Prod.snd_add]
        omega

private theorem locallyRightmost_transfer_of_nonnegative_height_agreement
    (ω η : Environment)
    (hagree : ∀ z : Lattice, 0 ≤ z.2 → ω z = η z)
    (k : ℤ) (γ : ℕ → Lattice)
    (hη : IsLocallyRightmostGeodesic η (k, 0) γ) :
    IsLocallyRightmostGeodesic ω (k, 0) γ := by
  refine ⟨hη.1, hη.2.1, ?_⟩
  intro m N hN
  obtain ⟨d, p, hd, htrace, hmax, hgreatest⟩ := hη.2.2 m N hN
  have hrectangle :
      Set.EqOn ω η
        (Set.Icc (γ m) (γ m + ((d.1 : ℤ), (d.2 : ℤ)))) := by
    intro z hz
    apply hagree z
    exact (locallyRightmost_nonnegative_height hη m).trans hz.1.2
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

/-- Environments agreeing at nonnegative heights have the same full set of
locally rightmost semi-infinite geodesics from each signed horizontal root. -/
theorem locallyRightmostGeodesic_set_eq_of_nonnegative_height_agreement
    (ω η : Environment)
    (hagree : ∀ z : Lattice, 0 ≤ z.2 → ω z = η z)
    (k : ℤ) :
    {γ : ℕ → Lattice | IsLocallyRightmostGeodesic ω (k, 0) γ} =
      {γ : ℕ → Lattice | IsLocallyRightmostGeodesic η (k, 0) γ} := by
  ext γ
  constructor
  · intro hγ
    exact locallyRightmost_transfer_of_nonnegative_height_agreement
      η ω (fun z hz => (hagree z hz).symm) k γ hγ
  · intro hγ
    exact locallyRightmost_transfer_of_nonnegative_height_agreement
      ω η hagree k γ hγ

end LPP.Busemann
