/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Busemann.Geometry.LocallyRightmostGeodesic
public import LPP_Foundations.Model.LastPassage.RightmostFinite
import Mathlib.Tactic

/-! Same-root prefixes of locally rightmost geodesics. -/

@[expose] public section

open LPPDifferentiability

namespace LPP.Busemann

/-- Locally rightmost rays from one site agree through any meeting time.
This is the finite-prefix consequence of the geodesic tree order in Strong
Existence, lines 160–195 and 725–736. -/
theorem locallyRightmostGeodesic_eq_prefix_of_meet
    (ω : Environment) (u : Lattice) (γ δ : ℕ → Lattice)
    (hγ : IsLocallyRightmostGeodesic ω u γ)
    (hδ : IsLocallyRightmostGeodesic ω u δ)
    (N : ℕ) (hMeet : γ N = δ N) :
    ∀ k : ℕ, k ≤ N → γ k = δ k := by
  classical
  intro k hk
  by_cases hN : N = 0
  · have hk0 : k = 0 := by omega
    simpa [hk0] using hγ.1.trans hδ.1.symm
  have hpos : 0 < N := Nat.pos_of_ne_zero hN
  -- The two positive segments start at the same signed lattice site.
  have hγseg : ∃ (d : ℕ × ℕ) (p : Path u d),
      d.1 + d.2 = N ∧
      (∀ i : Fin (d.1 + d.2 + 1), p.vertex i = γ i.val) ∧
      pathWeight ω p = lastPassage ω u d ∧
      ∀ q : Path u d, pathWeight ω q = lastPassage ω u d →
        ∀ i : Fin (d.1 + d.2 + 1),
          (q.vertex i).1 ≤ (p.vertex i).1 ∧ (p.vertex i).2 ≤ (q.vertex i).2 := by
    have hseg := hγ.2.2 0 N hpos
    rw [hγ.1] at hseg
    simpa only [Nat.zero_add] using hseg
  have hδseg : ∃ (d : ℕ × ℕ) (p : Path u d),
      d.1 + d.2 = N ∧
      (∀ i : Fin (d.1 + d.2 + 1), p.vertex i = δ i.val) ∧
      pathWeight ω p = lastPassage ω u d ∧
      ∀ q : Path u d, pathWeight ω q = lastPassage ω u d →
        ∀ i : Fin (d.1 + d.2 + 1),
          (q.vertex i).1 ≤ (p.vertex i).1 ∧ (p.vertex i).2 ≤ (q.vertex i).2 := by
    have hseg := hδ.2.2 0 N hpos
    rw [hδ.1] at hseg
    simpa only [Nat.zero_add] using hseg
  obtain ⟨d, p, hpLen, hpTrace, hpWeight, hpGreat⟩ := hγseg
  obtain ⟨e, q, hqLen, hqTrace, hqWeight, hqGreat⟩ := hδseg
  -- Their common terminal vertex fixes the natural displacement coordinates.
  have hpEnd : u + ((d.1 : ℤ), (d.2 : ℤ)) = γ N := by
    rw [← p.finish, hpTrace]
    simp only [Fin.val_last, hpLen]
  have hqEnd : u + ((e.1 : ℤ), (e.2 : ℤ)) = δ N := by
    rw [← q.finish, hqTrace]
    simp only [Fin.val_last, hqLen]
  have hend : u + ((d.1 : ℤ), (d.2 : ℤ)) =
      u + ((e.1 : ℤ), (e.2 : ℤ)) := hpEnd.trans (hMeet.trans hqEnd.symm)
  have hde : d = e := by
    have hx := congrArg Prod.fst hend
    have hy := congrArg Prod.snd hend
    simp only [Prod.fst_add, Prod.snd_add] at hx hy
    apply Prod.ext <;> omega
  subst e
  -- Both witnesses satisfy the unique greatest-maximizer property.
  have hUnique := exists_unique_rightmost_maximizing_path ω u d
  have hpProp : pathWeight ω p = lastPassage ω u d ∧
      ∀ r : Path u d, pathWeight ω r = lastPassage ω u d →
        ∀ i : Fin (d.1 + d.2 + 1), (r.vertex i).1 ≤ (p.vertex i).1 :=
    ⟨hpWeight, fun r hr i => (hpGreat r hr i).1⟩
  have hqProp : pathWeight ω q = lastPassage ω u d ∧
      ∀ r : Path u d, pathWeight ω r = lastPassage ω u d →
        ∀ i : Fin (d.1 + d.2 + 1), (r.vertex i).1 ≤ (q.vertex i).1 :=
    ⟨hqWeight, fun r hr i => (hqGreat r hr i).1⟩
  have hpq : p = q := hUnique.unique hpProp hqProp
  let i : Fin (d.1 + d.2 + 1) := ⟨k, by omega⟩
  calc
    γ k = p.vertex i := (hpTrace i).symm
    _ = q.vertex i := by rw [hpq]
    _ = δ k := hqTrace i

end LPP.Busemann
