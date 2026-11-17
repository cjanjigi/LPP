/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LPP_Foundations.Model.LastPassage.Basic

/-! Literal finite-segment and shared-level order predicates for the geodesic source. -/

@[expose] public section

open LPPDifferentiability

namespace LPP.Busemann

/-- Each positive-length finite segment is a greatest maximizing path.
Local time n represents absolute level u.1 + u.2 + n.
Strong Existence manuscript, lines 161–169 and 187–195. -/
def IsLocallyRightmostGeodesic
    (ω : Environment) (u : Lattice) (γ : ℕ → Lattice) : Prop :=
  γ 0 = u ∧
  (∀ n : ℕ,
    γ (n + 1) = γ n + ((1 : ℤ), (0 : ℤ)) ∨
      γ (n + 1) = γ n + ((0 : ℤ), (1 : ℤ))) ∧
  ∀ m N : ℕ, 0 < N →
    ∃ (d : ℕ × ℕ) (p : Path (γ m) d),
      d.1 + d.2 = N ∧
      (∀ i : Fin (d.1 + d.2 + 1), p.vertex i = γ (m + i.val)) ∧
      pathWeight ω p = lastPassage ω (γ m) d ∧
      ∀ q : Path (γ m) d,
        pathWeight ω q = lastPassage ω (γ m) d →
        ∀ i : Fin (d.1 + d.2 + 1),
          (q.vertex i).1 ≤ (p.vertex i).1 ∧
            (p.vertex i).2 ≤ (q.vertex i).2

/-- Southeast comparison at every shared absolute level, including different
signed starting sites. Strong Existence manuscript, lines 171–175. -/
def pathSoutheastLE (γ δ : ℕ → Lattice) : Prop :=
  ∀ m n : ℕ,
    (γ 0).1 + (γ 0).2 + (m : ℤ) =
      (δ 0).1 + (δ 0).2 + (n : ℤ) →
      (γ m).1 ≤ (δ n).1 ∧ (δ n).2 ≤ (γ m).2

end LPP.Busemann
