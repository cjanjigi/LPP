/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Busemann.Geometry.LocallyRightmostGeodesic
import Busemann.Geometry.GeodesicPrefixOrder
import LPP_Foundations.Model.Paths.HeightOrder
import Lean.Elab.Tactic.Omega

/-! Shared-level comparison for same-root locally rightmost geodesics. -/

@[expose] public section

open LPPDifferentiability LPP.Busemann

namespace LPP.Busemann

private theorem locallyRightmost_level
    (ω : Environment) (u : Lattice) (γ : ℕ → Lattice)
    (hγ : IsLocallyRightmostGeodesic ω u γ) (n : ℕ) :
    (γ n).1 + (γ n).2 = u.1 + u.2 + (n : ℤ) := by
  -- Each unit step raises the signed level by one.
  induction n with
  | zero => simp [hγ.1]
  | succ n ih =>
      rcases hγ.2.1 n with hEast | hNorth
      · rw [hEast]
        simp only [Prod.fst_add, Prod.snd_add, Nat.cast_succ]
        omega
      · rw [hNorth]
        simp only [Prod.fst_add, Prod.snd_add, Nat.cast_succ]
        omega

private theorem no_reverse_order_after
    (ω : Environment) (u : Lattice) (γ δ : ℕ → Lattice)
    (hγ : IsLocallyRightmostGeodesic ω u γ)
    (hδ : IsLocallyRightmostGeodesic ω u δ)
    {a b : ℕ} (hab : a ≤ b)
    (hStart : (γ a).1 < (δ a).1)
    (hEnd : (δ b).1 < (γ b).1) : False := by
  -- Restart the two rays at the earlier time, in reverse vertical order.
  let p : ℕ → Lattice := fun k => δ (a + k)
  let q : ℕ → Lattice := fun k => γ (a + k)
  let N : ℕ := b - a
  have hN : a + N = b := by
    dsimp [N]
    exact Nat.add_sub_of_le hab

  have hpStep : ∀ k, p (k + 1) = p k + (1, 0) ∨
      p (k + 1) = p k + (0, 1) := by
    intro k
    simpa [p, Nat.add_assoc] using hδ.2.1 (a + k)
  have hqStep : ∀ k, q (k + 1) = q k + (1, 0) ∨
      q (k + 1) = q k + (0, 1) := by
    intro k
    simpa [q, Nat.add_assoc] using hγ.2.1 (a + k)

  have hStartLevel : (p 0).1 + (p 0).2 = (q 0).1 + (q 0).2 := by
    simpa [p, q] using
      (locallyRightmost_level ω u δ hδ a).trans
        (locallyRightmost_level ω u γ hγ a).symm

  -- A meeting would force the root prefixes to agree through the strict start.
  have hAvoid : ∀ k, k ≤ N → p k ≠ q k := by
    intro k _hk hEqual
    change δ (a + k) = γ (a + k) at hEqual
    have hMeet := locallyRightmostGeodesic_eq_prefix_of_meet
      ω u δ γ hδ hγ (a + k) hEqual
    have hAtStart : δ a = γ a := hMeet a (by omega)
    have hFirst := congrArg Prod.fst hAtStart
    exact (ne_of_gt hStart) hFirst

  -- Finite height order preserves the initial strict vertical order.
  have hOrder :=
    LPPDifferentiability.up_right_paths_strict_height_order_iff_of_disjoint
      p q N hpStep hqStep hStartLevel hAvoid
  have hStartHeight : (p 0).2 < (q 0).2 := by
    have hLevel :=
      (locallyRightmost_level ω u γ hγ a).trans
        (locallyRightmost_level ω u δ hδ a).symm
    have hSecond : (δ a).2 < (γ a).2 := by omega
    simpa [p, q] using hSecond
  have hEndHeight : (q N).2 < (p N).2 := by
    have hLevel :=
      (locallyRightmost_level ω u γ hγ b).trans
        (locallyRightmost_level ω u δ hδ b).symm
    have hSecond : (γ b).2 < (δ b).2 := by omega
    simpa [p, q, N, hN] using hSecond
  have hPreserved := hOrder.mp hStartHeight
  omega

private theorem no_opposite_orders
    (ω : Environment) (u : Lattice) (γ δ : ℕ → Lattice)
    (hγ : IsLocallyRightmostGeodesic ω u γ)
    (hδ : IsLocallyRightmostGeodesic ω u δ) :
    ∀ a b, ¬ ((γ a).1 < (δ a).1 ∧ (δ b).1 < (γ b).1) := by
  intro a b hOrders
  by_cases hab : a ≤ b
  · exact no_reverse_order_after ω u γ δ hγ hδ hab hOrders.1 hOrders.2
  · have hba : b ≤ a := by omega
    exact no_reverse_order_after ω u δ γ hδ hγ hba hOrders.2 hOrders.1

/-- Two locally rightmost geodesics from the same signed root are ordered at
every shared absolute level. Strong Existence manuscript, lines 725–842. -/
theorem pathSoutheastLE_total_of_isLocallyRightmostGeodesic
    (ω : Environment) (u : Lattice) (γ δ : ℕ → Lattice)
    (hγ : IsLocallyRightmostGeodesic ω u γ)
    (hδ : IsLocallyRightmostGeodesic ω u δ) :
    pathSoutheastLE γ δ ∨ pathSoutheastLE δ γ := by
  classical
  have hSameLevel (n : ℕ) :
      (γ n).1 + (γ n).2 = (δ n).1 + (δ n).2 := by
    calc
      (γ n).1 + (γ n).2 = u.1 + u.2 + (n : ℤ) :=
        locallyRightmost_level ω u γ hγ n
      _ = (δ n).1 + (δ n).2 :=
        (locallyRightmost_level ω u δ hδ n).symm

  have hNoOpposite := no_opposite_orders ω u γ δ hγ hδ
  -- A failure of either weak direction would give two opposite strict times.
  have hFirstOrder :
      (∀ n, (γ n).1 ≤ (δ n).1) ∨ (∀ n, (δ n).1 ≤ (γ n).1) := by
    by_cases hForward : ∀ n, (γ n).1 ≤ (δ n).1
    · exact Or.inl hForward
    · right
      intro n
      by_contra hNot
      have hγδ : (γ n).1 < (δ n).1 := lt_of_not_ge hNot
      obtain ⟨m, hm⟩ := not_forall.mp hForward
      have hδγ : (δ m).1 < (γ m).1 := lt_of_not_ge hm
      exact hNoOpposite n m ⟨hγδ, hδγ⟩

  have hSharedTime {m n : ℕ}
      (hLevel : (γ 0).1 + (γ 0).2 + (m : ℤ) =
        (δ 0).1 + (δ 0).2 + (n : ℤ)) : m = n := by
    rw [hγ.1, hδ.1] at hLevel
    omega

  -- Equal absolute levels have equal local times because the roots coincide.
  rcases hFirstOrder with hForward | hBackward
  · left
    intro m n hLevel
    have hmn := hSharedTime hLevel
    subst n
    refine ⟨hForward m, ?_⟩
    -- The common level converts first-coordinate order to second-coordinate order.
    have hFirst := hForward m
    have h := hSameLevel m
    omega
  · right
    intro m n hLevel
    have hnm := hSharedTime hLevel.symm
    have hmn : m = n := hnm.symm
    subst n
    refine ⟨hBackward m, ?_⟩
    have hFirst := hBackward m
    have h := hSameLevel m
    omega

end LPP.Busemann
