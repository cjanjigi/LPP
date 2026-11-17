/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Busemann.Geometry.GeodesicOrder
public import Busemann.Geometry.GeodesicPrefixOrder
import Lean.Elab.Tactic.Omega

/-! Opposite strict orders prevent aligned outer coalescence of crossed rays. -/

@[expose] public section

open LPPDifferentiability

namespace LPP.Busemann

private theorem locallyRightmost_absolute_level
    (ω : Environment) (u : Lattice) (γ : ℕ → Lattice)
    (hγ : IsLocallyRightmostGeodesic ω u γ) (n : ℕ) :
    (γ n).1 + (γ n).2 = u.1 + u.2 + (n : ℤ) := by
  -- The geodesic definition has one east or north step at each time.
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

private theorem locallyRightmost_same_root_level
    (ω : Environment) (u : Lattice) (γ δ : ℕ → Lattice)
    (hγ : IsLocallyRightmostGeodesic ω u γ)
    (hδ : IsLocallyRightmostGeodesic ω u δ) (n : ℕ) :
    (γ 0).1 + (γ 0).2 + (n : ℤ) =
      (δ 0).1 + (δ 0).2 + (n : ℤ) := by
  calc
    (γ 0).1 + (γ 0).2 + (n : ℤ) = u.1 + u.2 + (n : ℤ) := by
      rw [hγ.1]
    _ = (δ 0).1 + (δ 0).2 + (n : ℤ) := by
      rw [hδ.1]

private theorem strict_first_coordinate_after_of_same_root_order
    (ω : Environment) (u : Lattice) (γ δ : ℕ → Lattice)
    (hγ : IsLocallyRightmostGeodesic ω u γ)
    (hδ : IsLocallyRightmostGeodesic ω u δ)
    (hOrder : pathSoutheastLE γ δ) (hDifferent : γ ≠ δ) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → (γ n).1 < (δ n).1 := by
  classical
  -- Distinct rays differ at at least one finite local time.
  have hUnequalAtSomeTime : ∃ n₀ : ℕ, γ n₀ ≠ δ n₀ := by
    by_contra hNoWitness
    apply hDifferent
    funext n
    by_contra hUnequal
    exact hNoWitness ⟨n, hUnequal⟩
  obtain ⟨n₀, hUnequalAtWitness⟩ := hUnequalAtSomeTime
  have hOrderAtWitness := hOrder n₀ n₀
    (locallyRightmost_same_root_level ω u γ δ hγ hδ n₀)
  -- Equal first coordinates at the witness would force the full vertices equal.
  have hStrictAtWitness : (γ n₀).1 < (δ n₀).1 := by
    by_contra hNotStrict
    have hFirstEq : (γ n₀).1 = (δ n₀).1 := by omega
    have hSecondEq : (γ n₀).2 = (δ n₀).2 := by
      have hγLevel := locallyRightmost_absolute_level ω u γ hγ n₀
      have hδLevel := locallyRightmost_absolute_level ω u δ hδ n₀
      omega
    exact hUnequalAtWitness (Prod.ext hFirstEq hSecondEq)
  refine ⟨n₀, ?_⟩
  intro n hn
  by_cases hn₀ : n = n₀
  · subst n
    exact hStrictAtWitness
  ·
    -- A later meeting forces equality of the two prefixes through n₀.
    have hNoMeet : γ n ≠ δ n := by
      intro hMeet
      have hPrefix := locallyRightmostGeodesic_eq_prefix_of_meet
        ω u γ δ hγ hδ n hMeet
      exact hUnequalAtWitness (hPrefix n₀ (by omega))
    have hOrderAtN := hOrder n n
      (locallyRightmost_same_root_level ω u γ δ hγ hδ n)
    -- The weak order is therefore still strict after every later time.
    by_contra hNotStrict
    have hFirstEq : (γ n).1 = (δ n).1 := by omega
    have hSecondEq : (γ n).2 = (δ n).2 := by
      have hγLevel := locallyRightmost_absolute_level ω u γ hγ n
      have hδLevel := locallyRightmost_absolute_level ω u δ hδ n
      omega
    exact hNoMeet (Prod.ext hFirstEq hSecondEq)

-- The named parameter `hkℓ` is part of the shared theorem interface.
set_option linter.unusedVariables false in
/-- Opposite strict same-root orders around coalescing middle rays prevent
coalescence of the outer rays at aligned absolute levels. Strong Existence,
lines 994–998. -/
theorem no_outer_coalescence_of_crossed_locallyRightmost_rays
    (ω : Environment) (k ℓ : ℤ) (hkℓ : k < ℓ)
    (γk δk δℓ γℓ : ℕ → Lattice)
    (hγk : IsLocallyRightmostGeodesic ω (k, 0) γk)
    (hδk : IsLocallyRightmostGeodesic ω (k, 0) δk)
    (hδℓ : IsLocallyRightmostGeodesic ω (ℓ, 0) δℓ)
    (hγℓ : IsLocallyRightmostGeodesic ω (ℓ, 0) γℓ)
    (hkOrder : pathSoutheastLE γk δk ∧ γk ≠ δk)
    (hℓOrder : pathSoutheastLE δℓ γℓ ∧ δℓ ≠ γℓ)
    (hMiddle : ∃ m n : ℕ,
      k + (m : ℤ) = ℓ + (n : ℤ) ∧
      ∀ q : ℕ, δk (m + q) = δℓ (n + q)) :
    ¬ ∃ m n : ℕ,
      k + (m : ℤ) = ℓ + (n : ℤ) ∧
      ∀ q : ℕ, γk (m + q) = γℓ (n + q) := by
  rintro ⟨mOuter, nOuter, hOuterLevel, hOuterTail⟩
  obtain ⟨mMiddle, nMiddle, hMiddleLevel, hMiddleTail⟩ := hMiddle
  -- The strict same-root inequalities persist after their first differing times.
  obtain ⟨nK, hStrictK⟩ := strict_first_coordinate_after_of_same_root_order
    ω (k, 0) γk δk hγk hδk hkOrder.1 hkOrder.2
  obtain ⟨nℓ, hStrictℓ⟩ := strict_first_coordinate_after_of_same_root_order
    ω (ℓ, 0) δℓ γℓ hδℓ hγℓ hℓOrder.1 hℓOrder.2
  -- Choose one late level beyond both order witnesses and both coalescence starts.
  let q : ℕ := (nK - mMiddle) + (nℓ - nMiddle) +
    (mOuter - mMiddle) + (nOuter - nMiddle)
  have hLateK : nK ≤ mMiddle + q := by dsimp [q]; omega
  have hLateℓ : nℓ ≤ nMiddle + q := by dsimp [q]; omega
  have hOuterK : mOuter ≤ mMiddle + q := by dsimp [q]; omega
  have hOuterℓ : nOuter ≤ nMiddle + q := by dsimp [q]; omega
  -- Align the outer tail with this same signed absolute level, not equal times.
  let r : ℕ := mMiddle + q - mOuter
  have hOuterIndexK : mOuter + r = mMiddle + q := by
    dsimp [r]
    omega
  have hOuterIndexℓ : nOuter + r = nMiddle + q := by
    dsimp [r]
    omega
  have hMiddleEqual : δk (mMiddle + q) = δℓ (nMiddle + q) :=
    hMiddleTail q
  have hOuterEqual : γk (mMiddle + q) = γℓ (nMiddle + q) := by
    calc
      γk (mMiddle + q) = γk (mOuter + r) := by rw [hOuterIndexK]
      _ = γℓ (nOuter + r) := hOuterTail r
      _ = γℓ (nMiddle + q) := by rw [hOuterIndexℓ]
  have hLeftStrict := hStrictK (mMiddle + q) hLateK
  have hRightStrict := hStrictℓ (nMiddle + q) hLateℓ
  have hMiddleFirst := congrArg Prod.fst hMiddleEqual
  have hOuterFirst := congrArg Prod.fst hOuterEqual
  -- At this level the strict chain contradicts the outer equality.
  have hStrictChain :
      (γk (mMiddle + q)).1 < (γℓ (nMiddle + q)).1 := by
    calc
      (γk (mMiddle + q)).1 < (δk (mMiddle + q)).1 := hLeftStrict
      _ = (δℓ (nMiddle + q)).1 := hMiddleFirst
      _ < (γℓ (nMiddle + q)).1 := hRightStrict
  have hImpossible : (γk (mMiddle + q)).1 < (γk (mMiddle + q)).1 := by
    rw [← hOuterFirst] at hStrictChain
    exact hStrictChain
  exact (lt_irrefl _) hImpossible

end LPP.Busemann
