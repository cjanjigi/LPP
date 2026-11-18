/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Busemann.Geometry.CrossedGeodesicCoalescence
public import LPP_Foundations.Model.Paths.Coalescence
import LPP_Foundations.Model.Paths.UpRightRay
import Lean.Elab.Tactic.Omega

/-! Opposite strict orders prevent aligned outer coalescence of crossed rays at arbitrary signed roots. -/

@[expose] public section

open LPPDifferentiability

namespace LPP.Busemann

private theorem root_ray_absolute_level
    (ω : Environment) (u : Lattice) (γ : ℕ → Lattice)
    (hγ : IsLocallyRightmostGeodesic ω u γ) (n : ℕ) :
    (γ n).1 + (γ n).2 = u.1 + u.2 + (n : ℤ) := by
  simpa only [hγ.1] using IsUpRightRay.level (γ := γ) hγ.2.1 n

private theorem root_rays_same_absolute_level
    (ω : Environment) (u : Lattice) (γ δ : ℕ → Lattice)
    (hγ : IsLocallyRightmostGeodesic ω u γ)
    (hδ : IsLocallyRightmostGeodesic ω u δ) (n : ℕ) :
    (γ 0).1 + (γ 0).2 + (n : ℤ) =
      (δ 0).1 + (δ 0).2 + (n : ℤ) := by
  -- Both rays start at the same root.
  calc
    (γ 0).1 + (γ 0).2 + (n : ℤ) = u.1 + u.2 + (n : ℤ) := by
      rw [hγ.1]
    _ = (δ 0).1 + (δ 0).2 + (n : ℤ) := by
      rw [hδ.1]

private theorem strict_first_coordinate_after_root_order
    (ω : Environment) (u : Lattice) (γ δ : ℕ → Lattice)
    (hγ : IsLocallyRightmostGeodesic ω u γ)
    (hδ : IsLocallyRightmostGeodesic ω u δ)
    (hOrder : pathSoutheastLE γ δ) (hDifferent : γ ≠ δ) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → (γ n).1 < (δ n).1 := by
  classical
  -- Distinct rays differ at some finite time.
  have hUnequalAtSomeTime : ∃ n₀ : ℕ, γ n₀ ≠ δ n₀ := by
    by_contra hNoWitness
    apply hDifferent
    funext n
    by_contra hUnequal
    exact hNoWitness ⟨n, hUnequal⟩
  obtain ⟨n₀, hUnequalAtWitness⟩ := hUnequalAtSomeTime
  have hOrderAtWitness := hOrder n₀ n₀
    (root_rays_same_absolute_level ω u γ δ hγ hδ n₀)
  -- Equal coordinate sums make the weak first-coordinate order strict at the witness.
  have hStrictAtWitness : (γ n₀).1 < (δ n₀).1 := by
    by_contra hNotStrict
    have hFirstEq : (γ n₀).1 = (δ n₀).1 := by omega
    have hSecondEq : (γ n₀).2 = (δ n₀).2 := by
      have hγLevel := root_ray_absolute_level ω u γ hγ n₀
      have hδLevel := root_ray_absolute_level ω u δ hδ n₀
      omega
    exact hUnequalAtWitness (Prod.ext hFirstEq hSecondEq)
  refine ⟨n₀, ?_⟩
  intro n hn
  by_cases hn₀ : n = n₀
  · subst n
    exact hStrictAtWitness
  ·
    -- A later meeting would force the distinct prefixes to agree.
    have hNoMeet : γ n ≠ δ n := by
      intro hMeet
      have hPrefix := locallyRightmostGeodesic_eq_prefix_of_meet
        ω u γ δ hγ hδ n hMeet
      exact hUnequalAtWitness (hPrefix n₀ (by omega))
    have hOrderAtN := hOrder n n
      (root_rays_same_absolute_level ω u γ δ hγ hδ n)
    -- Without a meeting, the weak order remains strict at every later time.
    by_contra hNotStrict
    have hFirstEq : (γ n).1 = (δ n).1 := by omega
    have hSecondEq : (γ n).2 = (δ n).2 := by
      have hγLevel := root_ray_absolute_level ω u γ hγ n
      have hδLevel := root_ray_absolute_level ω u δ hδ n
      omega
    exact hNoMeet (Prod.ext hFirstEq hSecondEq)

/-- Opposite strict same-root orders around coalescing middle rays prevent
coalescence of the outer rays at aligned absolute levels for arbitrary signed roots.
Strong Existence, lines 994–998. -/
theorem no_outer_coalescence_of_crossed_locallyRightmost_rays_at_roots
    (ω : Environment) (u v : Lattice)
    (γu δu δv γv : ℕ → Lattice)
    (hγu : IsLocallyRightmostGeodesic ω u γu)
    (hδu : IsLocallyRightmostGeodesic ω u δu)
    (hδv : IsLocallyRightmostGeodesic ω v δv)
    (hγv : IsLocallyRightmostGeodesic ω v γv)
    (huOrder : pathSoutheastLE γu δu ∧ γu ≠ δu)
    (hvOrder : pathSoutheastLE δv γv ∧ δv ≠ γv)
    (hMiddle : paths_coalesce u v δu δv) :
    ¬ paths_coalesce u v γu γv := by
  -- Assume the outer rays coalesce at an aligned level.
  rintro ⟨mOuter, nOuter, hOuterLevel, hOuterTail⟩
  obtain ⟨mMiddle, nMiddle, hMiddleLevel, hMiddleTail⟩ := hMiddle
  -- Each same-root strict order persists after its first difference.
  obtain ⟨nU, hStrictU⟩ := strict_first_coordinate_after_root_order
    ω u γu δu hγu hδu huOrder.1 huOrder.2
  obtain ⟨nV, hStrictV⟩ := strict_first_coordinate_after_root_order
    ω v δv γv hδv hγv hvOrder.1 hvOrder.2
  -- Choose one late level beyond both strictness witnesses and all tail starts.
  let q : ℕ := (nU - mMiddle) + (nV - nMiddle) +
    (mOuter - mMiddle) + (nOuter - nMiddle)
  have hLateU : nU ≤ mMiddle + q := by
    dsimp [q]
    omega
  have hLateV : nV ≤ nMiddle + q := by
    dsimp [q]
    omega
  have hOuterU : mOuter ≤ mMiddle + q := by
    dsimp [q]
    omega
  have hOuterV : nOuter ≤ nMiddle + q := by
    dsimp [q]
    omega
  -- Translate the common middle level into each outer tail.
  let r : ℕ := mMiddle + q - mOuter
  have hOuterIndexU : mOuter + r = mMiddle + q := by
    dsimp [r]
    omega
  have hOuterIndexV : nOuter + r = nMiddle + q := by
    dsimp [r]
    omega
  have hMiddleEqual : δu (mMiddle + q) = δv (nMiddle + q) :=
    hMiddleTail q
  have hOuterEqual : γu (mMiddle + q) = γv (nMiddle + q) := by
    calc
      γu (mMiddle + q) = γu (mOuter + r) := by rw [hOuterIndexU]
      _ = γv (nOuter + r) := hOuterTail r
      _ = γv (nMiddle + q) := by rw [hOuterIndexV]
  have hLeftStrict := hStrictU (mMiddle + q) hLateU
  have hRightStrict := hStrictV (nMiddle + q) hLateV
  have hMiddleFirst := congrArg Prod.fst hMiddleEqual
  have hOuterFirst := congrArg Prod.fst hOuterEqual
  -- The middle equality lies strictly between the outer coordinates.
  have hStrictChain :
      (γu (mMiddle + q)).1 < (γv (nMiddle + q)).1 := by
    calc
      (γu (mMiddle + q)).1 < (δu (mMiddle + q)).1 := hLeftStrict
      _ = (δv (nMiddle + q)).1 := hMiddleFirst
      _ < (γv (nMiddle + q)).1 := hRightStrict
  have hImpossible : (γu (mMiddle + q)).1 < (γu (mMiddle + q)).1 := by
    rw [← hOuterFirst] at hStrictChain
    exact hStrictChain
  exact (lt_irrefl _) hImpossible

end LPP.Busemann
