/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Busemann.Geometry.GeodesicInfimum
public import Busemann.Geometry.GeodesicCompactness
public import Busemann.Geometry.GeodesicOrder

import Busemann.Geometry.GreatestGeodesicExtension
import LPP_Foundations.Model.Paths.HorizontalFirst

@[expose] public section
open LPPDifferentiability
namespace LPP.Busemann

/-- A nonempty family of actual same-root geodesics has a unique least upper
bound in the existing geodesic tree. This is the missing geometric supremum
used by the real-parameter quantile definition in Strong Existence, public
source lines 801–802 and 823–830. -/
theorem exists_unique_geodesic_supremum
    (ω : Environment) (u : Lattice) (F : Set (ℕ → Lattice))
    (hne : F.Nonempty)
    (hvalid : ∀ γ ∈ F, IsLocallyRightmostGeodesic ω u γ) :
    ∃! q : ℕ → Lattice,
      IsLocallyRightmostGeodesic ω u q ∧
      (∀ γ ∈ F, pathSoutheastLE γ q) ∧
      (∀ δ : ℕ → Lattice,
        IsLocallyRightmostGeodesic ω u δ →
        (∀ γ ∈ F, pathSoutheastLE γ δ) → pathSoutheastLE q δ) := by
  classical
  -- Source step 1: an actual member realizes the zero-length prefix.
  obtain ⟨γ₀, hγ₀F⟩ := hne
  have hγ₀Valid : IsLocallyRightmostGeodesic ω u γ₀ := hvalid γ₀ hγ₀F
  let p : LPPDifferentiability.Path u (0, 0) :=
    LPPDifferentiability.horizontalFirst u (0, 0)
  have hzeroPrefix (γ : ℕ → Lattice)
      (hγ : IsLocallyRightmostGeodesic ω u γ) :
      ∀ k : Fin (0 + 0 + 1), γ k.val = p.vertex k := by
    intro k
    have hk : k = 0 := Fin.ext (by omega)
    subst k
    exact hγ.1.trans p.start.symm
  have hmemberPrefix := hzeroPrefix γ₀ hγ₀Valid

  -- Source step 2: the greatest-extension theorem supplies an
  -- actual ray above every actual ray from this signed root.
  obtain ⟨t, htProof, _htUnique⟩ :=
    exists_unique_greatest_locallyRightmostGeodesic_extension
      ω u (0, 0) p ⟨γ₀, hγ₀Valid, hmemberPrefix⟩
  rcases htProof with ⟨htValid, htPrefix, htGreatest⟩
  have htAboveActual (γ : ℕ → Lattice)
      (hγ : IsLocallyRightmostGeodesic ω u γ) : pathSoutheastLE γ t := by
    exact htGreatest γ hγ (hzeroPrefix γ hγ)

  -- Source step 3: the greatest extension makes the family of actual upper
  -- bounds nonempty.
  let U : Set (ℕ → Lattice) :=
    {δ | IsLocallyRightmostGeodesic ω u δ ∧
      ∀ γ ∈ F, pathSoutheastLE γ δ}
  have htInU : t ∈ U := by
    change IsLocallyRightmostGeodesic ω u t ∧
      ∀ γ ∈ F, pathSoutheastLE γ t
    refine ⟨htValid, ?_⟩
    intro γ hγF
    exact htAboveActual γ (hvalid γ hγF)
  have hUNonempty : U.Nonempty := ⟨t, htInU⟩

  -- Source step 4: take the infimum of all actual upper bounds.
  obtain ⟨q, hqProof, _hqUnique⟩ :=
    exists_unique_geodesic_infimum ω u U hUNonempty
      (fun δ hδ => hδ.1)
  rcases hqProof with ⟨hqValid, hqLower, hqGreatest⟩
  have hfamilyLower (γ : ℕ → Lattice) (hγF : γ ∈ F) :
      ∀ δ ∈ U, pathSoutheastLE γ δ := by
    intro δ hδU
    exact hδU.2 γ hγF
  have hqAboveFamily : ∀ γ ∈ F, pathSoutheastLE γ q := by
    intro γ hγF
    exact hqGreatest γ (hvalid γ hγF) (hfamilyLower γ hγF)
  have hqBelowEveryUpperBound (δ : ℕ → Lattice)
      (hδ : IsLocallyRightmostGeodesic ω u δ)
      (hδUpper : ∀ γ ∈ F, pathSoutheastLE γ δ) :
      pathSoutheastLE q δ := by
    have hδInU : δ ∈ U := by
      change IsLocallyRightmostGeodesic ω u δ ∧
        ∀ γ ∈ F, pathSoutheastLE γ δ
      exact ⟨hδ, hδUpper⟩
    exact hqLower δ hδInU

  -- Source step 5: two least upper bounds compare both ways, so their
  -- common-root paths agree at every time.
  refine ⟨q, ⟨hqValid, hqAboveFamily, hqBelowEveryUpperBound⟩, ?_⟩
  rintro δ ⟨hδValid, hδAboveFamily, hδLeast⟩
  have hδq : pathSoutheastLE δ q :=
    hδLeast q hqValid hqAboveFamily
  have hqδ : pathSoutheastLE q δ :=
    hqBelowEveryUpperBound δ hδValid hδAboveFamily
  have hroot : δ 0 = q 0 := hδValid.1.trans hqValid.1.symm
  have hδqAtEveryTime :=
    (pathSoutheastLE_iff_all_times_of_same_root δ q hroot).mp hδq
  have hqδAtEveryTime :=
    (pathSoutheastLE_iff_all_times_of_same_root q δ hroot.symm).mp hqδ
  funext n
  exact Prod.ext
    (le_antisymm (hδqAtEveryTime n).1 (hqδAtEveryTime n).1)
    (le_antisymm (hqδAtEveryTime n).2 (hδqAtEveryTime n).2)

end LPP.Busemann
