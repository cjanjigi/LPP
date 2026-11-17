/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Busemann.Geometry.LocallyRightmostGeodesic
public import Busemann.Geometry.GeodesicOrder
public import Mathlib.MeasureTheory.Constructions.UnitInterval
public import Mathlib.Probability.Kernel.CondDistrib

import Busemann.Geometry.GeodesicInfimum

@[expose] public section
open MeasureTheory ProbabilityTheory LPPDifferentiability
open scoped ENNReal
namespace LPP.Busemann

/-- A conditional-CDF quantile family that agrees on a dense parameter set
agrees at every positive parameter, including the left-supremum endpoint one.
The same actual sampler and kernel are used throughout. Strong Existence,
lm:orig_space, lines 1094–1099. -/
theorem real_quantile_paths_eq_of_dense_parameter_eq
    (ω : Environment)
    (κ : Lattice → Kernel Environment (ℕ → Lattice))
    (q : Lattice → Environment → unitInterval → (ℕ → Lattice))
    (hCDF : ∀ (u : Lattice) (s : unitInterval),
      IsLocallyRightmostGeodesic ω u (q u ω s) ∧
      ∀ γ : ℕ → Lattice, IsLocallyRightmostGeodesic ω u γ →
        (pathSoutheastLE (q u ω s) γ ↔
          ENNReal.ofReal (s : ℝ) ≤
            (κ u) ω {η : ℕ → Lattice | pathSoutheastLE η γ}))
    (D : Set unitInterval) (hDense : Dense D)
    (hEqualDense : ∀ r ∈ D, ∀ t ∈ D, ∀ u : Lattice,
      q u ω r = q u ω t) :
    ∀ (s t : unitInterval), 0 < (s : ℝ) → 0 < (t : ℝ) →
      ∀ u : Lattice, q u ω s = q u ω t := by
  intro s t hs ht u

  -- At one root, the public finite-coordinate characterization gives
  -- antisymmetry of the path order.
  have hPathAntisymm (γ δ : ℕ → Lattice)
      (hγ : IsLocallyRightmostGeodesic ω u γ)
      (hδ : IsLocallyRightmostGeodesic ω u δ)
      (hγδ : pathSoutheastLE γ δ)
      (hδγ : pathSoutheastLE δ γ) : γ = δ := by
    have hroot : γ 0 = δ 0 := hγ.1.trans hδ.1.symm
    have hForward :=
      (pathSoutheastLE_iff_all_times_of_same_root γ δ hroot).mp hγδ
    have hBackward :=
      (pathSoutheastLE_iff_all_times_of_same_root δ γ hroot.symm).mp hδγ
    funext n
    apply Prod.ext
    · exact le_antisymm (hForward n).1 (hBackward n).1
    · exact le_antisymm (hBackward n).2 (hForward n).2

  have hPathRefl (γ : ℕ → Lattice) : pathSoutheastLE γ γ := by
    apply (pathSoutheastLE_iff_all_times_of_same_root γ γ rfl).mpr
    intro n
    exact ⟨le_rfl, le_rfl⟩

  -- Testing the CDF of q s against q s itself gives the cutoff needed to
  -- compare any earlier parameter with s.
  have hMono (r s : unitInterval) (hrs : r ≤ s) :
      pathSoutheastLE (q u ω r) (q u ω s) := by
    have hSelf : pathSoutheastLE (q u ω s) (q u ω s) :=
      hPathRefl (q u ω s)
    have hSelfCutoff :
        ENNReal.ofReal (s : ℝ) ≤
          (κ u) ω {η : ℕ → Lattice | pathSoutheastLE η (q u ω s)} :=
      ((hCDF u s).2 (q u ω s) (hCDF u s).1).mp hSelf
    have hrsReal : (r : ℝ) ≤ (s : ℝ) := by
      exact_mod_cast hrs
    have hLevel : ENNReal.ofReal (r : ℝ) ≤ ENNReal.ofReal (s : ℝ) :=
      ENNReal.ofReal_le_ofReal hrsReal
    exact ((hCDF u r).2 (q u ω s) (hCDF u s).1).mpr
      (hLevel.trans hSelfCutoff)

  -- Fix one dense parameter below one; dense equality makes its path the
  -- common reference path at this root.
  have h01 : (0 : unitInterval) < 1 := by
    exact Subtype.coe_lt_coe.mpr (by norm_num : (0 : ℝ) < 1)
  obtain ⟨r₀, hr₀D, hr₀Between⟩ := hDense.exists_between h01
  have hr₀LtOne : r₀ < 1 := hr₀Between.2
  let π := q u ω r₀
  have hπLoc : IsLocallyRightmostGeodesic ω u π := (hCDF u r₀).1
  have hDensePathEq (r : unitInterval) (hr : r ∈ D) : q u ω r = π :=
    hEqualDense r hr r₀ hr₀D u

  -- The dense cutoffs all bound one fixed kernel mass below π.
  let m : ℝ≥0∞ := (κ u) ω {η : ℕ → Lattice | pathSoutheastLE η π}
  have hDenseCutoff : ∀ r ∈ D, ENNReal.ofReal (r : ℝ) ≤ m := by
    intro r hr
    have hEq := hDensePathEq r hr
    have hBelow : pathSoutheastLE (q u ω r) π := by
      rw [hEq]
      exact hPathRefl π
    have hCutoff := ((hCDF u r).2 π hπLoc).mp hBelow
    simpa only [m] using hCutoff

  -- Continuity of ofReal makes this lower cutoff closed, so density reaches
  -- the endpoint value one.
  have hCutoffClosed :
      IsClosed {r : unitInterval | ENNReal.ofReal (r : ℝ) ≤ m} := by
    change IsClosed
      ((fun r : unitInterval => ENNReal.ofReal (r : ℝ)) ⁻¹' Set.Iic m)
    exact isClosed_Iic.preimage
      (ENNReal.continuous_ofReal.comp continuous_subtype_val)
  have hOneClosure : (1 : unitInterval) ∈ closure D := by
    rw [hDense.closure_eq]
    simp
  have hOneCutoff : ENNReal.ofReal (1 : ℝ) ≤ m :=
    (closure_minimal hDenseCutoff hCutoffClosed) hOneClosure

  -- The endpoint uses the same kernel cutoff and the monotonicity from r₀.
  have hEndpointEq : q u ω 1 = π := by
    have hEndpointCutoff :
        ENNReal.ofReal (1 : ℝ) ≤
          (κ u) ω {η : ℕ → Lattice | pathSoutheastLE η π} := by
      simpa only [m] using hOneCutoff
    have hEndpointLe : pathSoutheastLE (q u ω 1) π :=
      ((hCDF u 1).2 π hπLoc).mpr hEndpointCutoff
    have hReferenceLe : pathSoutheastLE π (q u ω 1) := by
      have h := hMono r₀ 1 (le_of_lt hr₀LtOne)
      simpa only [π] using h
    exact hPathAntisymm (q u ω 1) π (hCDF u 1).1 hπLoc
      hEndpointLe hReferenceLe

  -- Interior parameters are squeezed between two dense parameters.
  have hToReference (s : unitInterval) (hs : 0 < (s : ℝ)) :
      q u ω s = π := by
    by_cases hsOne : s = 1
    · rw [hsOne]
      exact hEndpointEq
    · have hsLeOne : s ≤ 1 := Subtype.coe_le_coe.mpr s.property.2
      have hsLtOne : s < 1 := lt_of_le_of_ne hsLeOne hsOne
      have hZeroLtS : (0 : unitInterval) < s :=
        Subtype.coe_lt_coe.mpr hs
      obtain ⟨r, hrD, hrBetween⟩ := hDense.exists_between hZeroLtS
      obtain ⟨t, htD, htBetween⟩ := hDense.exists_between hsLtOne
      have hrs : r < s := hrBetween.2
      have hst : s < t := htBetween.1
      have hRight : pathSoutheastLE (q u ω s) π := by
        have h := hMono s t (le_of_lt hst)
        rw [hDensePathEq t htD] at h
        exact h
      have hLeft : pathSoutheastLE π (q u ω s) := by
        have h := hMono r s (le_of_lt hrs)
        rw [hDensePathEq r hrD] at h
        exact h
      exact hPathAntisymm (q u ω s) π (hCDF u s).1 hπLoc hRight hLeft

  exact (hToReference s hs).trans (hToReference t ht).symm

end LPP.Busemann
