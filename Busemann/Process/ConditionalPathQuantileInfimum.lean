/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Busemann.Process.ConditionalPathKernel
public import Busemann.Geometry.RightIsolatedGeodesicFamily
public import Busemann.Geometry.GeodesicCompactness
public import Busemann.Geometry.GeodesicOrder
public import Busemann.Geometry.GeodesicInfimum
public import LPP_Foundations.Model.Paths.HorizontalFirst
import Mathlib.Tactic

@[expose] public section
open MeasureTheory ProbabilityTheory LPPDifferentiability
open scoped ENNReal
namespace LPP.Busemann

/-- First source-order prerequisite for the rational conditional-path quantile:
on one full physical-environment event, the qualifying right-isolated
geodesics have their greatest lower bound in the actual geodesic tree.
Strong Existence, public source lines 754–760 and 775–814. -/
theorem exists_unique_rational_right_isolated_quantile_inf
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (P : Measure ProcessSample) [IsProbabilityMeasure P]
    (hMarginal : P.map processEnvironment = environmentLaw μ)
    (B : Lattice → Lattice → ProcessSample → ℝ)
    (hB : IsGeneralizedBusemann P processShift processEnvironment B)
    (u : Lattice) :
    let κ : Kernel Environment (ℕ → Lattice) :=
      condDistrib
        (fun s : ProcessSample => rightmostCocyclePath (fun x y => B x y s) u)
        processEnvironment P
    let R : (Σ d : ℕ × ℕ, Path u d) → Environment → (ℕ → Lattice) :=
      Classical.choose (exists_unique_measurable_right_isolated_geodesic_family u).exists
    ∀ᵐ ω ∂environmentLaw μ, ∀ (r : ℚ), 0 ≤ r → r ≤ 1 →
      ∃! q : ℕ → Lattice,
        IsLocallyRightmostGeodesic ω u q ∧
        (∀ i : Σ d : ℕ × ℕ, Path u d,
          ENNReal.ofReal (r : ℝ) ≤
            κ ω {γ : ℕ → Lattice | pathSoutheastLE γ (R i ω)} →
          pathSoutheastLE q (R i ω)) ∧
        (∀ δ : ℕ → Lattice,
          IsLocallyRightmostGeodesic ω u δ →
          (∀ i : Σ d : ℕ × ℕ, Path u d,
            ENNReal.ofReal (r : ℝ) ≤
              κ ω {γ : ℕ → Lattice | pathSoutheastLE γ (R i ω)} →
            pathSoutheastLE δ (R i ω)) →
          pathSoutheastLE δ q)
    := by
  classical
  let κ : Kernel Environment (ℕ → Lattice) :=
    condDistrib
      (fun s : ProcessSample => rightmostCocyclePath (fun x y => B x y s) u)
      processEnvironment P
  let R : (Σ d : ℕ × ℕ, LPPDifferentiability.Path u d) →
      Environment → (ℕ → Lattice) :=
    Classical.choose (exists_unique_measurable_right_isolated_geodesic_family u).exists
  have hR := Classical.choose_spec
    (exists_unique_measurable_right_isolated_geodesic_family u).exists
  have hKernel := conditional_rightmost_path_law_and_thresholds
    μ P hMarginal B hB
  obtain ⟨A, hAmeas, hAone, hAproperty⟩ := hKernel.2.2.2.2
  have hAE : ∀ᵐ ω ∂environmentLaw μ, ω ∈ A :=
    (mem_ae_iff_prob_eq_one hAmeas).mpr hAone
  filter_upwards [hAE] with ω hω
  intro r hr0 hr1
  let i₀ : Σ d : ℕ × ℕ, LPPDifferentiability.Path u d :=
    ⟨(0, 0), horizontalFirst u (0, 0)⟩
  have hRactual (i : Σ d : ℕ × ℕ, LPPDifferentiability.Path u d) :
      IsLocallyRightmostGeodesic ω u (R i ω) := by
    obtain ⟨e, q, hg, _, _⟩ := hR.2.2.1 i ω
    exact hg
  have hZeroPrefix (γ : ℕ → Lattice)
      (hγ : IsLocallyRightmostGeodesic ω u γ) :
      ∀ k : Fin (i₀.1.1 + i₀.1.2 + 1), i₀.2.vertex k = γ k.val := by
    intro k
    have hk : k.val = 0 := by
      have hlt : k.val < 1 := by simp [i₀]
      omega
    have hkFin : k = 0 := Fin.ext hk
    subst k
    simpa [i₀] using (horizontalFirst u (0, 0)).start.trans hγ.1.symm
  have hTop : ∀ γ : ℕ → Lattice,
      IsLocallyRightmostGeodesic ω u γ → pathSoutheastLE γ (R i₀ ω) := by
    have hA : ∃ γ : ℕ → Lattice,
        IsLocallyRightmostGeodesic ω u γ ∧
        ∀ k : Fin (i₀.1.1 + i₀.1.2 + 1), i₀.2.vertex k = γ k.val :=
      ⟨R i₀ ω, hRactual i₀, hZeroPrefix (R i₀ ω) (hRactual i₀)⟩
    have hPrefix := (hR.2.1 i₀ ω).1 hA
    intro γ hγ
    exact hPrefix.2.2 γ hγ (fun k => (hZeroPrefix γ hγ k).symm)
  have hMass : κ ω {γ : ℕ → Lattice | pathSoutheastLE γ (R i₀ ω)} = 1 := by
    have hSubset :
        {γ : ℕ → Lattice | IsLocallyRightmostGeodesic ω u γ} ⊆
          {γ : ℕ → Lattice | pathSoutheastLE γ (R i₀ ω)} := by
      intro γ hγ
      exact hTop γ hγ
    have hUpper : κ ω {γ : ℕ → Lattice | pathSoutheastLE γ (R i₀ ω)} ≤ 1 := by
      calc
        κ ω {γ : ℕ → Lattice | pathSoutheastLE γ (R i₀ ω)} ≤
            κ ω Set.univ := measure_mono (Set.subset_univ _)
        _ = 1 := by
          exact measure_univ
    have hLocal : κ ω {γ : ℕ → Lattice | IsLocallyRightmostGeodesic ω u γ} = 1 :=
      (hAproperty ω hω u).1
    exact le_antisymm hUpper (by rw [← hLocal]; exact measure_mono hSubset)
  have hLevel : ENNReal.ofReal (r : ℝ) ≤ 1 := by
    simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal
      (show (r : ℝ) ≤ 1 by exact_mod_cast hr1)
  let F : Set (ℕ → Lattice) :=
    {γ | ∃ i : Σ d : ℕ × ℕ, LPPDifferentiability.Path u d,
      γ = R i ω ∧ ENNReal.ofReal (r : ℝ) ≤
        κ ω {η : ℕ → Lattice | pathSoutheastLE η (R i ω)}}
  have hFnonempty : F.Nonempty := by
    refine ⟨R i₀ ω, i₀, rfl, ?_⟩
    rw [hMass]
    exact hLevel
  have hFvalid : ∀ γ ∈ F, IsLocallyRightmostGeodesic ω u γ := by
    intro γ hγ
    obtain ⟨i, rfl, _⟩ := hγ
    exact hRactual i
  obtain ⟨q, hq, huniq⟩ :=
    exists_unique_geodesic_infimum ω u F hFnonempty hFvalid
  refine ⟨q, ?_, ?_⟩
  · refine ⟨hq.1, ?_, ?_⟩
    · intro i hi
      exact hq.2.1 (R i ω) ⟨i, rfl, hi⟩
    · intro δ hδ hd
      apply hq.2.2 δ hδ
      intro γ hγ
      obtain ⟨i, rfl, hi⟩ := hγ
      exact hd i hi
  · intro δ hδ
    apply huniq δ
    refine ⟨hδ.1, ?_, ?_⟩
    · intro γ hγ
      obtain ⟨i, rfl, hi⟩ := hγ
      exact hδ.2.1 i hi
    · intro η hη hηlower
      apply hδ.2.2 η hη
      intro i hi
      exact hηlower (R i ω) ⟨i, rfl, hi⟩

end LPP.Busemann
