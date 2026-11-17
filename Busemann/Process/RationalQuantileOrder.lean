/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Busemann.Process.QuantileInfimaComparison

@[expose] public section
open MeasureTheory ProbabilityTheory LPPDifferentiability Filter
open scoped ENNReal
namespace LPP.Busemann

private theorem pathSoutheastLE_trans_same_root
    (a b c : ℕ → Lattice) (hab : pathSoutheastLE a b)
    (hbc : pathSoutheastLE b c) (hrootab : a 0 = b 0)
    (hrootbc : b 0 = c 0) : pathSoutheastLE a c := by
  apply (pathSoutheastLE_iff_all_times_of_same_root a c
    (hrootab.trans hrootbc)).mpr
  have hab' :=
    (pathSoutheastLE_iff_all_times_of_same_root a b hrootab).mp hab
  have hbc' :=
    (pathSoutheastLE_iff_all_times_of_same_root b c hrootbc).mp hbc
  intro n
  exact ⟨(hab' n).1.trans (hbc' n).1, (hbc' n).2.trans (hab' n).2⟩

private theorem pathSoutheastLE_antisymm_same_root
    (a b : ℕ → Lattice) (hroot : a 0 = b 0)
    (hab : pathSoutheastLE a b) (hba : pathSoutheastLE b a) : a = b := by
  have hab' := (pathSoutheastLE_iff_all_times_of_same_root a b hroot).mp hab
  have hba' :=
    (pathSoutheastLE_iff_all_times_of_same_root b a hroot.symm).mp hba
  funext n
  exact Prod.ext (le_antisymm (hab' n).1 (hba' n).1)
    (le_antisymm (hba' n).2 (hab' n).2)

/-- The rational right-isolated quantile lies below a valid geodesic exactly
when its literal conditional lower-cone mass reaches the threshold. This is
the rational case of Strong Existence, public source lines 816–820. -/
theorem rational_quantile_order_iff_conditional_cdf
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
            κ ω {η : ℕ → Lattice | pathSoutheastLE η (R i ω)} →
          pathSoutheastLE q (R i ω)) ∧
        (∀ δ : ℕ → Lattice,
          IsLocallyRightmostGeodesic ω u δ →
          (∀ i : Σ d : ℕ × ℕ, Path u d,
            ENNReal.ofReal (r : ℝ) ≤
              κ ω {η : ℕ → Lattice | pathSoutheastLE η (R i ω)} →
            pathSoutheastLE δ (R i ω)) →
          pathSoutheastLE δ q) ∧
        (∀ γ : ℕ → Lattice,
          IsLocallyRightmostGeodesic ω u γ →
          (pathSoutheastLE q γ ↔
            ENNReal.ofReal (r : ℝ) ≤
              κ ω {η : ℕ → Lattice | pathSoutheastLE η γ})) := by
  classical
  let κ : Kernel Environment (ℕ → Lattice) :=
    condDistrib
      (fun s : ProcessSample => rightmostCocyclePath (fun x y => B x y s) u)
      processEnvironment P
  let R : (Σ d : ℕ × ℕ, Path u d) → Environment → (ℕ → Lattice) :=
    Classical.choose (exists_unique_measurable_right_isolated_geodesic_family u).exists
  have hRI := exists_unique_rational_right_isolated_quantile_inf
    μ P hMarginal B hB u
  have hComparison := rational_right_isolated_infimum_eq_full_geodesic_infimum
    μ P hMarginal B hB u
  have hFullMass := rational_full_geodesic_infimum_cdf_mass
    μ P hMarginal B hB u
  have hKernel := conditional_rightmost_path_law_and_thresholds
    μ P hMarginal B hB
  obtain ⟨A, hAmeas, hAone, hAproperty⟩ := hKernel.2.2.2.2
  have hKernelSupport : ∀ᵐ ω ∂environmentLaw μ, ω ∈ A :=
    (mem_ae_iff_prob_eq_one hAmeas).mpr hAone
  -- Intersect all four environment-a.e. events before introducing the rational.
  filter_upwards [hRI, hComparison, hFullMass, hKernelSupport]
    with ω hRIω hComparisonω hFullMassω hAω
  intro r hr0 hr1
  let : IsProbabilityMeasure (κ ω) :=
    (hKernel.1 u).isProbabilityMeasure ω
  obtain ⟨qRI, hqRI, hRIUnique⟩ := hRIω r hr0 hr1
  obtain ⟨qCmp, hqCmp, _⟩ := hComparisonω r hr0 hr1
  obtain ⟨qFull, hqFull, _⟩ := hFullMassω r hr0 hr1

  -- Reciprocal full-family GLB clauses identify the witnesses before mass transport.
  have hCmpBelowFull : pathSoutheastLE qCmp qFull := by
    exact hqFull.2.2.1 qCmp hqCmp.1 hqCmp.2.2.2.1
  have hFullBelowCmp : pathSoutheastLE qFull qCmp := by
    apply hqCmp.2.2.2.2 qFull hqFull.1
    intro γ hγ hγmass
    exact hqFull.2.1 γ hγ hγmass
  have hCmpFullRoot : qCmp 0 = qFull 0 :=
    hqCmp.1.1.trans hqFull.1.1.symm
  have hCmpEqFull : qCmp = qFull :=
    pathSoutheastLE_antisymm_same_root qCmp qFull hCmpFullRoot
      hCmpBelowFull hFullBelowCmp

  -- Final uniqueness is only the right-isolated GLB uniqueness.
  have hCmpRI :
      IsLocallyRightmostGeodesic ω u qCmp ∧
        (∀ i : Σ d : ℕ × ℕ, Path u d,
          ENNReal.ofReal (r : ℝ) ≤
            κ ω {η : ℕ → Lattice | pathSoutheastLE η (R i ω)} →
          pathSoutheastLE qCmp (R i ω)) ∧
        (∀ δ : ℕ → Lattice,
          IsLocallyRightmostGeodesic ω u δ →
          (∀ i : Σ d : ℕ × ℕ, Path u d,
            ENNReal.ofReal (r : ℝ) ≤
              κ ω {η : ℕ → Lattice | pathSoutheastLE η (R i ω)} →
            pathSoutheastLE δ (R i ω)) →
          pathSoutheastLE δ qCmp) :=
    ⟨hqCmp.1, hqCmp.2.1, hqCmp.2.2.1⟩
  have hCmpEqRI : qCmp = qRI := hRIUnique qCmp hCmpRI
  have hRIEqFull : qRI = qFull := hCmpEqRI.symm.trans hCmpEqFull
  have hMassAtRI : ENNReal.ofReal (r : ℝ) ≤
      κ ω {η : ℕ → Lattice | pathSoutheastLE η qRI} := by
    rw [hRIEqFull]
    exact hqFull.2.2.2

  -- Kernel support turns raw lower-cone masses into literal CDFs.
  let G : Set (ℕ → Lattice) :=
    {η | IsLocallyRightmostGeodesic ω u η}
  let C (b : ℕ → Lattice) : Set (ℕ → Lattice) :=
    {η | pathSoutheastLE η b}
  have hGmeas : MeasurableSet G :=
    measurableSet_isLocallyRightmostGeodesic.preimage
      (measurable_const.prodMk (measurable_const.prodMk measurable_id))
  have hGfull : κ ω G = 1 := (hAproperty ω hAω u).1
  have hGnull : κ ω Gᶜ = 0 :=
    (prob_compl_eq_zero_iff hGmeas).mpr hGfull
  have hSupportedMass (b : ℕ → Lattice) :
      κ ω (G ∩ C b) = κ ω (C b) := by
    change κ ω (G ∩ {η | pathSoutheastLE η b}) =
      κ ω {η | pathSoutheastLE η b}
    rw [Set.inter_comm]
    exact MeasureTheory.measure_inter_conull hGnull
  have hConeInclusion (γ : ℕ → Lattice)
      (hγ : IsLocallyRightmostGeodesic ω u γ)
      (hqγ : pathSoutheastLE qRI γ) : G ∩ C qRI ⊆ G ∩ C γ := by
    rintro η ⟨hη, hηq⟩
    refine ⟨hη, ?_⟩
    exact pathSoutheastLE_trans_same_root η qRI γ hηq hqγ
      (hη.1.trans hqRI.1.1.symm)
      (hqRI.1.1.trans hγ.1.symm)
  have hOrderToMass (γ : ℕ → Lattice)
      (hγ : IsLocallyRightmostGeodesic ω u γ)
      (hqγ : pathSoutheastLE qRI γ) :
      ENNReal.ofReal (r : ℝ) ≤ κ ω (C γ) := by
    calc
      ENNReal.ofReal (r : ℝ) ≤ κ ω (C qRI) := hMassAtRI
      _ = κ ω (G ∩ C qRI) := (hSupportedMass qRI).symm
      _ ≤ κ ω (G ∩ C γ) := measure_mono (hConeInclusion γ hγ hqγ)
      _ = κ ω (C γ) := hSupportedMass γ
  have hMassToOrder (γ : ℕ → Lattice)
      (hγ : IsLocallyRightmostGeodesic ω u γ)
      (hγmass : ENNReal.ofReal (r : ℝ) ≤ κ ω (C γ)) :
      pathSoutheastLE qRI γ := by
    rw [hRIEqFull]
    exact hqFull.2.1 γ hγ hγmass

  refine ⟨qRI, ?_, ?_⟩
  · refine ⟨hqRI.1, hqRI.2.1, hqRI.2.2, ?_⟩
    intro γ hγ
    exact ⟨hOrderToMass γ hγ, hMassToOrder γ hγ⟩
  · intro q' hq'
    apply hRIUnique q'
    exact ⟨hq'.1, hq'.2.1, hq'.2.2.1⟩

end LPP.Busemann
