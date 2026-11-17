/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Busemann.Process.RealQuantileExtension
public import Busemann.Geometry.GeodesicLowerCut
public import Mathlib.MeasureTheory.Constructions.UnitInterval

import Busemann.Geometry.RootedCoordinateBarrier
import Lean.Elab.Tactic.Omega

@[expose] public section
open MeasureTheory ProbabilityTheory LPPDifferentiability
open scoped ENNReal
namespace LPP.Busemann

private theorem locally_rightmost_coordinate_bounds
    (ω : Environment) (u : Lattice) (γ : ℕ → Lattice)
    (hγ : IsLocallyRightmostGeodesic ω u γ) (n : ℕ) :
    u.1 ≤ (γ n).1 ∧ (γ n).1 ≤ u.1 + (n : ℤ) ∧
      (γ n).1 + (γ n).2 = u.1 + u.2 + (n : ℤ) := by
  induction n with
  | zero =>
      rw [hγ.1]
      simp
  | succ n ih =>
      rcases hγ.2.1 n with hEast | hNorth
      · rw [hEast]
        simp only [Prod.fst_add, Prod.snd_add, Nat.cast_succ]
        omega
      · rw [hNorth]
        simp only [Prod.fst_add, Prod.snd_add, Nat.cast_succ]
        omega

-- The rational CDF bounds below a real parameter are equivalent to its
-- inclusive real CDF bound, including both endpoints of the unit interval.
private theorem real_cdf_bound_iff_all_lower_rational_bounds
    (m : ENNReal) (hm : m ≤ 1) (s : ℝ) (hs1 : s ≤ 1) :
    (ENNReal.ofReal s ≤ m ↔
      ∀ (r : ℚ), 0 ≤ r → r ≤ 1 → (r : ℝ) < s →
        ENNReal.ofReal (r : ℝ) ≤ m) := by
  constructor
  · intro hs r _hr0 _hr1 hrs
    exact (ENNReal.ofReal_le_ofReal (le_of_lt hrs)).trans hs
  · intro hLower
    have hmTop : m ≠ ⊤ := ne_top_of_le_ne_top (by simp) hm
    have hsReal : s ≤ m.toReal := by
      by_contra hNot
      have hms : m.toReal < s := lt_of_not_ge hNot
      obtain ⟨r, hmr, hrs⟩ := exists_rat_btwn hms
      have hr0Real : (0 : ℝ) ≤ (r : ℝ) :=
        le_of_lt (lt_of_le_of_lt ENNReal.toReal_nonneg hmr)
      have hr0 : (0 : ℚ) ≤ r := by exact_mod_cast hr0Real
      have hr1Real : (r : ℝ) ≤ 1 := (le_of_lt hrs).trans hs1
      have hr1 : r ≤ 1 := by exact_mod_cast hr1Real
      have hrMass : ENNReal.ofReal (r : ℝ) ≤ m := hLower r hr0 hr1 hrs
      have hrReal : (r : ℝ) ≤ m.toReal :=
        (ENNReal.ofReal_le_iff_le_toReal hmTop).mp hrMass
      exact (not_lt_of_ge hrReal) hmr
    exact (ENNReal.ofReal_le_iff_le_toReal hmTop).mpr hsReal

/-- The published rational-infimum and real-left-supremum quantiles form one
jointly measurable path family with their geodesic CDF characterization.
Strong Existence, public source lines 754–835. -/
theorem exists_measurable_real_rightmost_quantile_family
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (P : Measure ProcessSample) [IsProbabilityMeasure P]
    (hMarginal : P.map processEnvironment = environmentLaw μ)
    (B : Lattice → Lattice → ProcessSample → ℝ)
    (hB : IsGeneralizedBusemann P processShift processEnvironment B) :
    let κ : Lattice → Kernel Environment (ℕ → Lattice) :=
      fun u => condDistrib
        (fun a : ProcessSample =>
          rightmostCocyclePath (fun x y => B x y a) u)
        processEnvironment P
    ∃ q : Lattice → Environment → unitInterval → (ℕ → Lattice),
      (∀ u : Lattice, Measurable
        (fun a : Environment × unitInterval => q u a.1 a.2)) ∧
      (∀ᵐ ω ∂environmentLaw μ, ∀ (u : Lattice) (s : unitInterval),
        IsLocallyRightmostGeodesic ω u (q u ω s) ∧
        ∀ γ : ℕ → Lattice, IsLocallyRightmostGeodesic ω u γ →
          (pathSoutheastLE (q u ω s) γ ↔
            ENNReal.ofReal (s : ℝ) ≤
              (κ u) ω {η : ℕ → Lattice | pathSoutheastLE η γ})) := by
  classical
  let κ : Lattice → Kernel Environment (ℕ → Lattice) :=
    fun u => condDistrib
      (fun a : ProcessSample =>
        rightmostCocyclePath (fun x y => B x y a) u)
      processEnvironment P
  -- Retain the two source families together. The rational CDF uniquely
  -- characterizes the rational-infimum family, and the real family
  -- is precisely its left supremum, not a newly sampled kernel path.
  let Good (u : Lattice) (ω : Environment) : Prop :=
    ∃ Q : ∀ r : ℚ, 0 ≤ r → r ≤ 1 → (ℕ → Lattice),
      (∀ (r : ℚ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1),
        IsLocallyRightmostGeodesic ω u (Q r hr0 hr1) ∧
        ∀ γ : ℕ → Lattice, IsLocallyRightmostGeodesic ω u γ →
          (pathSoutheastLE (Q r hr0 hr1) γ ↔
            ENNReal.ofReal (r : ℝ) ≤
              (κ u) ω {η : ℕ → Lattice | pathSoutheastLE η γ})) ∧
      ∃ q : ∀ s : ℝ, 0 ≤ s → s ≤ 1 → (ℕ → Lattice),
        ∀ (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1),
          IsLocallyRightmostGeodesic ω u (q s hs0 hs1) ∧
          ∀ γ : ℕ → Lattice, IsLocallyRightmostGeodesic ω u γ →
            (pathSoutheastLE (q s hs0 hs1) γ ↔
              ∀ (r : ℚ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1), (r : ℝ) < s →
                pathSoutheastLE (Q r hr0 hr1) γ)
  have hGoodAE (u : Lattice) : ∀ᵐ ω ∂environmentLaw μ, Good u ω := by
    have hReal := exists_unique_real_quantile_family_left_supremum
      μ P hMarginal B hB u
    filter_upwards [hReal] with ω hω
    obtain ⟨Q, hQ, q, hq, _⟩ := hω
    refine ⟨Q, ?_, q, hq.1⟩
    intro r hr0 hr1
    have hr := hQ r hr0 hr1
    exact ⟨hr.1, hr.2.1⟩
  have hAllAE : ∀ᵐ ω ∂environmentLaw μ, ∀ u : Lattice, Good u ω :=
    ae_all_iff.mpr hGoodAE
  let G : Set Environment := {ω | ∀ u : Lattice, Good u ω}
  have hGNull : environmentLaw μ Gᶜ = 0 := (mem_ae_iff).mp hAllAE
  have hGNullMeas : NullMeasurableSet G (environmentLaw μ) := by
    simpa only [compl_compl] using (NullMeasurableSet.of_null hGNull).compl
  obtain ⟨A, hAG, hAMeas, hAeq⟩ := hGNullMeas.exists_measurable_subset_ae_eq
  have hAae : ∀ᵐ ω ∂environmentLaw μ, ω ∈ A := by
    apply (ae_eq_univ).mp
    exact hAeq.trans ((ae_eq_univ).mpr hGNull)
  have hKernel := conditional_rightmost_path_law_and_thresholds
    μ P hMarginal B hB
  obtain ⟨K, hKMeas, hKOne, hKSupport⟩ := hKernel.2.2.2.2
  have hKae : ∀ᵐ ω ∂environmentLaw μ, ω ∈ K :=
    (mem_ae_iff_prob_eq_one hKMeas).mpr hKOne
  let C : Set Environment := A ∩ K
  have hCMeas : MeasurableSet C := hAMeas.inter hKMeas
  have hCae : ∀ᵐ ω ∂environmentLaw μ, ω ∈ C := by
    filter_upwards [hAae, hKae] with ω hωA hωK
    exact ⟨hωA, hωK⟩
  let qSource (u : Lattice) (ω : Environment) (hω : ω ∈ C) :=
    Classical.choose ((Classical.choose_spec ((hAG hω.1) u)).2)
  let q : Lattice → Environment → unitInterval → (ℕ → Lattice) :=
    fun u ω s =>
      if hω : ω ∈ C then
        qSource u ω hω s.val s.property.1 s.property.2
      else
        fun n : ℕ => u + ((0 : ℤ), (n : ℤ))
  have hRealCDF (u : Lattice) (ω : Environment) (hω : ω ∈ C)
      (s : unitInterval) (γ : ℕ → Lattice)
      (hγ : IsLocallyRightmostGeodesic ω u γ) :
      IsLocallyRightmostGeodesic ω u
          (qSource u ω hω s.val s.property.1 s.property.2) ∧
        (pathSoutheastLE
            (qSource u ω hω s.val s.property.1 s.property.2) γ ↔
          ENNReal.ofReal (s : ℝ) ≤
            (κ u) ω {η : ℕ → Lattice | pathSoutheastLE η γ}) := by
    have hSource := Classical.choose_spec ((hAG hω.1) u)
    have hQ (r : ℚ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :=
      hSource.1 r hr0 hr1
    have hq := Classical.choose_spec hSource.2
    have hqAt := hq s.val s.property.1 s.property.2
    let : IsProbabilityMeasure ((κ u) ω) := (hKernel.1 u).isProbabilityMeasure ω
    let m : ENNReal :=
      (κ u) ω {η : ℕ → Lattice | pathSoutheastLE η γ}
    have hm : m ≤ 1 := by
      calc
        m ≤ (κ u) ω Set.univ := measure_mono (Set.subset_univ _)
        _ = 1 := measure_univ
    have hBound := real_cdf_bound_iff_all_lower_rational_bounds
      m hm s.val s.property.2
    refine ⟨hqAt.1, ?_⟩
    constructor
    · intro hqγ
      apply hBound.mpr
      intro r hr0 hr1 hrs
      exact ((hQ r hr0 hr1).2 γ hγ).mp
        ((hqAt.2 γ hγ).mp hqγ r hr0 hr1 hrs)
    · intro hMass
      apply (hqAt.2 γ hγ).mpr
      intro r hr0 hr1 hrs
      exact ((hQ r hr0 hr1).2 γ hγ).mpr
        (hBound.mp hMass r hr0 hr1 hrs)
  have hCutMass (u : Lattice) (ω : Environment) (hω : ω ∈ C)
      (β g : ℕ → Lattice)
      (hCut : ∀ η : ℕ → Lattice, IsLocallyRightmostGeodesic ω u η →
        (pathSoutheastLE η β ↔ pathSoutheastLE η g)) :
      (κ u) ω {η : ℕ → Lattice | pathSoutheastLE η β} =
        (κ u) ω {η : ℕ → Lattice | pathSoutheastLE η g} := by
    let : IsProbabilityMeasure ((κ u) ω) := (hKernel.1 u).isProbabilityMeasure ω
    have hFiberMeas : MeasurableSet
        {η : ℕ → Lattice | IsLocallyRightmostGeodesic ω u η} :=
      measurableSet_isLocallyRightmostGeodesic.preimage
        (measurable_const.prodMk
          (measurable_const.prodMk measurable_id))
    have hFiberAE : ∀ᵐ η ∂(κ u) ω,
        IsLocallyRightmostGeodesic ω u η :=
      (mem_ae_iff_prob_eq_one hFiberMeas).mpr (hKSupport ω hω.2 u).1
    apply measure_congr
    filter_upwards [hFiberAE] with η hη
    exact propext (hCut η hη)
  have hFixedThreshold (u : Lattice) (β : ℕ → Lattice) :
      MeasurableSet
        {a : Environment × unitInterval |
          ENNReal.ofReal (a.2 : ℝ) ≤
            (κ u) a.1 {η : ℕ → Lattice | pathSoutheastLE η β}} := by
    have hMap : Measurable
        (fun a : Environment × unitInterval => (a.1, (β, a.2))) :=
      measurable_fst.prodMk (measurable_const.prodMk measurable_snd)
    exact (hKernel.2.2.2.1 u).preimage hMap
  have hChosenValid (u : Lattice) (ω : Environment) (hω : ω ∈ C)
      (s : unitInterval) :
      IsLocallyRightmostGeodesic ω u
        (qSource u ω hω s.val s.property.1 s.property.2) := by
    have hq := Classical.choose_spec
      ((Classical.choose_spec ((hAG hω.1) u)).2)
    exact (hq s.val s.property.1 s.property.2).1
  have hGlobalBounds (u : Lattice) (a : Environment × unitInterval)
      (n : ℕ) :
      u.1 ≤ (q u a.1 a.2 n).1 ∧
      (q u a.1 a.2 n).1 ≤ u.1 + (n : ℤ) ∧
      (q u a.1 a.2 n).1 + (q u a.1 a.2 n).2 =
        u.1 + u.2 + (n : ℤ) := by
    by_cases hω : a.1 ∈ C
    · have hValid := hChosenValid u a.1 hω a.2
      simpa only [q, dite_eq_left hω] using
        locally_rightmost_coordinate_bounds a.1 u
          (qSource u a.1 hω a.2.val a.2.property.1 a.2.property.2)
          hValid n
    · simp [q, hω]; omega
  have hCoordinateThresholdOfBarrier
      (u : Lattice) (n k : ℕ) (β : ℕ → Lattice)
      (hβroot : β 0 = u)
      (hβstep : ∀ t : ℕ,
        β (t + 1) = β t + ((1 : ℤ), (0 : ℤ)) ∨
          β (t + 1) = β t + ((0 : ℤ), (1 : ℤ)))
      (hβcoordinate : ∀ (ω : Environment) (γ : ℕ → Lattice),
        IsLocallyRightmostGeodesic ω u γ →
          (pathSoutheastLE γ β ↔ (γ n).1 ≤ u.1 + (k : ℤ)))
      (hβnonempty : ∀ ω : Environment, ∃ γ : ℕ → Lattice,
        IsLocallyRightmostGeodesic ω u γ ∧ pathSoutheastLE γ β) :
      MeasurableSet
        {a : Environment × unitInterval |
          (q u a.1 a.2 n).1 ≤ u.1 + (k : ℤ)} := by
    have hPointwise (a : Environment × unitInterval) (ha : a.1 ∈ C) :
        ((q u a.1 a.2 n).1 ≤ u.1 + (k : ℤ) ↔
          ENNReal.ofReal (a.2 : ℝ) ≤
            (κ u) a.1 {η : ℕ → Lattice | pathSoutheastLE η β}) := by
      obtain ⟨g, hgValid, _hgBarrier, hgCut⟩ :=
        exists_greatest_geodesic_below_rooted_upRight_path
          a.1 u β hβroot hβstep (hβnonempty a.1)
      have hSelectedValid := hChosenValid u a.1 ha a.2
      have hCDF := (hRealCDF u a.1 ha a.2 g hgValid).2
      have hMassEq := hCutMass u a.1 ha β g hgCut
      simp only [q, dite_eq_left ha]
      constructor
      · intro hCoordinate
        have hBelowβ := (hβcoordinate a.1 _ hSelectedValid).mpr hCoordinate
        have hBelowG := (hgCut _ hSelectedValid).mp hBelowβ
        have hBoundG := hCDF.mp hBelowG
        simpa only [hMassEq] using hBoundG
      · intro hBoundβ
        have hBoundG : ENNReal.ofReal (a.2 : ℝ) ≤
            (κ u) a.1 {η : ℕ → Lattice | pathSoutheastLE η g} := by
          simpa only [hMassEq] using hBoundβ
        have hBelowG := hCDF.mpr hBoundG
        have hBelowβ := (hgCut _ hSelectedValid).mpr hBelowG
        exact (hβcoordinate a.1 _ hSelectedValid).mp hBelowβ
    have hThreshold := hFixedThreshold u β
    have hCProduct : MeasurableSet
        {a : Environment × unitInterval | a.1 ∈ C} :=
      hCMeas.preimage measurable_fst
    have hSetEq :
        {a : Environment × unitInterval |
          (q u a.1 a.2 n).1 ≤ u.1 + (k : ℤ)} =
        {a | a.1 ∉ C} ∪
          ({a | a.1 ∈ C} ∩
            {a | ENNReal.ofReal (a.2 : ℝ) ≤
              (κ u) a.1 {η : ℕ → Lattice | pathSoutheastLE η β}}) := by
      ext a
      by_cases ha : a.1 ∈ C
      · simp only [Set.mem_ofPred_eq, ha, not_true_eq_false, Set.mem_union,
          Set.mem_inter_iff, false_or, true_and]
        exact hPointwise a ha
      · simp only [Set.mem_ofPred_eq, ha, not_false_eq_true, Set.mem_union,
          Set.mem_inter_iff, true_or, false_and]
        simp [q, ha]
    rw [hSetEq]
    exact hCProduct.compl.union (hCProduct.inter hThreshold)
  have hMeasFromCoordinateThresholds
      (hThresholds : ∀ (u : Lattice) (n k : ℕ), k ≤ n →
        MeasurableSet
          {a : Environment × unitInterval |
            (q u a.1 a.2 n).1 ≤ u.1 + (k : ℤ)}) :
      ∀ u : Lattice,
        Measurable (fun a : Environment × unitInterval => q u a.1 a.2) := by
    intro u
    apply measurable_pi_iff.mpr
    intro n
    have hFirst : Measurable
        (fun a : Environment × unitInterval => (q u a.1 a.2 n).1) := by
      apply measurable_of_Iic
      intro z
      change MeasurableSet
        {a : Environment × unitInterval | (q u a.1 a.2 n).1 ≤ z}
      by_cases hzBelow : z < u.1
      · have hEmpty :
            {a : Environment × unitInterval | (q u a.1 a.2 n).1 ≤ z} = ∅ := by
          ext a
          have hLow := (hGlobalBounds u a n).1
          simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
          omega
        rw [hEmpty]
        exact MeasurableSet.empty
      by_cases hzAbove : u.1 + (n : ℤ) ≤ z
      · have hUniv :
            {a : Environment × unitInterval | (q u a.1 a.2 n).1 ≤ z} =
              Set.univ := by
          ext a
          have hHigh := (hGlobalBounds u a n).2.1
          simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true]
          omega
        rw [hUniv]
        exact MeasurableSet.univ
      let k : ℕ := (z - u.1).toNat
      have hk : k ≤ n := by omega
      have hkValue : u.1 + (k : ℤ) = z := by omega
      simpa only [hkValue] using hThresholds u n k hk
    have hSecondEq :
        (fun a : Environment × unitInterval => (q u a.1 a.2 n).2) =
        (fun a : Environment × unitInterval =>
          u.1 + u.2 + (n : ℤ) - (q u a.1 a.2 n).1) := by
      funext a
      have hLevel := (hGlobalBounds u a n).2.2
      omega
    have hSecond : Measurable
        (fun a : Environment × unitInterval => (q u a.1 a.2 n).2) := by
      rw [hSecondEq]
      exact measurable_const.sub hFirst
    exact hFirst.prodMk hSecond
  have hFinalAE : ∀ᵐ ω ∂environmentLaw μ,
      ∀ (u : Lattice) (s : unitInterval),
        IsLocallyRightmostGeodesic ω u (q u ω s) ∧
        ∀ γ : ℕ → Lattice, IsLocallyRightmostGeodesic ω u γ →
          (pathSoutheastLE (q u ω s) γ ↔
            ENNReal.ofReal (s : ℝ) ≤
              (κ u) ω {η : ℕ → Lattice | pathSoutheastLE η γ}) := by
    filter_upwards [hCae] with ω hω
    intro u s
    constructor
    · simpa only [q, dite_eq_left hω] using hChosenValid u ω hω s
    · intro γ hγ
      simpa only [q, dite_eq_left hω] using
        (hRealCDF u ω hω s γ hγ).2
  have hCoordinateThresholds (u : Lattice) (n k : ℕ) (hk : k ≤ n) :
      MeasurableSet
        {a : Environment × unitInterval |
          (q u a.1 a.2 n).1 ≤ u.1 + (k : ℤ)} := by
    obtain ⟨β, hβroot, hβstep, hβcoordinate, hβnonempty⟩ :=
      exists_rooted_coordinate_barrier u n k hk
    exact hCoordinateThresholdOfBarrier u n k β hβroot hβstep
      hβcoordinate hβnonempty
  exact ⟨q, hMeasFromCoordinateThresholds hCoordinateThresholds, hFinalAE⟩

end LPP.Busemann
