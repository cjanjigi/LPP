/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Busemann.Process.RationalQuantileOrder

@[expose] public section
open MeasureTheory ProbabilityTheory LPPDifferentiability
open scoped ENNReal
namespace LPP.Busemann

/-- The rational quantile at a threshold is the least upper bound, among
actual geodesics, of quantiles at smaller rational thresholds. The statement
includes the empty lower family at zero. Strong Existence, public source
lines 801–802 and 823–828. -/
theorem exists_unique_rational_quantile_family_left_supremum
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
    ∀ᵐ ω ∂environmentLaw μ,
      ∃! Q : ∀ r : ℚ, 0 ≤ r → r ≤ 1 → (ℕ → Lattice),
        (∀ (r : ℚ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1),
          IsLocallyRightmostGeodesic ω u (Q r hr0 hr1) ∧
          (∀ i : Σ d : ℕ × ℕ, Path u d,
            ENNReal.ofReal (r : ℝ) ≤
              κ ω {η : ℕ → Lattice | pathSoutheastLE η (R i ω)} →
            pathSoutheastLE (Q r hr0 hr1) (R i ω)) ∧
          (∀ δ : ℕ → Lattice,
            IsLocallyRightmostGeodesic ω u δ →
            (∀ i : Σ d : ℕ × ℕ, Path u d,
              ENNReal.ofReal (r : ℝ) ≤
                κ ω {η : ℕ → Lattice | pathSoutheastLE η (R i ω)} →
              pathSoutheastLE δ (R i ω)) →
            pathSoutheastLE δ (Q r hr0 hr1)) ∧
          (∀ γ : ℕ → Lattice,
            IsLocallyRightmostGeodesic ω u γ →
            (pathSoutheastLE (Q r hr0 hr1) γ ↔
              ENNReal.ofReal (r : ℝ) ≤
                κ ω {η : ℕ → Lattice | pathSoutheastLE η γ}))) ∧
        (∀ (s : ℚ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
          (γ : ℕ → Lattice),
          IsLocallyRightmostGeodesic ω u γ →
          (pathSoutheastLE (Q s hs0 hs1) γ ↔
            ∀ (r : ℚ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1), r < s →
              pathSoutheastLE (Q r hr0 hr1) γ)) := by
  classical
  let κ : Kernel Environment (ℕ → Lattice) :=
    condDistrib
      (fun s : ProcessSample => rightmostCocyclePath (fun x y => B x y s) u)
      processEnvironment P
  let R : (Σ d : ℕ × ℕ, Path u d) → Environment → (ℕ → Lattice) :=
    Classical.choose (exists_unique_measurable_right_isolated_geodesic_family u).exists

  -- The producer supplies every rational witness on one event.
  have hProducer := rational_quantile_order_iff_conditional_cdf
    μ P hMarginal B hB u
  have hKernel := conditional_rightmost_path_law_and_thresholds
    μ P hMarginal B hB
  filter_upwards [hProducer] with ω hProducerω
  let : IsProbabilityMeasure (κ ω) := (hKernel.1 u).isProbabilityMeasure ω

  -- Choose the pointwise unique witness only on the valid rational domain.
  let Q : ∀ r : ℚ, 0 ≤ r → r ≤ 1 → ℕ → Lattice :=
    fun r hr0 hr1 => Classical.choose (hProducerω r hr0 hr1).exists
  have hQ (r : ℚ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
      IsLocallyRightmostGeodesic ω u (Q r hr0 hr1) ∧
        (∀ i : Σ d : ℕ × ℕ, Path u d,
          ENNReal.ofReal (r : ℝ) ≤
            κ ω {η : ℕ → Lattice | pathSoutheastLE η (R i ω)} →
          pathSoutheastLE (Q r hr0 hr1) (R i ω)) ∧
        (∀ δ : ℕ → Lattice,
          IsLocallyRightmostGeodesic ω u δ →
          (∀ i : Σ d : ℕ × ℕ, Path u d,
            ENNReal.ofReal (r : ℝ) ≤
              κ ω {η : ℕ → Lattice | pathSoutheastLE η (R i ω)} →
            pathSoutheastLE δ (R i ω)) →
          pathSoutheastLE δ (Q r hr0 hr1)) ∧
        (∀ γ : ℕ → Lattice,
          IsLocallyRightmostGeodesic ω u γ →
          (pathSoutheastLE (Q r hr0 hr1) γ ↔
            ENNReal.ofReal (r : ℝ) ≤
              κ ω {η : ℕ → Lattice | pathSoutheastLE η γ})) := by
    exact Classical.choose_spec (hProducerω r hr0 hr1).exists

  -- The CDF equivalence turns the order statement into a real threshold bound.
  have hLeftSupremum (s : ℚ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
      (γ : ℕ → Lattice) (hγ : IsLocallyRightmostGeodesic ω u γ) :
      (pathSoutheastLE (Q s hs0 hs1) γ ↔
        ∀ (r : ℚ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1), r < s →
          pathSoutheastLE (Q r hr0 hr1) γ) := by
    let Cγ : Set (ℕ → Lattice) := {η | pathSoutheastLE η γ}
    have hCDF := (hQ s hs0 hs1).2.2.2 γ hγ
    constructor
    · intro hAtS r hr0 hr1 hrs
      apply ((hQ r hr0 hr1).2.2.2 γ hγ).mpr
      calc
        ENNReal.ofReal (r : ℝ) ≤ ENNReal.ofReal (s : ℝ) :=
          ENNReal.ofReal_le_ofReal (by exact_mod_cast le_of_lt hrs)
        _ ≤ κ ω Cγ := hCDF.mp hAtS
    · intro hBelow
      apply hCDF.mpr
      by_cases hsZero : s = 0
      · -- At zero there is no smaller valid rational; nonnegativity suffices.
        subst s
        simpa only [Rat.cast_zero, ENNReal.ofReal_zero] using
          (zero_le : (0 : ENNReal) ≤
            κ ω {η : ℕ → Lattice | pathSoutheastLE η γ})
      · -- The conditional kernel is a probability measure, so this CDF is finite.
        have hCDFleOne : κ ω Cγ ≤ 1 := by
          calc
            κ ω Cγ ≤ κ ω Set.univ := measure_mono (Set.subset_univ Cγ)
            _ = 1 := measure_univ
        have hCDFneTop : κ ω Cγ ≠ ⊤ :=
          ne_top_of_le_ne_top (by simp) hCDFleOne
        have hRealBound : (s : ℝ) ≤ (κ ω Cγ).toReal := by
          by_contra hNotBound
          have hCDFltS : (κ ω Cγ).toReal < (s : ℝ) := lt_of_not_ge hNotBound
          obtain ⟨r, hCDFltR, hRltS⟩ := exists_rat_btwn hCDFltS
          have hRnonnegReal : (0 : ℝ) ≤ (r : ℝ) :=
            le_of_lt (lt_of_le_of_lt ENNReal.toReal_nonneg hCDFltR)
          have hr0 : (0 : ℚ) ≤ r := by exact_mod_cast hRnonnegReal
          have hRleOneReal : (r : ℝ) ≤ 1 := by
            exact le_trans (le_of_lt hRltS) (by exact_mod_cast hs1)
          have hr1 : r ≤ 1 := by exact_mod_cast hRleOneReal
          have hrs : r < s := by exact_mod_cast hRltS
          have hOrder : pathSoutheastLE (Q r hr0 hr1) γ :=
            hBelow r hr0 hr1 hrs
          have hRMass : ENNReal.ofReal (r : ℝ) ≤ κ ω Cγ :=
            ((hQ r hr0 hr1).2.2.2 γ hγ).mp hOrder
          have hRReal : (r : ℝ) ≤ (κ ω Cγ).toReal :=
            (ENNReal.ofReal_le_iff_le_toReal hCDFneTop).mp hRMass
          exact (not_lt_of_ge hRReal) hCDFltR
        exact (ENNReal.ofReal_le_iff_le_toReal hCDFneTop).mpr hRealBound

  -- Pointwise uniqueness of the CDF witnesses gives uniqueness of the family.
  refine ⟨Q, ?_, ?_⟩
  · constructor
    · intro r hr0 hr1
      exact hQ r hr0 hr1
    · exact hLeftSupremum
  · intro Q' hQ'
    funext r
    funext hr0
    funext hr1
    obtain ⟨q, _, hUnique⟩ := hProducerω r hr0 hr1
    have hChosenEq : Q r hr0 hr1 = q := hUnique (Q r hr0 hr1) (hQ r hr0 hr1)
    have hOtherEq : Q' r hr0 hr1 = q := hUnique (Q' r hr0 hr1) (hQ'.1 r hr0 hr1)
    exact hOtherEq.trans hChosenEq.symm

end LPP.Busemann
