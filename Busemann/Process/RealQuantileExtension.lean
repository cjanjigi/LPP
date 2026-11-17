/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Busemann.Process.RationalQuantileFamily
public import Busemann.Geometry.GeodesicSupremum

@[expose] public section
open MeasureTheory ProbabilityTheory LPPDifferentiability
open scoped ENNReal
namespace LPP.Busemann

/-- On one environment event, the rational conditional quantiles extend
uniquely to the printed real parameter interval by taking the least upper
bound of all smaller rational quantiles, with agreement at rational times.
Strong Existence, public source lines 762–766 and 823–830. -/
theorem exists_unique_real_quantile_family_left_supremum
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
    ∀ᵐ ω ∂environmentLaw μ,
      ∃ Q : ∀ r : ℚ, 0 ≤ r → r ≤ 1 → (ℕ → Lattice),
        (∀ (r : ℚ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1),
          IsLocallyRightmostGeodesic ω u (Q r hr0 hr1) ∧
          (∀ γ : ℕ → Lattice,
            IsLocallyRightmostGeodesic ω u γ →
            (pathSoutheastLE (Q r hr0 hr1) γ ↔
              ENNReal.ofReal (r : ℝ) ≤
                κ ω {η : ℕ → Lattice | pathSoutheastLE η γ})) ∧
          (∀ γ : ℕ → Lattice,
            IsLocallyRightmostGeodesic ω u γ →
            (pathSoutheastLE (Q r hr0 hr1) γ ↔
              ∀ (v : ℚ) (hv0 : 0 ≤ v) (hv1 : v ≤ 1), v < r →
                pathSoutheastLE (Q v hv0 hv1) γ))) ∧
        ∃! q : ∀ s : ℝ, 0 ≤ s → s ≤ 1 → (ℕ → Lattice),
          (∀ (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1),
            IsLocallyRightmostGeodesic ω u (q s hs0 hs1) ∧
            (∀ γ : ℕ → Lattice,
              IsLocallyRightmostGeodesic ω u γ →
              (pathSoutheastLE (q s hs0 hs1) γ ↔
                ∀ (r : ℚ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1), (r : ℝ) < s →
                  pathSoutheastLE (Q r hr0 hr1) γ))) ∧
          (∀ (r : ℚ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
            (hreal0 : (0 : ℝ) ≤ (r : ℝ)) (hreal1 : (r : ℝ) ≤ 1),
            q (r : ℝ) hreal0 hreal1 = Q r hr0 hr1) := by
  classical
  let κ : Kernel Environment (ℕ → Lattice) :=
    condDistrib
      (fun s : ProcessSample => rightmostCocyclePath (fun x y => B x y s) u)
      processEnvironment P
  -- Source step 1: retain one rational family on its single common event.
  have hRationalAE :=
    exists_unique_rational_quantile_family_left_supremum μ P hMarginal B hB u
  filter_upwards [hRationalAE] with ω hRationalω
  obtain ⟨Q, hQSource, _hQSourceUnique⟩ := hRationalω
  have hQProperties :
      ∀ (r : ℚ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1),
        IsLocallyRightmostGeodesic ω u (Q r hr0 hr1) ∧
        (∀ γ : ℕ → Lattice,
          IsLocallyRightmostGeodesic ω u γ →
          (pathSoutheastLE (Q r hr0 hr1) γ ↔
            ENNReal.ofReal (r : ℝ) ≤
              κ ω {η : ℕ → Lattice | pathSoutheastLE η γ})) ∧
        (∀ γ : ℕ → Lattice,
          IsLocallyRightmostGeodesic ω u γ →
          (pathSoutheastLE (Q r hr0 hr1) γ ↔
            ∀ (v : ℚ) (hv0 : 0 ≤ v) (hv1 : v ≤ 1), v < r →
              pathSoutheastLE (Q v hv0 hv1) γ)) := by
    intro r hr0 hr1
    have hSource := hQSource.1 r hr0 hr1
    refine ⟨hSource.1, ?_, ?_⟩
    · exact hSource.2.2.2
    · exact hQSource.2 r hr0 hr1

  have hQzeroBelow (γ : ℕ → Lattice)
      (hγ : IsLocallyRightmostGeodesic ω u γ) :
      pathSoutheastLE (Q 0 (by norm_num) (by norm_num)) γ := by
    apply ((hQProperties 0 (by norm_num) (by norm_num)).2.2 γ hγ).mpr
    intro r hr0 _hr1 hrNegative
    have hrNonnegative : (0 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr0
    have hrNegativeReal : (r : ℝ) < 0 := by exact_mod_cast hrNegative
    exact False.elim ((not_lt_of_ge hrNonnegative) hrNegativeReal)

  -- Common-root coordinate comparisons provide the order facts used below.
  have hOrderRefl (γ : ℕ → Lattice) : pathSoutheastLE γ γ := by
    apply (pathSoutheastLE_iff_all_times_of_same_root γ γ rfl).mpr
    intro n
    exact ⟨le_rfl, le_rfl⟩
  have hOrderTransSameRoot (a b c : ℕ → Lattice)
      (hab : pathSoutheastLE a b) (hbc : pathSoutheastLE b c)
      (hrootAB : a 0 = b 0) (hrootBC : b 0 = c 0) :
      pathSoutheastLE a c := by
    apply (pathSoutheastLE_iff_all_times_of_same_root a c
      (hrootAB.trans hrootBC)).mpr
    have habAtEveryTime :=
      (pathSoutheastLE_iff_all_times_of_same_root a b hrootAB).mp hab
    have hbcAtEveryTime :=
      (pathSoutheastLE_iff_all_times_of_same_root b c hrootBC).mp hbc
    intro n
    exact ⟨(habAtEveryTime n).1.trans (hbcAtEveryTime n).1,
      (hbcAtEveryTime n).2.trans (habAtEveryTime n).2⟩
  have hOrderAntisymmSameRoot (a b : ℕ → Lattice)
      (hroot : a 0 = b 0)
      (hab : pathSoutheastLE a b) (hba : pathSoutheastLE b a) :
      a = b := by
    have habAtEveryTime :=
      (pathSoutheastLE_iff_all_times_of_same_root a b hroot).mp hab
    have hbaAtEveryTime :=
      (pathSoutheastLE_iff_all_times_of_same_root b a hroot.symm).mp hba
    funext n
    exact Prod.ext (le_antisymm (habAtEveryTime n).1 (hbaAtEveryTime n).1)
      (le_antisymm (hbaAtEveryTime n).2 (habAtEveryTime n).2)

  -- Source step 2: this set contains exactly the valid rational values below s.
  let F (s : ℝ) : Set (ℕ → Lattice) :=
    {γ | ∃ (r : ℚ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1),
      (r : ℝ) < s ∧ γ = Q r hr0 hr1}
  have hFamilyUpperIff (s : ℝ) (δ : ℕ → Lattice) :
      (∀ γ ∈ F s, pathSoutheastLE γ δ) ↔
        ∀ (r : ℚ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1),
          (r : ℝ) < s → pathSoutheastLE (Q r hr0 hr1) δ := by
    constructor
    · intro hUpper r hr0 hr1 hrs
      exact hUpper (Q r hr0 hr1) ⟨r, hr0, hr1, hrs, rfl⟩
    · intro hUpper γ hγF
      rcases hγF with ⟨r, hr0, hr1, hrs, hγEq⟩
      rw [hγEq]
      exact hUpper r hr0 hr1 hrs
  have hFValid (s : ℝ) :
      ∀ γ ∈ F s, IsLocallyRightmostGeodesic ω u γ := by
    intro γ hγF
    rcases hγF with ⟨r, hr0, hr1, _hrs, hγEq⟩
    have hQrValid := (hQProperties r hr0 hr1).1
    rw [hγEq]
    exact hQrValid
  have hFNonempty (s : ℝ) (hPositive : 0 < s) : (F s).Nonempty := by
    have hZeroBelow : ((0 : ℚ) : ℝ) < s := by simpa using hPositive
    refine ⟨Q 0 (by norm_num) (by norm_num), ?_⟩
    exact ⟨0, by norm_num, by norm_num, hZeroBelow, rfl⟩
  have hFZeroEmpty : F 0 = ∅ := by
    ext γ
    constructor
    · intro hγF
      rcases hγF with ⟨r, hr0, _hr1, hrs, _hγEq⟩
      have hNonnegative : (0 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr0
      exact False.elim (not_lt_of_ge hNonnegative hrs)
    · intro hγEmpty
      cases hγEmpty
  have hIndexUpperAtZero (δ : ℕ → Lattice) :
      ∀ (r : ℚ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1),
        (r : ℝ) < 0 → pathSoutheastLE (Q r hr0 hr1) δ := by
    apply (hFamilyUpperIff 0 δ).mp
    intro γ hγF
    rw [hFZeroEmpty] at hγF
    cases hγF

  -- Source steps 3 and 4: resolve zero from Q 0 and positive s by an actual
  -- nonempty supremum, then state each result as the full upper-bound test.
  have hPointwiseSupremum (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
      ∃! q : ℕ → Lattice,
        IsLocallyRightmostGeodesic ω u q ∧
        (∀ γ : ℕ → Lattice,
          IsLocallyRightmostGeodesic ω u γ →
          (pathSoutheastLE q γ ↔
            ∀ (r : ℚ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1), (r : ℝ) < s →
              pathSoutheastLE (Q r hr0 hr1) γ)) := by
    by_cases hsZero : s = 0
    · subst s
      refine ⟨Q 0 (by norm_num) (by norm_num), ⟨(hQProperties 0 (by norm_num) (by norm_num)).1, ?_⟩, ?_⟩
      · intro γ hγ
        constructor
        · intro _hQBelow
          exact hIndexUpperAtZero γ
        · intro _hIndexUpper
          exact hQzeroBelow γ hγ
      · intro q' hq'
        have hq'Valid := hq'.1
        have hq'BelowQZero :
            pathSoutheastLE q' (Q 0 (by norm_num) (by norm_num)) :=
          (hq'.2 (Q 0 (by norm_num) (by norm_num))
            ((hQProperties 0 (by norm_num) (by norm_num)).1)).mpr
            (hIndexUpperAtZero (Q 0 (by norm_num) (by norm_num)))
        exact hOrderAntisymmSameRoot q' (Q 0 (by norm_num) (by norm_num))
          (hq'Valid.1.trans
            ((hQProperties 0 (by norm_num) (by norm_num)).1).1.symm)
          hq'BelowQZero
          (hQzeroBelow q' hq'Valid)
    · have hPositive : 0 < s := by
        rcases lt_or_eq_of_le hs0 with hPositive | hZero
        · exact hPositive
        · exact False.elim (hsZero hZero.symm)
      obtain ⟨q, hSupremum, hSupremumUnique⟩ :=
        exists_unique_geodesic_supremum ω u (F s)
          (hFNonempty s hPositive) (hFValid s)
      have hqCharacterization :
          ∀ γ : ℕ → Lattice,
            IsLocallyRightmostGeodesic ω u γ →
            (pathSoutheastLE q γ ↔
              ∀ (r : ℚ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1), (r : ℝ) < s →
                pathSoutheastLE (Q r hr0 hr1) γ) := by
        intro γ hγ
        constructor
        · intro hqγ r hr0 hr1 hrs
          have hQrValid := (hQProperties r hr0 hr1).1
          have hQInFamily :
              Q r hr0 hr1 ∈ F s := ⟨r, hr0, hr1, hrs, rfl⟩
          have hQBelowSupremum := hSupremum.2.1 (Q r hr0 hr1) hQInFamily
          exact hOrderTransSameRoot (Q r hr0 hr1) q γ
            hQBelowSupremum hqγ
            (hQrValid.1.trans hSupremum.1.1.symm)
            (hSupremum.1.1.trans hγ.1.symm)
        · intro hBelow
          apply hSupremum.2.2 γ hγ
          exact (hFamilyUpperIff s γ).mpr hBelow
      refine ⟨q, ⟨hSupremum.1, hqCharacterization⟩, ?_⟩
      intro q' hq'
      have hq'IndexUpper :
          ∀ (r : ℚ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1),
            (r : ℝ) < s → pathSoutheastLE (Q r hr0 hr1) q' :=
        (hq'.2 q' hq'.1).mp (hOrderRefl q')
      have hq'FamilyUpper : ∀ γ ∈ F s, pathSoutheastLE γ q' :=
        (hFamilyUpperIff s q').mpr hq'IndexUpper
      have hq'Least : ∀ δ : ℕ → Lattice,
          IsLocallyRightmostGeodesic ω u δ →
          (∀ γ ∈ F s, pathSoutheastLE γ δ) → pathSoutheastLE q' δ := by
        intro δ hδ hFamilyUpper
        apply (hq'.2 δ hδ).mpr
        exact (hFamilyUpperIff s δ).mp hFamilyUpper
      exact hSupremumUnique q' ⟨hq'.1, hq'FamilyUpper, hq'Least⟩

  -- Source step 5: choose the pointwise unique path only on [0, 1].
  let q : ∀ s : ℝ, 0 ≤ s → s ≤ 1 → ℕ → Lattice :=
    fun s hs0 hs1 => Classical.choose (hPointwiseSupremum s hs0 hs1).exists
  have hqProperties (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
      IsLocallyRightmostGeodesic ω u (q s hs0 hs1) ∧
      (∀ γ : ℕ → Lattice,
        IsLocallyRightmostGeodesic ω u γ →
        (pathSoutheastLE (q s hs0 hs1) γ ↔
          ∀ (r : ℚ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1), (r : ℝ) < s →
            pathSoutheastLE (Q r hr0 hr1) γ)) := by
    exact Classical.choose_spec (hPointwiseSupremum s hs0 hs1).exists

  -- Source step 6: rational Q r has the same least-upper-bound property at r.
  have hRationalAgreement
      (r : ℚ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
      (hreal0 : (0 : ℝ) ≤ (r : ℝ)) (hreal1 : (r : ℝ) ≤ 1) :
      q (r : ℝ) hreal0 hreal1 = Q r hr0 hr1 := by
    have hQAtRational := hQProperties r hr0 hr1
    have hQRealCharacterization (γ : ℕ → Lattice)
        (hγ : IsLocallyRightmostGeodesic ω u γ) :
        (pathSoutheastLE (Q r hr0 hr1) γ ↔
          ∀ (v : ℚ) (hv0 : 0 ≤ v) (hv1 : v ≤ 1),
            (v : ℝ) < (r : ℝ) → pathSoutheastLE (Q v hv0 hv1) γ) := by
      have hQLeftSupremum := hQAtRational.2.2 γ hγ
      constructor
      · intro hQrγ v hv0 hv1 hvReal
        have hvRational : v < r := by exact_mod_cast hvReal
        exact hQLeftSupremum.mp hQrγ v hv0 hv1 hvRational
      · intro hBelow
        apply hQLeftSupremum.mpr
        intro v hv0 hv1 hvRational
        have hvReal : (v : ℝ) < (r : ℝ) := by exact_mod_cast hvRational
        exact hBelow v hv0 hv1 hvReal
    have hQHasRealProperty :
        IsLocallyRightmostGeodesic ω u (Q r hr0 hr1) ∧
          (∀ γ : ℕ → Lattice,
            IsLocallyRightmostGeodesic ω u γ →
            (pathSoutheastLE (Q r hr0 hr1) γ ↔
              ∀ (v : ℚ) (hv0 : 0 ≤ v) (hv1 : v ≤ 1),
                (v : ℝ) < (r : ℝ) →
                  pathSoutheastLE (Q v hv0 hv1) γ)) :=
      ⟨hQAtRational.1, hQRealCharacterization⟩
    have hUniqueAtRational :=
      (hPointwiseSupremum (r : ℝ) hreal0 hreal1).unique
        (hqProperties (r : ℝ) hreal0 hreal1) hQHasRealProperty
    exact hUniqueAtRational

  -- Source step 7: pointwise uniqueness gives uniqueness of the whole family.
  refine ⟨Q, hQProperties, ?_⟩
  refine ⟨q, ⟨?_, hRationalAgreement⟩, ?_⟩
  · exact hqProperties
  · intro q' hq'
    funext s
    funext hs0
    funext hs1
    exact (hPointwiseSupremum s hs0 hs1).unique
      (hq'.1 s hs0 hs1) (hqProperties s hs0 hs1)

end LPP.Busemann
