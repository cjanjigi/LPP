/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LPP_Foundations.Probability.TranslationErgodic
public import LPP_Foundations.Probability.CoordinateLaw
import Mathlib.Dynamics.Ergodic.Conservative
import Mathlib.Order.Filter.Finite
import Mathlib.Tactic

/-! High weights recur on arbitrarily far columns. -/

@[expose] public section

open MeasureTheory Filter Set

namespace LPPDifferentiability

/-- If a site has positive probability of exceeding `K`, then almost surely
arbitrarily far positive columns contain such weights at unbounded heights.
The column is fixed before the height is chosen. This is the weight-factor
recurrence step in GRS arXiv:1510.00860v1, Lemma A.3, lines 1492–1516. -/
theorem ae_arbitrarily_far_columns_with_unbounded_high_weights
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (K : ℝ) (hK : 0 < μ (Set.Ioi K)) :
    ∀ᵐ ω ∂environmentLaw μ, ∀ B : ℤ,
      ∃ m : ℕ, B < (m : ℤ) ∧
        ∀ H : ℤ, ∃ r : ℕ, H < (r : ℤ) ∧
          K < ω ((m : ℤ), (r : ℤ)) := by
  classical
  let ρ := environmentLaw μ
  let horizontal : Environment → Environment := fun ω z => ω (((1 : ℤ), (0 : ℤ)) + z)
  let vertical : Environment → Environment := fun ω z => ω (((0 : ℤ), (1 : ℤ)) + z)
  let A (n : ℕ) : Set Environment :=
    {ω | ∃ z : Lattice, |z.1| + |z.2| ≤ (n : ℤ) ∧ K < ω z}
  let E : Set Environment := {ω | ∃ z : Lattice, K < ω z}
  have hA (n : ℕ) : MeasurableSet (A n) := by
    change MeasurableSet {ω : Environment | ∃ z : Lattice,
      |z.1| + |z.2| ≤ (n : ℤ) ∧ K < ω z}
    simp only [Set.ofPred_exists]
    apply MeasurableSet.iUnion
    intro z
    by_cases hz : |z.1| + |z.2| ≤ (n : ℤ)
    · simpa only [hz, true_and] using
        measurableSet_lt measurable_const (measurable_environment_eval z)
    · simp [hz]
  have hE : MeasurableSet E := by
    change MeasurableSet {ω : Environment | ∃ z : Lattice, K < ω z}
    simp only [Set.ofPred_exists]
    exact MeasurableSet.iUnion fun z => measurableSet_lt measurable_const (measurable_environment_eval z)
  -- A high coordinate exists almost surely by ergodicity of the weight factor.
  have hEshift : horizontal ⁻¹' E = E := by
    ext ω
    constructor
    · rintro ⟨z, hz⟩
      exact ⟨((1 : ℤ), (0 : ℤ)) + z, hz⟩
    · rintro ⟨z, hz⟩
      refine ⟨z - ((1 : ℤ), (0 : ℤ)), ?_⟩
      change K < ω (((1 : ℤ), (0 : ℤ)) + (z - ((1 : ℤ), (0 : ℤ))))
      simpa using hz
  have horigin : 0 < ρ {ω : Environment | K < ω 0} := by
    have hm := Measure.map_apply (μ := environmentLaw μ)
      (measurable_environment_eval 0) (measurableSet_Ioi : MeasurableSet (Set.Ioi K))
    rw [environmentLaw_map_eval μ 0] at hm
    simpa only [Set.preimage, Set.mem_ofPred_eq, Set.mem_Ioi, ρ] using hm ▸ hK
  have hEpos : 0 < ρ E := lt_of_lt_of_le horigin (measure_mono (by
    intro ω hω
    exact ⟨0, hω⟩))
  have hEone : ρ E = 1 := by
    rcases environmentLaw_invariant_zero_one μ (1, 0) (by decide) hE hEshift with h | h
    · exact False.elim (ne_of_gt hEpos h)
    · exact h
  have hEae : ∀ᵐ ω ∂ρ, ω ∈ E := (mem_ae_iff_prob_eq_one hE).mpr hEone
  have hballEx (z : Lattice) : ∃ n : ℕ, |z.1| + |z.2| ≤ (n : ℤ) := by
    refine ⟨(|z.1| + |z.2|).toNat, ?_⟩
    rw [Int.toNat_of_nonneg (add_nonneg (abs_nonneg _) (abs_nonneg _))]
  have hAex : ∀ᵐ ω ∂ρ, ∃ n, ω ∈ A n := by
    filter_upwards [hEae] with ω hω
    obtain ⟨z, hz⟩ := hω
    obtain ⟨n, hn⟩ := hballEx z
    exact ⟨n, z, hn, hz⟩
  have hHpres : MeasurePreserving horizontal ρ ρ :=
    measurePreserving_environment_translation μ (1, 0)
  have hVpres : MeasurePreserving vertical ρ ρ :=
    measurePreserving_environment_translation μ (0, 1)
  -- Recurrence for every radius and every horizontal iterate is simultaneous.
  have hHrec : ∀ᵐ ω ∂ρ, ∀ n, ω ∈ A n →
      ∃ᶠ k : ℕ in atTop, horizontal^[k] ω ∈ A n := by
    apply ae_all_iff.mpr
    intro n
    exact hHpres.conservative.ae_mem_imp_frequently_image_mem (hA n).nullMeasurableSet
  have hVrec : ∀ᵐ ω ∂ρ, ∀ n k, horizontal^[k] ω ∈ A n →
      ∃ᶠ l : ℕ in atTop, vertical^[l] (horizontal^[k] ω) ∈ A n := by
    apply ae_all_iff.mpr
    intro n
    apply ae_all_iff.mpr
    intro k
    exact (hHpres.iterate k).quasiMeasurePreserving.ae
      (hVpres.conservative.ae_mem_imp_frequently_image_mem (hA n).nullMeasurableSet)
  filter_upwards [hAex, hHrec, hVrec] with ω hsome hh hv
  obtain ⟨n, hn⟩ := hsome
  intro B
  let L : ℕ := (max B 0).toNat + n + 1
  obtain ⟨k, hkA, hkL⟩ := ((hh n hn).and_eventually (eventually_ge_atTop L)).exists
  have hkn : (n : ℤ) < (k : ℤ) ∧ B < (k : ℤ) - (n : ℤ) := by
    have hmax : ((max B 0).toNat : ℤ) = max B 0 :=
      Int.toNat_of_nonneg (le_max_right B 0)
    dsimp [L] at hkL
    omega
  -- At a fixed horizontal return, infinitely many vertical returns have one
  -- of finitely many horizontal offsets. Choose that offset once.
  have hfreq : ∃ᶠ l : ℕ in atTop, ∃ d ∈ Finset.Icc (-(n : ℤ)) (n : ℤ),
      ∃ e : ℤ, -(n : ℤ) ≤ e ∧ e ≤ (n : ℤ) ∧
        K < ω ((k : ℤ) + d, (l : ℤ) + e) := by
    apply (hv n k hkA).mono
    intro l hl
    obtain ⟨z, hz, hw⟩ := hl
    have hxabs : |z.1| ≤ (n : ℤ) := by have := abs_nonneg z.2; omega
    have hyabs : |z.2| ≤ (n : ℤ) := by have := abs_nonneg z.1; omega
    have hx := abs_le.mp hxabs
    have hy := abs_le.mp hyabs
    refine ⟨z.1, Finset.mem_Icc.mpr hx, z.2, hy.1, hy.2, ?_⟩
    have htV := environment_translate_iterate (horizontal^[k] ω) (0, 1) l z
    have htH := environment_translate_iterate ω (1, 0) k (l • ((0, 1) : Lattice) + z)
    change horizontal^[k] ω (l • ((0, 1) : Lattice) + z) = _ at htH
    change K < vertical^[l] (horizontal^[k] ω) z at hw
    rw [htV, htH] at hw
    have hpoint : ((k : ℤ), (0 : ℤ)) + (((0 : ℤ), (l : ℤ)) + z) =
        ((k : ℤ) + z.1, (l : ℤ) + z.2) := by
      apply Prod.ext <;> simp
    simpa [Prod.smul_fst, Prod.smul_snd, nsmul_eq_mul, hpoint] using hw
  obtain ⟨d, hd, hdFreq⟩ := (frequently_exists_finset (Finset.Icc (-(n : ℤ)) (n : ℤ))).mp hfreq
  have hd' := Finset.mem_Icc.mp hd
  let m : ℕ := ((k : ℤ) + d).toNat
  have hm : (m : ℤ) = (k : ℤ) + d := Int.toNat_of_nonneg (by omega)
  refine ⟨m, by omega, ?_⟩
  intro H
  let Q : ℕ := (max H 0).toNat + n + 1
  obtain ⟨l, ⟨e, he1, he2, he⟩, hlQ⟩ :=
    (hdFreq.and_eventually (eventually_ge_atTop Q)).exists
  have hmax : ((max H 0).toNat : ℤ) = max H 0 :=
    Int.toNat_of_nonneg (le_max_right H 0)
  have hnonneg : 0 ≤ (l : ℤ) + e := by
    dsimp [Q] at hlQ
    omega
  let r : ℕ := ((l : ℤ) + e).toNat
  have hr : (r : ℤ) = (l : ℤ) + e := Int.toNat_of_nonneg hnonneg
  refine ⟨r, ?_, ?_⟩
  · dsimp [Q] at hlQ
    omega
  · simpa only [hm, hr] using he

end LPPDifferentiability
