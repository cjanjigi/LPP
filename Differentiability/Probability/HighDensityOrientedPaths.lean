/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Differentiability.Probability.OrientedPathEvent
public import Differentiability.Probability.FiniteContourFamilyBadEvent
import Differentiability.Model.ContourBadLabelCover
import Differentiability.Analysis.PeierlsContourSeries
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Tactic

/-!
# Peierls estimate for high-density oriented site paths

A Peierls-type estimate bounds the probability of a high-density set of oriented
site paths by a sum over contours.
-/

public section

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace LPPDifferentiability

private theorem contour_power_identity (k n : ℕ) (ζ : ℝ) (hζ : 0 < ζ) :
    (((n + 6) ^ 2 * 4 * 3 ^ (n + 3) : ℕ) : ℝ) *
        ζ ^ (((n + 4 : ℕ) : ℝ) / (8 * (((2 * k + 1) ^ 2 : ℕ) : ℝ))) =
      ((n + 6 : ℕ) : ℝ) ^ 2 * 4 *
        (3 * ζ ^ (1 / (8 * (((2 * k + 1) ^ 2 : ℕ) : ℝ)))) ^ (n + 3) *
          ζ ^ (1 / (8 * (((2 * k + 1) ^ 2 : ℕ) : ℝ))) := by
  let d : ℝ := 8 * (((2 * k + 1) ^ 2 : ℕ) : ℝ)
  have he : ((n + 4 : ℕ) : ℝ) / d =
      (1 / d) * ((n + 3 : ℕ) : ℝ) + 1 / d := by
    push_cast
    ring
  have hc : (((n + 6) ^ 2 * 4 * 3 ^ (n + 3) : ℕ) : ℝ) =
      ((n + 6 : ℕ) : ℝ) ^ 2 * 4 * (3 : ℝ) ^ (n + 3) := by
    push_cast
    rfl
  change _ * ζ ^ (((n + 4 : ℕ) : ℝ) / d) =
    ((n + 6 : ℕ) : ℝ) ^ 2 * 4 * (3 * ζ ^ (1 / d)) ^ (n + 3) * ζ ^ (1 / d)
  rw [hc, he, Real.rpow_add hζ, Real.rpow_mul_natCast hζ.le, mul_pow]
  ring

private theorem measureReal_iUnion_le_of_summable
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (E : ℕ → Set Ω) (t : ℕ → ℝ) (ht : ∀ n, 0 ≤ t n)
    (hs : Summable t) (hE : ∀ n, P.real (E n) ≤ t n) :
    P.real (⋃ n, E n) ≤ ∑' n, t n := by
  have hEach (n : ℕ) : P (E n) ≤ ENNReal.ofReal (t n) := by
    rw [← ENNReal.ofReal_toReal (measure_ne_top P (E n))]
    exact ENNReal.ofReal_le_ofReal (hE n)
  have hUnion : P (⋃ n, E n) ≤ ENNReal.ofReal (∑' n, t n) := by
    calc
      _ ≤ ∑' n, P (E n) := measure_iUnion_le E
      _ ≤ ∑' n, ENNReal.ofReal (t n) := ENNReal.tsum_le_tsum hEach
      _ = ENNReal.ofReal (∑' n, t n) := (ENNReal.ofReal_tsum_of_nonneg ht hs).symm
  have hReal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hUnion
  simpa only [Measure.real, ENNReal.toReal_ofReal (tsum_nonneg ht)] using hReal

/-- For each dependence range one cutoff works for every probability space and
all measurable site events satisfying the marginal and independence conditions.
The path event includes the initial site at zero. -/
theorem exists_high_density_oriented_path_cutoff (k : ℕ) :
    ∃ ζ : ℝ, 0 < ζ ∧ ζ < 1 ∧
      ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (G : ℕ × ℕ → Set Ω),
        (∀ v, MeasurableSet (G v)) →
        (∀ v, P.real ((G v)ᶜ) ≤ ζ) →
        (∀ T : Finset (ℕ × ℕ),
          (∀ u ∈ T, ∀ v ∈ T, u ≠ v →
            k < Nat.dist u.1 v.1 ∨ k < Nat.dist u.2 v.2) →
          iIndepSet (fun v : {u : ℕ × ℕ // u ∈ T} => G v.1) P) →
        MeasurableSet
          {ω : Ω | ∃ q : ℕ → ℕ × ℕ, q 0 = (0, 0) ∧
            (∀ i, q (i + 1) = q i + (1, 0) ∨ q (i + 1) = q i + (0, 1)) ∧
            ∀ i, ω ∈ G (q i)} ∧
        0 < P.real
          {ω : Ω | ∃ q : ℕ → ℕ × ℕ, q 0 = (0, 0) ∧
            (∀ i, q (i + 1) = q i + (1, 0) ∨ q (i + 1) = q i + (0, 1)) ∧
            ∀ i, ω ∈ G (q i)} := by
  classical
  obtain ⟨ζ, hζpos, hζlt, hsum, hsumlt⟩ := exists_peierls_contour_series_bound k
  refine ⟨ζ, hζpos, hζlt, ?_⟩
  intro Ω _ P _ G hG hMarginal hIndep
  obtain ⟨W, B, hCount, hLabels, hCover⟩ := exists_contour_bad_label_cover
  let E (n : ℕ) : Set Ω := {ω | ∃ v : {u // u ∈ W n},
    ∀ x ∈ B n v, ω ∉ G x}
  let t (n : ℕ) : ℝ := ((n + 6 : ℕ) : ℝ) ^ 2 * 4 *
    (3 * ζ ^ (1 / (8 * (((2 * k + 1) ^ 2 : ℕ) : ℝ)))) ^ (n + 3) *
      ζ ^ (1 / (8 * (((2 * k + 1) ^ 2 : ℕ) : ℝ)))
  have hFinite (n : ℕ) : MeasurableSet (E n) ∧
      P.real (E n) ≤ ((W n).card : ℝ) *
        ζ ^ (((n + 4 : ℕ) : ℝ) / (8 * (((2 * k + 1) ^ 2 : ℕ) : ℝ))) := by
    let _ := Fintype.ofFinite {u // u ∈ W n}
    have hf := measurable_and_measureReal_exists_all_bad_natural_site_family_le
      P G hG k (n + 4) ζ hζpos hζlt (fun v _ => hMarginal v) hIndep
      (Finset.univ : Finset {u // u ∈ W n}) (B n)
      (fun v _ => (hLabels n v).2.2.2.2.2)
    simpa only [Finset.mem_univ, true_and, Finset.card_univ,
      Fintype.card_coe, Real.rpow_eq_pow, E] using hf
  have hBound (n : ℕ) : P.real (E n) ≤ t n := by
    calc
      _ ≤ ((W n).card : ℝ) *
          ζ ^ (((n + 4 : ℕ) : ℝ) / (8 * (((2 * k + 1) ^ 2 : ℕ) : ℝ))) :=
        (hFinite n).2
      _ ≤ (((n + 6) ^ 2 * 4 * 3 ^ (n + 3) : ℕ) : ℝ) *
          ζ ^ (((n + 4 : ℕ) : ℝ) / (8 * (((2 * k + 1) ^ 2 : ℕ) : ℝ))) :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hCount n)
          (Real.rpow_nonneg hζpos.le _)
      _ = t n := contour_power_identity k n ζ hζpos
  let A : Set Ω := {ω | ∃ q : ℕ → ℕ × ℕ, q 0 = (0, 0) ∧
    (∀ i, q (i + 1) = q i + (1, 0) ∨ q (i + 1) = q i + (0, 1)) ∧
    ∀ i, ω ∈ G (q i)}
  have hA : MeasurableSet A := measurableSet_exists_infinite_good_oriented_path G hG
  have hSubset : Aᶜ ⊆ ⋃ n, E n := by
    intro ω hω
    obtain ⟨n, v, hv⟩ := hCover {x | ω ∈ G x} hω
    exact Set.mem_iUnion.mpr ⟨n, v, hv⟩
  have hUnion : P.real (⋃ n, E n) ≤ ∑' n, t n :=
    measureReal_iUnion_le_of_summable P E t (fun n => by dsimp [t]; positivity)
      hsum hBound
  have hComplement : P.real Aᶜ < 1 :=
    lt_of_le_of_lt ((measureReal_mono hSubset).trans hUnion) hsumlt
  refine ⟨hA, ?_⟩
  have hIdentity := probReal_compl_eq_one_sub (μ := P) hA
  change 0 < P.real A
  linarith only [hIdentity, hComplement]

end LPPDifferentiability
