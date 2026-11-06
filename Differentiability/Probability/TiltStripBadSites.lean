/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Differentiability.Model.TiltStripStartSlice
public import Differentiability.Probability.PeierlsBadPath
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.Tactic

/-!
# Bad collected sites in the tilt strip

This file bounds the probability that a path in the closed tilt strip collects too
many sites with weight in a given set. The bound decays like `4⁻ⁿ` in the length `n`
of the path, which is what makes the bad event rare at the cubic length.
-/

public section
noncomputable section
open MeasureTheory Filter
namespace LPPDifferentiability

/-- The lower start level and upper terminal level force level zero. -/
theorem Path.start_level_zero_of_closed_strip {u : Lattice} {n : ℕ}
    (q : Σ i : Fin (n + 1), Path u (i.val, n - i.val))
    (h : ∀ j, 0 ≤ (q.2.vertex j).1 + (q.2.vertex j).2 ∧
      (q.2.vertex j).1 + (q.2.vertex j).2 ≤ (n : ℤ)) :
    u.1 + u.2 = 0 := by
  have hstart := (h 0).1
  rw [q.2.start] at hstart
  have hend := (h (Fin.last (q.1.val + (n - q.1.val)))).2
  rw [q.2.level] at hend
  have hlen : q.1.val + (n - q.1.val) = n := Nat.add_sub_of_le (by omega)
  simp only [Fin.val_last, hlen] at hend
  omega

private theorem measurable_bad_count (A : Set ℝ) (hA : MeasurableSet A)
    (S : Finset Lattice) :
    Measurable (fun ω : Environment =>
      (@Finset.filter Lattice (fun z => ω z ∈ A) (Classical.decPred _) S).card) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa only [Finset.filter_empty, Finset.card_empty] using
      (measurable_const : Measurable (fun _ : Environment => (0 : ℕ)))
  | @insert z S hz ih =>
    have hm : MeasurableSet {ω : Environment | ω z ∈ A} :=
      (measurable_environment_eval z) hA
    have heq : (fun ω : Environment =>
        (@Finset.filter Lattice (fun z => ω z ∈ A) (Classical.decPred _)
          (insert z S)).card) =
        (fun ω => if ω z ∈ A then
          (@Finset.filter Lattice (fun z => ω z ∈ A) (Classical.decPred _) S).card + 1
          else (@Finset.filter Lattice (fun z => ω z ∈ A) (Classical.decPred _) S).card) := by
      funext ω
      by_cases h : ω z ∈ A <;> simp [Finset.filter_insert, h, hz]
    rw [heq]
    exact Measurable.ite hm (ih.add measurable_const) ih

/-- The closed-strip bad event is measurable. Its path condition includes all
vertices, while the filtered collected sites exclude the terminal vertex. -/
theorem measurableSet_exists_closed_strip_bad_sites
    (A : Set ℝ) (hA : MeasurableSet A) (a s φ : ℝ) (n : ℕ) :
    MeasurableSet {ω : Environment |
      ∃ u : Lattice, ∃ q : Σ i : Fin (n + 1), Path u (i.val, n - i.val),
        (∀ j, 0 ≤ (q.2.vertex j).1 + (q.2.vertex j).2 ∧
          (q.2.vertex j).1 + (q.2.vertex j).2 ≤ (n : ℤ) ∧
          |(1 - a) * ((q.2.vertex j).1 : ℝ) - a * ((q.2.vertex j).2 : ℝ)| ≤ 8 * s) ∧
        φ * (n : ℝ) < ((@Finset.filter Lattice (fun z => ω z ∈ A)
          (Classical.decPred _) q.2.collectedSites).card : ℝ)} := by
  classical
  rw [Set.ofPred_exists]
  apply MeasurableSet.iUnion
  intro u
  rw [Set.ofPred_exists]
  apply MeasurableSet.iUnion
  intro q
  exact MeasurableSet.inter (MeasurableSet.const _)
    (measurableSet_lt measurable_const ((measurable_of_countable (fun k : ℕ => (k : ℝ))).comp
      (measurable_bad_count A hA q.2.collectedSites)))

/-- The bound `17 s 4⁻ⁿ` on the closed-strip bad event. -/
theorem measure_exists_closed_strip_bad_sites_le
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (A : Set ℝ) (hA : MeasurableSet A)
    (a s φ : ℝ) (hs : 1 ≤ s) (hφ : 0 < φ)
    (hMass : (μ A).toReal ≤ Real.rpow 16 (-1 / φ)) (n : ℕ) :
    (environmentLaw μ) {ω : Environment |
      ∃ u : Lattice, ∃ q : Σ i : Fin (n + 1), Path u (i.val, n - i.val),
        (∀ j, 0 ≤ (q.2.vertex j).1 + (q.2.vertex j).2 ∧
          (q.2.vertex j).1 + (q.2.vertex j).2 ≤ (n : ℤ) ∧
          |(1 - a) * ((q.2.vertex j).1 : ℝ) - a * ((q.2.vertex j).2 : ℝ)| ≤ 8 * s) ∧
        φ * (n : ℝ) < ((@Finset.filter Lattice (fun z => ω z ∈ A)
          (Classical.decPred _) q.2.collectedSites).card : ℝ)} ≤
      ENNReal.ofReal (17 * s * (1 / 4 : ℝ) ^ n) := by
  classical
  let S : Finset Lattice := (Finset.Icc (Int.ceil (-8 * s)) (Int.floor (8 * s))).image
    (fun i => (i, -i))
  have hsubset : {ω : Environment |
      ∃ u : Lattice, ∃ q : Σ i : Fin (n + 1), Path u (i.val, n - i.val),
        (∀ j, 0 ≤ (q.2.vertex j).1 + (q.2.vertex j).2 ∧
          (q.2.vertex j).1 + (q.2.vertex j).2 ≤ (n : ℤ) ∧
          |(1 - a) * ((q.2.vertex j).1 : ℝ) - a * ((q.2.vertex j).2 : ℝ)| ≤ 8 * s) ∧
        φ * (n : ℝ) < ((@Finset.filter Lattice (fun z => ω z ∈ A)
          (Classical.decPred _) q.2.collectedSites).card : ℝ)} ⊆
      {ω : Environment | ∃ u ∈ S, ∃ q : Σ i : Fin (n + 1), Path u (i.val, n - i.val),
        φ * (n : ℝ) < ((@Finset.filter Lattice (fun z => ω z ∈ A)
          (Classical.decPred _) q.2.collectedSites).card : ℝ)} := by
    rintro ω ⟨u, q, hstrip, hcount⟩
    have hlevel := Path.start_level_zero_of_closed_strip q (fun j =>
      ⟨(hstrip j).1, (hstrip j).2.1⟩)
    have hrho := (hstrip 0).2.2
    rw [q.2.start] at hrho
    exact ⟨u, (tiltStripStartSlice_mem_iff a s u).2 ⟨hlevel, hrho⟩, q, hcount⟩
  have hcard : (S.card : ℝ) ≤ 17 * s := tiltStripCanonicalStartSlice_card_le a s hs
  have hcast : (S.card : ENNReal) ≤ ENNReal.ofReal (17 * s) := by
    rw [← ENNReal.ofReal_natCast]
    exact ENNReal.ofReal_le_ofReal hcard
  calc
    _ ≤ _ := measure_mono hsubset
    _ ≤ (S.card : ENNReal) * (1 / 4 : ENNReal) ^ n :=
      measure_exists_start_path_bad_collected_sites_gt_phi_le μ A hA S φ hφ hMass n
    _ ≤ ENNReal.ofReal (17 * s) * (1 / 4 : ENNReal) ^ n :=
      mul_le_mul_of_nonneg_right hcast (by positivity)
    _ = ENNReal.ofReal (17 * s * (1 / 4 : ℝ) ^ n) := by
      rw [ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 17 * s),
        ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 1 / 4),
        ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 4)]
      norm_num

/-- At the scale `⌈s³⌉`, the probability of the bad event tends to zero. -/
theorem tendsto_closed_strip_bad_sites_probability
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (A : Set ℝ) (hA : MeasurableSet A)
    (a φ : ℝ) (hφ : 0 < φ)
    (hMass : (μ A).toReal ≤ Real.rpow 16 (-1 / φ)) :
    Tendsto (fun s : ℝ => ((environmentLaw μ) {ω : Environment |
      ∃ u : Lattice, ∃ q : Σ i : Fin (Nat.ceil (s ^ 3) + 1),
        Path u (i.val, Nat.ceil (s ^ 3) - i.val),
        (∀ j, 0 ≤ (q.2.vertex j).1 + (q.2.vertex j).2 ∧
          (q.2.vertex j).1 + (q.2.vertex j).2 ≤ (Nat.ceil (s ^ 3) : ℤ) ∧
          |(1 - a) * ((q.2.vertex j).1 : ℝ) - a * ((q.2.vertex j).2 : ℝ)| ≤ 8 * s) ∧
        φ * (Nat.ceil (s ^ 3) : ℝ) < ((@Finset.filter Lattice (fun z => ω z ∈ A)
          (Classical.decPred _) q.2.collectedSites).card : ℝ)}).toReal)
      atTop (nhds 0) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    tendsto_peierls_bad_path_rarity_prefactor
  · exact Eventually.of_forall fun _ => ENNReal.toReal_nonneg
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with s hs
    have hbound := measure_exists_closed_strip_bad_sites_le μ A hA a s φ hs hφ hMass
      (Nat.ceil (s ^ 3))
    exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hbound).trans_eq
      (ENNReal.toReal_ofReal (by positivity))

end LPPDifferentiability
end
