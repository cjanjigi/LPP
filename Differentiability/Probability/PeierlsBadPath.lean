/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Differentiability.Probability.PathBadSiteTail
public import Mathlib.Algebra.Order.Floor.Defs
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! # Finite-start Peierls bounds for bad sites on actual paths

The bound on a fixed path follows from independence, and counting the actual
path family gives a `4^n` factor. A real-power estimate then converts a small
one-site bad-event probability into an exponential path bound.
-/

public section

noncomputable section

open MeasureTheory
open Filter

namespace LPPDifferentiability

/-- A finite set of starts contributes its cardinality to the endpoint-free
actual-path estimate. -/
theorem measure_exists_start_path_bad_collected_sites_ge_le
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (A : Set ℝ) (hA : MeasurableSet A)
    (S : Finset Lattice) (n m : ℕ) :
    (environmentLaw μ) {ω : Environment |
      ∃ u ∈ S, ∃ q : Σ i : Fin (n + 1), Path u (i.val, n - i.val),
        m ≤ (@Finset.filter Lattice (fun z => ω z ∈ A) (Classical.decPred _)
          q.2.collectedSites).card} ≤
      (S.card : ENNReal) * (4 ^ n : ENNReal) * μ A ^ m := by
  classical
  let bad (u : Lattice) : Set Environment := {ω : Environment |
    ∃ q : Σ i : Fin (n + 1), Path u (i.val, n - i.val),
      m ≤ (@Finset.filter Lattice (fun z => ω z ∈ A) (Classical.decPred _)
        q.2.collectedSites).card}
  have hevent :
      {ω : Environment | ∃ u ∈ S, ∃ q : Σ i : Fin (n + 1), Path u (i.val, n - i.val),
        m ≤ (@Finset.filter Lattice (fun z => ω z ∈ A) (Classical.decPred _)
          q.2.collectedSites).card} = ⋃ u ∈ S, bad u := by
    ext ω
    simp [bad]
  rw [hevent]
  calc
    (environmentLaw μ) (⋃ u ∈ S, bad u) ≤
        ∑ u ∈ S, (environmentLaw μ) (bad u) := measure_biUnion_finset_le _ _
    _ ≤ ∑ u ∈ S, (4 ^ n : ENNReal) * μ A ^ m := by
      apply Finset.sum_le_sum
      intro u hu
      exact measure_exists_path_bad_collected_sites_ge_le μ A hA u n m
    _ = (S.card : ENNReal) * ((4 ^ n : ENNReal) * μ A ^ m) := by simp
    _ = (S.card : ENNReal) * (4 ^ n : ENNReal) * μ A ^ m := by ac_rfl

/-- Under the one-site bound `μ(A) ≤ 16^(-1/φ)`, the ceiling-threshold event on
actual paths from a finite set of starts has rate at most `4^(-n)`. -/
theorem measure_exists_start_path_bad_collected_sites_ge_ceil_le
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (A : Set ℝ) (hA : MeasurableSet A)
    (S : Finset Lattice) (φ : ℝ) (hφ : 0 < φ)
    (hMass : (μ A).toReal ≤ Real.rpow 16 (-1 / φ)) (n : ℕ) :
    (environmentLaw μ) {ω : Environment |
      ∃ u ∈ S, ∃ q : Σ i : Fin (n + 1), Path u (i.val, n - i.val),
        Nat.ceil (φ * (n : ℝ)) ≤
          (@Finset.filter Lattice (fun z => ω z ∈ A) (Classical.decPred _)
            q.2.collectedSites).card} ≤
      (S.card : ENNReal) * (1 / 4 : ENNReal) ^ n := by
  classical
  let β : ℝ := Real.rpow 16 (-1 / φ)
  let m : ℕ := Nat.ceil (φ * (n : ℝ))
  have hβpos : 0 < β := by
    dsimp [β]
    exact Real.rpow_pos_of_pos (by norm_num) _
  have hneg : -1 / φ < 0 := by
    rw [neg_div]
    exact neg_lt_zero.mpr (one_div_pos.mpr hφ)
  have hβlt : β < 1 := by
    dsimp [β]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) hneg
  have hMass' : (μ A).toReal ≤ β := by simpa [β] using hMass
  have hAfinite : μ A ≠ ⊤ := (measure_lt_top μ A).ne
  have hμleβ : μ A ≤ ENNReal.ofReal β := by
    rw [← ENNReal.ofReal_toReal hAfinite]
    exact ENNReal.ofReal_le_ofReal hMass'
  have hmceil : φ * (n : ℝ) ≤ (m : ℝ) := by
    dsimp [m]
    exact Nat.le_ceil _
  have hβpower : β ^ m ≤ Real.rpow 16 (-(n : ℝ)) := by
    rw [← Real.rpow_natCast]
    calc
      Real.rpow β (m : ℝ) ≤ Real.rpow β (φ * (n : ℝ)) :=
        Real.rpow_le_rpow_of_exponent_ge hβpos hβlt.le hmceil
      _ = Real.rpow 16 ((-1 / φ) * (φ * (n : ℝ))) := by
        dsimp [β]
        rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 16)]
      _ = Real.rpow 16 (-(n : ℝ)) := by
        congr 1
        field_simp [hφ.ne']
  have hμpower : μ A ^ m ≤ ENNReal.ofReal (Real.rpow 16 (-(n : ℝ))) := by
    calc
      μ A ^ m ≤ (ENNReal.ofReal β) ^ m := pow_le_pow_left' hμleβ m
      _ = ENNReal.ofReal (β ^ m) := (ENNReal.ofReal_pow hβpos.le m).symm
      _ ≤ ENNReal.ofReal (Real.rpow 16 (-(n : ℝ))) :=
        ENNReal.ofReal_le_ofReal hβpower
  have hconstant :
      (4 ^ n : ENNReal) * ENNReal.ofReal (Real.rpow 16 (-(n : ℝ))) =
        (1 / 4 : ENNReal) ^ n := by
    have hreal :
        (4 : ℝ) ^ n * Real.rpow 16 (-(n : ℝ)) = (1 / 4 : ℝ) ^ n := by
      change (4 : ℝ) ^ n * (16 : ℝ) ^ (-(n : ℝ)) = (1 / 4 : ℝ) ^ n
      rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 16) (n : ℝ), Real.rpow_natCast]
      rw [← div_eq_mul_inv, ← div_pow]
      norm_num
    have hfour : (4 ^ n : ENNReal) = ENNReal.ofReal ((4 : ℝ) ^ n) := by
      rw [ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 4)]
      norm_num
    calc
      (4 ^ n : ENNReal) * ENNReal.ofReal (Real.rpow 16 (-(n : ℝ))) =
          ENNReal.ofReal ((4 : ℝ) ^ n) * ENNReal.ofReal (Real.rpow 16 (-(n : ℝ))) := by
        rw [hfour]
      _ = ENNReal.ofReal ((4 : ℝ) ^ n * Real.rpow 16 (-(n : ℝ))) := by
        rw [← ENNReal.ofReal_mul (by positivity)]
      _ = ENNReal.ofReal ((1 / 4 : ℝ) ^ n) := by rw [hreal]
      _ = (1 / 4 : ENNReal) ^ n := by
        have hquarter : ENNReal.ofReal (1 / 4 : ℝ) = (1 / 4 : ENNReal) := by
          rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 4)]
          norm_num
        rw [ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ (1 / 4 : ℝ)), hquarter]
  have hbase : (4 ^ n : ENNReal) * μ A ^ m ≤ (1 / 4 : ENNReal) ^ n := by
    calc
      (4 ^ n : ENNReal) * μ A ^ m ≤
          (4 ^ n : ENNReal) * ENNReal.ofReal (Real.rpow 16 (-(n : ℝ))) :=
        mul_le_mul_of_nonneg_left hμpower (by positivity)
      _ = (1 / 4 : ENNReal) ^ n := hconstant
  have hgeneral := measure_exists_start_path_bad_collected_sites_ge_le μ A hA S n m
  calc
    (environmentLaw μ) {ω : Environment |
        ∃ u ∈ S, ∃ q : Σ i : Fin (n + 1), Path u (i.val, n - i.val),
          m ≤ (@Finset.filter Lattice (fun z => ω z ∈ A) (Classical.decPred _)
            q.2.collectedSites).card} ≤
        (S.card : ENNReal) * (4 ^ n : ENNReal) * μ A ^ m := hgeneral
    _ = (S.card : ENNReal) * ((4 ^ n : ENNReal) * μ A ^ m) := by ac_rfl
    _ ≤ (S.card : ENNReal) * (1 / 4 : ENNReal) ^ n :=
      mul_le_mul_of_nonneg_left hbase (by positivity)

/-- The strict `> φ*n` bad-site event is included in the
`Nat.ceil (φ*n)` event, including when `φ*n` is an integer. -/
theorem measure_exists_start_path_bad_collected_sites_gt_phi_le
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (A : Set ℝ) (hA : MeasurableSet A)
    (S : Finset Lattice) (φ : ℝ) (hφ : 0 < φ)
    (hMass : (μ A).toReal ≤ Real.rpow 16 (-1 / φ)) (n : ℕ) :
    (environmentLaw μ) {ω : Environment |
      ∃ u ∈ S, ∃ q : Σ i : Fin (n + 1), Path u (i.val, n - i.val),
        φ * (n : ℝ) <
          ((@Finset.filter Lattice (fun z => ω z ∈ A) (Classical.decPred _)
            q.2.collectedSites).card : ℝ)} ≤
      (S.card : ENNReal) * (1 / 4 : ENNReal) ^ n := by
  have hsubset :
      {ω : Environment | ∃ u ∈ S, ∃ q : Σ i : Fin (n + 1), Path u (i.val, n - i.val),
        φ * (n : ℝ) <
          ((@Finset.filter Lattice (fun z => ω z ∈ A) (Classical.decPred _)
            q.2.collectedSites).card : ℝ)} ⊆
      {ω : Environment | ∃ u ∈ S, ∃ q : Σ i : Fin (n + 1), Path u (i.val, n - i.val),
        Nat.ceil (φ * (n : ℝ)) ≤
          (@Finset.filter Lattice (fun z => ω z ∈ A) (Classical.decPred _)
            q.2.collectedSites).card} := by
    rintro ω ⟨u, hu, q, hcount⟩
    exact ⟨u, hu, q, Nat.ceil_le.mpr hcount.le⟩
  calc
    (environmentLaw μ) {ω : Environment | ∃ u ∈ S, ∃ q : Σ i : Fin (n + 1),
        Path u (i.val, n - i.val), φ * (n : ℝ) <
          ((@Finset.filter Lattice (fun z => ω z ∈ A) (Classical.decPred _)
            q.2.collectedSites).card : ℝ)} ≤
        (environmentLaw μ) {ω : Environment | ∃ u ∈ S, ∃ q : Σ i : Fin (n + 1),
          Path u (i.val, n - i.val), Nat.ceil (φ * (n : ℝ)) ≤
            (@Finset.filter Lattice (fun z => ω z ∈ A) (Classical.decPred _)
              q.2.collectedSites).card} := measure_mono hsubset
    _ ≤ (S.card : ENNReal) * (1 / 4 : ENNReal) ^ n :=
      measure_exists_start_path_bad_collected_sites_ge_ceil_le μ A hA S φ hφ hMass n

/-- The finite-start scalar prefactor in the source tends to zero. -/
theorem tendsto_peierls_bad_path_rarity_prefactor :
    Tendsto (fun s : ℝ => (17 * s) * (1 / 4 : ℝ) ^ Nat.ceil (s ^ 3)) atTop (nhds 0) := by
  have hcube : Tendsto (fun s : ℝ => s ^ 3) atTop atTop :=
    tendsto_pow_atTop (by norm_num : (3 : ℕ) ≠ 0)
  have hceil : Tendsto (fun s : ℝ => Nat.ceil (s ^ 3)) atTop atTop := by
    apply tendsto_atTop.2
    intro N
    filter_upwards [hcube.eventually_ge_atTop (N : ℝ)] with s hs
    have hsceil : (N : ℝ) ≤ (Nat.ceil (s ^ 3) : ℝ) := hs.trans (Nat.le_ceil _)
    exact Nat.cast_le.mp hsceil
  have hsequence :
      Tendsto (fun k : ℕ => (17 * (k : ℝ)) * (1 / 4 : ℝ) ^ k) atTop (nhds 0) := by
    simpa [mul_assoc] using
      (tendsto_self_mul_const_pow_of_lt_one (by norm_num : 0 ≤ (1 / 4 : ℝ))
        (by norm_num : (1 / 4 : ℝ) < 1)).const_mul 17
  have hupper :
      Tendsto (fun s : ℝ => (17 * (Nat.ceil (s ^ 3) : ℝ)) *
        (1 / 4 : ℝ) ^ Nat.ceil (s ^ 3)) atTop (nhds 0) := hsequence.comp hceil
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with s hs
    positivity
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with s hs
    have hs_sq : 1 ≤ s ^ 2 := by nlinarith [sq_nonneg (s - 1)]
    have hs_le_cube : s ≤ s ^ 3 := by
      have hs_nonneg : 0 ≤ s := le_trans (by norm_num : (0 : ℝ) ≤ 1) hs
      have hprod : 0 ≤ s * (s ^ 2 - 1) := mul_nonneg hs_nonneg (sub_nonneg.mpr hs_sq)
      nlinarith [hprod]
    have hs_le_ceil : s ≤ (Nat.ceil (s ^ 3) : ℝ) := hs_le_cube.trans (Nat.le_ceil _)
    have hmul : 17 * s ≤ 17 * (Nat.ceil (s ^ 3) : ℝ) := by gcongr
    calc
      (17 * s) * (1 / 4 : ℝ) ^ Nat.ceil (s ^ 3) ≤
          (17 * (Nat.ceil (s ^ 3) : ℝ)) * (1 / 4 : ℝ) ^ Nat.ceil (s ^ 3) :=
        mul_le_mul_of_nonneg_right hmul (by positivity)

end LPPDifferentiability

end
