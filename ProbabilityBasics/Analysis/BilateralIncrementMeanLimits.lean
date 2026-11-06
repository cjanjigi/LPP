/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

/-!
# Finite bilateral increment means

For an arbitrary real sequence with a normalized limit, the centered
positive- and negative-coordinate increments have exact finite sums and the
same limiting mean. These are deterministic helpers for the centered
construction; they do not define an array law or an increment process.
-/

public section

open Filter Topology

namespace LPPDifferentiability

/-- A fixed shift of the endpoint does not change the normalized limit. -/
private theorem tendsto_shifted_endpoint_div
    (a : ℕ → ℝ) (q : ℝ)
    (ha : Tendsto (fun n : ℕ => a (n + 1) / ((n + 1 : ℕ) : ℝ)) atTop (𝓝 q))
    (c : ℕ) :
    Tendsto (fun n : ℕ => a (n + c + 1) / (n : ℝ)) atTop (𝓝 q) := by
  have hbase : Tendsto
      (fun n : ℕ => a (c + n + 1) / ((c + n + 1 : ℕ) : ℝ)) atTop (𝓝 q) := by
    simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, Nat.cast_add,
      Nat.cast_one] using (tendsto_add_atTop_iff_nat c).2 ha
  have hc : Tendsto (fun n : ℕ => ((c + 1 : ℕ) : ℝ) / (n : ℝ))
      atTop (𝓝 0) := tendsto_const_div_atTop_nhds_zero_nat _
  have hratio' : Tendsto
      (fun n : ℕ => 1 + ((c + 1 : ℕ) : ℝ) / (n : ℝ)) atTop (𝓝 1) := by
    simpa only [add_zero] using (tendsto_const_nhds (x := (1 : ℝ))).add hc
  have hratio : Tendsto
      (fun n : ℕ => ((n + c + 1 : ℕ) : ℝ) / (n : ℝ)) atTop (𝓝 1) := by
    apply hratio'.congr'
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
    push_cast
    field_simp [hn0]
    ring
  have hprod : Tendsto
      (fun n : ℕ =>
        (a (c + n + 1) / ((c + n + 1 : ℕ) : ℝ)) *
          (((n + c + 1 : ℕ) : ℝ) / (n : ℝ))) atTop (𝓝 q) := by
    simpa only [mul_one] using hbase.mul hratio
  apply hprod.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
  have hindex : c + n + 1 = n + c + 1 := by omega
  rw [hindex]
  field_simp [hn0]

/-- The sum of the positive-coordinate increments telescopes exactly. -/
theorem sum_positive_coordinate_increments
    (a : ℕ → ℝ) (t N : ℕ) :
    (∑ r ∈ Finset.Icc 1 N, (a (r + t + 1) - a (r + t))) =
      a (N + t + 1) - a (t + 1) := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Finset.sum_Icc_succ_top (a := 1) (b := N) (by omega), ih]
      have hstart : N + 1 + t = N + t + 1 := by omega
      rw [hstart]
      ring

/-- A constant sums to its expected number of copies over `1,...,h`. -/
private theorem sum_const_Icc_one (h : ℕ) (hh : 0 < h) (c : ℝ) :
    (∑ _r ∈ Finset.Icc 1 h, c) = (h : ℝ) * c := by
  have h1 : 1 ≤ h := Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hh)
  calc
    (∑ _r ∈ Finset.Icc 1 h, c) =
        (∑ r ∈ Finset.Ico 1 h, c) + c :=
      (Finset.sum_Ico_add_eq_sum_Icc h1).symm
    _ = ∑ r ∈ Finset.Ico 1 (h + 1), c :=
      Finset.sum_Ico_add_eq_sum_Ico_add_one h1 (fun _ : ℕ => c)
    _ = ∑ k ∈ Finset.range h, c := by
      rw [Finset.sum_Ico_eq_sum_range]
      have hlen : h + 1 - 1 = h := by omega
      rw [hlen]
    _ = (h : ℝ) * c := by simp [nsmul_eq_mul]

/-- Summing the negative-coordinate boundary rule from `1` through `h+k`
gives one endpoint value and the finite boundary correction. -/
private theorem sum_negative_coordinate_increments_add
    (a : ℕ → ℝ) (h : ℕ) (hh : 0 < h) (k : ℕ) :
    (∑ r ∈ Finset.Icc 1 (h + k),
      (if r ≤ h then a 1 else a (r - h + 1) - a (r - h))) =
        a (k + 1) + ((h - 1 : ℕ) : ℝ) * a 1 := by
  induction k with
  | zero =>
      have hterms :
          (∑ r ∈ Finset.Icc 1 h,
            (if r ≤ h then a 1 else a (r - h + 1) - a (r - h))) =
            ∑ _r ∈ Finset.Icc 1 h, a 1 := by
        apply Finset.sum_congr rfl
        intro r hr
        have hrh : r ≤ h := (Finset.mem_Icc.mp hr).2
        simp [hrh]
      rw [Nat.add_zero, hterms, sum_const_Icc_one h hh]
      have hcast : ((h - 1 : ℕ) : ℝ) + 1 = (h : ℝ) := by
        exact_mod_cast Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr
          (Nat.ne_of_gt hh))
      rw [← hcast]
      ring
  | succ k ih =>
      have hupper : 1 ≤ h + k + 1 := by omega
      rw [show h + (k + 1) = (h + k) + 1 by omega,
        Finset.sum_Icc_succ_top hupper, ih]
      have hnot : ¬ h + k + 1 ≤ h := by omega
      have hsub₁ : h + k + 1 - h = k + 1 := by omega
      have hsub₂ : h + k + 1 - h + 1 = k + 2 := by omega
      simp [hnot, hsub₁]
      ring

/-- For `N≥h≥1`, the negative-coordinate increments have an exact finite sum.
The boundary value at `r=h` is included in the first branch. -/
theorem sum_negative_coordinate_increments
    (a : ℕ → ℝ) (h N : ℕ) (hh : 0 < h) (hN : h ≤ N) :
    (∑ r ∈ Finset.Icc 1 N,
      (if r ≤ h then a 1 else a (r - h + 1) - a (r - h))) =
        a (N - h + 1) + ((h - 1 : ℕ) : ℝ) * a 1 := by
  have hsum := sum_negative_coordinate_increments_add a h hh (N - h)
  have hdecomp : h + (N - h) = N := by omega
  rw [hdecomp] at hsum
  exact hsum

/-- The positive-coordinate increment means converge to the normalized rate. -/
theorem tendsto_positive_coordinate_increment_mean
    (a : ℕ → ℝ) (q : ℝ)
    (ha : Tendsto (fun n : ℕ => a (n + 1) / ((n + 1 : ℕ) : ℝ)) atTop (𝓝 q))
    (t : ℕ) :
    Tendsto
      (fun N : ℕ =>
        (∑ r ∈ Finset.Icc 1 N, (a (r + t + 1) - a (r + t))) / (N : ℝ))
      atTop (𝓝 q) := by
  have hshift := tendsto_shifted_endpoint_div a q ha t
  have hconst : Tendsto (fun N : ℕ => a (t + 1) / (N : ℝ)) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat _
  have hlimit : Tendsto
      (fun N : ℕ => a (N + t + 1) / (N : ℝ) - a (t + 1) / (N : ℝ))
      atTop (𝓝 q) := by
    simpa only [sub_zero] using hshift.sub hconst
  apply hlimit.congr'
  filter_upwards [] with N
  rw [sum_positive_coordinate_increments]
  rw [sub_div]

/-- The negative-coordinate increment means converge to the same normalized
rate. The finitely many values with `N<h` do not enter the limit. -/
theorem tendsto_negative_coordinate_increment_mean
    (a : ℕ → ℝ) (q : ℝ)
    (ha : Tendsto (fun n : ℕ => a (n + 1) / ((n + 1 : ℕ) : ℝ)) atTop (𝓝 q))
    (h : ℕ) (hh : 0 < h) :
    Tendsto
      (fun N : ℕ =>
        (∑ r ∈ Finset.Icc 1 N,
          (if r ≤ h then a 1 else a (r - h + 1) - a (r - h))) / (N : ℝ))
      atTop (𝓝 q) := by
  have hratio : Tendsto
      (fun n : ℕ => ((n + 1 : ℕ) : ℝ) / ((n + h : ℕ) : ℝ)) atTop (𝓝 1) := by
    convert tendsto_add_mul_div_add_mul_atTop_nhds (1 : ℝ) (h : ℝ) 1
      one_ne_zero using 1
    · ext n
      push_cast
      ring
    · norm_num
  have hbase : Tendsto
      (fun n : ℕ => (a (n + 1) / ((n + 1 : ℕ) : ℝ)) *
        (((n + 1 : ℕ) : ℝ) / ((n + h : ℕ) : ℝ))) atTop (𝓝 q) := by
    simpa only [mul_one] using ha.mul hratio
  have hsub : Tendsto (fun N : ℕ => N - h) atTop atTop := by
    apply Filter.tendsto_atTop.2
    intro m
    filter_upwards [eventually_ge_atTop (m + h)] with N hN
    omega
  have hcomp : Tendsto
      (fun N : ℕ =>
        (a (N - h + 1) / ((N - h + 1 : ℕ) : ℝ)) *
          (((N - h + 1 : ℕ) : ℝ) / ((N - h + h : ℕ) : ℝ)))
      atTop (𝓝 q) := hbase.comp hsub
  have hshift : Tendsto
      (fun N : ℕ => a (N - h + 1) / ((N - h + h : ℕ) : ℝ))
      atTop (𝓝 q) := by
    apply hcomp.congr'
    filter_upwards [] with N
    have hnum : ((N - h + 1 : ℕ) : ℝ) ≠ 0 := by positivity
    field_simp [hnum]
  have hendpoint : Tendsto
      (fun N : ℕ => a (N - h + 1) / (N : ℝ)) atTop (𝓝 q) := by
    apply hshift.congr'
    filter_upwards [eventually_ge_atTop h] with N hN
    have hdecomp : N - h + h = N := Nat.sub_add_cancel hN
    rw [hdecomp]
  have hboundary : Tendsto
      (fun N : ℕ => ((h - 1 : ℕ) : ℝ) * a 1 / (N : ℝ)) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat _
  have hlimit : Tendsto
      (fun N : ℕ => a (N - h + 1) / (N : ℝ) +
        ((h - 1 : ℕ) : ℝ) * a 1 / (N : ℝ)) atTop (𝓝 q) := by
    simpa only [add_zero] using hendpoint.add hboundary
  apply hlimit.congr'
  filter_upwards [eventually_ge_atTop h] with N hN
  rw [sum_negative_coordinate_increments a h N hh hN, add_div]

end LPPDifferentiability
