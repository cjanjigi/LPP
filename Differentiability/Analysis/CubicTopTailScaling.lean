/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Differentiability.Analysis.CubicTiltScaling
public import Differentiability.Model.TiltStripCardinality
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Cubic strip top-count tail arithmetic

This file proves the scalar exponential bounds for the closed tilted strip.
It keeps the finite geometry of the strip separate from the Gaussian limit.
-/

public section

open Filter
open scoped Topology

namespace LPPDifferentiability

/-- A cardinality bound gives the exact two-step exponential chain used for the tail. -/
theorem cubic_top_tail_exp_chain_of_cardinality
    (s phi n card : ℝ)
    (hs : 0 < s) (hphi : 0 < phi) (hn : s ^ 3 ≤ n)
    (hcard_pos : 0 < card) (hcard_le : card ≤ 34 * n * s) :
    Real.exp (-(2 * (phi * n) ^ 2 / card)) ≤
        Real.exp (-(phi ^ 2 * n / (17 * s))) ∧
      Real.exp (-(phi ^ 2 * n / (17 * s))) ≤
        Real.exp (-(phi ^ 2 * s ^ 2 / 17)) := by
  have hphi_sq_pos : 0 < phi ^ 2 := sq_pos_of_pos hphi
  have hphi_sq_nonneg : 0 ≤ phi ^ 2 := hphi_sq_pos.le
  have hn_pos : 0 < n := lt_of_lt_of_le (by positivity) hn
  have hcoeff : 0 ≤ phi ^ 2 * n := mul_nonneg hphi_sq_nonneg hn_pos.le
  have hnum : phi ^ 2 * n * card ≤ 2 * (phi * n) ^ 2 * (17 * s) := by
    calc
      phi ^ 2 * n * card ≤ phi ^ 2 * n * (34 * n * s) :=
        mul_le_mul_of_nonneg_left hcard_le hcoeff
      _ = 2 * (phi * n) ^ 2 * (17 * s) := by ring
  have hfrac : phi ^ 2 * n / (17 * s) ≤ 2 * (phi * n) ^ 2 / card := by
    rw [div_le_div_iff₀ (by positivity : 0 < 17 * s) hcard_pos]
    exact hnum
  have hratio : s ^ 2 ≤ n / s := by
    apply (le_div_iff₀ hs).2
    nlinarith [hn]
  have hscale : phi ^ 2 * s ^ 2 / 17 ≤ phi ^ 2 * n / (17 * s) := by
    have hcoeff : 0 ≤ phi ^ 2 / 17 := div_nonneg hphi_sq_nonneg (by norm_num)
    calc
      phi ^ 2 * s ^ 2 / 17 = (phi ^ 2 / 17) * s ^ 2 := by ring
      _ ≤ (phi ^ 2 / 17) * (n / s) :=
        mul_le_mul_of_nonneg_left hratio hcoeff
      _ = phi ^ 2 * n / (17 * s) := by
        field_simp [hs.ne']
  exact ⟨Real.exp_le_exp.mpr (neg_le_neg hfrac),
    Real.exp_le_exp.mpr (neg_le_neg hscale)⟩

/-- The closed strip is nonempty and has the cardinality bound used for the tail. -/
theorem cubic_top_tail_region_cardinality_bounds (a s : ℝ) (hs : 1 ≤ s) :
    let n : ℕ := Nat.ceil (s ^ 3)
    let slice : ℤ → Finset Lattice := fun k =>
      (Finset.Icc
        (Int.ceil (a * (k : ℝ) - 8 * s))
        (Int.floor (a * (k : ℝ) + 8 * s))).image (fun i => (i, k - i))
    let region : Finset Lattice := (Finset.Icc (0 : ℤ) (n : ℤ)).biUnion slice
    0 < (region.card : ℝ) ∧ (region.card : ℝ) ≤ 34 * (n : ℝ) * s := by
  dsimp only
  let n : ℕ := Nat.ceil (s ^ 3)
  let slice : ℤ → Finset Lattice := fun k =>
    (Finset.Icc
      (Int.ceil (a * (k : ℝ) - 8 * s))
      (Int.floor (a * (k : ℝ) + 8 * s))).image (fun i => (i, k - i))
  let region : Finset Lattice := (Finset.Icc (0 : ℤ) (n : ℤ)).biUnion slice
  change 0 < (region.card : ℝ) ∧ (region.card : ℝ) ≤ 34 * (n : ℝ) * s
  have hn : 1 ≤ n := by
    simpa only [n] using (cubic_length_ceil_bounds s hs).1
  have hbounds := tiltStripRegion_card_bounds a s n hs hn
  have hcard : (region.card : ℝ) ≤ 34 * (n : ℝ) * s := by
    simpa only [region, slice] using hbounds.1.trans hbounds.2
  have hzero_mem : ((0 : ℤ), (0 : ℤ)) ∈ region := by
    have hmem :=
      (tiltStripRegion_mem_iff a s n ((0 : ℤ), (0 : ℤ))).2
        (by
          constructor
          · norm_num
          constructor
          · omega
          · have hs0 : 0 ≤ s := le_trans (by norm_num) hs
            simpa only [Int.cast_zero, mul_zero, zero_sub, neg_zero, abs_zero] using
              (mul_nonneg (show 0 ≤ (8 : ℝ) by norm_num) hs0))
    simpa only [region, slice] using hmem
  have hpos : 0 < (region.card : ℝ) := by
    exact Nat.cast_pos.mpr (Finset.card_pos.mpr ⟨(0, 0), hzero_mem⟩)
  exact ⟨hpos, hcard⟩

/-- The exact scalar chain for the finite strip; positivity and
cardinality are proved from its explicit enumeration. -/
theorem cubic_top_tail_actual_region_exp_chain (a phi s : ℝ)
    (hphi : 0 < phi) (hs : 1 ≤ s) :
    let n : ℕ := Nat.ceil (s ^ 3)
    let slice : ℤ → Finset Lattice := fun k =>
      (Finset.Icc
        (Int.ceil (a * (k : ℝ) - 8 * s))
        (Int.floor (a * (k : ℝ) + 8 * s))).image (fun i => (i, k - i))
    let region : Finset Lattice := (Finset.Icc (0 : ℤ) (n : ℤ)).biUnion slice
    Real.exp (-(2 * (phi * (n : ℝ)) ^ 2 / (region.card : ℝ))) ≤
        Real.exp (-(phi ^ 2 * (n : ℝ) / (17 * s))) ∧
      Real.exp (-(phi ^ 2 * (n : ℝ) / (17 * s))) ≤
        Real.exp (-(phi ^ 2 * s ^ 2 / 17)) := by
  dsimp only
  let n : ℕ := Nat.ceil (s ^ 3)
  let slice : ℤ → Finset Lattice := fun k =>
    (Finset.Icc
      (Int.ceil (a * (k : ℝ) - 8 * s))
      (Int.floor (a * (k : ℝ) + 8 * s))).image (fun i => (i, k - i))
  let region : Finset Lattice := (Finset.Icc (0 : ℤ) (n : ℤ)).biUnion slice
  change
    Real.exp (-(2 * (phi * (n : ℝ)) ^ 2 / (region.card : ℝ))) ≤
        Real.exp (-(phi ^ 2 * (n : ℝ) / (17 * s))) ∧
      Real.exp (-(phi ^ 2 * (n : ℝ) / (17 * s))) ≤
        Real.exp (-(phi ^ 2 * s ^ 2 / 17))
  have hregion := cubic_top_tail_region_cardinality_bounds a s hs
  have hpos : 0 < (region.card : ℝ) := by
    simpa only [n, slice, region] using hregion.1
  have hcard : (region.card : ℝ) ≤ 34 * (n : ℝ) * s := by
    simpa only [n, slice, region] using hregion.2
  have hn : (s ^ 3) ≤ (n : ℝ) := by
    simpa only [n] using (cubic_length_ceil_bounds s hs).2.1
  have hspos : 0 < s := lt_of_lt_of_le zero_lt_one hs
  exact cubic_top_tail_exp_chain_of_cardinality s phi (n : ℝ)
    (region.card : ℝ) hspos hphi hn hpos hcard

/-- The ordered product of the endpoint slices has the prefactor bound used for the tail. -/
theorem cubic_top_tail_endpoint_pairs_card_le (a s : ℝ) (hs : 1 ≤ s) :
    let n : ℕ := Nat.ceil (s ^ 3)
    let startSlice : Finset Lattice :=
      (Finset.Icc
        (Int.ceil (a * (0 : ℝ) - 8 * s))
        (Int.floor (a * (0 : ℝ) + 8 * s))).image (fun i => (i, (0 : ℤ) - i))
    let endSlice : Finset Lattice :=
      (Finset.Icc
        (Int.ceil (a * ((n : ℤ) : ℝ) - 8 * s))
        (Int.floor (a * ((n : ℤ) : ℝ) + 8 * s))).image
          (fun i => (i, (n : ℤ) - i))
    ((startSlice ×ˢ endSlice).card : ℝ) ≤ 289 * s ^ 2 := by
  dsimp only
  exact tiltStripEndpointPairs_card_le a s (Nat.ceil (s ^ 3)) hs

/-- The polynomial prefactor times its Gaussian tail tends to zero. -/
theorem tendsto_cubic_top_tail_gaussian_prefactor (phi : ℝ) (hphi : 0 < phi) :
    Tendsto (fun s : ℝ => 289 * s ^ 2 * Real.exp (-(phi ^ 2 * s ^ 2 / 17)))
      atTop (𝓝 0) := by
  have hc : 0 < phi ^ 2 / 17 := by positivity
  let c : ℝ := phi ^ 2 / 17
  have hpow : Tendsto (fun s : ℝ => s ^ 2) atTop atTop :=
    tendsto_pow_atTop (by norm_num)
  have hscale : Tendsto (fun s : ℝ => c * s ^ 2) atTop atTop :=
    hpow.const_mul_atTop (by positivity : 0 < c)
  have hbase : Tendsto
      (fun s : ℝ => (c * s ^ 2) * Real.exp (-(c * s ^ 2))) atTop (𝓝 0) := by
    have hpowexp : Tendsto
        (fun x : ℝ => x ^ 1 * Real.exp (-x)) atTop (𝓝 0) :=
      Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1
    have hcomp : Tendsto
        (fun s : ℝ => (c * s ^ 2) ^ 1 * Real.exp (-(c * s ^ 2)))
        atTop (𝓝 0) := hpowexp.comp hscale
    simpa only [pow_one] using hcomp
  have hfactor : Tendsto
      (fun s : ℝ => (289 / c) * ((c * s ^ 2) * Real.exp (-(c * s ^ 2))))
      atTop (𝓝 ((289 / c) * 0)) :=
    tendsto_const_nhds.mul hbase
  have hlimit : Tendsto
      (fun s : ℝ => (289 / c) * ((c * s ^ 2) * Real.exp (-(c * s ^ 2))))
      atTop (𝓝 0) := by
    simpa only [mul_zero] using hfactor
  apply Tendsto.congr' ?_ hlimit
  filter_upwards [] with s
  have hexp : phi ^ 2 * s ^ 2 / 17 = c * s ^ 2 := by
    dsimp [c]
    ring
  have hfactor_identity : (289 / c) * (c * s ^ 2) = 289 * s ^ 2 := by
    calc
      (289 / c) * (c * s ^ 2) = ((289 / c) * c) * s ^ 2 := by ring
      _ = 289 * s ^ 2 := by rw [div_mul_cancel₀ _ hc.ne']
  rw [hexp]
  calc
    (289 / c) * (c * s ^ 2 * Real.exp (-(c * s ^ 2))) =
        ((289 / c) * (c * s ^ 2)) * Real.exp (-(c * s ^ 2)) := by ring
    _ = 289 * s ^ 2 * Real.exp (-(c * s ^ 2)) := by
      rw [hfactor_identity]

end LPPDifferentiability

end
