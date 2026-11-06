/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

/-! # Rational floor transfer -/

public section

open Filter
open scoped Topology

namespace LPPDifferentiability

/-- For a positive natural denominator, coordinatewise floors of a rational
multiple of a natural pair lie between the adjacent integer multiples of that
pair. -/
theorem nat_floor_rational_sandwich (A : ℕ × ℕ) (d n : ℕ) (hd : 0 < d) :
    (n / d) • A ≤
        (⌊(n : ℝ) * (A.1 : ℝ) / (d : ℝ)⌋₊,
          ⌊(n : ℝ) * (A.2 : ℝ) / (d : ℝ)⌋₊) ∧
      (⌊(n : ℝ) * (A.1 : ℝ) / (d : ℝ)⌋₊,
        ⌊(n : ℝ) * (A.2 : ℝ) / (d : ℝ)⌋₊) ≤
          (n / d + 1) • A := by
  let k : ℕ := n / d
  let r : ℕ := n % d
  have hn : n = d * k + r := by
    simpa [k, r] using (Nat.div_add_mod n d).symm
  have hdR : 0 < (d : ℝ) := Nat.cast_pos.mpr hd
  have hcoord (a : ℕ) :
      k * a ≤ ⌊(n : ℝ) * (a : ℝ) / (d : ℝ)⌋₊ ∧
        ⌊(n : ℝ) * (a : ℝ) / (d : ℝ)⌋₊ ≤ (k + 1) * a := by
    let x : ℝ := (n : ℝ) * (a : ℝ) / (d : ℝ)
    have hx : x = ((k * a : ℕ) : ℝ) + ((r * a : ℕ) : ℝ) / (d : ℝ) := by
      dsimp [x]
      rw [hn]
      push_cast
      field_simp [hdR.ne']
    have hrD : (r : ℝ) ≤ (d : ℝ) := by
      exact_mod_cast (Nat.le_of_lt (Nat.mod_lt n hd))
    have hfrac_nonneg : 0 ≤ ((r * a : ℕ) : ℝ) / (d : ℝ) := by
      positivity
    have hfrac_le : ((r * a : ℕ) : ℝ) / (d : ℝ) ≤ (a : ℝ) := by
      apply (div_le_iff₀ hdR).2
      have hmul := mul_le_mul_of_nonneg_right hrD (Nat.cast_nonneg a)
      simpa only [Nat.cast_mul, mul_comm] using hmul
    have hfrac_le' : (r : ℝ) * (a : ℝ) / (d : ℝ) ≤ (a : ℝ) := by
      simpa only [Nat.cast_mul] using hfrac_le
    have hlo : ((k * a : ℕ) : ℝ) ≤ x := by
      rw [hx, Nat.cast_mul]
      exact le_add_of_nonneg_right hfrac_nonneg
    have hhi : x ≤ (((k + 1) * a : ℕ) : ℝ) := by
      rw [hx]
      push_cast
      nlinarith [hfrac_le']
    have hx0 : 0 ≤ x := by
      dsimp [x]
      positivity
    constructor
    · exact (Nat.le_floor_iff hx0).2 hlo
    · exact Nat.floor_le_of_le hhi
  have h1 := hcoord A.1
  have h2 := hcoord A.2
  constructor
  · constructor
    · simpa [k, nsmul_eq_mul] using h1.1
    · simpa [k, nsmul_eq_mul] using h2.1
  · constructor
    · simpa [k, nsmul_eq_mul] using h1.2
    · simpa [k, nsmul_eq_mul] using h2.2

/-- A coordinatewise monotone signed sequence has the same normalized limit
along rationally floored multiples as along its integer ray. This is a pure
sequence lemma; it introduces no rate function or expectation object. -/
theorem tendsto_rational_floor_of_tendsto_ray
    (B : (ℕ × ℕ) → ℝ) (hB : Monotone B) (A : ℕ × ℕ)
    (d : ℕ) (hd : 0 < d) (L : ℝ)
    (hray : Tendsto (fun j : ℕ => B (j • A) / (j : ℝ)) atTop (𝓝 L)) :
    Tendsto
      (fun n : ℕ =>
        B (⌊(n : ℝ) * (A.1 : ℝ) / (d : ℝ)⌋₊,
          ⌊(n : ℝ) * (A.2 : ℝ) / (d : ℝ)⌋₊) / (n : ℝ))
      atTop (𝓝 (L / (d : ℝ))) := by
  let k : ℕ → ℕ := fun n => n / d
  have hk : Tendsto k atTop atTop := by
    simpa only [k] using Nat.tendsto_div_const_atTop (Nat.ne_of_gt hd)
  have hk1 : Tendsto (fun n : ℕ => k n + 1) atTop atTop :=
    tendsto_atTop_mono (fun n => Nat.le_add_right (k n) 1) hk
  have hrayk : Tendsto (fun n : ℕ => B (k n • A) / (k n : ℝ))
      atTop (𝓝 L) := by
    simpa only [Function.comp_def] using hray.comp hk
  have hrayk1 : Tendsto (fun n : ℕ => B ((k n + 1) • A) / ((k n + 1 : ℕ) : ℝ))
      atTop (𝓝 L) := hray.comp hk1
  have hmod : Tendsto (fun n : ℕ => ((n % d : ℕ) : ℝ) / (n : ℝ)) atTop (𝓝 0) :=
    tendsto_mod_div_atTop_nhds_zero_nat hd
  have hratio_eq (n : ℕ) (hnpos : 0 < n) :
      (k n : ℝ) / (n : ℝ) =
        1 / (d : ℝ) - (((n % d : ℕ) : ℝ) / (n : ℝ)) / (d : ℝ) := by
    have hnR : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hnpos.ne'
    have hdR : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hd.ne'
    have hdecomp : (k n : ℝ) * (d : ℝ) + ((n % d : ℕ) : ℝ) = (n : ℝ) := by
      dsimp [k]
      exact_mod_cast (by simpa [Nat.mul_comm] using Nat.div_add_mod n d)
    have hkd : (k n : ℝ) * (d : ℝ) = (n : ℝ) - ((n % d : ℕ) : ℝ) := by
      linarith
    calc
      (k n : ℝ) / (n : ℝ) = ((k n : ℝ) * (d : ℝ)) / ((n : ℝ) * (d : ℝ)) := by
        field_simp [hnR, hdR]
      _ = ((n : ℝ) - ((n % d : ℕ) : ℝ)) / ((n : ℝ) * (d : ℝ)) := by
        rw [hkd]
      _ = 1 / (d : ℝ) - (((n % d : ℕ) : ℝ) / (n : ℝ)) / (d : ℝ) := by
        field_simp [hnR, hdR]
  have hratio_eq_event :
      (fun n : ℕ => (k n : ℝ) / (n : ℝ)) =ᶠ[atTop]
        fun n => 1 / (d : ℝ) - (((n % d : ℕ) : ℝ) / (n : ℝ)) / (d : ℝ) := by
    filter_upwards [eventually_atTop.2 ⟨1, fun n hn => hn⟩] with n hn
    exact hratio_eq n hn
  have hratio : Tendsto (fun n : ℕ => (k n : ℝ) / (n : ℝ))
      atTop (𝓝 (1 / (d : ℝ))) := by
    have hconst : Tendsto (fun _ : ℕ => 1 / (d : ℝ)) atTop (𝓝 (1 / (d : ℝ))) :=
      tendsto_const_nhds
    have hbase : Tendsto
        (fun n : ℕ => 1 / (d : ℝ) - (((n % d : ℕ) : ℝ) / (n : ℝ)) / (d : ℝ))
        atTop (𝓝 (1 / (d : ℝ) - (0 : ℝ) / (d : ℝ))) :=
      hconst.sub (hmod.div_const (d : ℝ))
    simpa using hbase.congr' hratio_eq_event.symm
  have hone_div_n : Tendsto (fun n : ℕ => (1 : ℝ) / (n : ℝ)) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ)
  have hratio_succ_eq :
      (fun n : ℕ => ((k n + 1 : ℕ) : ℝ) / (n : ℝ)) =ᶠ[atTop]
        fun n => (k n : ℝ) / (n : ℝ) + (1 : ℝ) / (n : ℝ) := by
    exact Eventually.of_forall fun n => by
      push_cast
      ring
  have hratio_succ : Tendsto (fun n : ℕ => ((k n + 1 : ℕ) : ℝ) / (n : ℝ))
      atTop (𝓝 (1 / (d : ℝ))) := by
    simpa using (hratio.add hone_div_n).congr' hratio_succ_eq.symm
  have hleft_eq :
      (fun n : ℕ => B (k n • A) / (n : ℝ)) =ᶠ[atTop]
        fun n => ((k n : ℝ) / (n : ℝ)) * (B (k n • A) / (k n : ℝ)) := by
    filter_upwards [eventually_gt_atTop (0 : ℕ), hk.eventually_gt_atTop 0]
      with n hn hkpos
    have hnR : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
    have hkR : (k n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hkpos.ne'
    field_simp [hnR, hkR]
  have hright_eq :
      (fun n : ℕ => B ((k n + 1) • A) / (n : ℝ)) =ᶠ[atTop]
        fun n => (((k n + 1 : ℕ) : ℝ) / (n : ℝ)) *
          (B ((k n + 1) • A) / ((k n + 1 : ℕ) : ℝ)) := by
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    have hnR : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
    have hk1R : ((k n + 1 : ℕ) : ℝ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Nat.succ_ne_zero (k n))
    field_simp [hnR, hk1R]
  have hvalue : (1 / (d : ℝ)) * L = L / (d : ℝ) := by
    field_simp [Nat.cast_ne_zero.mpr hd.ne']
  have hleft : Tendsto (fun n : ℕ => B (k n • A) / (n : ℝ))
      atTop (𝓝 (L / (d : ℝ))) := by
    rw [← hvalue]
    exact (hratio.mul hrayk).congr' hleft_eq.symm
  have hright : Tendsto (fun n : ℕ => B ((k n + 1) • A) / (n : ℝ))
      atTop (𝓝 (L / (d : ℝ))) := by
    rw [← hvalue]
    exact (hratio_succ.mul hrayk1).congr' hright_eq.symm
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hleft hright
  · filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    have hsandwich := nat_floor_rational_sandwich A d n hd
    exact div_le_div_of_nonneg_right (hB hsandwich.1) (Nat.cast_nonneg n)
  · filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    have hsandwich := nat_floor_rational_sandwich A d n hd
    exact div_le_div_of_nonneg_right (hB hsandwich.2) (Nat.cast_nonneg n)

end LPPDifferentiability
