/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import ProbabilityBasics.Analysis.RationalFloorTransfer

/-! # Restoring the signed linear mean after floor transfer

These conditional sequence lemmas subtract a signed linear correction before
using monotonicity, and restore it after taking the limit. They do not assume
that the original signed sequence is monotone.
-/

public section

open Filter
open scoped Topology

namespace LPPDifferentiability

/-- The normalized natural floor has the expected limit, including at zero. -/
theorem tendsto_nat_floor_mul_div_nat (u : ℝ) (hu : 0 ≤ u) :
    Tendsto (fun n : ℕ => (⌊(n : ℝ) * u⌋₊ : ℝ) / (n : ℝ))
      atTop (𝓝 u) := by
  simpa only [Function.comp_def, mul_comm u] using
    (tendsto_nat_floor_mul_div_atTop hu).comp
      (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop)

/-- The sum of the two floored coordinates has the normalized length limit. -/
theorem tendsto_floor_pair_length (u v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    Tendsto (fun n : ℕ =>
      (((⌊(n : ℝ) * u⌋₊ + ⌊(n : ℝ) * v⌋₊ : ℕ) : ℝ) / (n : ℝ)))
      atTop (𝓝 (u + v)) := by
  simpa only [Nat.cast_add, add_div] using
    (tendsto_nat_floor_mul_div_nat u hu).add (tendsto_nat_floor_mul_div_nat v hv)

/-- A ray limit of a signed sequence gives its rational floor limit when
subtracting length times a signed coefficient makes the sequence monotone. -/
theorem tendsto_rational_floor_of_corrected_ray
    (E : (ℕ × ℕ) → ℝ) (m : ℝ)
    (hmono : Monotone (fun z : ℕ × ℕ => E z - ((z.1 + z.2 : ℕ) : ℝ) * m))
    (A : ℕ × ℕ) (d : ℕ) (hd : 0 < d) (L : ℝ)
    (hray : Tendsto (fun j : ℕ => E (j • A) / (j : ℝ)) atTop (𝓝 L)) :
    Tendsto (fun n : ℕ =>
      E (⌊(n : ℝ) * (A.1 : ℝ) / (d : ℝ)⌋₊,
        ⌊(n : ℝ) * (A.2 : ℝ) / (d : ℝ)⌋₊) / (n : ℝ))
      atTop (𝓝 (L / (d : ℝ))) := by
  let B : (ℕ × ℕ) → ℝ := fun z => E z - ((z.1 + z.2 : ℕ) : ℝ) * m
  have hcorrected : Tendsto (fun j : ℕ => B (j • A) / (j : ℝ))
      atTop (𝓝 (L - ((A.1 + A.2 : ℕ) : ℝ) * m)) := by
    apply (hray.sub tendsto_const_nhds).congr'
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with j hj
    have hj0 : (j : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hj.ne'
    dsimp [B]
    simp only [Nat.cast_add, Nat.cast_mul]
    field_simp
  have hfloor := tendsto_rational_floor_of_tendsto_ray B hmono A d hd
    (L - ((A.1 + A.2 : ℕ) : ℝ) * m) hcorrected
  have hlength : Tendsto (fun n : ℕ =>
      (((⌊(n : ℝ) * (A.1 : ℝ) / (d : ℝ)⌋₊ +
        ⌊(n : ℝ) * (A.2 : ℝ) / (d : ℝ)⌋₊ : ℕ) : ℝ) / (n : ℝ)))
      atTop (𝓝 (((A.1 : ℝ) + A.2) / (d : ℝ))) := by
    simpa only [← mul_div_assoc, ← add_div] using
      tendsto_floor_pair_length ((A.1 : ℝ) / d) ((A.2 : ℝ) / d)
        (by positivity) (by positivity)
  have hsum := hfloor.add (hlength.mul_const m)
  have hvalue : (L - ((A.1 + A.2 : ℕ) : ℝ) * m) / (d : ℝ) +
      (((A.1 : ℝ) + A.2) / (d : ℝ)) * m = L / (d : ℝ) := by
    push_cast
    ring
  rw [hvalue] at hsum
  convert hsum using 1
  funext n
  dsimp [B]
  ring

end LPPDifferentiability
