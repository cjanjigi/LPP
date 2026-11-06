/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import LPP_Foundations.Frozen.Model.Lattice
public import Mathlib.Algebra.Order.Floor.Defs
public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Finset.Prod
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-! Finite counts for the closed tilted strips used in the proof of the tilt lemma. -/

@[expose] public section

namespace LPPDifferentiability

/-- On a fixed integer level, the closed strip is the image of a closed integer interval. -/
theorem tiltStripLevelSlice_mem_iff (a s : ℝ) (k : ℤ) (z : Lattice) :
    z ∈ (Finset.Icc
        (Int.ceil (a * (k : ℝ) - 8 * s))
        (Int.floor (a * (k : ℝ) + 8 * s))).image (fun i => (i, k - i)) ↔
      z.1 + z.2 = k ∧
        |(1 - a) * (z.1 : ℝ) - a * (z.2 : ℝ)| ≤ 8 * s := by
  classical
  constructor
  · intro hz
    rcases Finset.mem_image.mp hz with ⟨i, hi, hzi⟩
    rcases Finset.mem_Icc.mp hi with ⟨hlo, hhi⟩
    have hfirst : z.1 = i := congrArg Prod.fst hzi.symm
    have hsecond : z.2 = k - i := congrArg Prod.snd hzi.symm
    refine ⟨?_, ?_⟩
    · rw [hfirst, hsecond]
      omega
    · have htrans :
          (1 - a) * (z.1 : ℝ) - a * (z.2 : ℝ) =
            (z.1 : ℝ) - a * (k : ℝ) := by
        rw [hfirst, hsecond]
        push_cast
        ring
      rw [htrans, abs_le]
      constructor
      · have hreal : a * (k : ℝ) - 8 * s ≤ (i : ℝ) := Int.ceil_le.mp hlo
        have hfirstReal : (z.1 : ℝ) = (i : ℝ) := by exact_mod_cast hfirst
        linarith
      · have hreal : (i : ℝ) ≤ a * (k : ℝ) + 8 * s := Int.le_floor.mp hhi
        have hfirstReal : (z.1 : ℝ) = (i : ℝ) := by exact_mod_cast hfirst
        linarith
  · rintro ⟨hlevel, htrans⟩
    have hlevelCast : ((z.1 + z.2 : ℤ) : ℝ) = (k : ℝ) := by
      exact_mod_cast hlevel
    have hcoord :
        (1 - a) * (z.1 : ℝ) - a * (z.2 : ℝ) =
          (z.1 : ℝ) - a * (k : ℝ) := by
      calc
        (1 - a) * (z.1 : ℝ) - a * (z.2 : ℝ) =
            (z.1 : ℝ) - a * ((z.1 + z.2 : ℤ) : ℝ) := by
              rw [Int.cast_add]
              ring
        _ = (z.1 : ℝ) - a * (k : ℝ) := by rw [hlevelCast]
    have hwindow :
        a * (k : ℝ) - 8 * s ≤ (z.1 : ℝ) ∧
          (z.1 : ℝ) ≤ a * (k : ℝ) + 8 * s := by
      rw [hcoord, abs_le] at htrans
      constructor <;> linarith
    have hlo : Int.ceil (a * (k : ℝ) - 8 * s) ≤ z.1 :=
      Int.ceil_le.mpr hwindow.1
    have hhi : z.1 ≤ Int.floor (a * (k : ℝ) + 8 * s) :=
      Int.le_floor.mpr hwindow.2
    have hsecond : z.2 = k - z.1 := by omega
    apply Finset.mem_image.mpr
    refine ⟨z.1, Finset.mem_Icc.mpr ⟨hlo, hhi⟩, ?_⟩
    apply Prod.ext
    · rfl
    · omega

/-- Every fixed-level slice contains at most `16s+1` lattice sites when `s ≥ 1`.

The estimate holds for every real `a`, hence in particular for directions
with `0 < a < 1`. -/
theorem tiltStripLevelSlice_card_le (a s : ℝ) (k : ℤ) (hs : 1 ≤ s) :
    ((Finset.Icc
        (Int.ceil (a * (k : ℝ) - 8 * s))
        (Int.floor (a * (k : ℝ) + 8 * s))).image (fun i => (i, k - i))).card ≤
      16 * s + 1 := by
  classical
  let lower : ℝ := a * (k : ℝ) - 8 * s
  let upper : ℝ := a * (k : ℝ) + 8 * s
  change ((Finset.Icc (Int.ceil lower) (Int.floor upper)).image
      (fun i => (i, k - i))).card ≤ 16 * s + 1
  have hwidth : lower + 1 ≤ upper := by
    dsimp [lower, upper]
    linarith
  have hinterval : Int.ceil lower ≤ Int.floor upper := by
    apply Int.le_floor.mpr
    exact (Int.ceil_lt_add_one lower).le.trans hwidth
  have hcardZ : ((Finset.Icc (Int.ceil lower) (Int.floor upper)).card : ℤ) =
      Int.floor upper + 1 - Int.ceil lower := by
    rw [Int.card_Icc_of_le (a := Int.ceil lower) (b := Int.floor upper)
      (by omega)]
  have hcardR : ((Finset.Icc (Int.ceil lower) (Int.floor upper)).card : ℝ) =
      (Int.floor upper : ℝ) + 1 - (Int.ceil lower : ℝ) := by
    exact_mod_cast hcardZ
  have hinj : Function.Injective (fun i : ℤ => (i, k - i)) := by
    intro i j hij
    exact congrArg Prod.fst hij
  calc
    (((Finset.Icc (Int.ceil lower) (Int.floor upper)).image
        (fun i => (i, k - i))).card : ℝ) =
        (Finset.Icc (Int.ceil lower) (Int.floor upper)).card := by
          rw [Finset.card_image_of_injective _ hinj]
    _ = (Int.floor upper : ℝ) + 1 - (Int.ceil lower : ℝ) := hcardR
    _ ≤ 16 * s + 1 := by
      have hfloor : (Int.floor upper : ℝ) ≤ upper := Int.floor_le upper
      have hceil : lower ≤ (Int.ceil lower : ℝ) := Int.le_ceil lower
      dsimp [lower, upper] at hfloor hceil ⊢
      linarith

/-- The finite closed region contains exactly the lattice points on levels `0` through `n`
whose literal transverse coordinate has absolute value at most `8s`. -/
theorem tiltStripRegion_mem_iff (a s : ℝ) (n : ℕ) (z : Lattice) :
    let slice : ℤ → Finset Lattice := fun k => (Finset.Icc
      (Int.ceil (a * (k : ℝ) - 8 * s))
      (Int.floor (a * (k : ℝ) + 8 * s))).image (fun i => (i, k - i))
    let region : Finset Lattice := (Finset.Icc (0 : ℤ) (n : ℤ)).biUnion slice
    z ∈ region ↔
      0 ≤ z.1 + z.2 ∧ (z.1 + z.2 : ℤ) ≤ n ∧
        |(1 - a) * (z.1 : ℝ) - a * (z.2 : ℝ)| ≤ 8 * s := by
  dsimp only
  classical
  constructor
  · intro hz
    rcases Finset.mem_biUnion.mp hz with ⟨k, hk, hslice⟩
    rcases Finset.mem_Icc.mp hk with ⟨hk0, hkn⟩
    rcases (tiltStripLevelSlice_mem_iff a s k z).mp hslice with ⟨hlevel, htrans⟩
    exact ⟨by omega, by omega, htrans⟩
  · rintro ⟨hz0, hzn, htrans⟩
    refine Finset.mem_biUnion.mpr ⟨z.1 + z.2, Finset.mem_Icc.mpr ⟨hz0, ?_⟩, ?_⟩
    · exact_mod_cast hzn
    · exact (tiltStripLevelSlice_mem_iff a s (z.1 + z.2) z).mpr ⟨rfl, htrans⟩

/-- The strip region has at most `(n+1)(16s+1)` sites, hence at most `34ns` for
`n ≥ 1` and `s ≥ 1`. The statement uses the actual finite union of the exact slices. -/
theorem tiltStripRegion_card_bounds (a s : ℝ) (n : ℕ)
    (hs : 1 ≤ s) (hn : 1 ≤ n) :
    let slice : ℤ → Finset Lattice := fun k => (Finset.Icc
      (Int.ceil (a * (k : ℝ) - 8 * s))
      (Int.floor (a * (k : ℝ) + 8 * s))).image (fun i => (i, k - i))
    let region : Finset Lattice := (Finset.Icc (0 : ℤ) (n : ℤ)).biUnion slice
    ((region.card : ℝ) ≤ (n + 1) * (16 * s + 1)) ∧
      ((n + 1) * (16 * s + 1) ≤ 34 * n * s) := by
  dsimp only
  classical
  let slice : ℤ → Finset Lattice := fun k =>
    (Finset.Icc
      (Int.ceil (a * (k : ℝ) - 8 * s))
      (Int.floor (a * (k : ℝ) + 8 * s))).image (fun i => (i, k - i))
  let levels : Finset ℤ := Finset.Icc (0 : ℤ) (n : ℤ)
  let region : Finset Lattice := levels.biUnion slice
  change ((region.card : ℝ) ≤ (n + 1) * (16 * s + 1)) ∧
    ((n + 1) * (16 * s + 1) ≤ 34 * n * s)
  have hslice (k : ℤ) : ((slice k).card : ℝ) ≤ 16 * s + 1 := by
    simpa only [slice] using tiltStripLevelSlice_card_le a s k hs
  have hbi : region.card ≤ ∑ k ∈ levels, (slice k).card := by
    dsimp only [region, levels]
    exact Finset.card_biUnion_le
  have hbiR : (region.card : ℝ) ≤ ∑ k ∈ levels, ((slice k).card : ℝ) := by
    calc
      (region.card : ℝ) ≤ ((∑ k ∈ levels, (slice k).card : ℕ) : ℝ) := by
        exact_mod_cast hbi
      _ = ∑ k ∈ levels, ((slice k).card : ℝ) := by norm_cast
  have hsum :
      (∑ k ∈ levels, ((slice k).card : ℝ)) ≤
        ∑ k ∈ levels, (16 * s + 1) := by
    apply Finset.sum_le_sum
    intro k hk
    exact hslice k
  have hlevelsZ : (levels.card : ℤ) = (n + 1 : ℤ) := by
    dsimp only [levels]
    rw [Int.card_Icc_of_le (a := 0) (b := (n : ℤ)) (by omega)]
    omega
  have hlevelsR : (levels.card : ℝ) = (n + 1 : ℝ) := by
    exact_mod_cast hlevelsZ
  have hconst : (∑ k ∈ levels, (16 * s + 1)) =
      (levels.card : ℝ) * (16 * s + 1) := by
    rw [Finset.sum_const, nsmul_eq_mul]
  constructor
  · calc
      (region.card : ℝ) ≤ ∑ k ∈ levels, ((slice k).card : ℝ) := hbiR
      _ ≤ ∑ k ∈ levels, (16 * s + 1) := hsum
      _ = (levels.card : ℝ) * (16 * s + 1) := hconst
      _ = (n + 1) * (16 * s + 1) := by rw [hlevelsR]
  · have hnNat : n + 1 ≤ 2 * n := by omega
    have hnReal : (n + 1 : ℝ) ≤ 2 * n := by exact_mod_cast hnNat
    have hsReal : 16 * s + 1 ≤ 17 * s := by linarith
    calc
      (n + 1) * (16 * s + 1) ≤ (2 * n) * (17 * s) := by
        exact mul_le_mul hnReal hsReal (by positivity) (by positivity)
      _ = 34 * n * s := by ring

/-- The actual starting slice on level zero has at most `17s` sites. -/
theorem tiltStripStartSlice_card_le (a s : ℝ) (hs : 1 ≤ s) :
    ((Finset.Icc
        (Int.ceil (a * (0 : ℝ) - 8 * s))
        (Int.floor (a * (0 : ℝ) + 8 * s))).image (fun i => (i, (0 : ℤ) - i))).card ≤
      17 * s := by
  have hslice := tiltStripLevelSlice_card_le a s 0 hs
  have hbound : 16 * s + 1 ≤ 17 * s := by linarith
  calc
    (((Finset.Icc
        (Int.ceil (a * (0 : ℝ) - 8 * s))
        (Int.floor (a * (0 : ℝ) + 8 * s))).image (fun i => (i, (0 : ℤ) - i))).card : ℝ)
        ≤ 16 * s + 1 := by
            simpa only [Int.cast_zero, mul_zero, zero_sub, zero_add] using hslice
    _ ≤ 17 * s := hbound

/-- The ordered product of the actual endpoint slices has at most `289s²` pairs.

All ordered pairs are counted; no coordinatewise-comparability condition is imposed. -/
theorem tiltStripEndpointPairs_card_le (a s : ℝ) (n : ℕ) (hs : 1 ≤ s) :
    (((Finset.Icc
        (Int.ceil (a * (0 : ℝ) - 8 * s))
        (Int.floor (a * (0 : ℝ) + 8 * s))).image (fun i => (i, (0 : ℤ) - i)) ×ˢ
      (Finset.Icc
        (Int.ceil (a * ((n : ℤ) : ℝ) - 8 * s))
        (Int.floor (a * ((n : ℤ) : ℝ) + 8 * s))).image (fun i => (i, (n : ℤ) - i))).card : ℝ)
      ≤ 289 * s ^ 2 := by
  classical
  let startSlice : Finset Lattice := (Finset.Icc
      (Int.ceil (a * (0 : ℝ) - 8 * s))
      (Int.floor (a * (0 : ℝ) + 8 * s))).image (fun i => (i, (0 : ℤ) - i))
  let endSlice : Finset Lattice := (Finset.Icc
      (Int.ceil (a * ((n : ℤ) : ℝ) - 8 * s))
      (Int.floor (a * ((n : ℤ) : ℝ) + 8 * s))).image (fun i => (i, (n : ℤ) - i))
  have hstart : (startSlice.card : ℝ) ≤ 16 * s + 1 := by
    simpa only [startSlice, Int.cast_zero, mul_zero, zero_sub, zero_add] using
      tiltStripLevelSlice_card_le a s 0 hs
  have hend : (endSlice.card : ℝ) ≤ 16 * s + 1 := by
    simpa only [endSlice] using tiltStripLevelSlice_card_le a s (n : ℤ) hs
  have hbound : 16 * s + 1 ≤ 17 * s := by linarith
  have hsmall : 0 ≤ 16 * s + 1 := by positivity
  have hlarge : 0 ≤ 17 * s := by positivity
  change ((startSlice ×ˢ endSlice).card : ℝ) ≤ 289 * s ^ 2
  calc
    ((startSlice ×ˢ endSlice).card : ℝ) =
        (startSlice.card : ℝ) * (endSlice.card : ℝ) := by
          rw [Finset.card_product, Nat.cast_mul]
    _ ≤ (16 * s + 1) * (16 * s + 1) :=
        mul_le_mul hstart hend (by exact_mod_cast Nat.zero_le endSlice.card) hsmall
    _ ≤ (17 * s) * (17 * s) := mul_le_mul hbound hbound hsmall hlarge
    _ = 289 * s ^ 2 := by ring

end LPPDifferentiability
