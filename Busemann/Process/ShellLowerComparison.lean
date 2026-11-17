/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Busemann.Frozen.Definitions.Additive
public import Busemann.Frozen.Definitions.FiniteEdgeStep
public import Busemann.Process.ShellComparisonBounds
public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Data.Finset.Prod
public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Tactic

/-! A finite lower shell comparison in JR1810.03580v3, Appendix B. -/

@[expose] public section

open LPPDifferentiability
open scoped BigOperators

namespace LPP.Busemann

private theorem grid_coordinate (n : ℕ) (δ : ℝ) (hδ : 0 < δ)
    (hnδ : 8 ≤ (n : ℝ) * δ) (b : ℤ) (hb : 0 ≤ b) (hbn : b ≤ (n : ℤ)) :
    ∃ k : ℕ, k ≤ ⌈8 / δ⌉₊ ∧
      b ≤ ⌊(n : ℝ) * (k : ℝ) * δ / 8⌋ ∧
      ⌊(n : ℝ) * (k : ℝ) * δ / 8⌋ <
        ⌊(n : ℝ) * ((k + 1 : ℕ) : ℝ) * δ / 8⌋ ∧
      ∀ y : ℤ, y < ⌊(n : ℝ) * ((k + 1 : ℕ) : ℝ) * δ / 8⌋ →
        (y : ℝ) < (b : ℝ) + (n : ℝ) * δ / 4 := by
  let t : ℝ := (n : ℝ) * δ / 8
  have ht1 : 1 ≤ t := by dsimp [t]; linarith only [hnδ]
  have ht : 0 < t := lt_of_lt_of_le zero_lt_one ht1
  have hbR : 0 ≤ (b : ℝ) := by exact_mod_cast hb
  have hbnR : (b : ℝ) ≤ (n : ℝ) := by exact_mod_cast hbn
  let k : ℕ := ⌈(b : ℝ) / t⌉₊
  have hratio : (b : ℝ) / t ≤ 8 / δ := by
    apply (div_le_iff₀ ht).2
    have heq : (8 / δ) * t = (n : ℝ) := by
      dsimp [t]
      field_simp
    rw [heq]
    exact hbnR
  have hk : k ≤ ⌈8 / δ⌉₊ := Nat.ceil_mono hratio
  have hbtk : (b : ℝ) ≤ t * (k : ℝ) := by
    have hh := (div_le_iff₀ ht).1 (Nat.le_ceil ((b : ℝ) / t))
    simpa only [mul_comm] using hh
  have hkupper : (k : ℝ) ≤ (b : ℝ) / t + 1 := by
    have hceil : (k : ℝ) ≤ (⌊(b : ℝ) / t⌋₊ : ℝ) + 1 := by
      exact_mod_cast Nat.ceil_le_floor_add_one ((b : ℝ) / t)
    have hfloor := Nat.floor_le (div_nonneg hbR ht.le)
    linarith only [hceil, hfloor]
  have htkupper : t * (k : ℝ) ≤ (b : ℝ) + t := by
    have hh := mul_le_mul_of_nonneg_left hkupper ht.le
    have heq : t * ((b : ℝ) / t + 1) = (b : ℝ) + t := by
      field_simp
    exact hh.trans_eq heq
  have hform (j : ℕ) : (n : ℝ) * (j : ℝ) * δ / 8 = t * (j : ℝ) := by
    dsimp [t]
    ring
  refine ⟨k, hk, ?_, ?_, ?_⟩
  · rw [hform]
    exact Int.le_floor.mpr hbtk
  · rw [hform, hform]
    have hstep : t * (k : ℝ) + 1 ≤ t * ((k + 1 : ℕ) : ℝ) := by
      push_cast
      linarith only [ht1]
    have hh := Int.floor_mono hstep
    rw [Int.floor_add_one] at hh
    omega
  · intro y hy
    have hyR : (y : ℝ) < (n : ℝ) * ((k + 1 : ℕ) : ℝ) * δ / 8 :=
      (Int.cast_lt.mpr hy).trans_le (Int.floor_le _)
    rw [hform] at hyR
    push_cast at hyR
    dsimp [t] at htkupper
    dsimp [t] at hyR
    nlinarith only [hyR, htkupper]

/-- Each native shell point is bounded below by an actual nearby rectangle average,
with two inclusive absolute-control windows and the samplewise drift error.
This is the finite lower comparison in JR1810.03580v3, Appendix B, proof of B.3. -/
theorem shell_point_lower_bound_by_rectangle
    (A : Lattice → Lattice → ℝ) (hA : is_additive A)
    (V : Fin 2 → Lattice → ℝ)
    (hUpper : ∀ (z : Lattice) (i : Fin 2),
      A z (z + finiteEdgeStep i) ≤ V i z)
    (m : Fin 2 → ℝ)
    (n : ℕ) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hnδ : 8 ≤ (n : ℝ) * δ) :
    let F : Lattice → Lattice → ℝ := fun x y =>
      A x y - (m 0 * ((y.1 - x.1 : ℤ) : ℝ) +
        m 1 * ((y.2 - x.2 : ℤ) : ℝ))
    let a : ℕ → ℤ := fun k => ⌊(n : ℝ) * (k : ℝ) * δ / 8⌋
    let K : Finset (ℕ × ℕ) :=
      (Finset.range (⌈8 / δ⌉₊ + 1)).product (Finset.range (⌈8 / δ⌉₊ + 1))
    let R : (ℕ × ℕ) → Finset Lattice := fun k =>
      (Finset.Ico (a k.1) (a (k.1 + 1))).product
        (Finset.Ico (a k.2) (a (k.2 + 1)))
    let C : Finset Lattice := insert 0
      (((Finset.Icc (-(2 * (n : ℤ))) (2 * (n : ℤ))).product
        (Finset.Icc (-(2 * (n : ℤ))) (2 * (n : ℤ)))).filter
          (fun z => z.1.natAbs + z.2.natAbs ≤ 2 * n))
    let W : Fin 2 → ℝ := fun i =>
      C.sup' (Finset.insert_nonempty _ _) (fun z =>
        (∑ t ∈ Finset.range (⌊(n : ℝ) * δ⌋₊ + 1),
          |V i (z + (t : ℤ) • finiteEdgeStep i)|) / (n : ℝ))
    ∀ x : Lattice, 0 ≤ x.1 → 0 ≤ x.2 → x.1 + x.2 = (n : ℤ) →
      ∃ k ∈ K, (R k).Nonempty ∧
        (∀ y ∈ R k, x.1 ≤ y.1 ∧ x.2 ≤ y.2 ∧
          (y.1 - x.1).toNat + (y.2 - x.2).toNat ≤ ⌊(n : ℝ) * δ⌋₊ ∧
          x ∈ C ∧ (y.1, x.2) ∈ C) ∧
        F 0 x / (n : ℝ) ≥
          (∑ y ∈ R k, F 0 y) / ((n : ℝ) * ((R k).card : ℝ)) -
            W 0 - W 1 - δ * max |m 0| |m 1| := by
  classical
  let F : Lattice → Lattice → ℝ := fun x y =>
    A x y - (m 0 * ((y.1 - x.1 : ℤ) : ℝ) + m 1 * ((y.2 - x.2 : ℤ) : ℝ))
  let a : ℕ → ℤ := fun k => ⌊(n : ℝ) * (k : ℝ) * δ / 8⌋
  let K : Finset (ℕ × ℕ) :=
    (Finset.range (⌈8 / δ⌉₊ + 1)).product (Finset.range (⌈8 / δ⌉₊ + 1))
  let R : (ℕ × ℕ) → Finset Lattice := fun k =>
    (Finset.Ico (a k.1) (a (k.1 + 1))).product (Finset.Ico (a k.2) (a (k.2 + 1)))
  let C : Finset Lattice := insert 0
    (((Finset.Icc (-(2 * (n : ℤ))) (2 * (n : ℤ))).product
      (Finset.Icc (-(2 * (n : ℤ))) (2 * (n : ℤ)))).filter
        (fun z => z.1.natAbs + z.2.natAbs ≤ 2 * n))
  let W : Fin 2 → ℝ := fun i => C.sup' (Finset.insert_nonempty _ _) (fun z =>
    (∑ t ∈ Finset.range (⌊(n : ℝ) * δ⌋₊ + 1),
      |V i (z + (t : ℤ) • finiteEdgeStep i)|) / (n : ℝ))
  change ∀ x : Lattice, 0 ≤ x.1 → 0 ≤ x.2 → x.1 + x.2 = (n : ℤ) → _
  have hn : 0 < (n : ℝ) := by
    by_contra hh
    have hnzero : n = 0 := by exact_mod_cast (le_antisymm (le_of_not_gt hh) (Nat.cast_nonneg n))
    subst n
    norm_num at hnδ
  have hnd : (n : ℝ) * δ ≤ (n : ℝ) := mul_le_of_le_one_right hn.le hδ1
  intro x hx1 hx2 hxsum
  have hx1n : x.1 ≤ (n : ℤ) := by omega
  have hx2n : x.2 ≤ (n : ℤ) := by omega
  obtain ⟨k1, hk1, hlow1, hwidth1, hupp1⟩ := grid_coordinate n δ hδ hnδ x.1 hx1 hx1n
  obtain ⟨k2, hk2, hlow2, hwidth2, hupp2⟩ := grid_coordinate n δ hδ hnδ x.2 hx2 hx2n
  let k : ℕ × ℕ := (k1, k2)
  have hk : k ∈ K := by
    dsimp only [K, k]
    exact Finset.mem_product.mpr ⟨Finset.mem_range.mpr (by omega), Finset.mem_range.mpr (by omega)⟩
  have hR : (R k).Nonempty := by
    refine ⟨(a k1, a k2), Finset.mem_product.mpr ?_⟩
    exact ⟨Finset.mem_Ico.mpr ⟨le_rfl, hwidth1⟩, Finset.mem_Ico.mpr ⟨le_rfl, hwidth2⟩⟩
  have hxnorm : x.1.natAbs + x.2.natAbs = n := by
    have hh : (x.1.natAbs : ℤ) + (x.2.natAbs : ℤ) = (n : ℤ) := by
      rw [Int.natCast_natAbs, Int.natCast_natAbs, abs_of_nonneg hx1, abs_of_nonneg hx2]
      exact hxsum
    exact_mod_cast hh
  have hxC : x ∈ C := (signed_ball_mem n x).2 (by omega)
  have hgeom (y : Lattice) (hy : y ∈ R k) :
      x.1 ≤ y.1 ∧ x.2 ≤ y.2 ∧
      (y.1 - x.1).toNat + (y.2 - x.2).toNat ≤ ⌊(n : ℝ) * δ⌋₊ ∧
      x ∈ C ∧ (y.1, x.2) ∈ C := by
    obtain ⟨hy1, hy2⟩ := Finset.mem_product.mp hy
    obtain ⟨hy1lo, hy1hi⟩ := Finset.mem_Ico.mp hy1
    obtain ⟨hy2lo, hy2hi⟩ := Finset.mem_Ico.mp hy2
    have hxy1 : x.1 ≤ y.1 := hlow1.trans hy1lo
    have hxy2 : x.2 ≤ y.2 := hlow2.trans hy2lo
    have hy1R := hupp1 y.1 hy1hi
    have hy2R := hupp2 y.2 hy2hi
    have hsumR : (x.1 : ℝ) + (x.2 : ℝ) = (n : ℝ) := by exact_mod_cast hxsum
    have hdx : ((y.1 - x.1).toNat : ℝ) = (y.1 : ℝ) - (x.1 : ℝ) := by
      exact_mod_cast Int.toNat_of_nonneg (sub_nonneg.mpr hxy1)
    have hdy : ((y.2 - x.2).toNat : ℝ) = (y.2 : ℝ) - (x.2 : ℝ) := by
      exact_mod_cast Int.toNat_of_nonneg (sub_nonneg.mpr hxy2)
    have hlen : (y.1 - x.1).toNat + (y.2 - x.2).toNat ≤ ⌊(n : ℝ) * δ⌋₊ := by
      apply (Nat.le_floor_iff (mul_nonneg hn.le hδ.le)).2
      push_cast
      rw [hdx, hdy]
      linarith only [hy1R, hy2R, hnδ]
    have helR : (y.1 : ℝ) + (x.2 : ℝ) ≤ 2 * (n : ℝ) := by
      linarith only [hy1R, hsumR, hnd, hn.le]
    have hel : y.1 + x.2 ≤ 2 * (n : ℤ) := by exact_mod_cast helR
    have helnorm : y.1.natAbs + x.2.natAbs ≤ 2 * n := by
      have hh : (y.1.natAbs : ℤ) + (x.2.natAbs : ℤ) ≤ 2 * (n : ℤ) := by
        rw [Int.natCast_natAbs, Int.natCast_natAbs, abs_of_nonneg (hx1.trans hxy1), abs_of_nonneg hx2]
        exact hel
      exact_mod_cast hh
    exact ⟨hxy1, hxy2, hlen, hxC, (signed_ball_mem n (y.1, x.2)).2 helnorm⟩
  refine ⟨k, hk, hR, hgeom, ?_⟩
  -- A grouped block is bounded by its inclusive absolute-control window.
  have hray (z : Lattice) (hz : z ∈ C) (i : Fin 2) (q : ℕ)
      (hq : q ≤ ⌊(n : ℝ) * δ⌋₊) :
      A z (z + (q : ℤ) • finiteEdgeStep i) ≤ (n : ℝ) * W i := by
    have hsum := additive_ray_upper A hA V hUpper z i q
    have hinc : (∑ t ∈ Finset.range q, |V i (z + (t : ℤ) • finiteEdgeStep i)|) ≤
        ∑ t ∈ Finset.range (⌊(n : ℝ) * δ⌋₊ + 1), |V i (z + (t : ℤ) • finiteEdgeStep i)| :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega)) (fun _ _ _ => abs_nonneg _)
    have hs : (∑ t ∈ Finset.range (⌊(n : ℝ) * δ⌋₊ + 1),
        |V i (z + (t : ℤ) • finiteEdgeStep i)|) / (n : ℝ) ≤ W i :=
      by
        dsimp only [W]
        exact Finset.le_sup' (fun u : Lattice =>
          (∑ t ∈ Finset.range (⌊(n : ℝ) * δ⌋₊ + 1),
            |V i (u + (t : ℤ) • finiteEdgeStep i)|) / (n : ℝ)) hz
    have hs' := (div_le_iff₀ hn).1 hs
    exact hsum.trans (hinc.trans (by nlinarith only [hs']))
  let M : ℝ := max |m 0| |m 1|
  have hM : 0 ≤ M := (abs_nonneg (m 0)).trans (le_max_left _ _)
  have hpoint (y : Lattice) (hy : y ∈ R k) :
      F 0 y ≤ F 0 x + (n : ℝ) * (W 0 + W 1 + δ * M) := by
    obtain ⟨hxy1, hxy2, hlen, hxmem, helmem⟩ := hgeom y hy
    let q1 := (y.1 - x.1).toNat
    let q2 := (y.2 - x.2).toNat
    have hq1 : (q1 : ℤ) = y.1 - x.1 := Int.toNat_of_nonneg (sub_nonneg.mpr hxy1)
    have hq2 : (q2 : ℤ) = y.2 - x.2 := Int.toNat_of_nonneg (sub_nonneg.mpr hxy2)
    have he1 : x + (q1 : ℤ) • finiteEdgeStep 0 = (y.1, x.2) := by
      apply Prod.ext <;> simp [finiteEdgeStep, hq1]
    have he2 : (y.1, x.2) + (q2 : ℤ) • finiteEdgeStep 1 = y := by
      apply Prod.ext <;> simp [finiteEdgeStep, hq2]
    have hb1 := hray x hxmem 0 q1 (by dsimp [q1]; omega)
    have hb2 := hray (y.1, x.2) helmem 1 q2 (by dsimp [q2]; omega)
    rw [he1] at hb1
    rw [he2] at hb2
    have hAxy : A x y ≤ (n : ℝ) * (W 0 + W 1) := by
      have hh := hA x (y.1, x.2) y
      linarith only [hh, hb1, hb2]
    have hd1 : 0 ≤ ((y.1 - x.1 : ℤ) : ℝ) := by exact_mod_cast (sub_nonneg.mpr hxy1)
    have hd2 : 0 ≤ ((y.2 - x.2 : ℤ) : ℝ) := by exact_mod_cast (sub_nonneg.mpr hxy2)
    have hlenR : ((y.1 - x.1 : ℤ) : ℝ) + ((y.2 - x.2 : ℤ) : ℝ) ≤ (n : ℝ) * δ := by
      have hh : ((q1 + q2 : ℕ) : ℝ) ≤ (n : ℝ) * δ :=
        (Nat.cast_le.mpr hlen).trans (Nat.floor_le (mul_nonneg hn.le hδ.le))
      have hq1R : (q1 : ℝ) = ((y.1 - x.1 : ℤ) : ℝ) := by exact_mod_cast hq1
      have hq2R : (q2 : ℝ) = ((y.2 - x.2 : ℤ) : ℝ) := by exact_mod_cast hq2
      simpa only [Nat.cast_add, hq1R, hq2R] using hh
    have hm1 : -(m 0) ≤ M := (neg_le_abs (m 0)).trans (le_max_left _ _)
    have hm2 : -(m 1) ≤ M := (neg_le_abs (m 1)).trans (le_max_right _ _)
    have hdri : -(m 0) * ((y.1 - x.1 : ℤ) : ℝ) +
        -(m 1) * ((y.2 - x.2 : ℤ) : ℝ) ≤ (n : ℝ) * δ * M := by
      calc
        _ ≤ M * ((y.1 - x.1 : ℤ) : ℝ) + M * ((y.2 - x.2 : ℤ) : ℝ) :=
          add_le_add (mul_le_mul_of_nonneg_right hm1 hd1) (mul_le_mul_of_nonneg_right hm2 hd2)
        _ = M * (((y.1 - x.1 : ℤ) : ℝ) + ((y.2 - x.2 : ℤ) : ℝ)) := by ring
        _ ≤ M * ((n : ℝ) * δ) := mul_le_mul_of_nonneg_left hlenR hM
        _ = (n : ℝ) * δ * M := by ring
    have hzero := hA 0 x y
    dsimp [F]
    push_cast
    push_cast at hdri
    linarith only [hzero, hAxy, hdri]
  -- Average the uniform pointwise comparison over the actual nonempty cell.
  have hsum := Finset.sum_le_sum (fun y hy => hpoint y hy)
  simp only [Finset.sum_const, nsmul_eq_mul] at hsum
  have hcard : 0 < ((R k).card : ℝ) := Nat.cast_pos.mpr hR.card_pos
  have havg : (∑ y ∈ R k, F 0 y) / ((n : ℝ) * ((R k).card : ℝ)) ≤
      F 0 x / (n : ℝ) + W 0 + W 1 + δ * M := by
    apply (div_le_iff₀ (mul_pos hn hcard)).2
    calc
      _ ≤ ((R k).card : ℝ) * (F 0 x + (n : ℝ) * (W 0 + W 1 + δ * M)) := hsum
      _ = (F 0 x / (n : ℝ) + W 0 + W 1 + δ * M) *
          ((n : ℝ) * ((R k).card : ℝ)) := by field_simp; ring
  dsimp [M] at havg
  linarith only [havg]

end LPP.Busemann
