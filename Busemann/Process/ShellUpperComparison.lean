/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Busemann.Process.ShellComparisonBounds
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Data.Fintype.Fin
import Mathlib.Tactic

/-! Finite masked upper shell comparison from JR1810.03580v3, Appendix B. -/

@[expose] public section

open LPPDifferentiability
open scoped BigOperators

namespace LPP.Busemann

private theorem below_coordinate (n : ℕ) (δ : ℝ) (hδ : 0 < δ)
    (hnδ : 8 ≤ (n : ℝ) * δ) (b : ℤ) (hb : 0 ≤ b) (hbn : b ≤ (n : ℤ)) :
    let a : ℕ → ℤ := fun k => ⌊(n : ℝ) * (k : ℝ) * δ / 8⌋
    let H : ℕ → Finset ℤ := fun k =>
      if (n : ℝ) * δ / 8 ≤ (b : ℝ) then Finset.Ico (a k) (a (k + 1)) else {0}
    ∃ k : ℕ, k ≤ ⌈8 / δ⌉₊ ∧ (H k).Nonempty ∧
      ∀ y ∈ H k, 0 ≤ y ∧ y ≤ b ∧ (b : ℝ) - (y : ℝ) < 3 * ((n : ℝ) * δ / 8) := by
  classical
  let t : ℝ := (n : ℝ) * δ / 8
  let a : ℕ → ℤ := fun k => ⌊(n : ℝ) * (k : ℝ) * δ / 8⌋
  let H : ℕ → Finset ℤ := fun k => if t ≤ (b : ℝ) then Finset.Ico (a k) (a (k + 1)) else {0}
  change ∃ k : ℕ, k ≤ ⌈8 / δ⌉₊ ∧ (H k).Nonempty ∧ _
  have ht1 : 1 ≤ t := by dsimp [t]; linarith only [hnδ]
  have ht : 0 < t := lt_of_lt_of_le zero_lt_one ht1
  have hbR : 0 ≤ (b : ℝ) := by exact_mod_cast hb
  have hbnR : (b : ℝ) ≤ (n : ℝ) := by exact_mod_cast hbn
  have hform (k : ℕ) : (n : ℝ) * (k : ℝ) * δ / 8 = t * (k : ℝ) := by dsimp [t]; ring
  by_cases hact : t ≤ (b : ℝ)
  · let q : ℕ := ⌊(b : ℝ) / t⌋₊
    have hq1 : 1 ≤ q := (Nat.one_le_floor_iff _).2 ((le_div_iff₀ ht).2 (by simpa using hact))
    let k : ℕ := q - 1
    have hkq : k + 1 = q := Nat.sub_add_cancel hq1
    have hratio : (b : ℝ) / t ≤ 8 / δ := by
      apply (div_le_iff₀ ht).2
      have heq : (8 / δ) * t = (n : ℝ) := by dsimp [t]; field_simp
      rw [heq]
      exact hbnR
    have hqbound : q ≤ ⌈8 / δ⌉₊ := (Nat.floor_mono hratio).trans (Nat.floor_le_ceil _)
    have hkbound : k ≤ ⌈8 / δ⌉₊ := (Nat.sub_le q 1).trans hqbound
    have hqR : (q : ℝ) ≤ (b : ℝ) / t := Nat.floor_le (div_nonneg hbR ht.le)
    have hprod : t * (q : ℝ) ≤ (b : ℝ) := by
      have hh := mul_le_mul_of_nonneg_left hqR ht.le
      have heq : t * ((b : ℝ) / t) = (b : ℝ) := by field_simp
      exact hh.trans_eq heq
    have hlow : 0 ≤ a k := by
      dsimp [a]
      have hvalue : (0 : ℝ) ≤ (n : ℝ) * (k : ℝ) * δ / 8 := by positivity
      have hcastValue : ((0 : ℤ) : ℝ) ≤ (n : ℝ) * (k : ℝ) * δ / 8 := by
        simpa only [Int.cast_zero] using hvalue
      exact Int.le_floor.mpr hcastValue
    have hwidth : a k < a (k + 1) := by
      dsimp only [a]
      rw [hform, hform]
      have hstep : t * (k : ℝ) + 1 ≤ t * ((k + 1 : ℕ) : ℝ) := by
        push_cast
        linarith only [ht1]
      have hh := Int.floor_mono hstep
      rw [Int.floor_add_one] at hh
      omega
    have hupper : a (k + 1) ≤ b := by
      have hh : (a (k + 1) : ℝ) ≤ (b : ℝ) := by
        calc
          (a (k + 1) : ℝ) ≤ (n : ℝ) * ((k + 1 : ℕ) : ℝ) * δ / 8 := Int.floor_le _
          _ = t * (q : ℝ) := by rw [hform, hkq]
          _ ≤ (b : ℝ) := hprod
      exact_mod_cast hh
    refine ⟨k, hkbound, ?_, ?_⟩
    · exact ⟨a k, by simpa only [H, ite_eq_left hact, Finset.mem_Ico] using And.intro le_rfl hwidth⟩
    · intro y hy
      change y ∈ H k at hy
      have hyI : y ∈ Finset.Ico (a k) (a (k + 1)) := by simpa only [H, ite_eq_left hact] using hy
      obtain ⟨hylo, hyhi⟩ := Finset.mem_Ico.mp hyI
      have hy0 : 0 ≤ y := hlow.trans hylo
      have hyb : y ≤ b := (le_of_lt hyhi).trans hupper
      have hbelow : (b : ℝ) < ((q : ℝ) + 1) * t :=
        (div_lt_iff₀ ht).1 (Nat.lt_floor_add_one ((b : ℝ) / t))
      rw [← hkq] at hbelow
      push_cast at hbelow
      have hfloor : t * (k : ℝ) < (a k : ℝ) + 1 := by
        calc
          _ = (n : ℝ) * (k : ℝ) * δ / 8 := (hform k).symm
          _ < (a k : ℝ) + 1 := Int.lt_floor_add_one _
      have hyR : (a k : ℝ) ≤ (y : ℝ) := by exact_mod_cast hylo
      refine ⟨hy0, hyb, ?_⟩
      change (b : ℝ) - (y : ℝ) < 3 * t
      nlinarith only [hbelow, hfloor, hyR, ht1]
  · refine ⟨0, Nat.zero_le _, ?_, ?_⟩
    · simpa only [H, ite_eq_right hact] using (Finset.singleton_nonempty (0 : ℤ))
    · intro y hy
      change y ∈ H 0 at hy
      have hy0 : y = 0 := Finset.mem_singleton.mp (by simpa only [H, ite_eq_right hact] using hy)
      subst y
      refine ⟨le_rfl, hb, ?_⟩
      have hbt : (b : ℝ) < t := lt_of_not_ge hact
      have hh : (b : ℝ) < 3 * t := by linarith only [hbt, ht]
      simpa only [Int.cast_zero, sub_zero, t] using hh

/-- Every native shell point has an upper comparison with an actual nonempty masked
lower cell, including one-dimensional cells near the axes. This is the finite upper
comparison in JR1810.03580v3, Appendix B, proof of B.3. -/
theorem shell_point_upper_bound_by_masked_rectangle
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
    let J : Finset (Finset (Fin 2)) := (Finset.univ : Finset (Fin 2)).powerset.erase ∅
    let K : Finset (ℕ × ℕ) :=
      (Finset.range (⌈8 / δ⌉₊ + 1)).product (Finset.range (⌈8 / δ⌉₊ + 1))
    let G : Finset (Finset (Fin 2) × (ℕ × ℕ)) := J.product K
    let R : (Finset (Fin 2) × (ℕ × ℕ)) → Finset Lattice := fun p =>
      (if (0 : Fin 2) ∈ p.1 then Finset.Ico (a p.2.1) (a (p.2.1 + 1)) else {0}).product
        (if (1 : Fin 2) ∈ p.1 then Finset.Ico (a p.2.2) (a (p.2.2 + 1)) else {0})
    let coord : Fin 2 → Lattice → ℤ := fun i z => if i = 0 then z.1 else z.2
    let C : Finset Lattice := insert 0
      (((Finset.Icc (-(2 * (n : ℤ))) (2 * (n : ℤ))).product
        (Finset.Icc (-(2 * (n : ℤ))) (2 * (n : ℤ)))).filter
          (fun z => z.1.natAbs + z.2.natAbs ≤ 2 * n))
    let W : Fin 2 → ℝ := fun i =>
      C.sup' (Finset.insert_nonempty _ _) (fun z =>
        (∑ t ∈ Finset.range (⌊(n : ℝ) * δ⌋₊ + 1),
          |V i (z + (t : ℤ) • finiteEdgeStep i)|) / (n : ℝ))
    ∀ x : Lattice, 0 ≤ x.1 → 0 ≤ x.2 → x.1 + x.2 = (n : ℤ) →
      ∃ p ∈ G, p.1.Nonempty ∧ (p.1.card = 1 ∨ p.1.card = 2) ∧
        p.1 = (Finset.univ : Finset (Fin 2)).filter
          (fun i => (n : ℝ) * δ / 8 ≤ (coord i x : ℝ)) ∧
        (R p).Nonempty ∧
        (∀ y ∈ R p, 0 ≤ y.1 ∧ 0 ≤ y.2 ∧ y.1 ≤ x.1 ∧ y.2 ≤ x.2 ∧
          (x.1 - y.1).toNat + (x.2 - y.2).toNat ≤ ⌊(n : ℝ) * δ⌋₊ ∧
          y ∈ C ∧ (x.1, y.2) ∈ C) ∧
        F 0 x / (n : ℝ) ≤
          (∑ y ∈ R p, F 0 y) / ((n : ℝ) * ((R p).card : ℝ)) +
            W 0 + W 1 + δ * max |m 0| |m 1| := by
  classical
  let F : Lattice → Lattice → ℝ := fun x y =>
    A x y - (m 0 * ((y.1 - x.1 : ℤ) : ℝ) +
      m 1 * ((y.2 - x.2 : ℤ) : ℝ))
  let a : ℕ → ℤ := fun k => ⌊(n : ℝ) * (k : ℝ) * δ / 8⌋
  let J : Finset (Finset (Fin 2)) := (Finset.univ : Finset (Fin 2)).powerset.erase ∅
  let K : Finset (ℕ × ℕ) :=
    (Finset.range (⌈8 / δ⌉₊ + 1)).product (Finset.range (⌈8 / δ⌉₊ + 1))
  let G : Finset (Finset (Fin 2) × (ℕ × ℕ)) := J.product K
  let R : (Finset (Fin 2) × (ℕ × ℕ)) → Finset Lattice := fun p =>
    (if (0 : Fin 2) ∈ p.1 then Finset.Ico (a p.2.1) (a (p.2.1 + 1)) else {0}).product
      (if (1 : Fin 2) ∈ p.1 then Finset.Ico (a p.2.2) (a (p.2.2 + 1)) else {0})
  let coord : Fin 2 → Lattice → ℤ := fun i z => if i = 0 then z.1 else z.2
  let C : Finset Lattice := insert 0
    (((Finset.Icc (-(2 * (n : ℤ))) (2 * (n : ℤ))).product
      (Finset.Icc (-(2 * (n : ℤ))) (2 * (n : ℤ)))).filter
        (fun z => z.1.natAbs + z.2.natAbs ≤ 2 * n))
  let W : Fin 2 → ℝ := fun i =>
    C.sup' (Finset.insert_nonempty _ _) (fun z =>
      (∑ t ∈ Finset.range (⌊(n : ℝ) * δ⌋₊ + 1),
        |V i (z + (t : ℤ) • finiteEdgeStep i)|) / (n : ℝ))
  change ∀ x : Lattice, 0 ≤ x.1 → 0 ≤ x.2 → x.1 + x.2 = (n : ℤ) → _
  have hn : 0 < (n : ℝ) := by
    by_contra hh
    have hnzero : n = 0 := by exact_mod_cast (le_antisymm (le_of_not_gt hh) (Nat.cast_nonneg n))
    subst n
    norm_num at hnδ
  have hnd : (n : ℝ) * δ ≤ (n : ℝ) := mul_le_of_le_one_right hn.le hδ1
  let t : ℝ := (n : ℝ) * δ / 8
  intro x hx1 hx2 hxsum
  have hx1n : x.1 ≤ (n : ℤ) := by omega
  have hx2n : x.2 ≤ (n : ℤ) := by omega
  obtain ⟨k0, hk0, hH0, hY0⟩ := below_coordinate n δ hδ hnδ x.1 hx1 hx1n
  obtain ⟨k1, hk1, hH1, hY1⟩ := below_coordinate n δ hδ hnδ x.2 hx2 hx2n
  let mask : Finset (Fin 2) := Finset.univ.filter (fun i => t ≤ (coord i x : ℝ))
  have hmem0 : (0 : Fin 2) ∈ mask ↔ t ≤ (x.1 : ℝ) := by simp [mask, coord]
  have hmem1 : (1 : Fin 2) ∈ mask ↔ t ≤ (x.2 : ℝ) := by simp [mask, coord]
  have hmask : mask.Nonempty := by
    by_contra hh
    have hnot0 : ¬t ≤ (x.1 : ℝ) := fun h => hh ⟨0, hmem0.mpr h⟩
    have hnot1 : ¬t ≤ (x.2 : ℝ) := fun h => hh ⟨1, hmem1.mpr h⟩
    have hsumR : (x.1 : ℝ) + (x.2 : ℝ) = (n : ℝ) := by exact_mod_cast hxsum
    dsimp [t] at hnot0 hnot1
    linarith only [lt_of_not_ge hnot0, lt_of_not_ge hnot1, hsumR, hnd, hn]
  have hmaskcard : mask.card = 1 ∨ mask.card = 2 := by
    have hlo := hmask.card_pos
    have hhi : mask.card ≤ 2 := by simpa using (Finset.card_le_card (Finset.subset_univ mask))
    omega
  have hmaskJ : mask ∈ J := by
    exact Finset.mem_erase.mpr ⟨hmask.ne_empty, Finset.mem_powerset.mpr (Finset.subset_univ mask)⟩
  let p : Finset (Fin 2) × (ℕ × ℕ) := (mask, (k0, k1))
  have hp : p ∈ G := by
    dsimp only [G, p]
    apply Finset.mem_product.mpr
    refine ⟨hmaskJ, ?_⟩
    dsimp only [K]
    exact Finset.mem_product.mpr ⟨Finset.mem_range.mpr (by omega), Finset.mem_range.mpr (by omega)⟩
  have hR0 : (if (0 : Fin 2) ∈ mask then Finset.Ico (a k0) (a (k0 + 1)) else {0}).Nonempty := by
    simpa only [hmem0, a, t] using hH0
  have hR1 : (if (1 : Fin 2) ∈ mask then Finset.Ico (a k1) (a (k1 + 1)) else {0}).Nonempty := by
    simpa only [hmem1, a, t] using hH1
  have hR : (R p).Nonempty := by
    obtain ⟨v, hv⟩ := hR0
    obtain ⟨w, hw⟩ := hR1
    exact ⟨(v, w), Finset.mem_product.mpr ⟨hv, hw⟩⟩
  -- Both block starts lie in the actual signed window, even when they coincide.
  have hstart (z : Lattice) (hz1 : 0 ≤ z.1) (hz2 : 0 ≤ z.2)
      (hzx1 : z.1 ≤ x.1) (hzx2 : z.2 ≤ x.2) : z ∈ C := by
    apply (signed_ball_mem n z).2
    have hh : (z.1.natAbs : ℤ) + (z.2.natAbs : ℤ) ≤ 2 * (n : ℤ) := by
      rw [Int.natCast_natAbs, Int.natCast_natAbs, abs_of_nonneg hz1, abs_of_nonneg hz2]
      omega
    exact_mod_cast hh
  have hgeom (y : Lattice) (hy : y ∈ R p) :
      0 ≤ y.1 ∧ 0 ≤ y.2 ∧ y.1 ≤ x.1 ∧ y.2 ≤ x.2 ∧
      (x.1 - y.1).toNat + (x.2 - y.2).toNat ≤ ⌊(n : ℝ) * δ⌋₊ ∧
      y ∈ C ∧ (x.1, y.2) ∈ C := by
    obtain ⟨hy0, hy1⟩ := Finset.mem_product.mp hy
    dsimp only [p] at hy0 hy1
    have hy0' : y.1 ∈ (if (n : ℝ) * δ / 8 ≤ (x.1 : ℝ) then
        Finset.Ico (a k0) (a (k0 + 1)) else {0}) := by
      simpa only [hmem0, t] using hy0
    have hy1' : y.2 ∈ (if (n : ℝ) * δ / 8 ≤ (x.2 : ℝ) then
        Finset.Ico (a k1) (a (k1 + 1)) else {0}) := by
      simpa only [hmem1, t] using hy1
    obtain ⟨hy0pos, hy0le, hgap0⟩ := hY0 y.1 hy0'
    obtain ⟨hy1pos, hy1le, hgap1⟩ := hY1 y.2 hy1'
    have hdx : ((x.1 - y.1).toNat : ℝ) = (x.1 : ℝ) - (y.1 : ℝ) := by
      exact_mod_cast Int.toNat_of_nonneg (sub_nonneg.mpr hy0le)
    have hdy : ((x.2 - y.2).toNat : ℝ) = (x.2 : ℝ) - (y.2 : ℝ) := by
      exact_mod_cast Int.toNat_of_nonneg (sub_nonneg.mpr hy1le)
    have hlen : (x.1 - y.1).toNat + (x.2 - y.2).toNat ≤ ⌊(n : ℝ) * δ⌋₊ := by
      apply (Nat.le_floor_iff (mul_nonneg hn.le hδ.le)).2
      push_cast
      rw [hdx, hdy]
      linarith only [hgap0, hgap1, hnδ]
    exact ⟨hy0pos, hy1pos, hy0le, hy1le, hlen,
      hstart y hy0pos hy1pos hy0le hy1le, hstart (x.1, y.2) hx1 hy1pos le_rfl hy1le⟩
  refine ⟨p, hp, hmask, hmaskcard, rfl, hR, hgeom, ?_⟩
  have hray (z : Lattice) (hz : z ∈ C) (i : Fin 2) (q : ℕ)
      (hq : q ≤ ⌊(n : ℝ) * δ⌋₊) :
      A z (z + (q : ℤ) • finiteEdgeStep i) ≤ (n : ℝ) * W i := by
    have hsum := additive_ray_upper A hA V hUpper z i q
    have hinc : (∑ r ∈ Finset.range q, |V i (z + (r : ℤ) • finiteEdgeStep i)|) ≤
        ∑ r ∈ Finset.range (⌊(n : ℝ) * δ⌋₊ + 1), |V i (z + (r : ℤ) • finiteEdgeStep i)| :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega)) (fun _ _ _ => abs_nonneg _)
    have hs : (∑ r ∈ Finset.range (⌊(n : ℝ) * δ⌋₊ + 1),
        |V i (z + (r : ℤ) • finiteEdgeStep i)|) / (n : ℝ) ≤ W i := by
      dsimp only [W]
      exact Finset.le_sup' (fun u : Lattice =>
        (∑ r ∈ Finset.range (⌊(n : ℝ) * δ⌋₊ + 1),
          |V i (u + (r : ℤ) • finiteEdgeStep i)|) / (n : ℝ)) hz
    have hs' := (div_le_iff₀ hn).1 hs
    exact hsum.trans (hinc.trans (by nlinarith only [hs']))
  let M : ℝ := max |m 0| |m 1|
  have hM : 0 ≤ M := (abs_nonneg (m 0)).trans (le_max_left _ _)
  have hpoint (y : Lattice) (hy : y ∈ R p) :
      F 0 x ≤ F 0 y + (n : ℝ) * (W 0 + W 1 + δ * M) := by
    obtain ⟨hy1pos, hy2pos, hy1le, hy2le, hlen, hymem, helmem⟩ := hgeom y hy
    let q1 := (x.1 - y.1).toNat
    let q2 := (x.2 - y.2).toNat
    have hq1 : (q1 : ℤ) = x.1 - y.1 := Int.toNat_of_nonneg (sub_nonneg.mpr hy1le)
    have hq2 : (q2 : ℤ) = x.2 - y.2 := Int.toNat_of_nonneg (sub_nonneg.mpr hy2le)
    have he1 : y + (q1 : ℤ) • finiteEdgeStep 0 = (x.1, y.2) := by
      apply Prod.ext <;> simp [finiteEdgeStep, hq1]
    have he2 : (x.1, y.2) + (q2 : ℤ) • finiteEdgeStep 1 = x := by
      apply Prod.ext <;> simp [finiteEdgeStep, hq2]
    have hb1 := hray y hymem 0 q1 (by dsimp [q1]; omega)
    have hb2 := hray (x.1, y.2) helmem 1 q2 (by dsimp [q2]; omega)
    rw [he1] at hb1
    rw [he2] at hb2
    have hAyx : A y x ≤ (n : ℝ) * (W 0 + W 1) := by
      have hh := hA y (x.1, y.2) x
      linarith only [hh, hb1, hb2]
    have hd1 : 0 ≤ ((x.1 - y.1 : ℤ) : ℝ) := by exact_mod_cast (sub_nonneg.mpr hy1le)
    have hd2 : 0 ≤ ((x.2 - y.2 : ℤ) : ℝ) := by exact_mod_cast (sub_nonneg.mpr hy2le)
    have hlenR : ((x.1 - y.1 : ℤ) : ℝ) + ((x.2 - y.2 : ℤ) : ℝ) ≤ (n : ℝ) * δ := by
      have hh : ((q1 + q2 : ℕ) : ℝ) ≤ (n : ℝ) * δ :=
        (Nat.cast_le.mpr hlen).trans (Nat.floor_le (mul_nonneg hn.le hδ.le))
      have hq1R : (q1 : ℝ) = ((x.1 - y.1 : ℤ) : ℝ) := by exact_mod_cast hq1
      have hq2R : (q2 : ℝ) = ((x.2 - y.2 : ℤ) : ℝ) := by exact_mod_cast hq2
      simpa only [Nat.cast_add, hq1R, hq2R] using hh
    have hm1 : -(m 0) ≤ M := (neg_le_abs (m 0)).trans (le_max_left _ _)
    have hm2 : -(m 1) ≤ M := (neg_le_abs (m 1)).trans (le_max_right _ _)
    have hdrift : -(m 0) * ((x.1 - y.1 : ℤ) : ℝ) +
        -(m 1) * ((x.2 - y.2 : ℤ) : ℝ) ≤ (n : ℝ) * δ * M := by
      calc
        _ ≤ M * ((x.1 - y.1 : ℤ) : ℝ) + M * ((x.2 - y.2 : ℤ) : ℝ) :=
          add_le_add (mul_le_mul_of_nonneg_right hm1 hd1) (mul_le_mul_of_nonneg_right hm2 hd2)
        _ = M * (((x.1 - y.1 : ℤ) : ℝ) + ((x.2 - y.2 : ℤ) : ℝ)) := by ring
        _ ≤ M * ((n : ℝ) * δ) := mul_le_mul_of_nonneg_left hlenR hM
        _ = (n : ℝ) * δ * M := by ring
    have hzero := hA 0 y x
    dsimp [F]
    push_cast
    push_cast at hdrift
    linarith only [hzero, hAyx, hdrift]
  have hsum := Finset.sum_le_sum (fun y hy => hpoint y hy)
  simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul] at hsum
  have hcard : 0 < ((R p).card : ℝ) := Nat.cast_pos.mpr hR.card_pos
  change F 0 x / (n : ℝ) ≤ (∑ y ∈ R p, F 0 y) / ((n : ℝ) * ((R p).card : ℝ)) +
    W 0 + W 1 + δ * M
  rw [show (∑ y ∈ R p, F 0 y) / ((n : ℝ) * ((R p).card : ℝ)) + W 0 + W 1 + δ * M =
      ((∑ y ∈ R p, F 0 y) + ((R p).card : ℝ) * ((n : ℝ) * (W 0 + W 1 + δ * M))) /
        ((n : ℝ) * ((R p).card : ℝ)) by field_simp; ring]
  apply (le_div_iff₀ (mul_pos hn hcard)).2
  have heq : F 0 x / (n : ℝ) * ((n : ℝ) * ((R p).card : ℝ)) =
      ((R p).card : ℝ) * F 0 x := by field_simp
  rw [heq]
  exact hsum

end LPP.Busemann
