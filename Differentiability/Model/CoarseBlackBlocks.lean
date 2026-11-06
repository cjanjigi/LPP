/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Differentiability.Model.OrientedPercolation
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Finset.Card
import Mathlib.Tactic

/-!
# A coarse path meets few black blocks

An up-right path from the origin to `(k, ℓ)` that is open at a large fraction of its
vertices can be coarse-grained into an up-right path of blocks. The coarse path meets
few black blocks. A black block that the path crosses with a large rightward move owns a
closed vertex, and a black block that the path crosses with a small rightward move
uses up a large share of the path's upward moves.

It is used in the argument for flat segments.
-/

public section

namespace LPPDifferentiability

open Finset

/-- Up-right steps: the coordinates grow, and the coordinate sum grows by the number of
steps. -/
private theorem walk_segment {n : ℕ} {X : ℕ → Lattice}
    (hstep : ∀ i, i < n → X (i + 1) = X i + (1, 0) ∨ X (i + 1) = X i + (0, 1))
    {a b : ℕ} (hab : a ≤ b) (hbn : b ≤ n) :
    (X a).1 ≤ (X b).1 ∧ (X a).2 ≤ (X b).2 ∧
      ((X b).1 - (X a).1) + ((X b).2 - (X a).2) = (b : ℤ) - a := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hab
  clear hab
  induction d with
  | zero => simp
  | succ d ih =>
    obtain ⟨h1, h2, h3⟩ := ih (by omega)
    have e : a + (d + 1) = (a + d) + 1 := by omega
    rw [e]
    rcases hstep (a + d) (by omega) with h | h <;> rw [h] <;>
      simp only [Prod.fst_add, Prod.snd_add] <;> push_cast <;> omega

/-- A walk from the origin has nonnegative coordinates, and its coordinate sum is the
time. -/
private theorem walk_basic {n : ℕ} {X : ℕ → Lattice} (hX0 : X 0 = 0)
    (hstep : ∀ i, i < n → X (i + 1) = X i + (1, 0) ∨ X (i + 1) = X i + (0, 1))
    {i : ℕ} (hi : i ≤ n) :
    0 ≤ (X i).1 ∧ 0 ≤ (X i).2 ∧ (X i).1 + (X i).2 = (i : ℤ) := by
  obtain ⟨h1, h2, h3⟩ := walk_segment hstep (Nat.zero_le i) hi
  simp only [hX0, Prod.fst_zero, Prod.snd_zero, Nat.cast_zero] at h1 h2 h3
  omega

/-- A stretch of a walk whose vertices after the start are open is an open path. -/
private theorem openReach_of_segment {n : ℕ} {X : ℕ → Lattice} {O : Set Lattice}
    (hstep : ∀ i, i < n → X (i + 1) = X i + (1, 0) ∨ X (i + 1) = X i + (0, 1))
    {a b : ℕ} (hab : a ≤ b) (hbn : b ≤ n)
    (hO : ∀ i, a < i → i ≤ b → X i ∈ O) : OpenReach O (X a) (X b) := by
  obtain ⟨h1, h2, h3⟩ := walk_segment hstep hab hbn
  obtain ⟨d, hd1, hd2⟩ :
      ∃ d : ℕ × ℕ, d.1 + d.2 = b - a ∧ X b = X a + ((d.1 : ℤ), (d.2 : ℤ)) := by
    refine ⟨(((X b).1 - (X a).1).toNat, ((X b).2 - (X a).2).toNat), ?_, ?_⟩
    · show ((X b).1 - (X a).1).toNat + ((X b).2 - (X a).2).toNat = b - a
      omega
    · refine Prod.ext ?_ ?_ <;> simp only [Prod.fst_add, Prod.snd_add] <;> omega
  have hpath : ∃ p : Path (X a) d,
      ∀ i : Fin (d.1 + d.2), p.vertex i.succ = X (a + i.val + 1) := by
    refine ⟨{ vertex := fun i => X (a + i.val), start := by simp, finish := ?_, step := ?_ },
      fun i => rfl⟩
    · show X (a + (Fin.last (d.1 + d.2)).val) = X a + ((d.1 : ℤ), (d.2 : ℤ))
      rw [Fin.val_last, show a + (d.1 + d.2) = b by omega]
      exact hd2
    · intro i
      have hi := i.isLt
      have hs := hstep (a + i.val) (by omega)
      have e : a + (i.val + 1) = a + i.val + 1 := by omega
      show X (a + (i.val + 1)) = X (a + i.val) + (1, 0) ∨
        X (a + (i.val + 1)) = X (a + i.val) + (0, 1)
      rw [e]
      exact hs
  obtain ⟨p, hp⟩ := hpath
  unfold OpenReach
  refine ⟨d, hd2.symm, p, fun i => ?_⟩
  have hi := i.isLt
  rw [hp i]
  exact hO _ (by omega) (by omega)

/-- Integer division by a positive number: the quotient and the remainder window. -/
private theorem floor_facts {N : ℕ} (hN : 0 < N) (x : ℤ) :
    (N : ℤ) * (x / N) ≤ x ∧ x < (N : ℤ) * (x / N) + N := by
  have h1 := Int.mul_ediv_add_emod x N
  have h2 := Int.emod_nonneg x (show (N : ℤ) ≠ 0 by omega)
  have h3 := Int.emod_lt_of_pos x (show (0 : ℤ) < N by omega)
  constructor <;> linarith

/-- A black block crossed by a walk with a large rightward move owns a closed vertex. -/
private theorem closed_in_good_block {n : ℕ} {X : ℕ → Lattice} {O : Set Lattice} {N : ℕ}
    {c₁ : ℝ}
    (hstep : ∀ i, i < n → X (i + 1) = X i + (1, 0) ∨ X (i + 1) = X i + (0, 1))
    {z : Lattice} (hz : IsBlackBlock O N c₁ z) {a : ℕ} (han : a + N ≤ n)
    (h1 : (N : ℤ) * z.1 ≤ (X a).1) (h2 : (N : ℤ) * z.2 ≤ (X a).2)
    (h3 : ((X a).1 - (N : ℤ) * z.1) + ((X a).2 - (N : ℤ) * z.2) = N)
    (hgood : c₁ * N ≤ (((X (a + N)).1 - (X a).1 : ℤ) : ℝ)) :
    ∃ i, a ≤ i ∧ i < a + N ∧ X (i + 1) ∉ O := by
  by_contra hcon
  push Not at hcon
  have hseg : OpenReach O (X a) (X (a + N)) :=
    openReach_of_segment hstep (Nat.le_add_right a N) han (fun i hi1 hi2 => by
      obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
      exact hcon j (by omega) (by omega))
  obtain ⟨s1, s2, s3⟩ := walk_segment hstep (Nat.le_add_right a N) han
  exact hz (X a) (X (a + N)) (Prod.le_def.2 ⟨h1, h2⟩) (Prod.le_def.2 ⟨s1, s2⟩) h3
    (by omega) hgood hseg

/-- The vertices of a path as a walk indexed by the natural numbers. -/
private theorem exists_walk {k ℓ : ℕ} (p : Path 0 (k, ℓ)) :
    ∃ X : ℕ → Lattice, X 0 = 0 ∧ X (k + ℓ) = ((k : ℤ), (ℓ : ℤ)) ∧
      (∀ i, i < k + ℓ → X (i + 1) = X i + (1, 0) ∨ X (i + 1) = X i + (0, 1)) ∧
      ∀ i : Fin (k + ℓ), p.vertex i.succ = X (i.val + 1) := by
  obtain ⟨X, hXdef⟩ : ∃ X : ℕ → Lattice,
      ∀ i, X i = p.vertex ⟨min i (k + ℓ), by show _ < k + ℓ + 1; omega⟩ :=
    ⟨fun i => p.vertex ⟨min i (k + ℓ), by show _ < k + ℓ + 1; omega⟩, fun _ => rfl⟩
  have hX : ∀ i (h : i < k + ℓ + 1), X i = p.vertex ⟨i, h⟩ := by
    intro i h
    rw [hXdef]
    exact congrArg p.vertex (Fin.ext (by show min i (k + ℓ) = i; omega))
  refine ⟨X, ?_, ?_, ?_, ?_⟩
  · rw [hX 0 (by omega)]
    exact (congrArg p.vertex (Fin.ext (by simp))).trans p.start
  · rw [hX (k + ℓ) (by omega)]
    exact (congrArg p.vertex (Fin.ext (by simp))).trans (p.finish.trans (zero_add _))
  · intro i hi
    rw [hX (i + 1) (by omega), hX i (by omega)]
    exact p.step ⟨i, hi⟩
  · intro i
    exact (congrArg p.vertex (Fin.ext (by simp))).trans (hX (i.val + 1) (by omega)).symm

open Classical in
private theorem coarse_of_walk (O : Set Lattice) (N : ℕ) (hN : 0 < N)
    (c₁ s δ : ℝ) (hc₁ : c₁ < 1) (k ℓ : ℕ) (hks : s * (k + ℓ) ≤ k) (hlen : 3 * N ≤ k + ℓ)
    (X : ℕ → Lattice) (hX0 : X 0 = 0) (hXn : X (k + ℓ) = ((k : ℤ), (ℓ : ℤ)))
    (hstep : ∀ i, i < k + ℓ → X (i + 1) = X i + (1, 0) ∨ X (i + 1) = X i + (0, 1))
    (hp : (1 - δ) * (k + ℓ) ≤
      ∑ i ∈ range (k + ℓ), (if X (i + 1) ∈ O then (1 : ℝ) else 0)) :
    ∃ q : Fin ((k + ℓ) / N - 2 + 1) → ℕ × ℕ, q 0 = (0, 0) ∧
      (∀ i : Fin ((k + ℓ) / N - 2), q i.succ = q i.castSucc + (1, 0) ∨
        q i.succ = q i.castSucc + (0, 1)) ∧
      ((Finset.univ.filter fun j =>
          IsBlackBlock O N c₁ (((q j).1 : ℤ), ((q j).2 : ℤ))).card : ℝ) ≤
        δ * (k + ℓ) + (1 - s) * (k + ℓ) / ((1 - c₁) * N) := by
  generalize hm : (k + ℓ) / N - 2 = m
  have hmN : (m + 2) * N ≤ k + ℓ := by
    have h3 : 3 ≤ (k + ℓ) / N := (Nat.le_div_iff_mul_le hN).2 hlen
    have h4 : m + 2 = (k + ℓ) / N := by omega
    rw [h4]
    exact Nat.div_mul_le_self _ _
  obtain ⟨T, hT⟩ : ∃ T : ℕ → ℕ, ∀ j, T j = (j + 1) * N :=
    ⟨fun j => (j + 1) * N, fun _ => rfl⟩
  have hT1 : ∀ j, T (j + 1) = T j + N := fun j => by rw [hT, hT]; try ring
  have hTN : ∀ j, N ≤ T j := fun j => by
    have h : (j + 1) * N = j * N + N := by ring
    rw [hT]; omega
  have hTmono : ∀ i j, i ≤ j → T i ≤ T j := fun i j h => by
    rw [hT, hT]; exact Nat.mul_le_mul_right N (by omega)
  have hTm : T (m + 1) ≤ k + ℓ := by rw [hT]; exact hmN
  have hjT : ∀ j, j ≤ m → T j ≤ k + ℓ := fun j hj =>
    le_trans (hTmono j (m + 1) (by omega)) hTm
  have hb : ∀ i, i ≤ k + ℓ → 0 ≤ (X i).1 ∧ 0 ≤ (X i).2 ∧ (X i).1 + (X i).2 = (i : ℤ) :=
    fun i hi => walk_basic hX0 hstep hi
  obtain ⟨A, hA⟩ : ∃ A : ℕ → ℤ, ∀ j, A j = (X (T j - 1)).1 / N :=
    ⟨fun j => (X (T j - 1)).1 / N, fun _ => rfl⟩
  have hAf : ∀ j, j ≤ m → 0 ≤ A j ∧ A j ≤ j ∧ (N : ℤ) * A j ≤ (X (T j - 1)).1 ∧
      (X (T j - 1)).1 < (N : ℤ) * A j + N := by
    intro j hj
    have hTj := hjT j hj
    have hN1 := hTN j
    obtain ⟨hx1, hx2, hx3⟩ := hb (T j - 1) (by omega)
    obtain ⟨f1, f2⟩ := floor_facts hN (X (T j - 1)).1
    have hTj' : (T j : ℤ) = ((j : ℤ) + 1) * N := by rw [hT]; push_cast; try ring
    have hcast : ((T j - 1 : ℕ) : ℤ) = (T j : ℤ) - 1 := by omega
    rw [← hA j] at f1 f2
    have hA0 : 0 ≤ A j := by rw [hA]; exact Int.ediv_nonneg hx1 (by omega)
    refine ⟨hA0, ?_, f1, f2⟩
    have hlt : (N : ℤ) * A j < (N : ℤ) * ((j : ℤ) + 1) := by nlinarith
    have := lt_of_mul_lt_mul_left hlt (by positivity)
    omega
  have hAstep : ∀ j, j < m → A (j + 1) = A j ∨ A (j + 1) = A j + 1 := by
    intro j hj
    obtain ⟨a0, a1, a2, a3⟩ := hAf j (by omega)
    obtain ⟨b0, b1, b2, b3⟩ := hAf (j + 1) (by omega)
    have hT1' := hT1 j
    have hjT' := hjT (j + 1) (by omega)
    have hN1 := hTN j
    obtain ⟨s1, s2, s3⟩ := walk_segment hstep (a := T j - 1) (b := T (j + 1) - 1)
      (by omega) (by omega)
    have hl : ((T (j + 1) - 1 : ℕ) : ℤ) - ((T j - 1 : ℕ) : ℤ) = N := by omega
    have e1 : (N : ℤ) * A (j + 1) < (N : ℤ) * (A j + 2) := by linarith
    have e2 : (N : ℤ) * A j < (N : ℤ) * (A (j + 1) + 1) := by linarith
    have r1 := lt_of_mul_lt_mul_left e1 (by positivity)
    have r2 := lt_of_mul_lt_mul_left e2 (by positivity)
    omega
  obtain ⟨q, hq⟩ : ∃ q : Fin (m + 1) → ℕ × ℕ, ∀ j : Fin (m + 1),
      q j = ((A j.val).toNat, j.val - (A j.val).toNat) :=
    ⟨fun j => ((A j.val).toNat, j.val - (A j.val).toNat), fun _ => rfl⟩
  have hq12 : ∀ j : Fin (m + 1),
      ((q j).1 : ℤ) = A j.val ∧ ((q j).2 : ℤ) = (j.val : ℤ) - A j.val := by
    intro j
    have hj := j.isLt
    obtain ⟨a0, a1, -, -⟩ := hAf j.val (by omega)
    rw [hq j]
    show (((A j.val).toNat : ℕ) : ℤ) = A j.val ∧
      ((j.val - (A j.val).toNat : ℕ) : ℤ) = (j.val : ℤ) - A j.val
    omega
  refine ⟨q, ?_, ?_, ?_⟩
  · have hA0 : A ((0 : Fin (m + 1)) : ℕ) = 0 := by
      rw [Fin.val_zero]
      obtain ⟨a0, a1, -, -⟩ := hAf 0 (Nat.zero_le m)
      omega
    rw [hq 0, hA0]
    simp
  · intro i
    have hi := i.isLt
    rw [hq i.succ, hq i.castSucc]
    simp only [Fin.val_succ, Fin.val_castSucc, Prod.mk_add_mk, Prod.mk.injEq]
    obtain ⟨a0, a1, -, -⟩ := hAf i.val (by omega)
    obtain ⟨b0, b1, -, -⟩ := hAf (i.val + 1) (by omega)
    rcases hAstep i.val hi with h | h <;> omega
  · suffices hmain : ∀ S : Finset (Fin (m + 1)),
        (∀ j, j ∈ S → IsBlackBlock O N c₁ (((q j).1 : ℤ), ((q j).2 : ℤ))) →
        (S.card : ℝ) ≤ δ * (k + ℓ) + (1 - s) * (k + ℓ) / ((1 - c₁) * N) from
      hmain _ (fun j hj => (Finset.mem_filter.1 hj).2)
    intro S hS
    have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
    have hD : 0 < (1 - c₁) * N := mul_pos (by linarith) hNpos
    have hTjN : ∀ j : Fin (m + 1), T j.val + N ≤ k + ℓ := fun j => by
      have h1 := hTmono (j.val + 1) (m + 1) (by have := j.isLt; omega)
      have h2 := hT1 j.val
      omega
    have hcard := Finset.card_filter_add_card_filter_not (s := S)
      (fun j : Fin (m + 1) => c₁ * N ≤ (((X (T j.val + N)).1 - (X (T j.val)).1 : ℤ) : ℝ))
    have hC : (((range (k + ℓ)).filter (fun i => X (i + 1) ∉ O)).card : ℝ) ≤
        δ * (k + ℓ) := by
      have h1 := Finset.card_filter_add_card_filter_not (s := range (k + ℓ))
        (fun i => X (i + 1) ∈ O)
      rw [Finset.sum_boole] at hp
      rw [Finset.card_range] at h1
      have h2 : (((range (k + ℓ)).filter (fun i => X (i + 1) ∈ O)).card : ℝ) +
          (((range (k + ℓ)).filter (fun i => X (i + 1) ∉ O)).card : ℝ) = (k : ℝ) + ℓ := by
        exact_mod_cast h1
      linarith
    have hGle : (S.filter fun j : Fin (m + 1) =>
          c₁ * N ≤ (((X (T j.val + N)).1 - (X (T j.val)).1 : ℤ) : ℝ)).card ≤
        ((range (k + ℓ)).filter (fun i => X (i + 1) ∉ O)).card := by
      have hex : ∀ j : Fin (m + 1), j ∈ S.filter (fun j : Fin (m + 1) =>
          c₁ * N ≤ (((X (T j.val + N)).1 - (X (T j.val)).1 : ℤ) : ℝ)) →
          ∃ i, T j.val ≤ i ∧ i < T j.val + N ∧ X (i + 1) ∉ O := by
        intro j hj
        obtain ⟨hjS, hjg⟩ := Finset.mem_filter.1 hj
        have hjm : j.val ≤ m := Nat.lt_succ_iff.1 j.isLt
        have hblack := hS j hjS
        rw [(hq12 j).1, (hq12 j).2] at hblack
        obtain ⟨a0, a1, a2, a3⟩ := hAf j.val hjm
        have hTj := hjT j.val hjm
        have hN1 := hTN j.val
        obtain ⟨hx1, hx2, hx3⟩ := hb (T j.val - 1) (by omega)
        obtain ⟨hu1, hu2, hu3⟩ := hb (T j.val) hTj
        obtain ⟨s1, s2, s3⟩ := walk_segment hstep (a := T j.val - 1) (b := T j.val)
          (by omega) hTj
        have hTj' : (T j.val : ℤ) = ((j.val : ℤ) + 1) * N := by rw [hT]; push_cast; try ring
        have hcast : ((T j.val - 1 : ℕ) : ℤ) = (T j.val : ℤ) - 1 := by omega
        exact closed_in_good_block hstep hblack (hTjN j)
          (by show (N : ℤ) * A j.val ≤ (X (T j.val)).1; linarith)
          (by show (N : ℤ) * ((j.val : ℤ) - A j.val) ≤ (X (T j.val)).2; nlinarith)
          (by show ((X (T j.val)).1 - (N : ℤ) * A j.val) +
                ((X (T j.val)).2 - (N : ℤ) * ((j.val : ℤ) - A j.val)) = N; nlinarith)
          hjg
      choose! f hf using hex
      refine Finset.card_le_card_of_injOn f ?_ ?_
      · intro j hj
        have hj' : j ∈ S.filter (fun j : Fin (m + 1) =>
            c₁ * N ≤ (((X (T j.val + N)).1 - (X (T j.val)).1 : ℤ) : ℝ)) := by
          exact hj
        obtain ⟨l1, u1, n1⟩ := hf j hj'
        have := hTjN j
        simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range]
        exact ⟨by omega, n1⟩
      · intro j hj j' hj' hff
        have hj1 : j ∈ S.filter (fun j : Fin (m + 1) =>
            c₁ * N ≤ (((X (T j.val + N)).1 - (X (T j.val)).1 : ℤ) : ℝ)) := by
          exact hj
        have hj2 : j' ∈ S.filter (fun j : Fin (m + 1) =>
            c₁ * N ≤ (((X (T j.val + N)).1 - (X (T j.val)).1 : ℤ) : ℝ)) := by
          exact hj'
        obtain ⟨l1, u1, -⟩ := hf j hj1
        obtain ⟨l2, u2, -⟩ := hf j' hj2
        by_contra hne
        have hne' : j.val ≠ j'.val := fun h => hne (Fin.ext h)
        rcases Nat.lt_or_gt_of_ne hne' with h | h
        · have h1 := hTmono (j.val + 1) j'.val h
          have h2 := hT1 j.val
          omega
        · have h1 := hTmono (j'.val + 1) j.val h
          have h2 := hT1 j'.val
          omega
    obtain ⟨Y, hY⟩ : ∃ Y : ℕ → ℤ, ∀ j, Y j = (X (T j)).2 :=
      ⟨fun j => (X (T j)).2, fun _ => rfl⟩
    have hseg : ∀ j : Fin (m + 1), 0 ≤ (X (T j.val + N)).2 - (X (T j.val)).2 ∧
        ((X (T j.val + N)).1 - (X (T j.val)).1) +
          ((X (T j.val + N)).2 - (X (T j.val)).2) = N := fun j => by
      obtain ⟨s1, s2, s3⟩ := walk_segment hstep (a := T j.val) (b := T j.val + N)
        (by omega) (hTjN j)
      constructor
      · omega
      · omega
    have hsumZ : ∑ j ∈ range (m + 1), ((X (T j + N)).2 - (X (T j)).2) ≤ (ℓ : ℤ) := by
      have e : ∀ j, (X (T j + N)).2 - (X (T j)).2 = Y (j + 1) - Y j := by
        intro j; rw [hY, hY, hT1]
      have hs : ∑ j ∈ range (m + 1), ((X (T j + N)).2 - (X (T j)).2) = Y (m + 1) - Y 0 := by
        rw [← Finset.sum_range_sub Y (m + 1)]
        exact Finset.sum_congr rfl (fun j _ => e j)
      rw [hs, hY, hY]
      obtain ⟨s1, s2, s3⟩ := walk_segment hstep (a := T (m + 1)) (b := k + ℓ) hTm le_rfl
      obtain ⟨z1, z2, z3⟩ := hb (T 0) (hjT 0 (Nat.zero_le m))
      have s2' : (X (T (m + 1))).2 ≤ (ℓ : ℤ) := by
        have h := s2
        rw [hXn] at h
        exact h
      omega
    have hsumR : ∑ j : Fin (m + 1), (((X (T j.val + N)).2 - (X (T j.val)).2 : ℤ) : ℝ) ≤ ℓ := by
      rw [Fin.sum_univ_eq_sum_range (fun j => (((X (T j + N)).2 - (X (T j)).2 : ℤ) : ℝ))
        (m + 1)]
      have h : ((∑ j ∈ range (m + 1), ((X (T j + N)).2 - (X (T j)).2) : ℤ) : ℝ) ≤ ℓ := by
        exact_mod_cast hsumZ
      rwa [Int.cast_sum] at h
    have hterm : ∀ j ∈ S.filter (fun j : Fin (m + 1) =>
          ¬ (c₁ * N ≤ (((X (T j.val + N)).1 - (X (T j.val)).1 : ℤ) : ℝ))),
        (1 - c₁) * N ≤ (((X (T j.val + N)).2 - (X (T j.val)).2 : ℤ) : ℝ) := by
      intro j hj
      have hjn := (Finset.mem_filter.1 hj).2
      have hxy : ((((X (T j.val + N)).1 - (X (T j.val)).1 : ℤ) : ℝ) +
          (((X (T j.val + N)).2 - (X (T j.val)).2 : ℤ) : ℝ)) = N := by
        exact_mod_cast (hseg j).2
      push Not at hjn
      linarith
    have hBle : ((S.filter (fun j : Fin (m + 1) =>
          ¬ (c₁ * N ≤ (((X (T j.val + N)).1 - (X (T j.val)).1 : ℤ) : ℝ)))).card : ℝ) *
        ((1 - c₁) * N) ≤ ℓ := by
      have h1 := Finset.card_nsmul_le_sum _ _ _ hterm
      rw [nsmul_eq_mul] at h1
      refine h1.trans (le_trans ?_ hsumR)
      refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun j _ _ => ?_)
      exact_mod_cast (hseg j).1
    have hcardR : (S.card : ℝ) =
        ((S.filter fun j : Fin (m + 1) =>
          c₁ * N ≤ (((X (T j.val + N)).1 - (X (T j.val)).1 : ℤ) : ℝ)).card : ℝ) +
        ((S.filter (fun j : Fin (m + 1) =>
          ¬ (c₁ * N ≤ (((X (T j.val + N)).1 - (X (T j.val)).1 : ℤ) : ℝ)))).card : ℝ) := by
      exact_mod_cast hcard.symm
    have hGR := (Nat.cast_le (α := ℝ)).2 hGle
    have hbad : ((S.filter (fun j : Fin (m + 1) =>
          ¬ (c₁ * N ≤ (((X (T j.val + N)).1 - (X (T j.val)).1 : ℤ) : ℝ)))).card : ℝ) ≤
        (1 - s) * (k + ℓ) / ((1 - c₁) * N) := by
      rw [le_div_iff₀ hD]
      nlinarith
    linarith

open Classical in
/-- A coarse path meets few black blocks. A dense open path from the origin
to `(k, ℓ)` gives an up-right path of `⌊(k + ℓ) / N⌋ - 2` coarse steps with few black
blocks, split into good blocks (each owning a closed vertex) and bad blocks (steep
crossings, limited by the direction). -/
theorem coarse_path_few_black_blocks (O : Set Lattice) (N : ℕ) (hN : 0 < N)
    (c₁ s δ : ℝ) (hc₁ : c₁ < 1) (k ℓ : ℕ) (hks : s * (k + ℓ) ≤ k) (hlen : 3 * N ≤ k + ℓ)
    (p : Path 0 (k, ℓ))
    (hp : (1 - δ) * (k + ℓ) ≤
      ∑ i : Fin (k + ℓ), (if p.vertex i.succ ∈ O then (1 : ℝ) else 0)) :
    ∃ q : Fin ((k + ℓ) / N - 2 + 1) → ℕ × ℕ, q 0 = (0, 0) ∧
      (∀ i : Fin ((k + ℓ) / N - 2), q i.succ = q i.castSucc + (1, 0) ∨
        q i.succ = q i.castSucc + (0, 1)) ∧
      ((Finset.univ.filter fun j =>
          IsBlackBlock O N c₁ (((q j).1 : ℤ), ((q j).2 : ℤ))).card : ℝ) ≤
        δ * (k + ℓ) + (1 - s) * (k + ℓ) / ((1 - c₁) * N) := by
  obtain ⟨X, hX0, hXn, hstep, hvert⟩ := exists_walk p
  have hs : ∑ i : Fin (k + ℓ), (if p.vertex i.succ ∈ O then (1 : ℝ) else 0) =
      ∑ i ∈ range (k + ℓ), (if X (i + 1) ∈ O then (1 : ℝ) else 0) := by
    rw [← Fin.sum_univ_eq_sum_range (fun i => if X (i + 1) ∈ O then (1 : ℝ) else 0) (k + ℓ)]
    exact Finset.sum_congr rfl (fun i _ => by rw [hvert i])
  exact coarse_of_walk O N hN c₁ s δ hc₁ k ℓ hks hlen X hX0 hXn hstep (by rw [← hs]; exact hp)

end LPPDifferentiability
