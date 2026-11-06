/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Martin2004.Model.LastPassage.RowBlocks
import Mathlib.Data.Nat.Find
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Blocking `r` sites of each row: the converse path correspondence

The second half of the row-block argument (Martin (2004), proof of Lemma 4.4):
from a block path to a fine path whose sites all lie in its blocks, and the maximum comparison of
the two passage times. This file continues the row-block argument of the `RowBlocks` module.
-/

@[expose] public section

namespace LPPDifferentiability

/-! ### From a block path to a fine path (the converse step of (4.6)) -/

section BlockToFine

variable {r n m : ℕ}

/-- The fine time at which the fine path reaches the first site of the block at block time `k`:
`r` fine steps for each east block step, one fine step for each north block step. -/
private def corner (r : ℕ) (p : Path 0 (n, m)) (k : ℕ) : ℤ :=
  (r : ℤ) * (vtx p k).1 + (vtx p k).2

private theorem corner_step (p : Path 0 (n, m)) {k : ℕ} (hk : k < n + m) :
    (corner r p (k + 1) = corner r p k + r ∧ vtx p (k + 1) = vtx p k + (1, 0)) ∨
    (corner r p (k + 1) = corner r p k + 1 ∧ vtx p (k + 1) = vtx p k + (0, 1)) := by
  rcases vtx_step p hk with h | h
  · refine Or.inl ⟨?_, h⟩
    unfold corner
    rw [h]
    simp only [Prod.fst_add, Prod.snd_add, add_zero]
    ring
  · refine Or.inr ⟨?_, h⟩
    unfold corner
    rw [h]
    simp only [Prod.fst_add, Prod.snd_add, add_zero]
    ring

private theorem corner_mono (p : Path 0 (n, m)) {k k' : ℕ} (h : k ≤ k') :
    corner r p k ≤ corner r p k' := by
  have h1 := mul_le_mul_of_nonneg_left (vtx_fst_mono p h) (Int.natCast_nonneg r)
  have h2 := vtx_snd_mono p h
  unfold corner
  omega

private theorem corner_lt_succ (hr : 1 ≤ r) (p : Path 0 (n, m)) {k : ℕ} (hk : k < n + m) :
    corner r p k + 1 ≤ corner r p (k + 1) := by
  rcases corner_step (r := r) p hk with ⟨h, _⟩ | ⟨h, _⟩ <;> omega

private theorem corner_succ_le (hr : 1 ≤ r) (p : Path 0 (n, m)) {k : ℕ} (hk : k < n + m) :
    corner r p (k + 1) ≤ corner r p k + r := by
  rcases corner_step (r := r) p hk with ⟨h, _⟩ | ⟨h, _⟩ <;> omega

private theorem corner_zero (p : Path 0 (n, m)) : corner r p 0 = 0 := by
  unfold corner
  rw [vtx_zero]
  simp

private theorem corner_finish (p : Path 0 (n, m)) :
    corner r p (n + m) = ((n * r + m : ℕ) : ℤ) := by
  unfold corner
  rw [vtx_last]
  show (r : ℤ) * (n : ℤ) + (m : ℤ) = ((n * r + m : ℕ) : ℤ)
  push_cast
  ring

/-- The block time of a fine time: the last block whose first site is reached by then. -/
private def blockTime (r : ℕ) (p : Path 0 (n, m)) (ℓ : ℕ) : ℕ :=
  Nat.findGreatest (fun k => corner r p k ≤ (ℓ : ℤ)) (n + m)

private theorem blockTime_eq (p : Path 0 (n, m)) {ℓ κ : ℕ} (h1 : κ ≤ n + m)
    (h2 : corner r p κ ≤ (ℓ : ℤ)) (h3 : κ < n + m → (ℓ : ℤ) < corner r p (κ + 1)) :
    blockTime r p ℓ = κ := by
  refine Nat.findGreatest_eq_iff.2 ⟨h1, fun _ => h2, fun k' hk' hle hcon => ?_⟩
  have h4 := corner_mono (r := r) p (show κ + 1 ≤ k' from hk')
  have h5 := h3 (lt_of_lt_of_le hk' hle)
  omega

private theorem blockTime_prop (p : Path 0 (n, m)) {ℓ : ℕ} (hℓ : 0 ≤ (ℓ : ℤ)) :
    corner r p (blockTime r p ℓ) ≤ (ℓ : ℤ) :=
  Nat.findGreatest_spec (P := fun k => corner r p k ≤ (ℓ : ℤ)) (m := 0) (Nat.zero_le _) (by
    show corner r p 0 ≤ (ℓ : ℤ)
    rw [corner_zero]
    exact hℓ)

private theorem blockTime_lt_corner (p : Path 0 (n, m)) {ℓ : ℕ}
    (hκ : blockTime r p ℓ < n + m) : (ℓ : ℤ) < corner r p (blockTime r p ℓ + 1) := by
  have h : ¬ corner r p (blockTime r p ℓ + 1) ≤ (ℓ : ℤ) :=
    Nat.findGreatest_is_greatest
      (P := fun k => corner r p k ≤ (ℓ : ℤ)) (Nat.lt_succ_self (blockTime r p ℓ))
      (Nat.succ_le_of_lt hκ)
  omega

private theorem blockTime_lt (p : Path 0 (n, m)) {ℓ : ℕ} (hℓ : ℓ < n * r + m) :
    blockTime r p ℓ < n + m := by
  have hle : blockTime r p ℓ ≤ n + m := Nat.findGreatest_le _
  have hp := blockTime_prop (r := r) p (Int.natCast_nonneg ℓ)
  by_contra hcon
  have heq : blockTime r p ℓ = n + m := by omega
  rw [heq, corner_finish] at hp
  omega

/-- The fine site at fine time `ℓ`: inside the block of block time `blockTime r p ℓ`, at the
position `ℓ - corner`. -/
private def fineSite (r : ℕ) (p : Path 0 (n, m)) (ℓ : ℕ) : Lattice :=
  ((r : ℤ) * (vtx p (blockTime r p ℓ)).1 + ((ℓ : ℤ) - corner r p (blockTime r p ℓ)),
    (vtx p (blockTime r p ℓ)).2)

private theorem fineSite_of_blockTime (p : Path 0 (n, m)) {ℓ κ : ℕ}
    (h : blockTime r p ℓ = κ) :
    fineSite r p ℓ = ((r : ℤ) * (vtx p κ).1 + ((ℓ : ℤ) - corner r p κ), (vtx p κ).2) := by
  unfold fineSite
  rw [h]

private theorem fineSite_zero (hr : 1 ≤ r) (p : Path 0 (n, m)) : fineSite r p 0 = 0 := by
  have h : blockTime r p 0 = 0 := by
    refine blockTime_eq p (Nat.zero_le _) (by rw [corner_zero]; simp) (fun hk => ?_)
    have := corner_lt_succ hr p hk
    rw [corner_zero] at this
    omega
  rw [fineSite_of_blockTime p h, vtx_zero, corner_zero]
  simp

private theorem fineSite_finish (p : Path 0 (n, m)) :
    fineSite r p (n * r + m) = (((n * r : ℕ) : ℤ), (m : ℤ)) := by
  have h : blockTime r p (n * r + m) = n + m := by
    apply Nat.findGreatest_eq
    show corner r p (n + m) ≤ ((n * r + m : ℕ) : ℤ)
    rw [corner_finish]
  rw [fineSite_of_blockTime p h, vtx_last, corner_finish]
  show ((r : ℤ) * (n : ℤ) + (((n * r + m : ℕ) : ℤ) - ((n * r + m : ℕ) : ℤ)), (m : ℤ)) = _
  rw [sub_self, add_zero]
  push_cast
  rw [mul_comm]

private theorem fineSite_step (hr : 1 ≤ r) (p : Path 0 (n, m)) {ℓ : ℕ} (hℓ : ℓ < n * r + m) :
    fineSite r p (ℓ + 1) = fineSite r p ℓ + (1, 0) ∨
      fineSite r p (ℓ + 1) = fineSite r p ℓ + (0, 1) := by
  have hκ := blockTime_lt (r := r) p hℓ
  have hlt := blockTime_lt_corner p hκ
  have hp := blockTime_prop (r := r) p (Int.natCast_nonneg ℓ)
  obtain ⟨κ, hκdef⟩ : ∃ κ, blockTime r p ℓ = κ := ⟨_, rfl⟩
  rw [hκdef] at hκ hlt hp
  rw [fineSite_of_blockTime p hκdef]
  have hstep := corner_step (r := r) p hκ
  by_cases hc : ((ℓ + 1 : ℕ) : ℤ) < corner r p (κ + 1)
  · -- the fine path stays in the same block and moves east
    have h : blockTime r p (ℓ + 1) = κ :=
      blockTime_eq p hκ.le (by push_cast; omega) (fun _ => hc)
    rw [fineSite_of_blockTime p h]
    refine Or.inl (Prod.ext ?_ ?_)
    · simp only [Prod.fst_add]
      push_cast
      omega
    · simp only [Prod.snd_add, add_zero]
  · -- the fine path reaches the first site of the next block
    have hnext : ((ℓ + 1 : ℕ) : ℤ) = corner r p (κ + 1) := by push_cast at hc ⊢; omega
    have h : blockTime r p (ℓ + 1) = κ + 1 := by
      refine blockTime_eq p hκ (by omega) (fun hk2 => ?_)
      have := corner_lt_succ hr p hk2
      omega
    rw [fineSite_of_blockTime p h]
    rcases hstep with ⟨hc1, hv⟩ | ⟨hc1, hv⟩
    · have hx : (vtx p (κ + 1)).1 = (vtx p κ).1 + 1 := by
        have := congrArg Prod.fst hv
        simpa using this
      have hy : (vtx p (κ + 1)).2 = (vtx p κ).2 := by
        have := congrArg Prod.snd hv
        simpa using this
      have hmul : (r : ℤ) * ((vtx p κ).1 + 1) = (r : ℤ) * (vtx p κ).1 + r := by ring
      refine Or.inl (Prod.ext ?_ ?_)
      · simp only [Prod.fst_add]
        rw [hx]
        push_cast at hnext ⊢
        omega
      · simpa using hy
    · have hx : (vtx p (κ + 1)).1 = (vtx p κ).1 := by
        have := congrArg Prod.fst hv
        simpa using this
      have hy : (vtx p (κ + 1)).2 = (vtx p κ).2 + 1 := by
        have := congrArg Prod.snd hv
        simpa using this
      refine Or.inr (Prod.ext ?_ ?_)
      · simp only [Prod.fst_add, add_zero]
        rw [hx]
        push_cast at hnext ⊢
        omega
      · simpa using hy

/-- Every site of the fine path `fineSite` lies in a block of the block path: the block of block
time `blockTime`, at a position between `0` and `r - 1`. -/
private theorem exists_cover_finePath (hr : 1 ≤ r) (π' : Path 0 (n, m)) :
    ∃ π : Path 0 (n * r, m), ∀ ℓ < n * r + m, ∃ k < n + m, ∃ j < r,
      vtx π ℓ = ((r : ℤ) * (vtx π' k).1 + (j : ℤ), (vtx π' k).2) := by
  refine ⟨pathOfFn (n * r) m (fineSite r π') (fineSite_zero hr π') (fineSite_finish π')
    (fun i hi => fineSite_step hr π' hi), ?_⟩
  intro ℓ hℓ
  have hκ := blockTime_lt (r := r) π' hℓ
  have hlt := blockTime_lt_corner π' hκ
  have hp := blockTime_prop (r := r) π' (Int.natCast_nonneg ℓ)
  have hsucc := corner_succ_le hr π' hκ
  have hv : vtx (pathOfFn (n * r) m (fineSite r π') (fineSite_zero hr π')
      (fineSite_finish π') (fun i hi => fineSite_step hr π' hi)) ℓ = fineSite r π' ℓ :=
    vtx_pathOfFn (n * r) m _ _ _ _ hℓ.le
  refine ⟨blockTime r π' ℓ, hκ, ((ℓ : ℤ) - corner r π' (blockTime r π' ℓ)).toNat, by omega, ?_⟩
  rw [hv]
  unfold fineSite
  refine Prod.ext ?_ rfl
  show (r : ℤ) * (vtx π' (blockTime r π' ℓ)).1 +
      ((ℓ : ℤ) - corner r π' (blockTime r π' ℓ)) =
    (r : ℤ) * (vtx π' (blockTime r π' ℓ)).1 +
      (((ℓ : ℤ) - corner r π' (blockTime r π' ℓ)).toNat : ℤ)
  omega

end BlockToFine

/-- Martin (2004), (4.6), converse direction: every path
of the block lattice from `0` to `(n, m)` has a fine path from `0` to `(n r, m)` all of whose sites
lie in its blocks. The fine path runs along a block when the block path leaves it eastward and
enters each block that the block path leaves northward at its first site. The weights differ by at
most `(r - 1) m K`. -/
theorem exists_finePath_of_blockPath (r n m : ℕ) (hr : 1 ≤ r) (K : ℝ)
    (ω ω' : Environment) (hω : ∀ z, |ω z| ≤ K)
    (hω' : ∀ z : Lattice, ω' z = ∑ j ∈ Finset.range r, ω ((r : ℤ) * z.1 + (j : ℤ), z.2))
    (π' : Path 0 (n, m)) :
    ∃ π : Path 0 (n * r, m),
      |pathWeight ω π - pathWeight ω' π'| ≤ ((r : ℝ) - 1) * (m : ℝ) * K := by
  obtain ⟨π, hcover⟩ := exists_cover_finePath hr π'
  exact ⟨π, abs_pathWeight_sub_le_of_cover r n m K ω ω' hω hω' π π' hcover⟩

/-- Martin (2004), the maximum step of Lemma 4.4, after (4.6): with weights in
`[-K, K]`, the last passage time of the fine lattice from `0` to `(n r, m)` and the last
passage time of the block environment from `0` to `(n, m)` differ by at most `(r - 1) m K`. -/
theorem abs_lastPassage_sub_blockPassage_le (r n m : ℕ) (hr : 1 ≤ r) (K : ℝ)
    (ω ω' : Environment) (hω : ∀ z, |ω z| ≤ K)
    (hω' : ∀ z : Lattice, ω' z = ∑ j ∈ Finset.range r, ω ((r : ℤ) * z.1 + (j : ℤ), z.2)) :
    |lastPassage ω 0 (n * r, m) - lastPassage ω' 0 (n, m)| ≤ ((r : ℝ) - 1) * (m : ℝ) * K := by
  rw [abs_le]
  constructor
  · -- block maximum at most fine maximum plus the constant
    obtain ⟨π', hπ'⟩ := exists_pathWeight_eq_lastPassage ω' 0 (n, m)
    obtain ⟨π, hπ⟩ := exists_finePath_of_blockPath r n m hr K ω ω' hω hω' π'
    have h1 := (abs_le.1 hπ).1
    have h2 := pathWeight_le_lastPassage ω π
    rw [hπ'] at h1
    linarith
  · -- fine maximum at most block maximum plus the constant
    obtain ⟨π, hπ⟩ := exists_pathWeight_eq_lastPassage ω 0 (n * r, m)
    obtain ⟨π', hπ'⟩ := exists_blockPath_of_finePath r n m hr K ω ω' hω hω' π
    have h1 := (abs_le.1 hπ').2
    have h2 := pathWeight_le_lastPassage ω' π'
    rw [hπ] at h1
    linarith

end LPPDifferentiability
