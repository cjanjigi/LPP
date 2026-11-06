/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import LPP_Foundations.Model.LastPassage.Basic
public import LPP_Foundations.Model.Paths.Geometry
public import LPP_Foundations.Model.Paths.Level
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Nat.Find
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Blocking `r` sites of each row: the path correspondence

Martin (2004), proof of Lemma 4.4. The block `B(z)` of a lattice site
`z = (x, y)` is `{(r x + i, y) : 0 <= i < r}`. A block environment gives each block the sum of the
weights of its `r` sites. This file proves the deterministic step (4.6): a path of the fine lattice
from `0` to `(n r, m)` and a path of the block lattice from `0` to `(n, m)` can be matched so that
every site of the fine path lies in a block of the block path. The blocks of the block path hold
`r (n + m)` sites and the fine path has `n r + m` of them, so the two sets differ by exactly
`(r - 1) m` sites, fewer than the bound `m r` in (4.6). With `|X| <= K`, the two path
weights differ by at most `(r - 1) m K`, and so do the last passage times.

No new definition is public: the block environment is the hypothesis `hω'`, and the helper
definitions below are private.
-/

@[expose] public section

namespace LPPDifferentiability

/-! ### Paths read at every natural time -/

/-- The vertex of a path at every natural time; times past the end repeat the endpoint. -/
def vtx {a b : ℕ} (p : Path 0 (a, b)) (i : ℕ) : Lattice :=
  p.vertex ⟨min i (a + b), Nat.lt_succ_of_le (min_le_right _ _)⟩

private theorem vtx_of_le {a b : ℕ} (p : Path 0 (a, b)) {i : ℕ} (hi : i ≤ a + b) :
    vtx p i = p.vertex ⟨i, Nat.lt_succ_of_le hi⟩ := by
  simp only [vtx, min_eq_left hi]

theorem vtx_zero {a b : ℕ} (p : Path 0 (a, b)) : vtx p 0 = 0 := by
  rw [vtx_of_le p (Nat.zero_le _)]
  simpa using p.start

theorem vtx_last {a b : ℕ} (p : Path 0 (a, b)) :
    vtx p (a + b) = ((a : ℤ), (b : ℤ)) := by
  rw [vtx_of_le p le_rfl]
  exact p.finish.trans (zero_add _)

private theorem vtx_level {a b : ℕ} (p : Path 0 (a, b)) {i : ℕ} (hi : i ≤ a + b) :
    (vtx p i).1 + (vtx p i).2 = (i : ℤ) := by
  rw [vtx_of_le p hi]
  simpa using p.level ⟨i, Nat.lt_succ_of_le hi⟩

theorem vtx_fst_mono {a b : ℕ} (p : Path 0 (a, b)) {i j : ℕ} (h : i ≤ j) :
    (vtx p i).1 ≤ (vtx p j).1 :=
  p.fst_monotone (Fin.mk_le_mk.2 (min_le_min_right _ h))

theorem vtx_snd_mono {a b : ℕ} (p : Path 0 (a, b)) {i j : ℕ} (h : i ≤ j) :
    (vtx p i).2 ≤ (vtx p j).2 :=
  p.snd_monotone (Fin.mk_le_mk.2 (min_le_min_right _ h))

private theorem vtx_nonneg {a b : ℕ} (p : Path 0 (a, b)) (i : ℕ) :
    0 ≤ (vtx p i).1 ∧ 0 ≤ (vtx p i).2 := by
  have h1 := vtx_fst_mono p (Nat.zero_le i)
  have h2 := vtx_snd_mono p (Nat.zero_le i)
  rw [vtx_zero] at h1 h2
  exact ⟨by simpa using h1, by simpa using h2⟩

theorem vtx_step {a b : ℕ} (p : Path 0 (a, b)) {i : ℕ} (hi : i < a + b) :
    vtx p (i + 1) = vtx p i + (1, 0) ∨ vtx p (i + 1) = vtx p i + (0, 1) := by
  rw [vtx_of_le p hi.le, vtx_of_le p (Nat.succ_le_of_lt hi)]
  exact p.step ⟨i, hi⟩

/-- A path from a function on natural times that starts at `0`, ends at `(a, b)` and moves by
one east or north step at each time before `a + b`. -/
def pathOfFn (a b : ℕ) (f : ℕ → Lattice) (h0 : f 0 = 0)
    (hN : f (a + b) = ((a : ℤ), (b : ℤ)))
    (hs : ∀ i, i < a + b → f (i + 1) = f i + (1, 0) ∨ f (i + 1) = f i + (0, 1)) :
    Path 0 (a, b) where
  vertex i := f i.val
  start := h0
  finish := by
    show f (a + b) = 0 + ((a : ℤ), (b : ℤ))
    rw [zero_add]
    exact hN
  step i := hs i.val i.isLt

theorem vtx_pathOfFn (a b : ℕ) (f : ℕ → Lattice) (h0 : f 0 = 0)
    (hN : f (a + b) = ((a : ℤ), (b : ℤ)))
    (hs : ∀ i, i < a + b → f (i + 1) = f i + (1, 0) ∨ f (i + 1) = f i + (0, 1))
    {k : ℕ} (hk : k ≤ a + b) : vtx (pathOfFn a b f h0 hN hs) k = f k := by
  rw [vtx_of_le _ hk]
  rfl

/-- The weight of a path is the sum over its natural times before the end. -/
private theorem pathWeight_eq_sum_range {a b : ℕ} (ω : Environment) (p : Path 0 (a, b)) :
    pathWeight ω p = ∑ ℓ ∈ Finset.range (a + b), ω (vtx p ℓ) := by
  unfold pathWeight
  rw [Finset.sum_range]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [vtx_of_le p i.isLt.le]
  rfl

/-! ### Comparing weights once every fine site lies in a block of the block path -/

/-- One block `B(c)` and a family of distinct sites inside it: replacing the family by the whole
block changes the weight by at most `K` times the number of sites of the block that the family
misses. -/
private theorem abs_sum_sub_blockSum_le {ι : Type*} (r : ℕ) (K : ℝ) (ω : Environment)
    (hω : ∀ z, |ω z| ≤ K) (c : Lattice) (F : Finset ι) (v : ι → Lattice)
    (hinj : Set.InjOn v F)
    (hsub : ∀ i ∈ F, ∃ j < r, v i = ((r : ℤ) * c.1 + (j : ℤ), c.2)) :
    |∑ i ∈ F, ω (v i) - ∑ j ∈ Finset.range r, ω ((r : ℤ) * c.1 + (j : ℤ), c.2)| ≤
      ((r : ℝ) - F.card) * K := by
  classical
  have heinj : Function.Injective (fun j : ℕ => (((r : ℤ) * c.1 + (j : ℤ), c.2) : Lattice)) := by
    intro j j' h
    have h1 := congrArg Prod.fst h
    simp only at h1
    omega
  obtain ⟨B, hB⟩ : ∃ B : Finset Lattice, B = (Finset.range r).image
      (fun j : ℕ => (((r : ℤ) * c.1 + (j : ℤ), c.2) : Lattice)) := ⟨_, rfl⟩
  obtain ⟨S, hS⟩ : ∃ S : Finset Lattice, S = F.image v := ⟨_, rfl⟩
  have hSB : S ⊆ B := by
    intro z hz
    rw [hS] at hz
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hz
    obtain ⟨j, hj, hvj⟩ := hsub i hi
    rw [hB]
    exact Finset.mem_image.2 ⟨j, Finset.mem_range.2 hj, hvj.symm⟩
  have hBcard : B.card = r := by
    rw [hB, Finset.card_image_of_injective _ heinj, Finset.card_range]
  have hScard : S.card = F.card := by
    rw [hS]
    exact Finset.card_image_of_injOn hinj
  have hsumB : ∑ z ∈ B, ω z =
      ∑ j ∈ Finset.range r, ω ((r : ℤ) * c.1 + (j : ℤ), c.2) := by
    rw [hB]
    exact Finset.sum_image (fun j _ j' _ h => heinj h)
  have hsumS : ∑ z ∈ S, ω z = ∑ i ∈ F, ω (v i) := by
    rw [hS]
    exact Finset.sum_image hinj
  have hsplit := Finset.sum_sdiff (f := ω) hSB
  have hdiff : |∑ z ∈ B \ S, ω z| ≤ ((B \ S).card : ℝ) * K := by
    calc |∑ z ∈ B \ S, ω z| ≤ ∑ z ∈ B \ S, |ω z| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ (B \ S).card • K := Finset.sum_le_card_nsmul _ _ _ (fun z _ => hω z)
      _ = ((B \ S).card : ℝ) * K := by rw [nsmul_eq_mul]
  have hle : S.card ≤ B.card := Finset.card_le_card hSB
  have hcardsd : ((B \ S).card : ℝ) = (r : ℝ) - F.card := by
    rw [Finset.card_sdiff_of_subset hSB, Nat.cast_sub hle, hBcard, hScard]
  have hneg : ∑ i ∈ F, ω (v i) - ∑ j ∈ Finset.range r, ω ((r : ℤ) * c.1 + (j : ℤ), c.2) =
      -∑ z ∈ B \ S, ω z := by
    rw [← hsumB, ← hsumS]
    linarith
  rw [hneg, abs_neg, ← hcardsd]
  exact hdiff

/-- Martin (2004), the bound after (4.6): if every site of the fine path lies in a
block of the block path, the two path weights differ by at most `(r - 1) m K`. The fine path has
`n r + m` sites, the blocks have `r (n + m)`, and each block misses `r` minus the number of fine
sites it holds. -/
theorem abs_pathWeight_sub_le_of_cover (r n m : ℕ) (K : ℝ) (ω ω' : Environment)
    (hω : ∀ z, |ω z| ≤ K)
    (hω' : ∀ z : Lattice, ω' z = ∑ j ∈ Finset.range r, ω ((r : ℤ) * z.1 + (j : ℤ), z.2))
    (π : Path 0 (n * r, m)) (π' : Path 0 (n, m))
    (hcover : ∀ ℓ < n * r + m, ∃ k < n + m, ∃ j < r,
      vtx π ℓ = ((r : ℤ) * (vtx π' k).1 + (j : ℤ), (vtx π' k).2)) :
    |pathWeight ω π - pathWeight ω' π'| ≤ ((r : ℝ) - 1) * (m : ℝ) * K := by
  classical
  choose! κ hκlt hκmem using hcover
  rw [pathWeight_eq_sum_range ω π, pathWeight_eq_sum_range ω' π']
  have hmaps : ∀ ℓ ∈ Finset.range (n * r + m), κ ℓ ∈ Finset.range (n + m) := fun ℓ hℓ =>
    Finset.mem_range.2 (hκlt ℓ (Finset.mem_range.1 hℓ))
  have hfib := Finset.sum_fiberwise_of_maps_to hmaps (fun ℓ => ω (vtx π ℓ))
  have key : ∀ k ∈ Finset.range (n + m),
      |∑ ℓ ∈ Finset.filter (fun ℓ => κ ℓ = k) (Finset.range (n * r + m)), ω (vtx π ℓ)
          - ω' (vtx π' k)| ≤
        ((r : ℝ) - (Finset.filter (fun ℓ => κ ℓ = k) (Finset.range (n * r + m))).card) * K := by
    intro k _
    rw [hω' (vtx π' k)]
    refine abs_sum_sub_blockSum_le r K ω hω (vtx π' k) _ (vtx π) ?_ ?_
    · intro ℓ hℓ ℓ' hℓ' h
      have hℓ1 := Finset.mem_range.1 (Finset.mem_filter.1 hℓ).1
      have hℓ2 := Finset.mem_range.1 (Finset.mem_filter.1 hℓ').1
      have e1 := vtx_level π (show ℓ ≤ n * r + m by omega)
      have e2 := vtx_level π (show ℓ' ≤ n * r + m by omega)
      rw [h] at e1
      omega
    · intro ℓ hℓ
      obtain ⟨hlt, hk⟩ := Finset.mem_filter.1 hℓ
      have hm := hκmem ℓ (Finset.mem_range.1 hlt)
      rw [hk] at hm
      exact hm
  have hcard := Finset.card_eq_sum_card_fiberwise
    (f := κ) (s := Finset.range (n * r + m)) (t := Finset.range (n + m))
    (fun ℓ hℓ => Finset.mem_coe.2 (hmaps ℓ (Finset.mem_coe.1 hℓ)))
  have hsum : ∑ k ∈ Finset.range (n + m),
      ((Finset.filter (fun ℓ => κ ℓ = k) (Finset.range (n * r + m))).card : ℝ) =
        ((n * r + m : ℕ) : ℝ) := by
    rw [← Nat.cast_sum, ← hcard, Finset.card_range]
  calc |∑ ℓ ∈ Finset.range (n * r + m), ω (vtx π ℓ) -
        ∑ k ∈ Finset.range (n + m), ω' (vtx π' k)|
      = |∑ k ∈ Finset.range (n + m),
          (∑ ℓ ∈ Finset.filter (fun ℓ => κ ℓ = k) (Finset.range (n * r + m)), ω (vtx π ℓ)
            - ω' (vtx π' k))| := by rw [Finset.sum_sub_distrib, hfib]
    _ ≤ ∑ k ∈ Finset.range (n + m),
          |∑ ℓ ∈ Finset.filter (fun ℓ => κ ℓ = k) (Finset.range (n * r + m)), ω (vtx π ℓ)
            - ω' (vtx π' k)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ Finset.range (n + m),
          ((r : ℝ) - (Finset.filter (fun ℓ => κ ℓ = k) (Finset.range (n * r + m))).card) * K :=
        Finset.sum_le_sum key
    _ = (∑ k ∈ Finset.range (n + m),
          ((r : ℝ) - (Finset.filter (fun ℓ => κ ℓ = k) (Finset.range (n * r + m))).card)) * K :=
        (Finset.sum_mul _ _ _).symm
    _ = ((r : ℝ) - 1) * (m : ℝ) * K := by
        rw [Finset.sum_sub_distrib, hsum, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        push_cast
        ring

/-! ### From a fine path to a block path (Martin (2004), (4.6), first direction) -/

/-- The block level of a site: its block column plus its row. A block path visits exactly one
block at each block level. -/
private def blockLevel (r : ℕ) (z : Lattice) : ℤ := z.1 / (r : ℤ) + z.2

private theorem blockLevel_mono {r : ℕ} (hr : 1 ≤ r) {z z' : Lattice} (h1 : z.1 ≤ z'.1)
    (h2 : z.2 ≤ z'.2) : blockLevel r z ≤ blockLevel r z' := by
  have hd := Int.ediv_le_ediv (show (0 : ℤ) < r by omega) h1
  unfold blockLevel
  omega

private theorem blockLevel_succ_le {r : ℕ} (hr : 1 ≤ r) {z z' : Lattice}
    (h : z' = z + (1, 0) ∨ z' = z + (0, 1)) : blockLevel r z' ≤ blockLevel r z + 1 := by
  have hd := Int.add_mul_ediv_right z.1 1 (show (r : ℤ) ≠ 0 by omega)
  have hm := Int.ediv_le_ediv (show (0 : ℤ) < r by omega)
    (show z.1 + 1 ≤ z.1 + 1 * (r : ℤ) by omega)
  rcases h with h | h <;> subst h <;>
    simp only [blockLevel, Prod.fst_add, Prod.snd_add, add_zero] <;> omega

private theorem blockLevel_nonneg {r : ℕ} (z : Lattice) (h1 : 0 ≤ z.1) (h2 : 0 ≤ z.2) :
    0 ≤ blockLevel r z := by
  have := Int.ediv_nonneg h1 (show (0 : ℤ) ≤ r by omega)
  unfold blockLevel
  omega

/-- Passing from one site to the next of a lattice path changes the pair `(a, y)` by an east or
a north step when the two levels differ by one and neither coordinate decreases. -/
private theorem step_of_levels {a a' y y' k : ℤ} (ha : a ≤ a') (hy : y ≤ y')
    (h1 : a + y = k) (h2 : a' + y' = k + 1) :
    ((a', y') : Lattice) = (a, y) + (1, 0) ∨ ((a', y') : Lattice) = (a, y) + (0, 1) := by
  rcases (show (a' = a + 1 ∧ y' = y) ∨ (a' = a ∧ y' = y + 1) by omega) with ⟨e1, e2⟩ | ⟨e1, e2⟩
  · exact Or.inl (Prod.ext (by simp [e1]) (by simp [e2]))
  · exact Or.inr (Prod.ext (by simp [e1]) (by simp [e2]))

section FineToBlock

variable {r n m : ℕ}

private theorem blockLevel_start (π : Path 0 (n * r, m)) : blockLevel r (vtx π 0) = 0 := by
  rw [vtx_zero]
  simp [blockLevel]

private theorem blockLevel_finish (hr : 1 ≤ r) (π : Path 0 (n * r, m)) :
    blockLevel r (vtx π (n * r + m)) = (n : ℤ) + m := by
  rw [vtx_last]
  have h : ((n * r : ℕ) : ℤ) / (r : ℤ) = n := by
    push_cast
    exact Int.mul_ediv_cancel _ (by omega)
  show ((n * r : ℕ) : ℤ) / (r : ℤ) + ((m : ℕ) : ℤ) = n + m
  rw [h]

private theorem blockLevel_mono_time (hr : 1 ≤ r) (π : Path 0 (n * r, m)) {i j : ℕ}
    (h : i ≤ j) : blockLevel r (vtx π i) ≤ blockLevel r (vtx π j) :=
  blockLevel_mono hr (vtx_fst_mono π h) (vtx_snd_mono π h)

private theorem blockLevel_succ_time (hr : 1 ≤ r) (π : Path 0 (n * r, m)) {ℓ : ℕ}
    (hℓ : ℓ < n * r + m) :
    blockLevel r (vtx π (ℓ + 1)) ≤ blockLevel r (vtx π ℓ) + 1 :=
  blockLevel_succ_le hr (vtx_step π hℓ)

/-- Before the end of the fine path the block level is below `n + m`: reaching `n + m` forces
the endpoint `(n r, m)`. -/
private theorem blockLevel_lt (hr : 1 ≤ r) (π : Path 0 (n * r, m)) {ℓ : ℕ}
    (hℓ : ℓ < n * r + m) : blockLevel r (vtx π ℓ) < (n : ℤ) + m := by
  have hle := blockLevel_mono_time hr π hℓ.le
  rw [blockLevel_finish hr π] at hle
  by_contra hcon
  have heq : blockLevel r (vtx π ℓ) = (n : ℤ) + m := by omega
  have hx := vtx_fst_mono π hℓ.le
  have hy := vtx_snd_mono π hℓ.le
  rw [vtx_last] at hx hy
  have hdn : (vtx π ℓ).1 / (r : ℤ) ≤ ((n * r : ℕ) : ℤ) / (r : ℤ) :=
    Int.ediv_le_ediv (show (0 : ℤ) < r by omega) hx
  have hn : ((n * r : ℕ) : ℤ) / (r : ℤ) = n := by
    push_cast
    exact Int.mul_ediv_cancel _ (by omega)
  have hmul := Int.mul_ediv_self_le (x := (vtx π ℓ).1) (k := (r : ℤ)) (by omega)
  have hlev := vtx_level π (show ℓ ≤ n * r + m by omega)
  have hcomm : (r : ℤ) * n = n * r := mul_comm _ _
  unfold blockLevel at heq
  simp only at hy hx
  push_cast at hx hy
  have hq : (vtx π ℓ).1 / (r : ℤ) = n := by omega
  rw [hq] at hmul
  omega

/-- The last time at which the block level of the fine path is at most `k`. -/
private def lastBelow (r : ℕ) {a b : ℕ} (p : Path 0 (a, b)) (k : ℕ) : ℕ :=
  Nat.findGreatest (fun ℓ => blockLevel r (vtx p ℓ) ≤ (k : ℤ)) (a + b)

private theorem lastBelow_prop (π : Path 0 (n * r, m)) (k : ℕ) :
    blockLevel r (vtx π (lastBelow r π k)) ≤ (k : ℤ) :=
  Nat.findGreatest_spec (P := fun ℓ => blockLevel r (vtx π ℓ) ≤ (k : ℤ)) (m := 0)
    (Nat.zero_le _) (by
      show blockLevel r (vtx π 0) ≤ (k : ℤ)
      rw [blockLevel_start]
      omega)

private theorem lastBelow_le (π : Path 0 (n * r, m)) (k : ℕ) :
    lastBelow r π k ≤ n * r + m :=
  Nat.findGreatest_le _

private theorem le_lastBelow (π : Path 0 (n * r, m)) {ℓ k : ℕ} (hℓ : ℓ ≤ n * r + m)
    (h : blockLevel r (vtx π ℓ) ≤ (k : ℤ)) : ℓ ≤ lastBelow r π k :=
  Nat.le_findGreatest hℓ h

private theorem lastBelow_level (hr : 1 ≤ r) (π : Path 0 (n * r, m)) {k : ℕ}
    (hk : k ≤ n + m) : blockLevel r (vtx π (lastBelow r π k)) = (k : ℤ) := by
  have hp := lastBelow_prop π k
  have hle := lastBelow_le π k
  rcases Nat.lt_or_ge (lastBelow r π k) (n * r + m) with hlt | hge
  · have hgr : ¬ (blockLevel r (vtx π (lastBelow r π k + 1)) ≤ (k : ℤ)) :=
      Nat.findGreatest_is_greatest
        (P := fun ℓ => blockLevel r (vtx π ℓ) ≤ (k : ℤ)) (Nat.lt_succ_self _)
        (Nat.succ_le_of_lt hlt)
    have hs := blockLevel_succ_time hr π hlt
    omega
  · have heq : lastBelow r π k = n * r + m := le_antisymm hle hge
    rw [heq, blockLevel_finish hr π] at hp ⊢
    omega

private theorem lastBelow_mono (π : Path 0 (n * r, m)) {k k' : ℕ} (h : k ≤ k') :
    lastBelow r π k ≤ lastBelow r π k' := by
  have hp := lastBelow_prop π k
  exact le_lastBelow π (lastBelow_le π k) (by omega)

private theorem lastBelow_finish (hr : 1 ≤ r) (π : Path 0 (n * r, m)) :
    lastBelow r π (n + m) = n * r + m := by
  apply Nat.findGreatest_eq
  show blockLevel r (vtx π (n * r + m)) ≤ ((n + m : ℕ) : ℤ)
  rw [blockLevel_finish hr π]
  push_cast
  exact le_rfl

/-- The block of the fine path at block level `k`: the column of the block and the row of the
last fine site whose block level is at most `k`. -/
private def coarse (r : ℕ) {a b : ℕ} (p : Path 0 (a, b)) (k : ℕ) : Lattice :=
  ((vtx p (lastBelow r p k)).1 / (r : ℤ), (vtx p (lastBelow r p k)).2)

private theorem coarse_zero (hr : 1 ≤ r) (π : Path 0 (n * r, m)) : coarse r π 0 = 0 := by
  have l := lastBelow_level hr π (Nat.zero_le (n + m))
  obtain ⟨n1, n2⟩ := vtx_nonneg π (lastBelow r π 0)
  have hd := Int.ediv_nonneg n1 (show (0 : ℤ) ≤ r by omega)
  unfold blockLevel at l
  refine Prod.ext ?_ ?_ <;> simp only [coarse, Prod.fst_zero, Prod.snd_zero] <;> omega

private theorem coarse_finish (hr : 1 ≤ r) (π : Path 0 (n * r, m)) :
    coarse r π (n + m) = ((n : ℤ), (m : ℤ)) := by
  have h : ((n * r : ℕ) : ℤ) / (r : ℤ) = n := by
    push_cast
    exact Int.mul_ediv_cancel _ (by omega)
  unfold coarse
  rw [lastBelow_finish hr π, vtx_last]
  show (((n * r : ℕ) : ℤ) / (r : ℤ), ((m : ℕ) : ℤ)) = ((n : ℤ), (m : ℤ))
  rw [h]

private theorem coarse_step (hr : 1 ≤ r) (π : Path 0 (n * r, m)) {k : ℕ} (hk : k < n + m) :
    coarse r π (k + 1) = coarse r π k + (1, 0) ∨ coarse r π (k + 1) = coarse r π k + (0, 1) := by
  have l1 := lastBelow_level hr π hk.le
  have l2 := lastBelow_level hr π (Nat.succ_le_of_lt hk)
  have hmono := lastBelow_mono π (Nat.le_succ k)
  have hd := Int.ediv_le_ediv (show (0 : ℤ) < r by omega) (vtx_fst_mono π hmono)
  have hy := vtx_snd_mono π hmono
  unfold blockLevel at l1 l2
  push_cast at l2
  exact step_of_levels hd hy l1 l2

/-- Every fine site lies in a block of the block path `coarse`: it lies in the block at its own
block level, because it is no later than the last site of that level and has the same level. -/
private theorem exists_cover_blockPath (hr : 1 ≤ r) (π : Path 0 (n * r, m)) :
    ∃ π' : Path 0 (n, m), ∀ ℓ < n * r + m, ∃ k < n + m, ∃ j < r,
      vtx π ℓ = ((r : ℤ) * (vtx π' k).1 + (j : ℤ), (vtx π' k).2) := by
  refine ⟨pathOfFn n m (coarse r π) (coarse_zero hr π) (coarse_finish hr π)
    (fun i hi => coarse_step hr π hi), ?_⟩
  intro ℓ hℓ
  obtain ⟨n1, n2⟩ := vtx_nonneg π ℓ
  have hnn := blockLevel_nonneg (r := r) (vtx π ℓ) n1 n2
  have hlt := blockLevel_lt hr π hℓ
  obtain ⟨k, hk⟩ : ∃ k : ℕ, (k : ℤ) = blockLevel r (vtx π ℓ) := ⟨_, Int.toNat_of_nonneg hnn⟩
  have hkn : k < n + m := by omega
  have hℓk : ℓ ≤ lastBelow r π k := le_lastBelow π hℓ.le (by omega)
  have hlev := lastBelow_level hr π hkn.le
  have h1 := vtx_fst_mono π hℓk
  have h2 := vtx_snd_mono π hℓk
  have hd := Int.ediv_le_ediv (show (0 : ℤ) < r by omega) h1
  have hm1 := Int.mul_ediv_self_le (x := (vtx π ℓ).1) (k := (r : ℤ)) (by omega)
  have hm2 := Int.lt_mul_ediv_self_add (x := (vtx π ℓ).1) (k := (r : ℤ)) (by omega)
  unfold blockLevel at hk hlev
  have e1 : (vtx π ℓ).1 / (r : ℤ) = (vtx π (lastBelow r π k)).1 / (r : ℤ) := by omega
  have e2 : (vtx π ℓ).2 = (vtx π (lastBelow r π k)).2 := by omega
  have hv : vtx (pathOfFn n m (coarse r π) (coarse_zero hr π) (coarse_finish hr π)
      (fun i hi => coarse_step hr π hi)) k = coarse r π k :=
    vtx_pathOfFn n m _ _ _ _ hkn.le
  refine ⟨k, hkn, ((vtx π ℓ).1 - (r : ℤ) * ((vtx π ℓ).1 / (r : ℤ))).toNat, by omega, ?_⟩
  rw [hv]
  refine Prod.ext ?_ ?_
  · simp only [coarse]
    rw [← e1]
    omega
  · simp only [coarse]
    omega

end FineToBlock

/-! ### The correspondence and its consequence for passage times -/

/-- Martin (2004), (4.6), first direction: every path of the fine
lattice from `0` to `(n r, m)` has a block path from `0` to `(n, m)` whose blocks contain all of its
sites. When the weights lie in `[-K, K]` and the block environment `ω'` gives each block the sum of
its `r` weights, the two path weights differ by at most `(r - 1) m K`: the blocks hold
`r (n + m)` sites, the fine path `n r + m`, so the symmetric difference has `(r - 1) m` sites. -/
theorem exists_blockPath_of_finePath (r n m : ℕ) (hr : 1 ≤ r) (K : ℝ)
    (ω ω' : Environment) (hω : ∀ z, |ω z| ≤ K)
    (hω' : ∀ z : Lattice, ω' z = ∑ j ∈ Finset.range r, ω ((r : ℤ) * z.1 + (j : ℤ), z.2))
    (π : Path 0 (n * r, m)) :
    ∃ π' : Path 0 (n, m),
      |pathWeight ω π - pathWeight ω' π'| ≤ ((r : ℝ) - 1) * (m : ℝ) * K := by
  obtain ⟨π', hcover⟩ := exists_cover_blockPath hr π
  exact ⟨π', abs_pathWeight_sub_le_of_cover r n m K ω ω' hω hω' π π' hcover⟩

end LPPDifferentiability
