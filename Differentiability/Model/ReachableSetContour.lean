/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Differentiability.Model.SquareBoundaryCircuit
public import LPP_Foundations.Model.FiniteBoxWalkCount
import LPP_Foundations.Model.ClosedLatticeWalkCounts
import Mathlib.Tactic

/-! The boundary circuit through the origin cell of a finite connected cell set `T` encloses `T`,
so `16 |T| ≤ m ^ 2`; a countable family of labelled walks covers these circuits. -/

public section

namespace LPPDifferentiability

private abbrev Step (c s : Lattice) : Prop :=
  s - c = (0, 1) ∨ s - c = (0, -1) ∨ s - c = (-1, 0) ∨ s - c = (1, 0)

/-- Signed crossings of the band between rows `b` and `b + 1` by one step, at columns in `P`. -/
private def crossTerm (b : ℤ) (P : ℤ → Prop) [DecidablePred P] (c s : Lattice) : ℤ :=
  if c.2 = b ∧ s.2 = b + 1 ∧ P c.1 then 1 else if c.2 = b + 1 ∧ s.2 = b ∧ P c.1 then -1 else 0

private def IsBdry (T : Finset Lattice) (E : Finset (Lattice × Lattice)) : Prop :=
  ∀ e, e ∈ E ↔ ∃ z, z ∈ T ∧
    ((e = ((z.1, z.2), (z.1 + 1, z.2)) ∧ (z.1, z.2 - 1) ∉ T) ∨
     (e = ((z.1 + 1, z.2), (z.1 + 1, z.2 + 1)) ∧ (z.1 + 1, z.2) ∉ T) ∨
     (e = ((z.1 + 1, z.2 + 1), (z.1, z.2 + 1)) ∧ (z.1, z.2 + 1) ∉ T) ∨
     (e = ((z.1, z.2 + 1), (z.1, z.2)) ∧ (z.1 - 1, z.2) ∉ T))

private theorem step_cases {c s : Lattice} (h : Step c s) :
    (s.1 = c.1 ∧ s.2 = c.2 + 1) ∨ (s.1 = c.1 ∧ s.2 = c.2 - 1) ∨
      (s.1 = c.1 - 1 ∧ s.2 = c.2) ∨ (s.1 = c.1 + 1 ∧ s.2 = c.2) := by
  rcases h with h | h | h | h <;> have hx := congrArg Prod.fst h <;>
    have hy := congrArg Prod.snd h <;> simp only [Prod.fst_sub, Prod.snd_sub] at hx hy <;> omega

private theorem sum_telescope_closed {m : ℕ} (v : Fin (m + 1) → Lattice)
    (hclosed : v 0 = v (Fin.last m)) (φ : Lattice → ℤ) :
    ∑ i : Fin m, (φ (v i.succ) - φ (v i.castSucc)) = 0 := by
  have h1 := Fin.sum_univ_succ (fun j : Fin (m + 1) => φ (v j))
  have h2 := Fin.sum_univ_castSucc (fun j : Fin (m + 1) => φ (v j))
  rw [← hclosed] at h2
  rw [Finset.sum_sub_distrib]
  omega

private theorem cross_split {c s : Lattice} (hs : Step c s) (a b : ℤ) :
    crossTerm b (fun x => a + 1 ≤ x) c s + crossTerm b (fun x => x ≤ a) c s =
      (if b + 1 ≤ s.2 then 1 else 0) - (if b + 1 ≤ c.2 then 1 else 0) := by
  have := step_cases hs; unfold crossTerm; split_ifs <;> omega

private theorem cross_shift {c s : Lattice} (hs : Step c s) (a b : ℤ)
    (h₁ : ¬ (c = (a + 1, b) ∧ s = (a + 1, b + 1)))
    (h₂ : ¬ (c = (a + 1, b + 1) ∧ s = (a + 1, b))) :
    crossTerm b (fun x => a + 1 ≤ x) c s = crossTerm b (fun x => a + 1 + 1 ≤ x) c s := by
  have := step_cases hs; simp only [Prod.ext_iff] at h₁ h₂; unfold crossTerm; split_ifs <;> omega

private theorem cross_vertical {c s : Lattice} (hs : Step c s) (a b : ℤ)
    (h₁ : ¬ (c = (a, b + 1) ∧ s = (a + 1, b + 1)))
    (h₂ : ¬ (c = (a + 1, b + 1) ∧ s = (a, b + 1))) :
    crossTerm b (fun x => a + 1 ≤ x) c s - crossTerm (b + 1) (fun x => a + 1 ≤ x) c s =
      (if s.2 = b + 1 ∧ a + 1 ≤ s.1 then 1 else 0) -
        (if c.2 = b + 1 ∧ a + 1 ≤ c.1 then 1 else 0) := by
  have := step_cases hs; simp only [Prod.ext_iff] at h₁ h₂; unfold crossTerm; split_ifs <;> omega

/-- The two cells next to a boundary edge: the left one is in the set, the right one is not. -/
private theorem edge_sides {T : Finset Lattice} {E : Finset (Lattice × Lattice)}
    (hmem : IsBdry T E) {c s : Lattice} (he : (c, s) ∈ E) :
    (s = (c.1, c.2 + 1) → (c.1 - 1, c.2) ∈ T ∧ (c.1, c.2) ∉ T) ∧
    (s = (c.1, c.2 - 1) → (c.1, c.2 - 1) ∈ T ∧ (c.1 - 1, c.2 - 1) ∉ T) ∧
    (s = (c.1 + 1, c.2) → (c.1, c.2) ∈ T ∧ (c.1, c.2 - 1) ∉ T) ∧
    (s = (c.1 - 1, c.2) → (c.1 - 1, c.2 - 1) ∈ T ∧ (c.1 - 1, c.2) ∉ T) := by
  obtain ⟨z, hz, hc⟩ := (hmem _).mp he
  obtain ⟨c1, c2⟩ := c
  obtain ⟨s1, s2⟩ := s
  obtain ⟨z1, z2⟩ := z
  simp only [Prod.mk.injEq] at hc
  rcases hc with ⟨⟨⟨rfl, rfl⟩, rfl, rfl⟩, hn⟩ | ⟨⟨⟨rfl, rfl⟩, rfl, rfl⟩, hn⟩ |
    ⟨⟨⟨rfl, rfl⟩, rfl, rfl⟩, hn⟩ | ⟨⟨⟨rfl, rfl⟩, rfl, rfl⟩, hn⟩ <;>
  refine ⟨?_, ?_, ?_, ?_⟩ <;> intro h <;> simp only [Prod.mk.injEq] at h ⊢ <;>
    first | omega | exact ⟨by simpa using hz, by simpa using hn⟩

private theorem two_abs_le_variation {m : ℕ} (f : Fin (m + 1) → ℤ) (hf : f 0 = f (Fin.last m))
    (p q : Fin (m + 1)) : 2 * |f q - f p| ≤ ∑ i : Fin m, |f i.succ - f i.castSucc| := by
  let g : ℕ → ℤ := fun n => f ⟨min n m, by omega⟩
  have hg : ∀ n (hn : n ≤ m), g n = f ⟨n, by omega⟩ := fun n hn => by simp only [g, min_eq_left hn]
  have hsum : ∑ i : Fin m, |f i.succ - f i.castSucc| =
      ∑ i ∈ Finset.range m, |g (i + 1) - g i| := by
    rw [← Fin.sum_univ_eq_sum_range (fun i => |g (i + 1) - g i|) m]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hg (i + 1) (by omega), hg i (by omega)]; rfl
  have hico : ∀ a b : ℕ, a ≤ b → |g b - g a| ≤ ∑ i ∈ Finset.Ico a b, |g (i + 1) - g i| := by
    intro a b hab
    induction b, hab using Nat.le_induction with
    | base => simp
    | succ b hab ih =>
      rw [Finset.sum_Ico_succ_top hab]
      have := abs_sub_le (g (b + 1)) (g b) (g a)
      linarith
  have g0 : g m = g 0 := by rw [hg m le_rfl, hg 0 (by omega)]; exact hf.symm
  have key : ∀ a b : ℕ, a ≤ b → b ≤ m →
      2 * |g b - g a| ≤ ∑ i ∈ Finset.range m, |g (i + 1) - g i| := by
    intro a b hab hbm
    have e1 := hico 0 a (Nat.zero_le _)
    have e2 := hico a b hab
    have e3 := hico b m hbm
    rw [Finset.range_eq_Ico, ← Finset.sum_Ico_consecutive _ (Nat.zero_le b) hbm,
      ← Finset.sum_Ico_consecutive _ (Nat.zero_le a) hab]
    have t1 := abs_sub_le (g b) (g 0) (g a)
    rw [g0] at e3
    have t2 := abs_sub_comm (g 0) (g b)
    have t3 := abs_sub_comm (g a) (g 0)
    linarith
  rw [hsum]
  by_cases hpq : p.val ≤ q.val
  · have := key p.val q.val hpq (by omega)
    rwa [hg p.val (by omega), hg q.val (by omega)] at this
  · have := key q.val p.val (by omega) (by omega)
    rw [hg p.val (by omega), hg q.val (by omega), abs_sub_comm] at this
    exact this

private theorem two_card_le_variation {m : ℕ} (f : Fin (m + 1) → ℤ) (hf : f 0 = f (Fin.last m))
    (S : Finset ℤ) (hS : ∀ a ∈ S, (∃ p, f p ≤ a) ∧ ∃ q, a + 1 ≤ f q) :
    2 * (S.card : ℤ) ≤ ∑ i : Fin m, |f i.succ - f i.castSucc| := by
  have hnn : 0 ≤ ∑ i : Fin m, |f i.succ - f i.castSucc| :=
    Finset.sum_nonneg fun i _ => abs_nonneg _
  rcases S.eq_empty_or_nonempty with rfl | hne
  · simpa using hnn
  obtain ⟨p, hp⟩ := (hS _ (S.min'_mem hne)).1
  obtain ⟨q, hq⟩ := (hS _ (S.max'_mem hne)).2
  have h1 := two_abs_le_variation f hf p q
  have h2 := Finset.card_le_card (show S ⊆ Finset.Icc (S.min' hne) (S.max' hne) from fun x hx =>
    Finset.mem_Icc.mpr ⟨S.min'_le x hx, S.le_max' x hx⟩)
  rw [Int.card_Icc] at h2
  have hx : 0 ≤ S.max' hne + 1 - S.min' hne := by
    have := S.min'_le _ (S.max'_mem hne); omega
  have h2' : (S.card : ℤ) ≤ ((S.max' hne + 1 - S.min' hne).toNat : ℤ) := by exact_mod_cast h2
  rw [Int.toNat_of_nonneg hx] at h2'
  have h4 := le_abs_self (f q - f p)
  omega

/-- The steps of a walk that go up or left. -/
private def upLeft {m : ℕ} (v : Fin (m + 1) → Lattice) : Finset (Fin m) :=
  Finset.univ.filter fun i => v i.succ - v i.castSucc = (0, 1) ∨ v i.succ - v i.castSucc = (-1, 0)

/-- The cell on the left of an up or left step, and the cell on its right. -/
private def leftLab {m : ℕ} (v : Fin (m + 1) → Lattice) (i : Fin m) : ℕ × ℕ :=
  (((v i.castSucc).1 - 1).toNat, ((v i.succ).2 - 1).toNat)

private def rightLab {m : ℕ} (v : Fin (m + 1) → Lattice) (i : Fin m) : ℕ × ℕ :=
  ((v i.succ).1.toNat, (min (v i.castSucc).2 (v i.succ).2).toNat)

private theorem label_card {m : ℕ} (v : Fin (m + 1) → Lattice) (hclosed : v 0 = v (Fin.last m))
    (hstep : ∀ i : Fin m, Step (v i.castSucc) (v i.succ)) (lab : Fin m → ℕ × ℕ)
    (hinj : ∀ i j, v i.succ - v i.castSucc = v j.succ - v j.castSucc →
      (v i.succ - v i.castSucc = (0, 1) ∨ v i.succ - v i.castSucc = (-1, 0)) →
      lab i = lab j → i = j) : m ≤ 8 * ((upLeft v).image lab).card := by
  classical
  let U := Finset.univ.filter fun i : Fin m => v i.succ - v i.castSucc = (0, 1)
  let L := Finset.univ.filter fun i : Fin m => v i.succ - v i.castSucc = (-1, 0)
  have hb : 2 * (U.card + L.card) = m :=
    (closed_lattice_walk_direction_balance m v hclosed hstep).2.2
  have hUi : Set.InjOn lab U := fun i hi j hj h => hinj i j
    (by rw [(Finset.mem_filter.mp hi).2, (Finset.mem_filter.mp hj).2])
    (Or.inl (Finset.mem_filter.mp hi).2) h
  have hLi : Set.InjOn lab L := fun i hi j hj h => hinj i j
    (by rw [(Finset.mem_filter.mp hi).2, (Finset.mem_filter.mp hj).2])
    (Or.inr (Finset.mem_filter.mp hi).2) h
  have h1 : U.card ≤ ((upLeft v).image lab).card := by
    rw [← Finset.card_image_of_injOn hUi]
    exact Finset.card_le_card (Finset.image_subset_image fun i hi =>
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inl (Finset.mem_filter.mp hi).2⟩)
  have h2 : L.card ≤ ((upLeft v).image lab).card := by
    rw [← Finset.card_image_of_injOn hLi]
    exact Finset.card_le_card (Finset.image_subset_image fun i hi =>
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inr (Finset.mem_filter.mp hi).2⟩)
  omega

/-- A countable cover of the boundary circuits of finite connected cell sets by labelled walks;
every such set has a circuit of length `m` with `16 |T| ≤ m ^ 2`, whose left cells lie in the set
with an exit outside it, and whose right cells lie outside it next to a cell of the set. -/
theorem exists_cell_set_contour_cover :
    ∃ (W : (n : ℕ) → Finset (Fin (n + 5) → Lattice))
      (B C : (n : ℕ) → (Fin (n + 5) → Lattice) → Finset (ℕ × ℕ)),
      (∀ n, (W n).card ≤ (n + 6) ^ 2 * 4 * 3 ^ (n + 3)) ∧
      (∀ n, ∀ v ∈ W n, n + 4 ≤ 8 * (B n v).card ∧ n + 4 ≤ 8 * (C n v).card) ∧
      ∀ T : Finset Lattice, (∀ x ∈ T, 0 ≤ x.1 ∧ 0 ≤ x.2) → ((0, 0) : Lattice) ∈ T →
        (∀ x ∈ T, x ≠ (0, 0) → x - (1, 0) ∈ T ∨ x - (0, 1) ∈ T) →
        ∃ n, ∃ v ∈ W n, 16 * T.card ≤ (n + 4) ^ 2 ∧
          (∀ x ∈ B n v, ((x.1 : ℤ), (x.2 : ℤ)) ∈ T ∧
            (((x.1 : ℤ) + 1, (x.2 : ℤ)) ∉ T ∨ ((x.1 : ℤ), (x.2 : ℤ) + 1) ∉ T)) ∧
          (∀ x ∈ C n v, ((x.1 : ℤ), (x.2 : ℤ)) ∉ T ∧
            (((x.1 : ℤ) - 1, (x.2 : ℤ)) ∈ T ∨ ((x.1 : ℤ), (x.2 : ℤ) - 1) ∈ T)) := by
  classical
  choose U hU hcU using fun n : ℕ =>
    exists_finset_nonbacktracking_walks_in_box (n + 4) (by omega)
  let B : (n : ℕ) → (Fin (n + 5) → Lattice) → Finset (ℕ × ℕ) := fun n v =>
    (upLeft (m := n + 4) v).image (leftLab v)
  let C : (n : ℕ) → (Fin (n + 5) → Lattice) → Finset (ℕ × ℕ) := fun n v =>
    (upLeft (m := n + 4) v).image (rightLab v)
  let W (n : ℕ) : Finset (Fin (n + 5) → Lattice) :=
    (U n).filter fun v => n + 4 ≤ 8 * (B n v).card ∧ n + 4 ≤ 8 * (C n v).card
  refine ⟨W, B, C, ?_, fun n v hv => (Finset.mem_filter.mp hv).2, ?_⟩
  · intro n
    have h := hcU n
    rw [show n + 4 - 1 = n + 3 by omega, show n + 4 + 2 = n + 6 by omega] at h
    exact (Finset.card_filter_le _ _).trans h
  intro T hq h0 hconn
  obtain ⟨E, m, v, w, hmem, hm, hclosed, hinj, he, hstep, -, hindex, hrev, hbox, hw⟩ :=
    exists_square_boundary_circuit T hq h0
  have harea : 16 * T.card ≤ m ^ 2 := by
    let N : ℤ → ℤ → ℤ := fun a b =>
      ∑ i : Fin m, crossTerm b (fun x => a + 1 ≤ x) (v i.castSucc) (v i.succ)
    have hvert : ∀ a b : ℤ, (a, b) ∈ T → (a + 1, b) ∈ T → ∀ i : Fin m,
        ¬ (v i.castSucc = (a + 1, b) ∧ v i.succ = (a + 1, b + 1)) ∧
        ¬ (v i.castSucc = (a + 1, b + 1) ∧ v i.succ = (a + 1, b)) := by
      intro a b h1 h2 i
      have hei := he i
      refine ⟨fun ⟨hc, hs⟩ => ?_, fun ⟨hc, hs⟩ => ?_⟩ <;> rw [hc, hs] at hei
      · exact ((edge_sides hmem hei).1 rfl).2 h2
      · have := ((edge_sides hmem hei).2.1 (by simp)).2
        dsimp only at this; simp only [add_sub_cancel_right] at this; exact this h1
    have hhorz : ∀ a b : ℤ, (a, b) ∈ T → (a, b + 1) ∈ T → ∀ i : Fin m,
        ¬ (v i.castSucc = (a, b + 1) ∧ v i.succ = (a + 1, b + 1)) ∧
        ¬ (v i.castSucc = (a + 1, b + 1) ∧ v i.succ = (a, b + 1)) := by
      intro a b h1 h2 i
      have hei := he i
      refine ⟨fun ⟨hc, hs⟩ => ?_, fun ⟨hc, hs⟩ => ?_⟩ <;> rw [hc, hs] at hei
      · have := ((edge_sides hmem hei).2.2.1 rfl).2
        dsimp only at this; simp only [add_sub_cancel_right] at this; exact this h1
      · have := ((edge_sides hmem hei).2.2.2 (by simp)).2
        dsimp only at this; simp only [add_sub_cancel_right] at this; exact this h2
    have hNh : ∀ a b : ℤ, (a, b) ∈ T → (a + 1, b) ∈ T → N a b = N (a + 1) b := fun a b h1 h2 =>
      Finset.sum_congr rfl fun i _ =>
        cross_shift (hstep i) a b (hvert a b h1 h2 i).1 (hvert a b h1 h2 i).2
    have hNv : ∀ a b : ℤ, (a, b) ∈ T → (a, b + 1) ∈ T → N a b = N a (b + 1) := by
      intro a b h1 h2
      have hd := sum_telescope_closed v hclosed
        (fun u => if u.2 = b + 1 ∧ a + 1 ≤ u.1 then (1 : ℤ) else 0)
      have hd' : ∑ i : Fin m, (crossTerm b (fun x => a + 1 ≤ x) (v i.castSucc) (v i.succ) -
          crossTerm (b + 1) (fun x => a + 1 ≤ x) (v i.castSucc) (v i.succ)) = 0 := by
        rw [← hd]
        exact Finset.sum_congr rfl fun i _ =>
          cross_vertical (hstep i) a b (hhorz a b h1 h2 i).1 (hhorz a b h1 h2 i).2
      rw [Finset.sum_sub_distrib] at hd'
      exact sub_eq_zero.mp hd'
    have hN00 : N 0 0 = 1 := by
      rw [← hindex]
      exact Finset.sum_congr rfl fun i _ => by simp only [crossTerm, zero_add]
    have hN : ∀ x ∈ T, N x.1 x.2 = 1 := by
      have key : ∀ k : ℕ, ∀ a b : ℤ, (a, b) ∈ T → a.toNat + b.toNat = k → N a b = 1 := by
        intro k
        induction k using Nat.strong_induction_on with
        | _ k ih =>
          intro a b hx hk
          have hxq := hq _ hx
          by_cases h0 : (a, b) = (0, 0)
          · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h0; exact hN00
          · rcases hconn (a, b) hx h0 with hp | hp
            · have hp' : (a - 1, b) ∈ T := by simpa using hp
              have hpq := hq _ hp'
              have e := hNh (a - 1) b hp' (by simpa using hx)
              rw [sub_add_cancel] at e; rw [← e]
              exact ih ((a - 1).toNat + b.toNat) (by simp only at hpq hxq hk; omega) _ _ hp' rfl
            · have hp' : (a, b - 1) ∈ T := by simpa using hp
              have hpq := hq _ hp'
              have e := hNv a (b - 1) hp' (by simpa using hx)
              rw [sub_add_cancel] at e; rw [← e]
              exact ih (a.toNat + (b - 1).toNat) (by simp only at hpq hxq hk; omega) _ _ hp' rfl
      exact fun x hx => key _ x.1 x.2 hx rfl
    have hhit : ∀ a b : ℤ, N a b = 1 → ((∃ p, (v p).1 ≤ a) ∧ ∃ q, a + 1 ≤ (v q).1) ∧
        ((∃ r, (v r).2 ≤ b) ∧ ∃ s, b + 1 ≤ (v s).2) := by
      intro a b hNab
      have hsplit : N a b + ∑ i : Fin m, crossTerm b (fun x => x ≤ a) (v i.castSucc) (v i.succ) = 0 := by
        rw [← Finset.sum_add_distrib,
          ← sum_telescope_closed v hclosed (fun u => if b + 1 ≤ u.2 then (1 : ℤ) else 0)]
        exact Finset.sum_congr rfl fun i _ => cross_split (hstep i) a b
      have hL : ∑ i : Fin m, crossTerm b (fun x => x ≤ a) (v i.castSucc) (v i.succ) ≠ 0 := by omega
      obtain ⟨i, _, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero (show N a b ≠ 0 by omega)
      obtain ⟨j, _, hj⟩ := Finset.exists_ne_zero_of_sum_ne_zero hL
      have hi' : ((v i.castSucc).2 = b ∧ (v i.succ).2 = b + 1 ∨
          (v i.castSucc).2 = b + 1 ∧ (v i.succ).2 = b) ∧ a + 1 ≤ (v i.castSucc).1 := by
        unfold crossTerm at hi
        split_ifs at hi with h1 h2
        exacts [⟨Or.inl ⟨h1.1, h1.2.1⟩, h1.2.2⟩, ⟨Or.inr ⟨h2.1, h2.2.1⟩, h2.2.2⟩, absurd rfl hi]
      have hj' : (v j.castSucc).1 ≤ a := by
        unfold crossTerm at hj
        split_ifs at hj with h1 h2
        exacts [h1.2.2, h2.2.2, absurd rfl hj]
      refine ⟨⟨⟨j.castSucc, hj'⟩, ⟨i.castSucc, hi'.2⟩⟩, ?_⟩
      rcases hi'.1 with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact ⟨⟨i.castSucc, h1.le⟩, ⟨i.succ, h2.ge⟩⟩
      · exact ⟨⟨i.succ, h2.le⟩, ⟨i.castSucc, h1.ge⟩⟩
    let mh : ℤ := ∑ i : Fin m, |(v i.succ).1 - (v i.castSucc).1|
    let mv : ℤ := ∑ i : Fin m, |(v i.succ).2 - (v i.castSucc).2|
    have hm : mh + mv = m := by
      have h1 : ∀ i : Fin m,
          |(v i.succ).1 - (v i.castSucc).1| + |(v i.succ).2 - (v i.castSucc).2| = 1 := by
        intro i
        have := step_cases (hstep i)
        simp only [abs_eq_max_neg]; omega
      simp only [mh, mv, ← Finset.sum_add_distrib, h1, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul, mul_one]
    have hC := two_card_le_variation (fun i => (v i).1) (congrArg Prod.fst hclosed)
      (T.image Prod.fst) (fun a ha => by
        obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp ha
        exact (hhit x.1 x.2 (hN x hx)).1)
    have hR := two_card_le_variation (fun i => (v i).2) (congrArg Prod.snd hclosed)
      (T.image Prod.snd) (fun a ha => by
        obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp ha
        exact (hhit x.1 x.2 (hN x hx)).2)
    have hT : T.card ≤ (T.image Prod.fst).card * (T.image Prod.snd).card := by
      simpa only [Finset.card_product] using Finset.card_le_card (show
        T ⊆ T.image Prod.fst ×ˢ T.image Prod.snd from fun x hx =>
          Finset.mem_product.mpr ⟨Finset.mem_image_of_mem _ hx, Finset.mem_image_of_mem _ hx⟩)
    have hT' : (T.card : ℤ) ≤ (T.image Prod.fst).card * (T.image Prod.snd).card := by
      exact_mod_cast hT
    have hCR : (2 * ((T.image Prod.fst).card : ℤ)) * (2 * ((T.image Prod.snd).card : ℤ)) ≤ mh * mv :=
      mul_le_mul hC hR (by positivity) (le_trans (by positivity) hC)
    have hm2 : (m : ℤ) ^ 2 = (mh + mv) ^ 2 := by rw [hm]
    have : ((16 * T.card : ℕ) : ℤ) ≤ ((m ^ 2 : ℕ) : ℤ) := by
      push_cast; nlinarith [sq_nonneg (mh - mv)]
    exact_mod_cast this
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, m = n + 4 := ⟨m - 4, by omega⟩
  have hvU : v ∈ U n := (hU n v).mpr ⟨⟨(hbox 0).1, (hbox 0).2.1⟩, ⟨(hbox 0).2.2.1, (hbox 0).2.2.2⟩,
    hstep, fun i hi hr => hrev ⟨i, by omega⟩ ⟨i + 1, by omega⟩ (Prod.ext rfl hr.symm)⟩
  have hwq := fun i : Fin (n + 4) => hq _ (hw i).1
  have hlab : ∀ i : Fin (n + 4), (v i.succ - v i.castSucc = (0, 1) ∨
      v i.succ - v i.castSucc = (-1, 0)) →
      ((leftLab v i).1 : ℤ) = (w i).1 ∧ ((leftLab v i).2 : ℤ) = (w i).2 ∧
      (v i.succ - v i.castSucc = (0, 1) → ((rightLab v i).1 : ℤ) = (w i).1 + 1 ∧
        ((rightLab v i).2 : ℤ) = (w i).2) ∧
      (v i.succ - v i.castSucc = (-1, 0) → ((rightLab v i).1 : ℤ) = (w i).1 ∧
        ((rightLab v i).2 : ℤ) = (w i).2 + 1) := by
    intro i hi
    have := hwq i
    rcases hi with hu | hl
    · obtain ⟨h1, h2, -⟩ := (hw i).2.1 hu
      have hl' : ¬ v i.succ - v i.castSucc = (-1, 0) := fun h => by
        rw [h] at hu; exact absurd (congrArg Prod.fst hu) (by norm_num)
      refine ⟨?_, ?_, fun _ => ?_, fun h => absurd h hl'⟩ <;> simp only [leftLab, rightLab, h1, h2] <;> omega
    · obtain ⟨h1, h2, -⟩ := (hw i).2.2 hl
      have hu' : ¬ v i.succ - v i.castSucc = (0, 1) := fun h => by
        rw [h] at hl; exact absurd (congrArg Prod.fst hl) (by norm_num)
      refine ⟨?_, ?_, fun h => absurd h hu', fun _ => ?_⟩ <;> simp only [leftLab, rightLab, h1, h2] <;> omega
  have hedge : ∀ i j : Fin (n + 4), v i.succ - v i.castSucc = v j.succ - v j.castSucc →
      (v i.succ - v i.castSucc = (0, 1) ∨ v i.succ - v i.castSucc = (-1, 0)) →
      w i = w j → i = j := by
    intro i j hd hi h
    apply hinj
    change (v i.castSucc, v i.succ) = (v j.castSucc, v j.succ)
    rcases hi with hu | hl
    · obtain ⟨a1, a2, -⟩ := (hw i).2.1 hu
      obtain ⟨b1, b2, -⟩ := (hw j).2.1 (hd.symm.trans hu)
      rw [a1, a2, b1, b2, h]
    · obtain ⟨a1, a2, -⟩ := (hw i).2.2 hl
      obtain ⟨b1, b2, -⟩ := (hw j).2.2 (hd.symm.trans hl)
      rw [a1, a2, b1, b2, h]
  have hBc : n + 4 ≤ 8 * (B n v).card :=
    label_card v hclosed hstep (leftLab v) fun i j hd hi h => by
      have a := hlab i hi
      have b := hlab j (hi.imp hd.symm.trans hd.symm.trans)
      rw [h] at a
      exact hedge i j hd hi (Prod.ext (by omega) (by omega))
  have hCc : n + 4 ≤ 8 * (C n v).card :=
    label_card v hclosed hstep (rightLab v) fun i j hd hi h => by
      rcases hi with hu | hl
      · have a := (hlab i (Or.inl hu)).2.2.1 hu
        have b := (hlab j (Or.inl (hd.symm.trans hu))).2.2.1 (hd.symm.trans hu)
        rw [h] at a
        exact hedge i j hd (Or.inl hu) (Prod.ext (by omega) (by omega))
      · have a := (hlab i (Or.inr hl)).2.2.2 hl
        have b := (hlab j (Or.inr (hd.symm.trans hl))).2.2.2 (hd.symm.trans hl)
        rw [h] at a
        exact hedge i j hd (Or.inr hl) (Prod.ext (by omega) (by omega))
  refine ⟨n, v, Finset.mem_filter.mpr ⟨hvU, hBc, hCc⟩, harea, ?_, ?_⟩
  · intro x hx
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
    have hi' := (Finset.mem_filter.mp hi).2
    obtain ⟨e1, e2, -⟩ := hlab i hi'
    rw [e1, e2]
    refine ⟨(hw i).1, ?_⟩
    by_cases hu : v i.succ - v i.castSucc = (0, 1)
    · exact Or.inl ((hw i).2.1 hu).2.2
    · exact Or.inr ((hw i).2.2 (hi'.resolve_left hu)).2.2
  · intro x hx
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
    have hi' := (Finset.mem_filter.mp hi).2
    by_cases hu : v i.succ - v i.castSucc = (0, 1)
    · obtain ⟨a1, a2⟩ := (hlab i hi').2.2.1 hu
      rw [a1, a2]
      exact ⟨((hw i).2.1 hu).2.2, Or.inl (by simpa using (hw i).1)⟩
    · obtain ⟨a1, a2⟩ := (hlab i hi').2.2.2 (hi'.resolve_left hu)
      rw [a1, a2]
      exact ⟨((hw i).2.2 (hi'.resolve_left hu)).2.2, Or.inr (by simpa using (hw i).1)⟩

end LPPDifferentiability
