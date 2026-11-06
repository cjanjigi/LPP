/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import LPP_Foundations.Frozen.Model.Environment
public import LPP_Foundations.Frozen.Model.Path
public import Differentiability.Model.StairTrappedComponents
public import Differentiability.Model.Paths.GreedyAttachmentSequence
public import LPP_Foundations.Model.Paths.Split
public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Data.Set.Card
import Mathlib.Tactic

/-! # Greedy paths avoiding the trapped vertices (item (ii) of Lemma B.5, forward)

The induction over the levels keeps a chain of forced steps (refused trapped next sites), of
length at most `Ntr` by item (i). `stair_greedy_core` is the deterministic part for any avoided
set; the backward statement reuses it for the reflected set. -/

public section

namespace LPPDifferentiability
open GreedyAttachment (vertex deviation forced preferred alternate)

private abbrev reachSet (ω : Environment) (T : ℝ) (z : Lattice) : Set Lattice :=
  {y | ∃ (d : ℕ × ℕ) (q : Path z d), z + ((d.1 : ℤ), (d.2 : ℤ)) = y ∧
    ∀ i : Fin (d.1 + d.2 + 1), i.val < d.1 + d.2 → -T ≤ ω (q.vertex i)}

private theorem reach_of_vertex (ω : Environment) (T : ℝ) {y w : Lattice} {d : ℕ × ℕ}
    (q : Path y d) (hw : y + ((d.1 : ℤ), (d.2 : ℤ)) = w)
    (hq : ∀ i : Fin (d.1 + d.2 + 1), i.val < d.1 + d.2 → -T ≤ ω (q.vertex i))
    (k : Fin (d.1 + d.2 + 1)) : w ∈ reachSet ω T (q.vertex k) := by
  have hle := q.splitDisplacement_le k
  have h1 := q.splitDisplacement_fst_cast k
  have h2 := q.splitDisplacement_snd_cast k
  refine ⟨d - q.splitDisplacement k, q.suffix k, ?_, fun i hi => ?_⟩
  · rw [← hw]
    apply Prod.ext <;> simp only [Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub,
      Nat.cast_sub hle.1, Nat.cast_sub hle.2] <;> omega
  · have hl := q.suffix_length k
    have hk2 := k.isLt
    exact hq ⟨k.val + i.val, by show k.val + i.val < _; omega⟩ (by show k.val + i.val < _; omega)

private theorem reach_finite_of_succ (ω : Environment) (T : ℝ) (y : Lattice)
    (h1 : (reachSet ω T (y + (1, 0))).Finite) (h2 : (reachSet ω T (y + (0, 1))).Finite) :
    (reachSet ω T y).Finite := by
  refine (((Set.finite_singleton y).union h1).union h2).subset ?_
  rintro w ⟨d, q, hw, hq⟩
  by_cases hd : d.1 + d.2 = 0
  · rw [show d.1 = 0 by omega, show d.2 = 0 by omega] at hw
    exact Or.inl (Or.inl (show w = y by rw [← hw]; apply Prod.ext <;> simp))
  · have hpos : 0 < d.1 + d.2 := Nat.pos_of_ne_zero hd
    have hs := q.step ⟨0, hpos⟩
    rw [show ((⟨0, hpos⟩ : Fin (d.1 + d.2)).castSucc : Fin (d.1 + d.2 + 1)) = 0 from Fin.ext rfl,
      q.start, show (⟨0, hpos⟩ : Fin (d.1 + d.2)).succ = (⟨1, by omega⟩ : Fin (d.1 + d.2 + 1))
        from Fin.ext rfl] at hs
    have hmem := reach_of_vertex ω T q hw hq ⟨1, by omega⟩
    rcases hs with h | h <;> rw [h] at hmem
    · exact Or.inl (Or.inr hmem)
    · exact Or.inr hmem

private theorem reach_finite_of_bad (ω : Environment) (T : ℝ) (x : Lattice) (h : ω x < -T) :
    (reachSet ω T x).Finite := by
  refine (Set.finite_singleton x).subset ?_
  rintro w ⟨d, q, hw, hq⟩
  by_cases hd : d.1 + d.2 = 0
  · rw [show d.1 = 0 by omega, show d.2 = 0 by omega] at hw
    exact show w = x by rw [← hw]; apply Prod.ext <;> simp
  · have h0 := hq ⟨0, by omega⟩ (by show 0 < d.1 + d.2; omega)
    rw [show (⟨0, by omega⟩ : Fin (d.1 + d.2 + 1)) = 0 from Fin.ext rfl, q.start] at h0
    exact absurd h0 (not_le.mpr h)

/-- A unit step `(1, 0)` or `(0, 1)` has `l1` length one. -/
theorem l1_one (y e : Lattice) (he : e = (1, 0) ∨ e = (0, 1)) :
    |(y + e).1 - y.1| + |(y + e).2 - y.2| = 1 := by
  rcases he with rfl | rfl <;> simp
private theorem abs_cand_le (d c : ℝ) (h0 : 0 ≤ c) (h1 : c ≤ 1) :
    |d + c| ≤ |d| + 1 ∧ |d + c - 1| ≤ |d| + 1 := by
  constructor <;> rw [abs_le] <;> constructor <;> linarith [neg_abs_le d, le_abs_self d]
private theorem min_abs_le (d c θ : ℝ) (hθ : 0 < θ) (hc1 : θ ≤ c) (hc2 : c ≤ 1 - θ) :
    min |d + c| |d + c - 1| ≤ max 1 (|d| - θ) := by
  rw [← not_lt]
  intro h
  rw [lt_min_iff] at h
  have m1 := le_max_left 1 (|d| - θ)
  have m2 := le_max_right 1 (|d| - θ)
  rcases abs_cases d with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;>
    rcases abs_cases (d + c) with ⟨e3, e4⟩ | ⟨e3, e4⟩ <;>
    rcases abs_cases (d + c - 1) with ⟨e5, e6⟩ | ⟨e5, e6⟩ <;> linarith [h.1, h.2]

private theorem abs_split_le (A B s q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hs0 : 0 ≤ s)
    (hAB : A + B = s) : |A| + |B| ≤ s + 2 * |A - s * q| := by
  have h1 := mul_nonneg hs0 hq0
  have h2 := mul_nonneg hs0 (sub_nonneg.mpr hq1)
  rcases abs_cases A with ⟨a, a'⟩ | ⟨a, a'⟩ <;> rcases abs_cases B with ⟨b, b'⟩ | ⟨b, b'⟩ <;>
    rcases abs_cases (A - s * q) with ⟨c, c'⟩ | ⟨c, c'⟩ <;> linarith

private theorem l1_le_dev (z v w : Lattice) (q : ℝ) (j j' : ℕ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hjj : j ≤ j') (hv : v.1 + v.2 = z.1 + z.2 + j) (hw : w.1 + w.2 = z.1 + z.2 + j') :
    ((|w.1 - v.1| + |w.2 - v.2| : ℤ) : ℝ) ≤ ((j' : ℝ) - j) +
      2 * |deviation z q j' w - deviation z q j v| := by
  have hs : ((w.1 : ℝ) - v.1) + ((w.2 : ℝ) - v.2) = (j' : ℝ) - j := by
    exact_mod_cast (show (w.1 - v.1) + (w.2 - v.2) = (j' : ℤ) - j by omega)
  have hδ : deviation z q j' w - deviation z q j v =
      ((w.1 : ℝ) - v.1) - ((j' : ℝ) - j) * q := by
    unfold GreedyAttachment.deviation; ring
  have hjr : (j : ℝ) ≤ j' := by exact_mod_cast hjj
  have := abs_split_le ((w.1 : ℝ) - v.1) ((w.2 : ℝ) - v.2) ((j' : ℝ) - j) q hq0 hq1
    (by linarith) hs
  rw [hδ]
  exact_mod_cast this

private theorem pref_alt (u : Lattice) (q : ℝ) (i : ℕ) (x : Lattice) :
    (preferred u q i x = x + (1, 0) ∧ alternate u q i x = x + (0, 1)) ∨
    (preferred u q i x = x + (0, 1) ∧ alternate u q i x = x + (1, 0)) := by
  unfold GreedyAttachment.preferred GreedyAttachment.alternate
  split_ifs <;> first | exact Or.inl ⟨rfl, rfl⟩ | exact Or.inr ⟨rfl, rfl⟩

section Aux

variable (z : Lattice) (q : ℝ) (S : Set Lattice) (i : ℕ)

private noncomputable def pv : Lattice := preferred z q i (vertex z q S i)
private noncomputable def dd : ℝ := deviation z q i (vertex z q S i)
private theorem pv_level :
    (pv z q S i).1 + (pv z q S i).2 = z.1 + z.2 + ((i + 1 : ℕ) : ℤ) := by
  have h1 := GreedyAttachment.candidate_level z (vertex z q S i) q i
  have h2 := GreedyAttachment.level z q S i
  unfold pv
  push_cast
  omega

private theorem alt_notin (hcand : ∀ y, y ∉ S → y + (1, 0) ∉ S ∨ y + (0, 1) ∉ S)
    (hxS : vertex z q S i ∉ S) (hf : forced z q S i) : alternate z q i (vertex z q S i) ∉ S := by
  have hf' : preferred z q i (vertex z q S i) ∈ S := hf
  rcases pref_alt z q i (vertex z q S i) with ⟨h, h'⟩ | ⟨h, h'⟩ <;> rw [h] at hf' <;> rw [h']
  · exact (hcand _ hxS).resolve_left (fun h1 => h1 hf')
  · exact (hcand _ hxS).resolve_right (fun h1 => h1 hf')

private theorem dev_unforced (θ : ℝ) (hθ : 0 < θ) (hqlo : θ ≤ q) (hqhi : q ≤ 1 - θ)
    (hf : ¬ forced z q S i) : |dd z q S (i + 1)| ≤ max 1 (|dd z q S i| - θ) := by
  have hm := min_abs_le (dd z q S i) (1 - q) θ hθ (by linarith) (by linarith)
  unfold dd at hm ⊢
  rw [GreedyAttachment.vertex_succ, ite_eq_right hf, GreedyAttachment.candidate_deviation]
  split_ifs with h
  · rwa [min_eq_left h] at hm
  · rwa [min_eq_right (not_le.mp h).le] at hm

private theorem dev_succ_le (h0 : 0 ≤ q) (h1 : q ≤ 1) :
    |dd z q S (i + 1)| ≤ |dd z q S i| + 1 := by
  have := abs_cand_le (dd z q S i) (1 - q) (by linarith) (by linarith)
  unfold dd at this ⊢
  rw [GreedyAttachment.deviation_step]
  split_ifs <;> first | exact this.1 | exact this.2

private theorem dev_pref_le (h0 : 0 ≤ q) (h1 : q ≤ 1) :
    |deviation z q (i + 1) (pv z q S i)| ≤ |dd z q S i| + 1 := by
  have := abs_cand_le (dd z q S i) (1 - q) (by linarith) (by linarith)
  unfold dd at this ⊢
  unfold pv
  rw [GreedyAttachment.candidate_deviation]
  split_ifs <;> first | exact this.1 | exact this.2

end Aux

-- Forced steps `s t`, `t < m`, in increasing order; consecutive refused next sites are within `D1`.
private abbrev ChainOK (z : Lattice) (q : ℝ) (S : Set Lattice) (Ntr D1 n m : ℕ)
    (s : ℕ → ℕ) : Prop :=
  (∀ t < m, forced z q S (s t) ∧ s t < n) ∧
  (∀ t, 0 < t → t < m → |(pv z q S (s t)).1 - (pv z q S (s (t - 1))).1| +
    |(pv z q S (s t)).2 - (pv z q S (s (t - 1))).2| ≤ (D1 : ℤ)) ∧
  (∀ t t', t < t' → t' < m → s t < s t') ∧
  (0 < m → |deviation z q (s (m - 1) + 1) (pv z q S (s (m - 1)))| ≤ (Ntr : ℝ) + 2)

private theorem chain_zero (z : Lattice) (q : ℝ) (S : Set Lattice) (Ntr D1 n : ℕ) :
    ChainOK z q S Ntr D1 n 0 (fun _ => 0) :=
  ⟨fun t ht => absurd ht (Nat.not_lt_zero t), fun _ _ ht => absurd ht (Nat.not_lt_zero _),
    fun _ t' _ ht => absurd ht (Nat.not_lt_zero t'), fun h => absurd h (lt_irrefl 0)⟩

private theorem chain_len_le (z : Lattice) (q : ℝ) (S C : Set Lattice) (Ntr D1 n m : ℕ)
    (s : ℕ → ℕ) (hC : ∀ i < n, pv z q S i ∈ C)
    (hchain : ¬ ∃ g : Fin (Ntr + 1) → Lattice, Function.Injective g ∧
      (∀ i, g i ∈ C ∧ g i ∈ S) ∧
      ∀ i : Fin (Ntr + 1), 0 < i.val → ∃ j : Fin (Ntr + 1), j.val < i.val ∧
        |(g i).1 - (g j).1| + |(g i).2 - (g j).2| ≤ (D1 : ℤ))
    (h : ChainOK z q S Ntr D1 n m s) : m ≤ Ntr := by
  by_contra hm
  have hm := not_le.mp hm
  obtain ⟨h1, h3, h4, -⟩ := h
  refine hchain ⟨fun i => pv z q S (s i.val), ?_, fun i => ?_, fun i hi => ?_⟩
  · intro i j hij
    have hs := GreedyAttachment.preferred_injective z q S (show preferred z q (s i.val)
      (vertex z q S (s i.val)) = preferred z q (s j.val) (vertex z q S (s j.val)) from hij)
    have hi := i.isLt
    have hj := j.isLt
    by_contra hne
    rcases lt_or_gt_of_ne (fun h => hne (Fin.ext h) : i.val ≠ j.val) with hlt | hlt
    · have := h4 i.val j.val hlt (by omega)
      omega
    · have := h4 j.val i.val hlt (by omega)
      omega
  · have hi := i.isLt
    exact ⟨hC _ (h1 i.val (by omega)).2, (h1 i.val (by omega)).1⟩
  · have hi' := i.isLt
    exact ⟨⟨i.val - 1, by omega⟩, by show i.val - 1 < i.val; omega, h3 i.val hi (by omega)⟩

/-- **Deterministic core of item (ii) of Lemma B.5.** `S` is the avoided set, `P` the region of
the path, `C` a set containing both possible next sites of every site of `P`. If every site outside
`S` has a possible next site outside `S`, and no chain of `Ntr + 1` sites of `C ∩ S`, each within
`D1` of an earlier one, exists, the greedy path avoids `S` and stays within `Ntr + 1` of the line.
Only sites `0..n-1` need lie in `P`. -/
theorem stair_greedy_core (θ q : ℝ) (Ntr D1 : ℕ) (S P C : Set Lattice) (z : Lattice)
    (hθ : 0 < θ) (hqlo : θ ≤ q) (hqhi : q ≤ 1 - θ) (hNtr : 1 ≤ Ntr)
    (hD1 : ⌊2 * ((Ntr + 1 : ℕ) : ℝ) / θ⌋₊ + 4 * (Ntr + 1) + 8 ≤ D1)
    (hPC : ∀ y ∈ P, y + (1, 0) ∈ C ∧ y + (0, 1) ∈ C)
    (hcand : ∀ y, y ∉ S → y + (1, 0) ∉ S ∨ y + (0, 1) ∉ S)
    (hchain : ¬ ∃ g : Fin (Ntr + 1) → Lattice, Function.Injective g ∧
      (∀ i, g i ∈ C ∧ g i ∈ S) ∧
      ∀ i : Fin (Ntr + 1), 0 < i.val → ∃ j : Fin (Ntr + 1), j.val < i.val ∧
        |(g i).1 - (g j).1| + |(g i).2 - (g j).2| ≤ (D1 : ℤ))
    (hz : z ∉ S) (n : ℕ) (hP : ∀ i, i < n → GreedyAttachment.vertex z q S i ∈ P) :
    ∀ i, i ≤ n → GreedyAttachment.vertex z q S i ∉ S ∧
      |GreedyAttachment.deviation z q i (GreedyAttachment.vertex z q S i)| ≤
        ((Ntr + 1 : ℕ) : ℝ) := by
  have hq0 : 0 ≤ q := by linarith
  have hq1 : q ≤ 1 := by linarith
  have hC : ∀ i < n, pv z q S i ∈ C := by
    intro i hi
    have := hPC _ (hP i hi)
    unfold pv
    rcases pref_alt z q i (vertex z q S i) with ⟨h, -⟩ | ⟨h, -⟩
    · rw [h]; exact this.1
    · rw [h]; exact this.2
  have key : ∀ i, i ≤ n → vertex z q S i ∉ S ∧ ∃ (m : ℕ) (s : ℕ → ℕ),
      m ≤ Ntr ∧ ChainOK z q S Ntr D1 n m s ∧
      (|dd z q S i| ≤ 1 ∨ (0 < m ∧ s (m - 1) + 1 ≤ i ∧
        |dd z q S i| ≤ 1 + (m : ℝ) - θ * ((i : ℝ) - ((s (m - 1) + 1 : ℕ) : ℝ)))) := by
    intro i
    induction i with
    | zero =>
      intro _
      refine ⟨hz, 0, fun _ => 0, Nat.zero_le _, chain_zero z q S Ntr D1 n, Or.inl ?_⟩
      simp [dd, GreedyAttachment.deviation]
    | succ i ih =>
      intro hi
      obtain ⟨hxS, m, s, hm, hch, hinv⟩ := ih (by omega)
      have hin : i < n := by omega
      by_cases hf : forced z q S i
      · have hv : vertex z q S (i + 1) = alternate z q i (vertex z q S i) := by
          rw [GreedyAttachment.vertex_succ, ite_eq_left hf]
        refine ⟨by rw [hv]; exact alt_notin z q S i hcand hxS hf, ?_⟩
        have hsucc := dev_succ_le z q S i hq0 hq1
        have hpd := dev_pref_le z q S i hq0 hq1
        have hN0 : (0 : ℝ) ≤ Ntr := Nat.cast_nonneg Ntr
        by_cases h1 : |dd z q S i| ≤ 1
        · refine ⟨1, fun _ => i, hNtr, ⟨fun t _ => ⟨hf, hin⟩,
            fun t h0 ht => absurd h0 (by omega), fun t t' h h' => absurd h' (by omega),
            fun _ => ?_⟩, Or.inr ⟨one_pos, le_rfl, ?_⟩⟩
          · show |deviation z q (i + 1) (pv z q S i)| ≤ (Ntr : ℝ) + 2
            linarith
          · show _ ≤ 1 + ((1 : ℕ) : ℝ) - θ * (((i + 1 : ℕ) : ℝ) - ((i + 1 : ℕ) : ℝ))
            linarith [(Nat.cast_one : ((1 : ℕ) : ℝ) = 1)]
        · rcases hinv with h | ⟨hm0, ha, hb⟩
          · exact absurd h h1
          have h1' := not_le.mp h1
          have hm' : (m : ℝ) ≤ Ntr := by exact_mod_cast hm
          have hnn : 0 ≤ θ * ((i : ℝ) - ((s (m - 1) + 1 : ℕ) : ℝ)) :=
            mul_nonneg hθ.le (sub_nonneg.mpr (by exact_mod_cast ha))
          have hdW : |dd z q S i| ≤ (Ntr : ℝ) + 1 := by linarith
          have hdist : |(pv z q S i).1 - (pv z q S (s (m - 1))).1| +
              |(pv z q S i).2 - (pv z q S (s (m - 1))).2| ≤ (D1 : ℤ) := by
            have hl := l1_le_dev z (pv z q S (s (m - 1))) (pv z q S i) q (s (m - 1) + 1) (i + 1)
              hq0 hq1 (by omega) (pv_level z q S (s (m - 1))) (pv_level z q S i)
            have hdv := hch.2.2.2 hm0
            have hdw : |deviation z q (i + 1) (pv z q S i)| ≤ (Ntr : ℝ) + 2 := by linarith
            have hdd : |deviation z q (i + 1) (pv z q S i) -
                deviation z q (s (m - 1) + 1) (pv z q S (s (m - 1)))| ≤ 2 * ((Ntr : ℝ) + 2) := by
              rw [abs_le] at hdw hdv ⊢
              constructor <;> linarith [hdw.1, hdw.2, hdv.1, hdv.2]
            have hsub : s (m - 1) ≤ i := by omega
            have hgN : (((i + 1 : ℕ) : ℝ) - ((s (m - 1) + 1 : ℕ) : ℝ)) =
                ((i - s (m - 1) : ℕ) : ℝ) := by
              rw [Nat.cast_sub hsub]; push_cast; ring
            have hNr : ((i - s (m - 1) : ℕ) : ℝ) ≤ (⌊2 * ((Ntr + 1 : ℕ) : ℝ) / θ⌋₊ : ℝ) :=
              Nat.cast_le.mpr (Nat.le_floor (by
                rw [le_div_iff₀ hθ, Nat.cast_sub hsub]
                push_cast at hb ⊢
                linarith))
            have hD1r : ((⌊2 * ((Ntr + 1 : ℕ) : ℝ) / θ⌋₊ : ℕ) : ℝ) + 4 * ((Ntr : ℝ) + 1) + 8 ≤
                (D1 : ℝ) := by exact_mod_cast hD1
            exact_mod_cast hl.trans (show _ ≤ (D1 : ℝ) by linarith)
          obtain ⟨s', hs'lt, hs'm⟩ : ∃ s' : ℕ → ℕ, (∀ t < m, s' t = s t) ∧ s' m = i :=
            ⟨fun t => if t < m then s t else i, fun t ht => ite_eq_left ht,
              ite_eq_right (lt_irrefl m)⟩
          have hm1 : m + 1 - 1 = m := by omega
          have hch' : ChainOK z q S Ntr D1 n (m + 1) s' := by
            refine ⟨fun t ht => ?_, fun t h0 ht => ?_, fun t t' htt ht' => ?_, fun _ => ?_⟩
            · by_cases h : t < m
              · rw [hs'lt t h]; exact hch.1 t h
              · rw [show t = m by omega, hs'm]; exact ⟨hf, hin⟩
            · by_cases h : t < m
              · rw [hs'lt t h, hs'lt (t - 1) (by omega)]; exact hch.2.1 t h0 h
              · rw [show t = m by omega, hs'm, hs'lt (m - 1) (by omega)]; exact hdist
            · by_cases h : t' < m
              · rw [hs'lt t (by omega), hs'lt t' h]; exact hch.2.2.1 t t' htt h
              · have hle : s t ≤ s (m - 1) := by
                  rcases Nat.lt_or_ge t (m - 1) with h2 | h2
                  · exact (hch.2.2.1 t (m - 1) h2 (by omega)).le
                  · rw [show t = m - 1 by omega]
                rw [show t' = m by omega, hs'm, hs'lt t (by omega)]; omega
            · rw [hm1, hs'm]
              linarith
          have hm2 : m + 1 ≤ Ntr := chain_len_le z q S C Ntr D1 n (m + 1) s' hC hchain hch'
          refine ⟨m + 1, s', hm2, hch', Or.inr ⟨Nat.succ_pos m, ?_, ?_⟩⟩
          · rw [hm1, hs'm]
          · rw [hm1, hs'm]
            push_cast
            linarith
      · have hv : vertex z q S (i + 1) = preferred z q i (vertex z q S i) := by
          rw [GreedyAttachment.vertex_succ, ite_eq_right hf]
        refine ⟨by rw [hv]; exact hf, ?_⟩
        have hdev := dev_unforced z q S i θ hθ hqlo hqhi hf
        by_cases h1 : |dd z q S (i + 1)| ≤ 1
        · exact ⟨0, fun _ => 0, Nat.zero_le _, chain_zero z q S Ntr D1 n, Or.inl h1⟩
        · have h1' := not_le.mp h1
          have hdd := (le_max_iff.mp hdev).resolve_left h1
          rcases hinv with h | ⟨hm0, ha, hb⟩
          · exfalso
            linarith
          · refine ⟨m, s, hm, hch, Or.inr ⟨hm0, by omega, ?_⟩⟩
            have e2 : θ * (((i + 1 : ℕ) : ℝ) - ((s (m - 1) + 1 : ℕ) : ℝ)) =
                θ * ((i : ℝ) - ((s (m - 1) + 1 : ℕ) : ℝ)) + θ := by push_cast; ring
            linarith
  intro i hi
  obtain ⟨hxS, m, s, hm, -, hinv⟩ := key i hi
  refine ⟨hxS, ?_⟩
  show |dd z q S i| ≤ _
  have hm' : (m : ℝ) ≤ Ntr := by exact_mod_cast hm
  have hN0 : (0 : ℝ) ≤ Ntr := Nat.cast_nonneg Ntr
  rcases hinv with h | ⟨-, ha, hb⟩
  · push_cast; linarith
  · have hnn : 0 ≤ θ * ((i : ℝ) - ((s (m - 1) + 1 : ℕ) : ℝ)) :=
      mul_nonneg hθ.le (sub_nonneg.mpr (by exact_mod_cast ha))
    push_cast; linarith

/-- **Forward greedy path** (item (ii) of Lemma B.5). -/
theorem stair_greedy_forward (ω : Environment) (T θ₁ : ℝ) (m1 K1 : ℕ) (Q : Set Lattice) :
  let reach : Environment → ℝ → Lattice → Set Lattice := fun ω T z =>
    {y | ∃ (d : ℕ × ℕ) (q : Path z d), z + ((d.1 : ℤ), (d.2 : ℤ)) = y ∧
      ∀ i : Fin (d.1 + d.2 + 1), i.val < d.1 + d.2 → -T ≤ ω (q.vertex i)}
  let reachBack : Environment → ℝ → Lattice → Set Lattice := fun ω T z =>
    {y | ∃ (d : ℕ × ℕ) (q : Path y d), y + ((d.1 : ℤ), (d.2 : ℤ)) = z ∧
      ∀ i : Fin (d.1 + d.2 + 1), i.val < d.1 + d.2 → -T ≤ ω (q.vertex i)}
  let Ntr : ℕ := K1 * (2 * m1 ^ 2 + 1) ^ 2
  let W0 : ℕ := Ntr + 1
  let L : ℕ := ⌈4 * ((W0 : ℝ) + 2) / θ₁⌉₊
  let r0 : ℕ := K1 * (2 * L + 1) + Ntr
  let D1 : ℕ := ⌊2 * (W0 : ℝ) / θ₁⌋₊ + 4 * W0 + 2 * r0 + 2 * L + 8
  let d0 : ℕ := D1 + 2 * m1 ^ 2
  let c0 : ℕ := W0 + 2 * L + 1
  let collar : Set Lattice → ℕ → Set Lattice := fun Q c =>
    {z | ∃ y ∈ Q, |z.1 - y.1| + |z.2 - y.2| ≤ (c : ℤ)}
  let Egeo : Environment → ℝ → Set Lattice → Prop := fun ω T Q =>
    (¬ ∃ f : Fin (K1 + 1) → Lattice, Function.Injective f ∧
        (∀ i, f i ∈ collar Q (c0 + m1 ^ 2) ∧ ω (f i) < -T) ∧
        ∀ i : Fin (K1 + 1), 0 < i.val → ∃ j : Fin (K1 + 1), j.val < i.val ∧
          |(f i).1 - (f j).1| + |(f i).2 - (f j).2| ≤ d0) ∧
    ∀ z ∈ collar Q c0,
      ((reach ω T z).Finite → (reach ω T z).ncard < m1 ^ 2) ∧
      ((reachBack ω T z).Finite → (reachBack ω T z).ncard < m1 ^ 2)
  0 < θ₁ → θ₁ ≤ 1 / 10 → 1 ≤ m1 → 1 ≤ K1 → Egeo ω T Q →
  ∀ z ∈ Q, ¬ (reach ω T z).Finite → ∀ q : ℝ, θ₁ ≤ q → q ≤ 1 - θ₁ → ∀ n : ℕ,
    (∀ i, i ≤ n → GreedyAttachment.vertex z q {y | (reach ω T y).Finite} i ∈ Q) →
    ∀ i, i ≤ n →
      ¬ (reach ω T (GreedyAttachment.vertex z q {y | (reach ω T y).Finite} i)).Finite ∧
      -T ≤ ω (GreedyAttachment.vertex z q {y | (reach ω T y).Finite} i) ∧
      |GreedyAttachment.deviation z q i
        (GreedyAttachment.vertex z q {y | (reach ω T y).Finite} i)| ≤ (W0 : ℝ) := by
  intro reach reachBack Ntr W0 L r0 D1 d0 c0 collar Egeo hθ hθ' hm hK hE z _ hz q hq1 hq2 n hQ i hi
  have hNtr : 1 ≤ Ntr := Nat.mul_pos hK (by positivity)
  have hc0 : 1 ≤ c0 := by show 1 ≤ W0 + 2 * L + 1; omega
  have hD1 : ⌊2 * ((Ntr + 1 : ℕ) : ℝ) / θ₁⌋₊ + 4 * (Ntr + 1) + 8 ≤ D1 := by
    show _ ≤ ⌊2 * ((Ntr + 1 : ℕ) : ℝ) / θ₁⌋₊ + 4 * (Ntr + 1) + 2 * r0 + 2 * L + 8
    omega
  have hPC : ∀ y ∈ Q, y + (1, 0) ∈ collar Q c0 ∧ y + (0, 1) ∈ collar Q c0 := fun y hy =>
    ⟨⟨y, hy, by rw [l1_one y _ (Or.inl rfl)]; exact_mod_cast hc0⟩,
      ⟨y, hy, by rw [l1_one y _ (Or.inr rfl)]; exact_mod_cast hc0⟩⟩
  have hcand : ∀ y : Lattice, y ∉ {y | (reach ω T y).Finite} →
      y + (1, 0) ∉ {y | (reach ω T y).Finite} ∨ y + (0, 1) ∉ {y | (reach ω T y).Finite} := by
    intro y hy
    by_contra hcon
    have hcon' := not_or.mp hcon
    exact hy (reach_finite_of_succ ω T y (not_not.mp hcon'.1) (not_not.mp hcon'.2))
  have hcore := stair_greedy_core θ₁ q Ntr D1 {y | (reach ω T y).Finite} Q (collar Q c0) z hθ hq1
    hq2 hNtr hD1 hPC hcand (stair_trapped_components_le ω T θ₁ m1 K1 Q hθ hθ' hm hK hE).1 hz n
    (fun j hj => hQ j hj.le) i hi
  refine ⟨hcore.1, ?_, hcore.2⟩
  by_contra h
  exact hcore.1 (reach_finite_of_bad ω T _ (not_le.mp h))

end LPPDifferentiability
