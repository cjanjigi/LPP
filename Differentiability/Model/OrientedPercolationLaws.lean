/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Differentiability.Model.OrientedPercolation
public import LPP_Foundations.Frozen.Model.LastPassage
import LPP_Foundations.Model.LastPassage.Basic
import LPP_Foundations.Model.Paths.Concat
import LPP_Foundations.Model.Paths.Geometry
import LPP_Foundations.Model.Paths.Level
import LPP_Foundations.Model.Paths.Nonempty
import LPP_Foundations.Model.Paths.Split
import LPP_Foundations.Model.Paths.Translate
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic.Linarith

/-!
# Laws of the oriented-percolation interface

Elementary laws for open paths, reachable sets, the integer edge `maxFirst`, and the
relation between open paths and last-passage times of the 0/1 top field. The
definitions are in the module `OrientedPercolation`.

The edge `openEdge` takes the value `0` when the reachable set is empty or unbounded
above (Mathlib's convention for `sSup` on `ℤ`), so the edge laws that need an actual
maximum take nonemptiness and boundedness as explicit hypotheses.
-/

@[expose] public section

namespace LPPDifferentiability

open Set

/-! ## Private helpers -/

/-- Openness of a path, stated at the vertex indices other than the start. -/
private theorem open_iff {O : Set Lattice} {u : Lattice} {d : ℕ × ℕ} (p : Path u d) :
    (∀ i : Fin (d.1 + d.2), p.vertex i.succ ∈ O) ↔
      ∀ i : Fin (d.1 + d.2 + 1), i.val ≠ 0 → p.vertex i ∈ O := by
  constructor
  · intro h i hi
    induction i using Fin.cases with
    | zero => simp at hi
    | succ j => exact h j
  · intro h i
    exact h i.succ (by simp)

/-- Concatenating two paths whose non-start vertices lie in `O` gives such a path. -/
private theorem concat_vertex_mem {O : Set Lattice} {u : Lattice} {d e : ℕ × ℕ}
    (p : Path u d) (q : Path (u + ((d.1 : ℤ), (d.2 : ℤ))) e)
    (hp : ∀ i : Fin (d.1 + d.2 + 1), i.val ≠ 0 → p.vertex i ∈ O)
    (hq : ∀ i : Fin (e.1 + e.2 + 1), i.val ≠ 0 → q.vertex i ∈ O) :
    ∀ i : Fin ((d + e).1 + (d + e).2 + 1), i.val ≠ 0 → (p.concat q).vertex i ∈ O := by
  intro i hi
  have hlt := i.isLt
  simp only [Prod.fst_add, Prod.snd_add] at hlt
  by_cases h : i.val ≤ d.1 + d.2
  · have e1 : (p.concat q).vertex i = p.vertex ⟨i.val, by omega⟩ :=
      Path.concat_vertex_left p q ⟨i.val, by omega⟩
    rw [e1]
    exact hp _ hi
  · show Path.concatVertex p q i ∈ O
    unfold Path.concatVertex
    have hn : ¬ i.val < d.1 + d.2 := by omega
    rw [dite_eq_right hn]
    exact hq _ (by show i.val - (d.1 + d.2) ≠ 0; omega)

/-- One direction of locality: an open set that agrees with another on the relevant
levels gives reachable sets contained in the other's. -/
private theorem openReachSet_subset_of_levels {O O' S : Set Lattice} (m : ℤ) (n : ℕ)
    (hS : S ⊆ levelSet m)
    (hOO' : ∀ z : Lattice, m < z.1 + z.2 → z.1 + z.2 ≤ m + n → z ∈ O → z ∈ O') :
    openReachSet O S n ⊆ openReachSet O' S n := by
  rintro v ⟨u, hu, ⟨d, hd, p, hp⟩, hl⟩
  have hu' : u.1 + u.2 = m := hS hu
  have h1 := congrArg Prod.fst hd
  have h2 := congrArg Prod.snd hd
  simp only [Prod.fst_add, Prod.snd_add] at h1 h2
  refine ⟨u, hu, ⟨d, hd, p, fun i => ?_⟩, hl⟩
  have hlev : (p.vertex i.succ).1 + (p.vertex i.succ).2 = u.1 + u.2 + ((i.succ.val : ℕ) : ℤ) :=
    p.level i.succ
  rw [Fin.val_succ] at hlev
  push_cast at hlev
  have hi := i.isLt
  exact hOO' _ (by omega) (by omega) (hp i)

/-! ## Further laws -/

theorem openReachSet_zero (O S : Set Lattice) : openReachSet O S 0 = S := by
  ext v
  constructor
  · rintro ⟨u, hu, ⟨d, hd, -⟩, hl⟩
    have h1 := congrArg Prod.fst hd
    have h2 := congrArg Prod.snd hd
    simp only [Prod.fst_add, Prod.snd_add] at h1 h2
    have hv : v = u := Prod.ext (by omega) (by omega)
    rw [hv]
    exact hu
  · intro hv
    refine ⟨v, hv, ⟨(0, 0), ?_, Classical.choice (pathNonempty v (0, 0)), fun i => ?_⟩, ?_⟩
    · ext <;> simp
    · exact absurd i.isLt (by simp)
    · simp

theorem openReachSet_add (O S : Set Lattice) (n k : ℕ) :
    openReachSet O (openReachSet O S n) k = openReachSet O S (n + k) := by
  ext v
  constructor
  · rintro ⟨w, ⟨u, hu, hr1, hl1⟩, hr2, hl2⟩
    obtain ⟨d, hd, p, hp⟩ := hr1
    obtain ⟨e, he, q, hq⟩ := hr2
    subst hd
    have h1 := congrArg Prod.fst he
    have h2 := congrArg Prod.snd he
    simp only [Prod.fst_add, Prod.snd_add] at h1 h2 hl1 hl2
    refine ⟨u, hu, ⟨d + e, ?_, p.concat q, ?_⟩, ?_⟩
    · exact Prod.ext (by simp only [Prod.fst_add, Prod.snd_add, Nat.cast_add]; omega)
        (by simp only [Prod.fst_add, Prod.snd_add, Nat.cast_add]; omega)
    · exact (open_iff (p.concat q)).2
        (concat_vertex_mem p q ((open_iff p).1 hp) ((open_iff q).1 hq))
    · push_cast
      omega
  · rintro ⟨u, hu, ⟨d, hd, p, hp⟩, hl⟩
    have h1 := congrArg Prod.fst hd
    have h2 := congrArg Prod.snd hd
    simp only [Prod.fst_add, Prod.snd_add] at h1 h2
    push_cast at hl
    have hlen : d.1 + d.2 = n + k := by omega
    have hk : n < d.1 + d.2 + 1 := by omega
    obtain ⟨kk, hkk⟩ : ∃ kk : Fin (d.1 + d.2 + 1), kk.val = n := ⟨⟨n, hk⟩, rfl⟩
    have hp' := (open_iff p).1 hp
    have hlev : (p.vertex kk).1 + (p.vertex kk).2 = u.1 + u.2 + ((kk.val : ℕ) : ℤ) :=
      p.level kk
    rw [hkk] at hlev
    have hle := p.splitDisplacement_le kk
    refine ⟨p.vertex kk, ⟨u, hu, ⟨p.splitDisplacement kk, (p.split_vertex kk).symm,
      p.prefixPath kk, fun i => ?_⟩, hlev⟩, ⟨d - p.splitDisplacement kk, ?_, p.suffix kk,
      fun i => ?_⟩, ?_⟩
    · exact hp' _ (by show i.succ.val ≠ 0; simp)
    · rw [p.split_vertex kk, ← hd]
      apply Prod.ext <;>
        simp only [Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub,
          Nat.cast_sub hle.1, Nat.cast_sub hle.2] <;> omega
    · exact hp' _ (by show kk.val + i.succ.val ≠ 0; simp only [Fin.val_succ]; omega)
    · omega

theorem openReachSet_mono {O O' S S' : Set Lattice} (hO : O ⊆ O') (hS : S ⊆ S') (n : ℕ) :
    openReachSet O S n ⊆ openReachSet O' S' n := by
  rintro v ⟨u, hu, ⟨d, hd, p, hp⟩, hl⟩
  exact ⟨u, hS hu, ⟨d, hd, p, fun i => hO (hp i)⟩, hl⟩

theorem openReachSet_union (O S S' : Set Lattice) (n : ℕ) :
    openReachSet O (S ∪ S') n = openReachSet O S n ∪ openReachSet O S' n := by
  ext v
  constructor
  · rintro ⟨u, hu | hu, h⟩
    · exact Or.inl ⟨u, hu, h⟩
    · exact Or.inr ⟨u, hu, h⟩
  · rintro (⟨u, hu, h⟩ | ⟨u, hu, h⟩)
    · exact ⟨u, Or.inl hu, h⟩
    · exact ⟨u, Or.inr hu, h⟩

theorem mem_openReachSet_translate (O S : Set Lattice) (t v : Lattice) (n : ℕ) :
    v ∈ openReachSet ((fun z => t + z) ⁻¹' O) S n ↔
      t + v ∈ openReachSet O ((fun z => t + z) '' S) n := by
  constructor
  · rintro ⟨u, hu, ⟨d, hd, p, hp⟩, hl⟩
    refine ⟨t + u, ⟨u, hu, rfl⟩, ⟨d, ?_, p.translate t, fun i => hp i⟩, ?_⟩
    · rw [add_assoc, hd]
    · simp only [Prod.fst_add, Prod.snd_add] at hl ⊢
      omega
  · rintro ⟨w, ⟨u, hu, hw⟩, ⟨d, hd, p, hp⟩, hl⟩
    have hw' : w = t + u := hw.symm
    subst hw'
    refine ⟨u, hu, ⟨d, ?_, Path.untranslate t p, fun i => ?_⟩, ?_⟩
    · rw [add_assoc] at hd
      exact add_left_cancel hd
    · show t + (-t + p.vertex i.succ) ∈ O
      rw [add_neg_cancel_left]
      exact hp i
    · simp only [Prod.fst_add, Prod.snd_add] at hl
      omega

theorem openReachSet_congr (O O' S : Set Lattice) (m : ℤ) (n : ℕ)
    (hS : S ⊆ levelSet m)
    (hOO' : ∀ z : Lattice, m < z.1 + z.2 → z.1 + z.2 ≤ m + n → (z ∈ O ↔ z ∈ O')) :
    openReachSet O S n = openReachSet O' S n :=
  Set.Subset.antisymm
    (openReachSet_subset_of_levels m n hS (fun z h1 h2 h => (hOO' z h1 h2).1 h))
    (openReachSet_subset_of_levels m n hS (fun z h1 h2 h => (hOO' z h1 h2).2 h))

theorem openReachSet_subset_levelSet (O S : Set Lattice) (m : ℤ) (n : ℕ)
    (hS : S ⊆ levelSet m) : openReachSet O S n ⊆ levelSet (m + n) := by
  rintro v ⟨u, hu, -, hl⟩
  have h : u.1 + u.2 = m := hS hu
  show v.1 + v.2 = m + n
  omega

theorem exists_le_of_mem_openReachSet (O S : Set Lattice) (n : ℕ) (v : Lattice)
    (hv : v ∈ openReachSet O S n) : ∃ u ∈ S, u ≤ v ∧ OpenReach O u v := by
  obtain ⟨u, hu, h, -⟩ := hv
  obtain ⟨d, hd, -⟩ := id h
  have h1 := congrArg Prod.fst hd
  have h2 := congrArg Prod.snd hd
  simp only [Prod.fst_add, Prod.snd_add] at h1 h2
  exact ⟨u, hu, ⟨by omega, by omega⟩, h⟩

theorem bddAbove_fst_openReachSet (O S : Set Lattice) (n : ℕ) (b : ℤ)
    (hS : ∀ u ∈ S, u.1 ≤ b) : ∀ v ∈ openReachSet O S n, v.1 ≤ b + n := by
  intro v hv
  obtain ⟨u, hu, ⟨d, hd, -⟩, hl⟩ := hv
  have h1 := congrArg Prod.fst hd
  have h2 := congrArg Prod.snd hd
  simp only [Prod.fst_add, Prod.snd_add] at h1 h2
  have := hS u hu
  omega

theorem maxFirst_mem (X : Set Lattice) (hX : X.Nonempty) (hb : BddAbove (Prod.fst '' X)) :
    ∃ v ∈ X, v.1 = maxFirst X := by
  obtain ⟨v, hv, hvv⟩ := Int.csSup_mem (hX.image Prod.fst) hb
  exact ⟨v, hv, hvv⟩

theorem le_maxFirst (X : Set Lattice) (hb : BddAbove (Prod.fst '' X)) {v : Lattice}
    (hv : v ∈ X) : v.1 ≤ maxFirst X := by
  unfold maxFirst
  exact le_csSup hb (Set.mem_image_of_mem Prod.fst hv)

theorem halfLineEdge_le (ω : Environment) (n : ℕ) : halfLineEdge ω n ≤ n := by
  unfold halfLineEdge openEdge maxFirst
  by_cases hne : (Prod.fst '' openReachSet (topSites ω) antidiagHalfLine n).Nonempty
  · refine csSup_le hne ?_
    rintro _ ⟨v, hv, rfl⟩
    have := bddAbove_fst_openReachSet (topSites ω) antidiagHalfLine n 0
      (fun u hu => (show u.1 + u.2 = 0 ∧ u.1 ≤ 0 from hu).2) v hv
    omega
  · rw [Set.not_nonempty_iff_eq_empty] at hne
    rw [hne, Int.csSup_empty]
    omega

theorem antidiagHalfLine_union_rightBlock (m : ℕ) :
    antidiagHalfLine ∪ antidiagRightBlock m =
      (fun z => ((m : ℤ), -(m : ℤ)) + z) '' antidiagHalfLine := by
  ext z
  constructor
  · intro h
    have key : z.1 + z.2 = 0 ∧ z.1 ≤ m := by
      rcases h with h | h
      · have h' : z.1 + z.2 = 0 ∧ z.1 ≤ 0 := h
        omega
      · have h' : z.1 + z.2 = 0 ∧ 1 ≤ z.1 ∧ z.1 ≤ m := h
        omega
    refine ⟨(z.1 - m, z.2 + m), ?_, ?_⟩
    · show z.1 - m + (z.2 + m) = 0 ∧ z.1 - m ≤ 0
      omega
    · exact Prod.ext (by show (m : ℤ) + (z.1 - m) = z.1; omega)
        (by show -(m : ℤ) + (z.2 + m) = z.2; omega)
  · rintro ⟨a, ha, haz⟩
    have ha' : a.1 + a.2 = 0 ∧ a.1 ≤ 0 := ha
    have h1 := congrArg Prod.fst haz
    have h2 := congrArg Prod.snd haz
    simp only [Prod.fst_add, Prod.snd_add] at h1 h2
    by_cases hz : z.1 ≤ 0
    · exact Or.inl (show z.1 + z.2 = 0 ∧ z.1 ≤ 0 from ⟨by omega, hz⟩)
    · exact Or.inr (show z.1 + z.2 = 0 ∧ 1 ≤ z.1 ∧ z.1 ≤ m from
        ⟨by omega, by omega, by omega⟩)

theorem openEdge_translate (ω : Environment) (S : Set Lattice) (t : Lattice) (n : ℕ)
    (hne : (openReachSet (topSites ω) ((fun z => t + z) '' S) n).Nonempty)
    (hb : BddAbove (Prod.fst '' S)) :
    openEdge (topSites ω) ((fun z => t + z) '' S) n =
      t.1 + openEdge (topSites (fun z => ω (t + z))) S n := by
  have key : ∀ v, v ∈ openReachSet (topSites fun z => ω (t + z)) S n ↔
      t + v ∈ openReachSet (topSites ω) ((fun z => t + z) '' S) n :=
    fun v => mem_openReachSet_translate (topSites ω) S t v n
  obtain ⟨b, hb'⟩ := hb
  have hbX : BddAbove (Prod.fst '' openReachSet (topSites ω) ((fun z => t + z) '' S) n) := by
    refine ⟨t.1 + b + n, ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    refine bddAbove_fst_openReachSet _ _ n (t.1 + b) ?_ x hx
    rintro _ ⟨s, hs, rfl⟩
    have := hb' (Set.mem_image_of_mem Prod.fst hs)
    simp only [Prod.fst_add]
    omega
  have hbX' : BddAbove (Prod.fst '' openReachSet (topSites fun z => ω (t + z)) S n) := by
    refine ⟨b + n, ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    exact bddAbove_fst_openReachSet _ S n b (fun u hu => hb' (Set.mem_image_of_mem Prod.fst hu)) x hx
  obtain ⟨x, hx⟩ := hne
  have hX' : (openReachSet (topSites fun z => ω (t + z)) S n).Nonempty :=
    ⟨-t + x, (key (-t + x)).2 (by rw [add_neg_cancel_left]; exact hx)⟩
  unfold openEdge
  apply le_antisymm
  · obtain ⟨v, hv, hvv⟩ := maxFirst_mem _ (Set.nonempty_of_mem hx) hbX
    have h1 : -t + v ∈ openReachSet (topSites fun z => ω (t + z)) S n :=
      (key (-t + v)).2 (by rw [add_neg_cancel_left]; exact hv)
    have h2 := le_maxFirst _ hbX' h1
    simp only [Prod.fst_add, Prod.fst_neg] at h2
    omega
  · obtain ⟨v, hv, hvv⟩ := maxFirst_mem _ hX' hbX'
    have h2 := le_maxFirst _ hbX ((key v).1 hv)
    simp only [Prod.fst_add] at h2
    omega

/-- Exact passage-time convention identity. -/
theorem excludedStart_weight_eq (ω : Environment) {u : Lattice} {d : ℕ × ℕ} (p : Path u d) :
    (∑ i : Fin (d.1 + d.2), ω (p.vertex i.succ)) =
      pathWeight ω p - ω u + ω (u + ((d.1 : ℤ), (d.2 : ℤ))) := by
  have h1 : ∑ i : Fin (d.1 + d.2 + 1), ω (p.vertex i) =
      ω (p.vertex 0) + ∑ i : Fin (d.1 + d.2), ω (p.vertex i.succ) := Fin.sum_univ_succ _
  have h2 : ∑ i : Fin (d.1 + d.2 + 1), ω (p.vertex i) =
      ∑ i : Fin (d.1 + d.2), ω (p.vertex i.castSucc) + ω (p.vertex (Fin.last (d.1 + d.2))) :=
    Fin.sum_univ_castSucc _
  rw [p.start] at h1
  rw [p.finish] at h2
  unfold pathWeight
  linarith

theorem excludedStart_le_and_attained (ω : Environment) (u : Lattice) (d : ℕ × ℕ) :
    (∀ p : Path u d, (∑ i : Fin (d.1 + d.2), ω (p.vertex i.succ)) ≤
      lastPassage ω u d - ω u + ω (u + ((d.1 : ℤ), (d.2 : ℤ)))) ∧
    ∃ p : Path u d, (∑ i : Fin (d.1 + d.2), ω (p.vertex i.succ)) =
      lastPassage ω u d - ω u + ω (u + ((d.1 : ℤ), (d.2 : ℤ))) := by
  constructor
  · intro p
    have h := pathWeight_le_lastPassage ω p
    rw [excludedStart_weight_eq ω p]
    linarith
  · obtain ⟨p, hp⟩ := exists_pathWeight_eq_lastPassage ω u d
    exact ⟨p, by rw [excludedStart_weight_eq ω p, hp]⟩

/-- A 0/1 top field value is at most one. -/
private theorem topField_le_one (ω : Environment) (z : Lattice) : topField ω z ≤ 1 := by
  by_cases h : ω z = 1 <;> simp [topField, h]

/-- The top field takes the value one exactly at the top sites. -/
private theorem topField_eq_one_iff (ω : Environment) (z : Lattice) :
    topField ω z = 1 ↔ ω z = 1 := by
  by_cases h : ω z = 1 <;> simp [topField, h]

/-- Along an open path the top field collects one at every vertex after the start. -/
private theorem passage_of_open (ω : Environment) (u : Lattice) (d : ℕ × ℕ) (p : Path u d)
    (hp : ∀ i : Fin (d.1 + d.2), p.vertex i.succ ∈ topSites ω) :
    lastPassage (topField ω) u d - topField ω u +
      topField ω (u + ((d.1 : ℤ), (d.2 : ℤ))) = ((d.1 + d.2 : ℕ) : ℝ) := by
  have hp' : ∀ i : Fin (d.1 + d.2), ω (p.vertex i.succ) = 1 := hp
  have hsum : ∑ i : Fin (d.1 + d.2), topField ω (p.vertex i.succ) =
      ((d.1 + d.2 : ℕ) : ℝ) :=
    calc ∑ i : Fin (d.1 + d.2), topField ω (p.vertex i.succ)
        = ∑ _i : Fin (d.1 + d.2), (1 : ℝ) :=
          Finset.sum_congr rfl (fun i _ => (topField_eq_one_iff ω _).2 (hp' i))
      _ = ((d.1 + d.2 : ℕ) : ℝ) := by simp
  have hle := (excludedStart_le_and_attained (topField ω) u d).1 p
  obtain ⟨q, hq⟩ := (excludedStart_le_and_attained (topField ω) u d).2
  have hqle : ∑ i : Fin (d.1 + d.2), topField ω (q.vertex i.succ) ≤
      ((d.1 + d.2 : ℕ) : ℝ) :=
    calc ∑ i : Fin (d.1 + d.2), topField ω (q.vertex i.succ)
        ≤ ∑ _i : Fin (d.1 + d.2), (1 : ℝ) :=
          Finset.sum_le_sum (fun i _ => topField_le_one ω _)
      _ = ((d.1 + d.2 : ℕ) : ℝ) := by simp
  linarith

theorem openReach_iff_topField_passage (ω : Environment) (u : Lattice) (d : ℕ × ℕ) :
    OpenReach (topSites ω) u (u + ((d.1 : ℤ), (d.2 : ℤ))) ↔
      lastPassage (topField ω) u d - topField ω u +
        topField ω (u + ((d.1 : ℤ), (d.2 : ℤ))) = ((d.1 + d.2 : ℕ) : ℝ) := by
  constructor
  · rintro ⟨d', hd', p, hp⟩
    obtain ⟨e1, e2⟩ := Prod.mk.inj (add_left_cancel hd')
    have hdd : d' = d := Prod.ext (by omega) (by omega)
    have h := passage_of_open ω u d' p hp
    rw [hdd] at h
    exact h
  · intro h
    obtain ⟨q, hq⟩ := (excludedStart_le_and_attained (topField ω) u d).2
    have hsum : ∑ i : Fin (d.1 + d.2), topField ω (q.vertex i.succ) =
        ∑ _i : Fin (d.1 + d.2), (1 : ℝ) := by
      rw [hq, h]
      simp
    have hall := (Finset.sum_eq_sum_iff_of_le (s := Finset.univ)
      (f := fun i : Fin (d.1 + d.2) => topField ω (q.vertex i.succ))
      (g := fun _ => (1 : ℝ)) (fun i _ => topField_le_one ω (q.vertex i.succ))).1 hsum
    refine ⟨d, rfl, q, fun i => ?_⟩
    exact (topField_eq_one_iff ω (q.vertex i.succ)).1 (hall i (Finset.mem_univ i))

end LPPDifferentiability
