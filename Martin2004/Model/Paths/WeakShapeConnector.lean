/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import LPP_Foundations.Model.Paths.HorizontalFirst
public import LPP_Foundations.Model.Paths.Geometry
public import LPP_Foundations.Model.Paths.Split
public import LPP_Foundations.Model.LastPassage.Basic
public import LPP_Foundations.Model.Animals.Extension
public import LPP_Foundations.Model.Animals.Maximum
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

public import Martin2004.Model.Paths.BackwardGreedy

/-! Finite directed backward greedy paths for the weak-negative case.
The construction chooses the left predecessor on ties and stays in the endpoint
rectangle. No probability or independence assertion occurs in this module. -/

@[expose] public section

open scoped BigOperators

namespace LPPDifferentiability
private theorem half_step (v t : Lattice)
    (h : t = v + (1, 0) ∨ t = v + (0, 1)) :
    (v.1 / 2, v.2 / 2) = (t.1 / 2, t.2 / 2) ∨
      nearestNeighborGraph.Adj (v.1 / 2, v.2 / 2) (t.1 / 2, t.2 / 2) := by
  rcases h with rfl | rfl
  · have hh : (v.1 + 1) / 2 = v.1 / 2 ∨ (v.1 + 1) / 2 = v.1 / 2 + 1 := by omega
    rcases hh with hh | hh
    · left
      simp only [Prod.fst_add, Prod.snd_add, add_zero, hh]
    · right
      left
      simp only [Prod.fst_add, Prod.snd_add, add_zero, hh,
        sub_add_cancel_left, abs_neg, abs_one, and_self]
  · have hh : (v.2 + 1) / 2 = v.2 / 2 ∨ (v.2 + 1) / 2 = v.2 / 2 + 1 := by omega
    rcases hh with hh | hh
    · left
      simp only [Prod.fst_add, Prod.snd_add, add_zero, hh]
    · right
      right
      simp only [Prod.fst_add, Prod.snd_add, add_zero, hh,
        sub_add_cancel_left, abs_neg, abs_one, and_self]

private theorem finite_sequence_image_connected (n : ℕ) (f : Fin (n + 1) → Lattice)
    (hstep : ∀ i : Fin n, f i.castSucc = f i.succ ∨
      nearestNeighborGraph.Adj (f i.castSucc) (f i.succ)) :
    IsConnectedAnimal (Finset.univ.image f) := by
  classical
  let s := Finset.univ.image f
  have hmem (i : Fin (n + 1)) : f i ∈ s := Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩
  have hreach : ∀ k (hk : k < n + 1),
      (nearestNeighborGraph.induce (↑s : Set Lattice)).Reachable
        ⟨f 0, hmem 0⟩ ⟨f ⟨k, hk⟩, hmem ⟨k, hk⟩⟩ := by
    intro k
    induction k with
    | zero => intro hk; exact .rfl
    | succ k ih =>
      intro hk
      have hk' : k < n := by omega
      apply (ih (by omega)).trans
      rcases hstep ⟨k, hk'⟩ with heq | hadj
      · have heq' : (⟨f (⟨k, hk'⟩ : Fin n).castSucc, hmem _⟩ : s) =
            ⟨f ⟨k + 1, hk⟩, hmem _⟩ := Subtype.ext heq
        rw [← heq']
        exact .rfl
      · exact SimpleGraph.Adj.reachable hadj
  apply (SimpleGraph.connected_iff_exists_forall_reachable _).2
  refine ⟨⟨f 0, hmem 0⟩, ?_⟩
  rintro ⟨v, hv⟩
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hv
  exact hreach i.val i.isLt

/-- Project every vertex, including the terminal vertex, by integer division by
two. The resulting actual rooted connected set extends to size `|d| + 3`. -/
theorem Path.exists_animalFamily_containing_halves {d : ℕ × ℕ} (p : Path 0 d) :
    ∃ s ∈ animalFamily (d.1 + d.2 + 3),
      ∀ i : Fin (d.1 + d.2 + 1), ((p.vertex i).1 / 2, (p.vertex i).2 / 2) ∈ s := by
  classical
  let f : Fin (d.1 + d.2 + 1) → Lattice := fun i =>
    ((p.vertex i).1 / 2, (p.vertex i).2 / 2)
  let s := Finset.univ.image f
  have hs : IsConnectedAnimal s := finite_sequence_image_connected _ f (fun i =>
    half_step _ _ (p.step i))
  have hzero : (0 : Lattice) ∈ s := by
    apply Finset.mem_image.mpr
    refine ⟨0, Finset.mem_univ 0, ?_⟩
    simp only [f, p.start, Prod.fst_zero, Prod.snd_zero, Int.zero_ediv, Prod.mk_zero_zero]
  have hcard : s.card ≤ d.1 + d.2 + 3 := by
    have h := Finset.card_image_le (s := (Finset.univ : Finset (Fin (d.1 + d.2 + 1)))) (f := f)
    simp only [Finset.card_univ, Fintype.card_fin] at h
    exact h.trans (by omega)
  obtain ⟨t, ht, hst⟩ := hs.exists_extension_mem_animalFamily hzero _ hcard
  refine ⟨t, ht, ?_⟩
  intro i
  exact hst (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩)

private def twoPredecessorMinimum (ω : Environment) (L : ℝ) (v : Lattice) : ℝ :=
  min (max (-L - ω (v - (1, 0))) 0) (max (-L - ω (v - (0, 1))) 0)

private theorem sum_twoPredecessorMinimum_le_four (ω : Environment) (L : ℝ)
    (A s : Finset Lattice) (n : ℕ) (hn : 1 ≤ n) (hs : s ∈ animalFamily n)
    (hA : ∀ v ∈ A, (v.1 / 2, v.2 / 2) ∈ s) :
    (∑ v ∈ A, twoPredecessorMinimum ω L v) ≤
      animalMaximum n hn (fun a => twoPredecessorMinimum ω L (2 * a.1, 2 * a.2)) +
      animalMaximum n hn (fun a => twoPredecessorMinimum ω L (2 * a.1, 2 * a.2 + 1)) +
      animalMaximum n hn (fun a => twoPredecessorMinimum ω L (2 * a.1 + 1, 2 * a.2)) +
      animalMaximum n hn (fun a => twoPredecessorMinimum ω L (2 * a.1 + 1, 2 * a.2 + 1)) := by
  classical
  let C : Finset Lattice := {(0, 0), (0, 1), (1, 0), (1, 1)}
  let color : Lattice → Lattice := fun v => (v.1 % 2, v.2 % 2)
  let half : Lattice → Lattice := fun v => (v.1 / 2, v.2 / 2)
  let field : Lattice → Lattice → ℝ := fun c a =>
    twoPredecessorMinimum ω L (2 * a.1 + c.1, 2 * a.2 + c.2)
  have hcolor (v : Lattice) : color v ∈ C := by
    have h₁ : v.1 % 2 = 0 ∨ v.1 % 2 = 1 := by omega
    have h₂ : v.2 % 2 = 0 ∨ v.2 % 2 = 1 := by omega
    rcases h₁ with h₁ | h₁ <;> rcases h₂ with h₂ | h₂ <;>
      simp only [color, C, h₁, h₂, Finset.mem_insert, Finset.mem_singleton,
        Prod.mk.injEq, true_or, or_true, and_self]
  have hbound (c : Lattice) :
      (∑ v ∈ A.filter (fun v => color v = c), twoPredecessorMinimum ω L v) ≤
        animalMaximum n hn (field c) := by
    apply le_trans ?_ (animalWeight_le_animalMaximum n hn (field c) hs)
    change _ ≤ ∑ a ∈ s, field c a
    apply Finset.sum_le_sum_of_injOn half
    · intro v hv t ht heq
      have hv' := (Finset.mem_filter.mp hv).2
      have ht' := (Finset.mem_filter.mp ht).2
      have hr₁ := congrArg Prod.fst (hv'.trans ht'.symm)
      have hr₂ := congrArg Prod.snd (hv'.trans ht'.symm)
      have hq₁ := congrArg Prod.fst heq
      have hq₂ := congrArg Prod.snd heq
      apply Prod.ext <;> dsimp only [color, half] at hr₁ hr₂ hq₁ hq₂ <;> omega
    · intro a ha
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp ha
      exact hA v (Finset.mem_filter.mp hv).1
    · intro v hv
      have hv' := (Finset.mem_filter.mp hv).2
      have hr₁ := congrArg Prod.fst hv'
      have hr₂ := congrArg Prod.snd hv'
      have heq : (2 * (half v).1 + c.1, 2 * (half v).2 + c.2) = v := by
        apply Prod.ext <;> dsimp only [color, half] at hr₁ hr₂ ⊢ <;> omega
      exact le_of_eq (congrArg (twoPredecessorMinimum ω L) heq.symm)
    · intro a _ _
      exact le_min (le_max_right _ _) (le_max_right _ _)
  calc
    (∑ v ∈ A, twoPredecessorMinimum ω L v) =
        ∑ c ∈ C, ∑ v ∈ A.filter (fun v => color v = c), twoPredecessorMinimum ω L v :=
      (Finset.sum_fiberwise_of_maps_to (fun v _ => hcolor v) _).symm
    _ ≤ ∑ c ∈ C, animalMaximum n hn (field c) :=
      Finset.sum_le_sum (fun c _ => hbound c)
    _ = _ := by
      norm_num [C, field]
      ring

/-- The pointwise four-color animal comparison for all current sites of an
actual directed path from zero. The terminal site is included as a current
site and in the projected rooted animal. -/
theorem Path.sum_twoPredecessorMinimum_le_four_animalMaximum
    (ω : Environment) (L : ℝ) {d : ℕ × ℕ} (p : Path 0 d) :
    (∑ i : Fin (d.1 + d.2),
      min (max (-L - ω (p.vertex i.succ - (1, 0))) 0)
        (max (-L - ω (p.vertex i.succ - (0, 1))) 0)) ≤
      animalMaximum (d.1 + d.2 + 3) (by omega)
        (fun a => min (max (-L - ω ((2 * a.1, 2 * a.2) - (1, 0))) 0)
          (max (-L - ω ((2 * a.1, 2 * a.2) - (0, 1))) 0)) +
      animalMaximum (d.1 + d.2 + 3) (by omega)
        (fun a => min (max (-L - ω ((2 * a.1, 2 * a.2 + 1) - (1, 0))) 0)
          (max (-L - ω ((2 * a.1, 2 * a.2 + 1) - (0, 1))) 0)) +
      animalMaximum (d.1 + d.2 + 3) (by omega)
        (fun a => min (max (-L - ω ((2 * a.1 + 1, 2 * a.2) - (1, 0))) 0)
          (max (-L - ω ((2 * a.1 + 1, 2 * a.2) - (0, 1))) 0)) +
      animalMaximum (d.1 + d.2 + 3) (by omega)
        (fun a => min (max (-L - ω ((2 * a.1 + 1, 2 * a.2 + 1) - (1, 0))) 0)
          (max (-L - ω ((2 * a.1 + 1, 2 * a.2 + 1) - (0, 1))) 0)) := by
  classical
  obtain ⟨s, hs, hcover⟩ := p.exists_animalFamily_containing_halves
  let A := Finset.univ.image (fun i : Fin (d.1 + d.2) => p.vertex i.succ)
  have hinj : Function.Injective (fun i : Fin (d.1 + d.2) => p.vertex i.succ) := by
    intro i j hij
    exact Fin.succ_injective _ (p.vertex_injective hij)
  have heq : (∑ i : Fin (d.1 + d.2), twoPredecessorMinimum ω L (p.vertex i.succ)) =
      ∑ v ∈ A, twoPredecessorMinimum ω L v := by
    dsimp only [A]
    rw [Finset.sum_image]
    exact fun i _ j _ hij => hinj hij
  change (∑ i : Fin (d.1 + d.2), twoPredecessorMinimum ω L (p.vertex i.succ)) ≤ _
  rw [heq]
  apply sum_twoPredecessorMinimum_le_four ω L A s _ (by omega) hs
  intro v hv
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hv
  exact hcover i.succ

/-- Every directed path has a last boundary vertex. Its later vertices are
strictly above both starting coordinates, so the boundary steps are exactly
a prefix, including for zero displacement and either axis. -/
theorem Path.exists_last_boundary_vertex {u : Lattice} {d : ℕ × ℕ} (p : Path u d) :
    ∃ k : Fin (d.1 + d.2 + 1),
      ((p.vertex k).1 = u.1 ∨ (p.vertex k).2 = u.2) ∧
      (∀ i : Fin (d.1 + d.2),
        (u.1 < (p.vertex i.succ).1 ∧ u.2 < (p.vertex i.succ).2) ↔ k.val ≤ i.val) := by
  classical
  let B := Finset.univ.filter (fun k : Fin (d.1 + d.2 + 1) =>
    (p.vertex k).1 = u.1 ∨ (p.vertex k).2 = u.2)
  have hzero : (0 : Fin (d.1 + d.2 + 1)) ∈ B := by
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ 0, Or.inl (congrArg Prod.fst p.start)⟩
  let k := B.max' ⟨0, hzero⟩
  have hk : k ∈ B := Finset.max'_mem B ⟨0, hzero⟩
  have hkb := (Finset.mem_filter.mp hk).2
  refine ⟨k, hkb, ?_⟩
  intro i
  constructor
  · intro hi
    by_contra hki
    have hik : i.succ ≤ k := by change i.val + 1 ≤ k.val; omega
    rcases hkb with hkfst | hksnd
    · have hmon := p.fst_monotone hik
      dsimp only at hmon
      rw [hkfst] at hmon
      exact (not_lt_of_ge hmon) hi.1
    · have hmon := p.snd_monotone hik
      dsimp only at hmon
      rw [hksnd] at hmon
      exact (not_lt_of_ge hmon) hi.2
  · intro hki
    have hnB : i.succ ∉ B := by
      intro hi
      have hle := Finset.le_max' B i.succ hi
      change i.val + 1 ≤ k.val at hle
      omega
    have hnot : ¬ ((p.vertex i.succ).1 = u.1 ∨ (p.vertex i.succ).2 = u.2) := by
      intro hi
      exact hnB (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩)
    have hlow := (p.vertex_mem_Icc i.succ).1
    constructor
    · have hne : (p.vertex i.succ).1 ≠ u.1 := fun h => hnot (Or.inl h)
      exact lt_of_le_of_ne hlow.1 hne.symm
    · have hne : (p.vertex i.succ).2 ≠ u.2 := fun h => hnot (Or.inr h)
      exact lt_of_le_of_ne hlow.2 hne.symm

/-- The constructed connector splits at an actual boundary vertex into a
straight prefix and a greedy suffix. Terminal exclusion assigns the joining
vertex only to the suffix, by the exact `pathWeight_split` identity. -/
theorem exists_backwardGreedyPath_split_charge (ω : Environment) (u : Lattice)
    (d : ℕ × ℕ) (L : ℝ) (hL : 0 ≤ L) :
    ∃ (p : Path u d) (k : Fin (d.1 + d.2 + 1)),
      ((p.splitDisplacement k).1 = 0 ∨ (p.splitDisplacement k).2 = 0) ∧
      (∀ i : Fin ((d - p.splitDisplacement k).1 + (d - p.splitDisplacement k).2),
        (p.suffix k).vertex i.castSucc =
          if max (-ω ((p.suffix k).vertex i.succ - (1, 0))) 0 ≤
              max (-ω ((p.suffix k).vertex i.succ - (0, 1))) 0 then
            (p.suffix k).vertex i.succ - (1, 0) else
            (p.suffix k).vertex i.succ - (0, 1)) ∧
      pathWeight (fun v => max (-ω v) 0) p ≤
        pathWeight (fun v => max (-ω v) 0) (p.prefixPath k) +
          ((d - p.splitDisplacement k).1 + (d - p.splitDisplacement k).2 : ℕ) * L +
          ∑ i : Fin ((d - p.splitDisplacement k).1 + (d - p.splitDisplacement k).2),
            min (max (-L - ω ((p.suffix k).vertex i.succ - (1, 0))) 0)
              (max (-L - ω ((p.suffix k).vertex i.succ - (0, 1))) 0) := by
  obtain ⟨p, hp⟩ := exists_backwardGreedyPath (fun v => max (-ω v) 0) u d
  obtain ⟨k, hk, hki⟩ := p.exists_last_boundary_vertex
  have haxis : (p.splitDisplacement k).1 = 0 ∨ (p.splitDisplacement k).2 = 0 := by
    rcases hk with hk | hk
    · left
      have hc := p.splitDisplacement_fst_cast k
      rw [hk, sub_self] at hc
      exact_mod_cast hc
    · right
      have hc := p.splitDisplacement_snd_cast k
      rw [hk, sub_self] at hc
      exact_mod_cast hc
  have hgreedy : ∀ i : Fin ((d - p.splitDisplacement k).1 + (d - p.splitDisplacement k).2),
      (p.suffix k).vertex i.castSucc =
        if max (-ω ((p.suffix k).vertex i.succ - (1, 0))) 0 ≤
            max (-ω ((p.suffix k).vertex i.succ - (0, 1))) 0 then
          (p.suffix k).vertex i.succ - (1, 0) else
          (p.suffix k).vertex i.succ - (0, 1) := by
    intro i
    have hlen := p.suffix_length k
    have hi := i.isLt
    have hklt := k.isLt
    let j : Fin (d.1 + d.2) := ⟨k.val + i.val, by omega⟩
    have hj := (hki j).2 (by dsimp only [j]; omega)
    have hc : (p.suffix k).vertex i.castSucc = p.vertex j.castSucc := rfl
    have hs : (p.suffix k).vertex i.succ = p.vertex j.succ := by
      change p.vertex ⟨k.val + i.succ.val, by
        have h := i.succ.isLt
        omega⟩ = p.vertex j.succ
      apply congrArg p.vertex
      apply Fin.ext
      dsimp only [j]
      simp only [Fin.val_succ]
      omega
    rw [hc, hs]
    exact hp j hj.1 hj.2
  refine ⟨p, k, haxis, hgreedy, ?_⟩
  rw [pathWeight_split _ p k]
  have hsuffix : pathWeight (fun v => max (-ω v) 0) (p.suffix k) ≤
      ((d - p.splitDisplacement k).1 + (d - p.splitDisplacement k).2 : ℕ) * L +
        ∑ i : Fin ((d - p.splitDisplacement k).1 + (d - p.splitDisplacement k).2),
          min (max (-L - ω ((p.suffix k).vertex i.succ - (1, 0))) 0)
            (max (-L - ω ((p.suffix k).vertex i.succ - (0, 1))) 0) := by
    calc
      pathWeight (fun v => max (-ω v) 0) (p.suffix k) ≤
          ∑ i : Fin ((d - p.splitDisplacement k).1 + (d - p.splitDisplacement k).2),
            (L + min (max (-L - ω ((p.suffix k).vertex i.succ - (1, 0))) 0)
              (max (-L - ω ((p.suffix k).vertex i.succ - (0, 1))) 0)) := by
        apply Finset.sum_le_sum
        intro i _
        rw [hgreedy i]
        exact backwardGreedy_negativePart_le_cutoff_min ω ((p.suffix k).vertex i.succ) L hL
      _ = _ := by simp only [Finset.sum_add_distrib, Finset.sum_const,
        Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  linarith only [hsuffix]

private theorem exists_rooted_extension (w : ℕ × ℕ) {d : ℕ × ℕ}
    (p : Path ((w.1 : ℤ), (w.2 : ℤ)) d) :
    ∃ r : Path 0 (w + d), ∀ i : Fin (d.1 + d.2 + 1),
      r.vertex ⟨w.1 + w.2 + i.val, by
        have hi := i.isLt
        simp only [Prod.fst_add, Prod.snd_add]
        omega⟩ = p.vertex i := by
  let q : Path ((0 : Lattice) + ((w.1 : ℤ), (w.2 : ℤ))) d :=
    { vertex := p.vertex
      start := p.start.trans (zero_add _).symm
      finish := p.finish.trans (congrArg (fun a : Lattice =>
        a + ((d.1 : ℤ), (d.2 : ℤ))) (zero_add _).symm)
      step := p.step }
  let a := horizontalFirst 0 w
  refine ⟨a.concat q, ?_⟩
  intro i
  exact a.concat_vertex_right q i

/-- All current sites of a connector with a natural starting point admit the
same four-color comparison at the absolute endpoint size. The root extension
is an actual directed path from zero, preceding the connector. -/
theorem Path.sum_twoPredecessorMinimum_le_four_animalMaximum_fromNatural
    (ω : Environment) (L : ℝ) (w : ℕ × ℕ) {d : ℕ × ℕ}
    (p : Path ((w.1 : ℤ), (w.2 : ℤ)) d) :
    (∑ i : Fin (d.1 + d.2),
      min (max (-L - ω (p.vertex i.succ - (1, 0))) 0)
        (max (-L - ω (p.vertex i.succ - (0, 1))) 0)) ≤
      animalMaximum ((w + d).1 + (w + d).2 + 3) (by omega)
        (fun a => min (max (-L - ω ((2 * a.1, 2 * a.2) - (1, 0))) 0)
          (max (-L - ω ((2 * a.1, 2 * a.2) - (0, 1))) 0)) +
      animalMaximum ((w + d).1 + (w + d).2 + 3) (by omega)
        (fun a => min (max (-L - ω ((2 * a.1, 2 * a.2 + 1) - (1, 0))) 0)
          (max (-L - ω ((2 * a.1, 2 * a.2 + 1) - (0, 1))) 0)) +
      animalMaximum ((w + d).1 + (w + d).2 + 3) (by omega)
        (fun a => min (max (-L - ω ((2 * a.1 + 1, 2 * a.2) - (1, 0))) 0)
          (max (-L - ω ((2 * a.1 + 1, 2 * a.2) - (0, 1))) 0)) +
      animalMaximum ((w + d).1 + (w + d).2 + 3) (by omega)
        (fun a => min (max (-L - ω ((2 * a.1 + 1, 2 * a.2 + 1) - (1, 0))) 0)
          (max (-L - ω ((2 * a.1 + 1, 2 * a.2 + 1) - (0, 1))) 0)) := by
  classical
  obtain ⟨r, hr⟩ := exists_rooted_extension w p
  obtain ⟨s, hs, hcover⟩ := r.exists_animalFamily_containing_halves
  let A := Finset.univ.image (fun i : Fin (d.1 + d.2) => p.vertex i.succ)
  have hinj : Function.Injective (fun i : Fin (d.1 + d.2) => p.vertex i.succ) := by
    intro i j hij
    exact Fin.succ_injective _ (p.vertex_injective hij)
  have heq : (∑ i : Fin (d.1 + d.2), twoPredecessorMinimum ω L (p.vertex i.succ)) =
      ∑ v ∈ A, twoPredecessorMinimum ω L v := by
    dsimp only [A]
    rw [Finset.sum_image]
    exact fun i _ j _ hij => hinj hij
  change (∑ i : Fin (d.1 + d.2), twoPredecessorMinimum ω L (p.vertex i.succ)) ≤ _
  rw [heq]
  apply sum_twoPredecessorMinimum_le_four ω L A s _ (by omega) hs
  intro v hv
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hv
  have hc := hcover ⟨w.1 + w.2 + i.succ.val, by
    have hi := i.isLt
    simp only [Prod.fst_add, Prod.snd_add, Fin.val_succ]
    omega⟩
  rw [hr i.succ] at hc
  exact hc

/-- For a nonnegative field, the suffix current-site sum is at most that of
the whole path. The map of indices retains its actual absolute sites. -/
theorem Path.sum_suffix_current_le (Y : Environment) (hY : ∀ v, 0 ≤ Y v)
    {u : Lattice} {d : ℕ × ℕ} (p : Path u d) (k : Fin (d.1 + d.2 + 1)) :
    (∑ i : Fin ((d - p.splitDisplacement k).1 + (d - p.splitDisplacement k).2),
      Y ((p.suffix k).vertex i.succ)) ≤
        ∑ i : Fin (d.1 + d.2), Y (p.vertex i.succ) := by
  classical
  have hlen := p.suffix_length k
  have hk := k.isLt
  let e : Fin ((d - p.splitDisplacement k).1 + (d - p.splitDisplacement k).2) →
      Fin (d.1 + d.2) := fun i => ⟨k.val + i.val, by have hi := i.isLt; omega⟩
  apply Finset.sum_le_sum_of_injOn e
  · intro i _ j _ hij
    have h := congrArg Fin.val hij
    apply Fin.ext
    dsimp only [e] at h
    omega
  · exact Finset.subset_univ _
  · intro i _
    apply le_of_eq
    apply congrArg Y
    change p.vertex ⟨k.val + i.succ.val, by
      have hi := i.succ.isLt
      omega⟩ = p.vertex (e i).succ
    apply congrArg p.vertex
    apply Fin.ext
    dsimp only [e]
    simp only [Fin.val_succ]
    omega
  · intro a _ _
    exact hY _

/-- Superadditivity gives the lower passage estimate for any actual connector.
The path before the connector excludes its endpoint; the connector collects
that endpoint exactly once whenever its displacement is nonzero. -/
theorem lastPassage_sub_negativePartPath_le (ω : Environment) (w d : ℕ × ℕ)
    (p : Path ((w.1 : ℤ), (w.2 : ℤ)) d) :
    lastPassage ω 0 w - pathWeight (fun v => max (-ω v) 0) p ≤
      lastPassage ω 0 (w + d) := by
  have hneg : -pathWeight (fun v => max (-ω v) 0) p ≤ pathWeight ω p := by
    unfold pathWeight
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_le_sum
    intro i _
    have h := le_max_left (-ω (p.vertex i.castSucc)) 0
    linarith only [h]
  have hp := pathWeight_le_lastPassage ω p
  have hs := lastPassage_superadditive ω 0 w d
  simp only [zero_add] at hs
  linarith only [hneg, hp, hs]

/-- In a deterministic cell, produce the actual greedy connector, its straight
boundary prefix, the finite four-color animal charge, and the signed passage
lower bound. Animal size uses the absolute endpoint, not the short gap. -/
theorem exists_backwardGreedy_cell_connector (ω : Environment) (w d : ℕ × ℕ)
    (L : ℝ) (hL : 0 ≤ L) (h : ℕ) (hd₁ : d.1 < h) (hd₂ : d.2 < h) :
    ∃ (p : Path ((w.1 : ℤ), (w.2 : ℤ)) d) (k : Fin (d.1 + d.2 + 1)),
      ((p.splitDisplacement k).1 = 0 ∨ (p.splitDisplacement k).2 = 0) ∧
      (∀ i : Fin ((d - p.splitDisplacement k).1 + (d - p.splitDisplacement k).2),
        (p.suffix k).vertex i.castSucc =
          if max (-ω ((p.suffix k).vertex i.succ - (1, 0))) 0 ≤
              max (-ω ((p.suffix k).vertex i.succ - (0, 1))) 0 then
            (p.suffix k).vertex i.succ - (1, 0) else
            (p.suffix k).vertex i.succ - (0, 1)) ∧
      pathWeight (fun v => max (-ω v) 0) p ≤
        2 * L * h + pathWeight (fun v => max (-ω v) 0) (p.prefixPath k) +
          ∑ c : Fin 2 × Fin 2,
            animalMaximum ((w + d).1 + (w + d).2 + 3) (by omega)
              (fun a =>
                min (max (-L - ω ((2 * a.1 + (c.1.val : ℤ),
                    2 * a.2 + (c.2.val : ℤ)) - (1, 0))) 0)
                  (max (-L - ω ((2 * a.1 + (c.1.val : ℤ),
                    2 * a.2 + (c.2.val : ℤ)) - (0, 1))) 0)) ∧
      lastPassage ω 0 w - pathWeight (fun v => max (-ω v) 0) p ≤
        lastPassage ω 0 (w + d) := by
  obtain ⟨p, k, haxis, hgreedy, hcharge⟩ :=
    exists_backwardGreedyPath_split_charge ω ((w.1 : ℤ), (w.2 : ℤ)) d L hL
  let A : ℝ := ∑ c : Fin 2 × Fin 2,
    animalMaximum ((w + d).1 + (w + d).2 + 3) (by omega)
      (fun a => min (max (-L - ω ((2 * a.1 + (c.1.val : ℤ),
          2 * a.2 + (c.2.val : ℤ)) - (1, 0))) 0)
        (max (-L - ω ((2 * a.1 + (c.1.val : ℤ),
          2 * a.2 + (c.2.val : ℤ)) - (0, 1))) 0))
  have hfour : (∑ i : Fin (d.1 + d.2), twoPredecessorMinimum ω L (p.vertex i.succ)) ≤ A := by
    have hb := p.sum_twoPredecessorMinimum_le_four_animalMaximum_fromNatural ω L w
    simpa [A, Fintype.sum_prod_type, Fin.sum_univ_two, twoPredecessorMinimum, add_assoc] using hb
  have hsuffix := p.sum_suffix_current_le (twoPredecessorMinimum ω L)
    (fun _ => le_min (le_max_right _ _) (le_max_right _ _)) k
  have hlen := p.suffix_length k
  have hfactor :
      (((d - p.splitDisplacement k).1 + (d - p.splitDisplacement k).2 : ℕ) : ℝ) * L ≤
        2 * L * h := by
    have hb : (d - p.splitDisplacement k).1 + (d - p.splitDisplacement k).2 ≤ 2 * h := by omega
    have hcast : (((d - p.splitDisplacement k).1 +
        (d - p.splitDisplacement k).2 : ℕ) : ℝ) ≤ 2 * (h : ℝ) := by exact_mod_cast hb
    calc
      _ ≤ (2 * (h : ℝ)) * L := mul_le_mul_of_nonneg_right hcast hL
      _ = 2 * L * h := by ring
  refine ⟨p, k, haxis, hgreedy, ?_, lastPassage_sub_negativePartPath_le ω w d p⟩
  change pathWeight (fun v => max (-ω v) 0) p ≤
    2 * L * h + pathWeight (fun v => max (-ω v) 0) (p.prefixPath k) + A
  change pathWeight (fun v => max (-ω v) 0) p ≤
    pathWeight (fun v => max (-ω v) 0) (p.prefixPath k) +
      (((d - p.splitDisplacement k).1 + (d - p.splitDisplacement k).2 : ℕ) : ℝ) * L +
      ∑ i : Fin ((d - p.splitDisplacement k).1 + (d - p.splitDisplacement k).2),
        twoPredecessorMinimum ω L ((p.suffix k).vertex i.succ) at hcharge
  linarith only [hcharge, hfactor, hsuffix, hfour]

/-- The same actual connector at endpoints `w ≤ z` has displacement `z - w`.
In particular the animal size is `|z| + 3`, including cells on either axis. -/
theorem exists_backwardGreedy_endpoint_connector (ω : Environment) (w z : ℕ × ℕ)
    (hwz : w ≤ z) (L : ℝ) (hL : 0 ≤ L) (h : ℕ)
    (hd₁ : (z - w).1 < h) (hd₂ : (z - w).2 < h) :
    ∃ (p : Path ((w.1 : ℤ), (w.2 : ℤ)) (z - w))
      (k : Fin ((z - w).1 + (z - w).2 + 1)),
      ((p.splitDisplacement k).1 = 0 ∨ (p.splitDisplacement k).2 = 0) ∧
      (∀ i : Fin (((z - w) - p.splitDisplacement k).1 + ((z - w) - p.splitDisplacement k).2),
        (p.suffix k).vertex i.castSucc =
          if max (-ω ((p.suffix k).vertex i.succ - (1, 0))) 0 ≤
              max (-ω ((p.suffix k).vertex i.succ - (0, 1))) 0 then
            (p.suffix k).vertex i.succ - (1, 0) else
            (p.suffix k).vertex i.succ - (0, 1)) ∧
      pathWeight (fun v => max (-ω v) 0) p ≤
        2 * L * h + pathWeight (fun v => max (-ω v) 0) (p.prefixPath k) +
          ∑ c : Fin 2 × Fin 2,
            animalMaximum (z.1 + z.2 + 3) (by omega)
              (fun a =>
                min (max (-L - ω ((2 * a.1 + (c.1.val : ℤ),
                    2 * a.2 + (c.2.val : ℤ)) - (1, 0))) 0)
                  (max (-L - ω ((2 * a.1 + (c.1.val : ℤ),
                    2 * a.2 + (c.2.val : ℤ)) - (0, 1))) 0)) ∧
      lastPassage ω 0 w - pathWeight (fun v => max (-ω v) 0) p ≤
        lastPassage ω 0 z := by
  have he : w + (z - w) = z := by
    apply Prod.ext
    · exact Nat.add_sub_of_le hwz.1
    · exact Nat.add_sub_of_le hwz.2
  simpa only [he] using exists_backwardGreedy_cell_connector ω w (z - w) L hL h hd₁ hd₂

end LPPDifferentiability
