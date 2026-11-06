/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Differentiability.Model.Paths.GreedyAvoidingAttachment

/-! Actual greedy attachments selected for every finite observation mask. -/

public section
namespace LPPDifferentiability
namespace GreedyAttachment

/-- Assemble the source greedy/box path for active local E1/E2/E3 conditions.
The observation region contains the path rectangles and the backward boxes;
the boxes need not lie in the source region containing the paths. -/
theorem exists_finite_mask_greedy_family
    {J : Type*} (R : Finset Lattice) (u : J → Lattice) (d : J → ℕ × ℕ)
    (K : ℕ) (hK : 2 ≤ K) (hm : ∀ j, 4 * K + 4 ≤ (d j).1 + (d j).2)
    (hq₁ : ∀ j, 1 / 4 ≤ ((d j).1 : ℝ) / ((d j).1 + (d j).2 : ℕ))
    (hq₂ : ∀ j, ((d j).1 : ℝ) / ((d j).1 + (d j).2 : ℕ) ≤ 3 / 4)
    (hrect : ∀ j z, z ∈ Set.Icc (u j) (u j + (((d j).1 : ℤ), ((d j).2 : ℤ))) → z ∈ R)
    (hboxR : ∀ j z, z ∈ Set.Icc
      (u j + (((d j).1 : ℤ), ((d j).2 : ℤ)) -
        (((4 * K + 4 : ℕ) : ℤ), ((4 * K + 4 : ℕ) : ℤ)))
      (u j + (((d j).1 : ℤ), ((d j).2 : ℤ))) → z ∈ R) :
    let V := fun a : R → Bool => {z : Lattice | ∃ hz : z ∈ R, a ⟨z, hz⟩ = true}
    let active := fun (a : R → Bool) (j : J) =>
      u j ∉ V a ∧
      (∀ z ∈ Set.Icc (u j) (u j + (((d j).1 : ℤ), ((d j).2 : ℤ))),
        ∀ w ∈ Set.Icc (u j) (u j + (((d j).1 : ℤ), ((d j).2 : ℤ))),
        z ∈ V a → w ∈ V a → z ≠ w →
        ¬ (|(z.1 : ℝ) - (w.1 : ℝ)| + |(z.2 : ℝ) - (w.2 : ℝ)| ≤ 2)) ∧
      (∀ z (hz : z ∈ Set.Icc
        (u j + (((d j).1 : ℤ), ((d j).2 : ℤ)) -
          (((4 * K + 4 : ℕ) : ℤ), ((4 * K + 4 : ℕ) : ℤ)))
        (u j + (((d j).1 : ℤ), ((d j).2 : ℤ)))), a ⟨z, hboxR j z hz⟩ = false) ∧
      ((Finset.Icc (u j) (u j + (((d j).1 : ℤ), ((d j).2 : ℤ)))).filter
        (fun z => z ∈ V a ∧
          |(z.1 : ℝ) - ((u j).1 : ℝ) -
            (((z.1 + z.2 - ((u j).1 + (u j).2) : ℤ) : ℝ)) *
              (((d j).1 : ℝ) / ((d j).1 + (d j).2 : ℕ))| ≤ (K : ℝ) + 2)).card < K
    ∃ q : (a : R → Bool) → (j : J) → Path (u j) (d j),
      (∀ a j, ¬ active a j → q a j = horizontalFirst (u j) (d j)) ∧
      (∀ a j i, (q a j).vertex i ∈ R) ∧
      (∀ a j, active a j →
        (∀ (i : ℕ) (hi : i ≤ (d j).1 + (d j).2 - (4 * K + 4)),
          (q a j).vertex ⟨i, by omega⟩ =
            vertex (u j) (((d j).1 : ℝ) / ((d j).1 + (d j).2 : ℕ)) (V a) i) ∧
        (∀ i, (q a j).vertex i ∉ V a)) := by
  classical
  intro V active
  have hex (a : R → Bool) (j : J) : ∃ q : Path (u j) (d j),
      (¬ active a j → q = horizontalFirst (u j) (d j)) ∧
      (active a j →
        (∀ (i : ℕ) (hi : i ≤ (d j).1 + (d j).2 - (4 * K + 4)),
          q.vertex ⟨i, by omega⟩ =
            vertex (u j) (((d j).1 : ℝ) / ((d j).1 + (d j).2 : ℕ)) (V a) i) ∧
        (∀ i, q.vertex i ∉ V a)) := by
    by_cases h : active a j
    · have hbox : ∀ z ∈ Set.Icc
          (u j + (((d j).1 : ℤ), ((d j).2 : ℤ)) -
            (((4 * K + 4 : ℕ) : ℤ), ((4 * K + 4 : ℕ) : ℤ)))
          (u j + (((d j).1 : ℤ), ((d j).2 : ℤ))), z ∉ V a := by
        intro z hz hbad
        obtain ⟨hzR, htrue⟩ := hbad
        have hfalse := h.2.2.1 z hz
        rw [htrue] at hfalse
        contradiction
      obtain ⟨q, hpref, _, hgood⟩ := exists_bad_avoiding_attachment (u j) (d j) (V a) K
        hK (hm j) (hq₁ j) (hq₂ j) h.1 h.2.1 hbox (by
          convert h.2.2.2 using 1; congr 1; ext z; simp only [Finset.mem_filter])
      exact ⟨q, fun hn => (hn h).elim, fun _ => ⟨hpref, hgood⟩⟩
    · exact ⟨horizontalFirst (u j) (d j), fun _ => rfl, fun ha => (h ha).elim⟩
  choose q hq using hex
  exact ⟨q, fun a j => (hq a j).1,
    fun a j i => hrect j _ ((q a j).vertex_mem_Icc i), fun a j => (hq a j).2⟩

end GreedyAttachment
end LPPDifferentiability
