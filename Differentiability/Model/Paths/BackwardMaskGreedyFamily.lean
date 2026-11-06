/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Differentiability.Model.Paths.FiniteMaskGreedyFamily
public import LPP_Foundations.Model.Paths.ReflectedReverse
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring

/-! Backward greedy attachments obtained from the actual reflected masks. -/

public section
namespace LPPDifferentiability
namespace GreedyAttachment

private theorem reflected_mem_Icc (a b z : Lattice) :
    z ∈ Set.Icc (-b) (-a) ↔ -z ∈ Set.Icc a b := by
  change ((-b.1 ≤ z.1 ∧ -b.2 ≤ z.2) ∧ (z.1 ≤ -a.1 ∧ z.2 ≤ -a.2)) ↔
    ((a.1 ≤ -z.1 ∧ a.2 ≤ -z.2) ∧ (-z.1 ≤ b.1 ∧ -z.2 ≤ b.2))
  omega

private theorem reflected_deviation (u z : Lattice) (q : ℝ) :
    |((-z).1 : ℝ) - (u.1 : ℝ) -
      ((((-z).1 + (-z).2 - (u.1 + u.2) : ℤ) : ℝ)) * q| =
    |(z.1 : ℝ) - ((-u).1 : ℝ) -
      (((z.1 + z.2 - ((-u).1 + (-u).2) : ℤ) : ℝ)) * q| := by
  have h : ((-z).1 : ℝ) - (u.1 : ℝ) -
      ((((-z).1 + (-z).2 - (u.1 + u.2) : ℤ) : ℝ)) * q =
      -((z.1 : ℝ) - ((-u).1 : ℝ) -
        (((z.1 + z.2 - ((-u).1 + (-u).2) : ℤ) : ℝ)) * q) := by
    simp only [Prod.fst_neg, Prod.snd_neg, Int.cast_neg, Int.cast_sub, Int.cast_add]
    ring
  rw [h, abs_neg]

/-- The active conditions are the backward versions of E1, E2 and E3 in Section B.2 of the
differentiability preprint.
The forward witness uses the reflected image of R and its transported bits;
the backward witness is its actual reverse-reflection, also on inactive masks. -/
theorem exists_backward_finite_mask_greedy_family
    {J : Type*} (R : Finset Lattice) (u : J → Lattice) (d : J → ℕ × ℕ)
    (K : ℕ) (hK : 2 ≤ K) (hm : ∀ j, 4 * K + 4 ≤ (d j).1 + (d j).2)
    (hq₁ : ∀ j, 1 / 4 ≤ ((d j).1 : ℝ) / ((d j).1 + (d j).2 : ℕ))
    (hq₂ : ∀ j, ((d j).1 : ℝ) / ((d j).1 + (d j).2 : ℕ) ≤ 3 / 4)
    (hrect : ∀ j z, z ∈ Set.Icc
      (u j - (((d j).1 : ℤ), ((d j).2 : ℤ))) (u j) → z ∈ R)
    (hboxR : ∀ j z, z ∈ Set.Icc
      (u j - (((d j).1 : ℤ), ((d j).2 : ℤ)))
      (u j - (((d j).1 : ℤ), ((d j).2 : ℤ)) +
        (((4 * K + 4 : ℕ) : ℤ), ((4 * K + 4 : ℕ) : ℤ))) → z ∈ R) :
    let V := fun a : R → Bool => {z : Lattice | ∃ hz : z ∈ R, a ⟨z, hz⟩ = true}
    let active := fun (a : R → Bool) (j : J) =>
      u j ∉ V a ∧
      (∀ z ∈ Set.Icc (u j - (((d j).1 : ℤ), ((d j).2 : ℤ))) (u j),
        ∀ w ∈ Set.Icc (u j - (((d j).1 : ℤ), ((d j).2 : ℤ))) (u j),
        z ∈ V a → w ∈ V a → z ≠ w →
        ¬ (|(z.1 : ℝ) - (w.1 : ℝ)| + |(z.2 : ℝ) - (w.2 : ℝ)| ≤ 2)) ∧
      (∀ z (hz : z ∈ Set.Icc
        (u j - (((d j).1 : ℤ), ((d j).2 : ℤ)))
        (u j - (((d j).1 : ℤ), ((d j).2 : ℤ)) +
          (((4 * K + 4 : ℕ) : ℤ), ((4 * K + 4 : ℕ) : ℤ)))),
        a ⟨z, hboxR j z hz⟩ = false) ∧
      ((Finset.Icc (u j - (((d j).1 : ℤ), ((d j).2 : ℤ))) (u j)).filter
        (fun z => z ∈ V a ∧
          |(z.1 : ℝ) - ((u j).1 : ℝ) -
            (((z.1 + z.2 - ((u j).1 + (u j).2) : ℤ) : ℝ)) *
              (((d j).1 : ℝ) / ((d j).1 + (d j).2 : ℕ))| ≤ (K : ℝ) + 2)).card < K
    ∃ qforward : (a : R → Bool) → (j : J) → Path (-u j) (d j),
    ∃ qback : (a : R → Bool) → (j : J) →
      Path (u j - (((d j).1 : ℤ), ((d j).2 : ℤ))) (d j),
      (∀ a j i, (qback a j).vertex i = -((qforward a j).vertex i.rev)) ∧
      (∀ a j i, (qback a j).vertex i ∈ R) ∧
      (∀ a j, active a j → ∀ i, (qback a j).vertex i ∉ V a) := by
  classical
  intro V active
  let D := fun j => (((d j).1 : ℤ), ((d j).2 : ℤ))
  let B : Lattice := (((4 * K + 4 : ℕ) : ℤ), ((4 * K + 4 : ℕ) : ℤ))
  let S := R.image Neg.neg
  have hS (z : Lattice) : z ∈ S ↔ -z ∈ R := by
    constructor
    · rintro hz
      obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hz
      simpa only [neg_neg] using hw
    · intro hz
      exact Finset.mem_image.mpr ⟨-z, hz, neg_neg z⟩
  let bits := fun (a : R → Bool) (z : S) => a ⟨-z.1, (hS z.1).mp z.2⟩
  let W := fun a : S → Bool => {z : Lattice | ∃ hz : z ∈ S, a ⟨z, hz⟩ = true}
  have hbad (a : R → Bool) (z : Lattice) : z ∈ W (bits a) ↔ -z ∈ V a := by
    constructor
    · rintro ⟨hz, hb⟩
      exact ⟨(hS z).mp hz, hb⟩
    · rintro ⟨hz, hb⟩
      exact ⟨(hS z).mpr hz, hb⟩
  have hend (j : J) : -u j + D j = -(u j - D j) := by abel
  have hboxend (j : J) : -u j + D j - B = -(u j - D j + B) := by abel
  have hr (j : J) (z : Lattice)
      (hz : z ∈ Set.Icc (-u j) (-u j + D j)) : z ∈ S := by
    rw [hend] at hz
    exact (hS z).mpr (hrect j (-z) ((reflected_mem_Icc _ _ _).mp hz))
  have hbr (j : J) (z : Lattice)
      (hz : z ∈ Set.Icc (-u j + D j - B) (-u j + D j)) : z ∈ S := by
    rw [hboxend, hend] at hz
    exact (hS z).mpr (hboxR j (-z) ((reflected_mem_Icc _ _ _).mp hz))
  obtain ⟨q, _, _, hq⟩ := exists_finite_mask_greedy_family S (fun j => -u j) d K
    hK hm hq₁ hq₂ hr hbr
  have hgood (a : R → Bool) (j : J) (ha : active a j) :
      ∀ i, (q (bits a) j).vertex i ∉ W (bits a) := by
    apply (hq (bits a) j ?_).2
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro h
      exact ha.1 (by simpa only [neg_neg] using (hbad a (-u j)).mp h)
    · intro z hz w hw hzbad hwbad hne hdist
      rw [hend] at hz hw
      have hn : -z ≠ -w := fun h => hne (neg_injective h)
      apply ha.2.1 (-z) ((reflected_mem_Icc _ _ _).mp hz)
        (-w) ((reflected_mem_Icc _ _ _).mp hw)
        ((hbad a z).mp hzbad) ((hbad a w).mp hwbad) hn
      simpa only [Prod.fst_neg, Prod.snd_neg, Int.cast_neg, neg_sub_neg,
        abs_sub_comm] using hdist
    · intro z hz
      have hz' := hz
      rw [hboxend, hend] at hz'
      exact ha.2.2.1 (-z) ((reflected_mem_Icc _ _ _).mp hz')
    · apply lt_of_le_of_lt (Finset.card_le_card_of_injOn Neg.neg ?_ ?_) ha.2.2.2
      · intro z hz
        obtain ⟨hzr, hzb, hzt⟩ := Finset.mem_filter.mp hz
        refine Finset.mem_filter.mpr ⟨?_, (hbad a z).mp hzb, ?_⟩
        · apply Finset.mem_Icc.mpr
          apply (reflected_mem_Icc _ _ _).mp
          rw [← hend]
          exact Finset.mem_Icc.mp hzr
        · rw [reflected_deviation]
          exact hzt
      · intro z _ w _ h
        exact neg_injective h
  have hex (a : R → Bool) (j : J) :
      ∃ qb : Path (u j - D j) (d j),
        ∀ i, qb.vertex i = -((q (bits a) j).vertex i.rev) := by
    have he : -(-u j + D j) = u j - D j := by abel
    rw [← he]
    exact (q (bits a) j).exists_reflected_reverse
  choose qb hqb using hex
  refine ⟨fun a j => q (bits a) j, qb, hqb, ?_, ?_⟩
  · intro a j i
    apply hrect j _
    simpa only [D, sub_add_cancel] using (qb a j).vertex_mem_Icc i
  · intro a j ha i hmem
    apply hgood a j ha i.rev
    apply (hbad a _).mpr
    simpa only [hqb a j i, neg_neg] using hmem

end GreedyAttachment
end LPPDifferentiability
