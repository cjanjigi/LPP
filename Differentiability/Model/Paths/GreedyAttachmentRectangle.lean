/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Differentiability.Model.Paths.GreedyAttachmentForcedCount
public import Differentiability.Analysis.GreedyAttachmentMargin
import Mathlib.Tactic

/-! Actual rectangle feasibility and bad avoidance during the greedy phase. -/

@[expose] public section
namespace LPPDifferentiability
namespace GreedyAttachment
open scoped Classical

variable (u : Lattice) (d : ℕ × ℕ) (V : Set Lattice)
local notation "m" => ((Prod.fst d + Prod.snd d : ℕ))
local notation "q" => (((Prod.fst d : ℕ) : ℝ) / (m : ℕ))
local notation "x" => vertex u q V
local notation "f" => forcedCount u q V
local notation "t" => (u + (((Prod.fst d : ℕ) : ℤ), ((Prod.snd d : ℕ) : ℤ)))

/-- The actual natural remaining coordinates satisfy the source line identities. -/
theorem remaining_equations (i : ℕ) (hi : i ≤ m) (hm : 0 < m)
    (hr : x i ∈ Set.Icc u t) :
    (((t.1 - (x i).1).toNat : ℕ) : ℝ) =
      ((m - i : ℕ) : ℝ) / (m : ℕ) * (d.1 : ℝ) - deviation u q i (x i) ∧
    (((t.2 - (x i).2).toNat : ℕ) : ℝ) =
      ((m - i : ℕ) : ℝ) / (m : ℕ) * ((m - d.1 : ℕ) : ℝ) + deviation u q i (x i) := by
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
  have ha : (((t.1 - (x i).1).toNat : ℕ) : ℝ) =
      (t.1 : ℝ) - ((x i).1 : ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg (sub_nonneg.mpr hr.2.1)
  have hb : (((t.2 - (x i).2).toNat : ℕ) : ℝ) =
      (t.2 : ℝ) - ((x i).2 : ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg (sub_nonneg.mpr hr.2.2)
  have hl : ((x i).1 : ℝ) + ((x i).2 : ℝ) =
      (u.1 : ℝ) + (u.2 : ℝ) + (i : ℝ) := by
    exact_mod_cast level u q V i
  constructor
  · rw [ha, Nat.cast_sub hi]
    simp only [Prod.fst_add, Int.cast_add, Int.cast_natCast, deviation]
    field_simp [hm0]
    ring
  · rw [hb, show m - d.1 = d.2 by omega, Nat.cast_sub hi]
    simp only [Prod.snd_add, Int.cast_add, Int.cast_natCast, deviation]
    field_simp [hm0]
    have hmadd : (m : ℝ) = (d.1 : ℝ) + (d.2 : ℝ) := Nat.cast_add d.1 d.2
    linear_combination -(m : ℝ) * hl - (i : ℝ) * hmadd

/-- Source margins make both actual remaining coordinates positive,
including the terminal greedy level. -/
theorem remaining_positive (K i : ℕ) (hm : 4 * K + 4 ≤ m)
    (hq₁ : 1 / 4 ≤ q) (hq₂ : q ≤ 3 / 4)
    (hi : i ≤ m - (4 * K + 4)) (hr : x i ∈ Set.Icc u t) (hf : f i < K) :
    1 ≤ (t.1 - (x i).1).toNat ∧ 1 ≤ (t.2 - (x i).2).toNat := by
  have him : i ≤ m := by omega
  have hmpos : 0 < m := by omega
  obtain ⟨ha, hb⟩ := remaining_equations u d V i him hmpos hr
  have hdev : |deviation u q i (x i)| ≤ (K : ℝ) := by
    have h := deviation_bound u q V hq₁ hq₂ i
    have hc : (f i : ℝ) + 1 ≤ (K : ℝ) := by exact_mod_cast hf
    linarith only [h, hc]
  have hmargin := greedy_attachment_remaining_coordinate_margin
    m d.1 (m - i) (t.1 - (x i).1).toNat (t.2 - (x i).2).toNat
    (deviation u q i (x i)) hmpos hq₁ hq₂ ha hb
  have hrlevel : (4 * K + 4 : ℕ) ≤ m - i := by omega
  have hrR : 4 * (K : ℝ) + 4 ≤ ((m - i : ℕ) : ℝ) := by exact_mod_cast hrlevel
  constructor
  · have : (1 : ℝ) ≤ (((t.1 - (x i).1).toNat : ℕ) : ℝ) := by
      linarith [hmargin.2.1]
    exact_mod_cast this
  · have : (1 : ℝ) ≤ (((t.2 - (x i).2).toNat : ℕ) : ℝ) := by
      linarith [hmargin.2.2]
    exact_mod_cast this

/-- Both possible next points are admissible; this is derived from the actual
remaining-coordinate margins, not assumed by the sequence. -/
theorem candidates_mem_rectangle (K i : ℕ) (hm : 4 * K + 4 ≤ m)
    (hq₁ : 1 / 4 ≤ q) (hq₂ : q ≤ 3 / 4)
    (hi : i < m - (4 * K + 4)) (hr : x i ∈ Set.Icc u t) (hf : f i < K) :
    preferred u q i (x i) ∈ Set.Icc u t ∧ alternate u q i (x i) ∈ Set.Icc u t := by
  obtain ⟨ha, hb⟩ := remaining_positive u d V K i hm hq₁ hq₂ (by omega) hr hf
  have haI : (x i).1 + 1 ≤ t.1 := by omega
  have hbI : (x i).2 + 1 ≤ t.2 := by omega
  obtain ⟨⟨hl₁, hl₂⟩, ⟨hu₁, hu₂⟩⟩ := hr
  simp only [Prod.fst_add, Prod.snd_add] at hu₁ hu₂
  have h₁ : x i + (1, 0) ∈ Set.Icc u t :=
    ⟨⟨by dsimp only [Prod.fst_add]; omega,
       by dsimp only [Prod.snd_add]; omega⟩,
     ⟨by dsimp only [Prod.fst_add]; omega,
       by dsimp only [Prod.snd_add]; omega⟩⟩
  have h₂ : x i + (0, 1) ∈ Set.Icc u t :=
    ⟨⟨by dsimp only [Prod.fst_add]; omega,
       by dsimp only [Prod.snd_add]; omega⟩,
     ⟨by dsimp only [Prod.fst_add]; omega,
       by dsimp only [Prod.snd_add]; omega⟩⟩
  unfold preferred alternate
  split_ifs
  · exact ⟨h₁, h₂⟩
  · exact ⟨h₂, h₁⟩

/-- Joint geometric induction: the actual greedy vertices stay admissible and
good, and the actual number of forced steps is strictly below K. -/
theorem greedy_phase (K : ℕ) (hK : 2 ≤ K) (hm : 4 * K + 4 ≤ m)
    (hq₁ : 1 / 4 ≤ q) (hq₂ : q ≤ 3 / 4) (hu : u ∉ V)
    (hsep : ∀ z ∈ Set.Icc u t, ∀ w ∈ Set.Icc u t,
      z ∈ V → w ∈ V → z ≠ w →
      ¬ (|(z.1 : ℝ) - (w.1 : ℝ)| + |(z.2 : ℝ) - (w.2 : ℝ)| ≤ 2))
    (hbad : ((Finset.Icc u t).filter (fun z => z ∈ V ∧
      |(z.1 : ℝ) - (u.1 : ℝ) - (((z.1 + z.2 - (u.1 + u.2) : ℤ) : ℝ)) * q|
        ≤ (K : ℝ) + 2)).card < K) :
    ∀ i ≤ m - (4 * K + 4), x i ∈ Set.Icc u t ∧ f i < K ∧ x i ∉ V := by
  intro i
  induction i using Nat.strong_induction_on with
  | h i ih =>
    intro hi
    cases i with
    | zero =>
      refine ⟨?_, ?_, ?_⟩
      · rw [vertex_zero]
        exact ⟨le_rfl, ⟨by dsimp only [Prod.fst_add]; omega,
          by dsimp only [Prod.snd_add]; omega⟩⟩
      · rw [forcedCount_zero]
        omega
      · exact hu
    | succ i =>
      obtain ⟨hir, hif, _hig⟩ := ih i (by omega) (by omega)
      obtain ⟨hp, ha⟩ := candidates_mem_rectangle u d V K i hm hq₁ hq₂ (by omega) hir hif
      refine ⟨?_, ?_, next_not_mem u q V i (Set.Icc u t) hsep hp ha⟩
      · rw [vertex_succ]
        split_ifs <;> assumption
      · apply lt_of_le_of_lt (forcedCount_le_bad_card u d V K (i + 1) hq₁ hq₂ ?_ ?_) hbad
        · intro j hj
          obtain ⟨hjr, hjf, _hjg⟩ := ih j (by omega) (by omega)
          exact (candidates_mem_rectangle u d V K j hm hq₁ hq₂ (by omega) hjr hjf).1
        · intro j hj
          exact (ih j (by omega) (by omega)).2.1

end GreedyAttachment
end LPPDifferentiability
