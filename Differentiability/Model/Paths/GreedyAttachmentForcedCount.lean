/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Differentiability.Model.Paths.GreedyAttachmentSequence
public import Mathlib.Data.Int.Interval
public import Mathlib.Order.Interval.Finset.Basic
import Mathlib.Tactic

/-! The injection from actual forced steps into actual bad sites. -/

@[expose] public section
namespace LPPDifferentiability
namespace GreedyAttachment
open scoped Classical

/-- Count actual preferred bad causes, using their distinct next levels.
The rectangle premise is supplied by the geometric induction, for every
actual earlier step; no cause injectivity or count estimate is assumed. -/
theorem forcedCount_le_bad_card (u : Lattice) (d : ℕ × ℕ) (V : Set Lattice)
    (K n : ℕ)
    (hq₁ : 1 / 4 ≤ (d.1 : ℝ) / (d.1 + d.2 : ℕ))
    (hq₂ : (d.1 : ℝ) / (d.1 + d.2 : ℕ) ≤ 3 / 4)
    (hrect : ∀ j < n, preferred u ((d.1 : ℝ) / (d.1 + d.2 : ℕ)) j
      (vertex u ((d.1 : ℝ) / (d.1 + d.2 : ℕ)) V j) ∈
        Set.Icc u (u + ((d.1 : ℤ), (d.2 : ℤ))))
    (hcount : ∀ j < n,
      forcedCount u ((d.1 : ℝ) / (d.1 + d.2 : ℕ)) V j < K) :
    forcedCount u ((d.1 : ℝ) / (d.1 + d.2 : ℕ)) V n ≤
      ((Finset.Icc u (u + ((d.1 : ℤ), (d.2 : ℤ)))).filter (fun z =>
        z ∈ V ∧ |(z.1 : ℝ) - (u.1 : ℝ) -
          (((z.1 + z.2 - (u.1 + u.2) : ℤ) : ℝ)) *
            ((d.1 : ℝ) / (d.1 + d.2 : ℕ))| ≤ (K : ℝ) + 2)).card := by
  classical
  let q : ℝ := (d.1 : ℝ) / (d.1 + d.2 : ℕ)
  unfold forcedCount
  apply Finset.card_le_card_of_injOn (fun j => preferred u q j (vertex u q V j))
  · intro j hj
    obtain ⟨hjn, hjbad⟩ := Finset.mem_filter.mp hj
    have hjlt := Finset.mem_range.mp hjn
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_Icc.mpr (hrect j hjlt), hjbad, ?_⟩
    have hl := candidate_level u (vertex u q V j) q j
    have hv := level u q V j
    have htime : (preferred u q j (vertex u q V j)).1 +
        (preferred u q j (vertex u q V j)).2 - (u.1 + u.2) = (j + 1 : ℕ) := by
      push_cast
      omega
    rw [htime]
    change |deviation u q (j + 1) (preferred u q j (vertex u q V j))| ≤ _
    have hb := preferred_deviation_le u q V hq₁ hq₂ j
    have hc : (forcedCount u q V j : ℝ) < (K : ℝ) := by
      exact_mod_cast hcount j hjlt
    linarith
  · intro i _ j _ hij
    exact preferred_injective u q V hij

/-- The two actual next sites are distinct and exactly distance two apart. -/
theorem candidates_separated (u x : Lattice) (q : ℝ) (i : ℕ) :
    preferred u q i x ≠ alternate u q i x ∧
      |((preferred u q i x).1 : ℝ) - ((alternate u q i x).1 : ℝ)| +
        |((preferred u q i x).2 : ℝ) - ((alternate u q i x).2 : ℝ)| = 2 := by
  unfold preferred alternate
  split_ifs <;> constructor
  · intro h
    have h₁ := congrArg Prod.fst h
    simp only [Prod.fst_add] at h₁
    omega
  · simp only [Prod.fst_add, Prod.snd_add, Int.cast_add, Int.cast_one, Int.cast_zero]
    ring_nf
    norm_num
  · intro h
    have h₁ := congrArg Prod.fst h
    simp only [Prod.fst_add] at h₁
    omega
  · simp only [Prod.fst_add, Prod.snd_add, Int.cast_add, Int.cast_one, Int.cast_zero]
    ring_nf
    norm_num

/-- Source separation makes the forced alternate good. -/
theorem next_not_mem (u : Lattice) (q : ℝ) (V : Set Lattice) (i : ℕ)
    (R : Set Lattice)
    (hsep : ∀ x ∈ R, ∀ y ∈ R, x ∈ V → y ∈ V → x ≠ y →
      ¬ (|((x.1 : ℝ) - (y.1 : ℝ))| + |((x.2 : ℝ) - (y.2 : ℝ))| ≤ 2))
    (hp : preferred u q i (vertex u q V i) ∈ R)
    (ha : alternate u q i (vertex u q V i) ∈ R) :
    vertex u q V (i + 1) ∉ V := by
  classical
  rw [vertex_succ]
  split_ifs with hf
  · intro hbad
    obtain ⟨hne, hdist⟩ := candidates_separated u (vertex u q V i) q i
    exact hsep _ hp _ ha hf hbad hne (le_of_eq hdist)
  · exact hf

end GreedyAttachment
end LPPDifferentiability
