/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import LPP_Foundations.Frozen.Model.Lattice
public import Mathlib.Data.Finset.Prod
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-! Exact l1 radius-two neighbors of a signed lattice site. -/

public section

namespace LPPDifferentiability

/-- Every signed lattice site has exactly twelve other sites at real l1-distance at most two. -/
theorem exists_lattice_l1_neighbors_card_eq_twelve (u : Lattice) :
    ∃ N : Finset Lattice,
      (∀ v : Lattice, v ∈ N ↔ v ≠ u ∧
        |(v.1 : ℝ) - (u.1 : ℝ)| + |(v.2 : ℝ) - (u.2 : ℝ)| ≤ 2) ∧
      N.card = 12 := by
  classical
  let offsets : Finset Lattice :=
    {(1, 0), (-1, 0), (2, 0), (-2, 0), (0, 1), (0, -1),
      (0, 2), (0, -2), (1, 1), (1, -1), (-1, 1), (-1, -1)}
  have offsets_iff (d : Lattice) :
      d ∈ offsets ↔ d ≠ (0, 0) ∧
        |(d.1 : ℝ)| + |(d.2 : ℝ)| ≤ 2 := by
    constructor
    · intro hd
      simp only [offsets, Finset.mem_insert, Finset.mem_singleton] at hd
      rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals norm_num
    · rintro ⟨hdne, hdist⟩
      rcases d with ⟨a, b⟩
      have ha_abs : |(a : ℝ)| ≤ 2 := by
        have hb_nonneg : 0 ≤ |(b : ℝ)| := abs_nonneg _
        linarith
      have hb_abs : |(b : ℝ)| ≤ 2 := by
        have ha_nonneg : 0 ≤ |(a : ℝ)| := abs_nonneg _
        linarith
      have ha_bounds : (-2 : ℤ) ≤ a ∧ a ≤ 2 := by
        exact_mod_cast (abs_le.mp ha_abs)
      have hb_bounds : (-2 : ℤ) ≤ b ∧ b ≤ 2 := by
        exact_mod_cast (abs_le.mp hb_abs)
      rcases ha_bounds with ⟨ha_lo, ha_hi⟩
      rcases hb_bounds with ⟨hb_lo, hb_hi⟩
      interval_cases a <;> interval_cases b <;> norm_num [offsets] at *
  have offsets_card : offsets.card = 12 := by
    norm_num [offsets]
  let N := offsets.image (fun d : Lattice => u + d)
  have translate_injective : Function.Injective (fun d : Lattice => u + d) := by
    intro a b hab
    exact add_left_cancel hab
  refine ⟨N, ?_, ?_⟩
  · intro v
    change v ∈ offsets.image (fun d : Lattice => u + d) ↔ _
    constructor
    · intro hv
      rcases Finset.mem_image.mp hv with ⟨d, hd, hEq⟩
      subst v
      rcases (offsets_iff d).mp hd with ⟨hdne, hdist⟩
      refine ⟨?_, ?_⟩
      · intro hu
        apply hdne
        apply add_left_cancel
        calc
          u + d = u := hu
          _ = u + (0, 0) := by simp
      · simpa using hdist
    · rintro ⟨hvne, hdist⟩
      have hdiff_ne : v - u ≠ (0, 0) := by
        intro hzero
        apply hvne
        calc
          v = (v - u) + u := by simp
          _ = (0, 0) + u := by rw [hzero]
          _ = u := by simp
      have hdiff_dist :
          |((v - u).1 : ℝ)| + |((v - u).2 : ℝ)| ≤ 2 := by
        simpa using hdist
      have hdiff_mem : v - u ∈ offsets :=
        (offsets_iff (v - u)).mpr ⟨hdiff_ne, hdiff_dist⟩
      apply Finset.mem_image.mpr
      refine ⟨v - u, hdiff_mem, ?_⟩
      calc
        u + (v - u) = (v - u) + u := add_comm _ _
        _ = v := sub_add_cancel _ _
  · change (offsets.image (fun d : Lattice => u + d)).card = 12
    rw [Finset.card_image_of_injective _ translate_injective, offsets_card]

end LPPDifferentiability

end
