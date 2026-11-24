/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Differentiability.FinalDraft.WitnessMultiplicity.Definitions

/-! The first-cut rule specifies a unique sequence of stages and remainder. -/

public section

namespace LPPDifferentiability

namespace Path

/-- Every path from the origin has a decomposition by the first-cut rule. -/
theorem exists_first_stage_decomposition {d : ℕ × ℕ} (p : Path 0 d)
    (a : ℝ) (m : ℕ) (s : ℝ) :
    ∃ N : ℕ, ∃ cuts : Fin (N + 2) → Fin (d.1 + d.2 + 1),
      p.is_first_stage_decomposition a m s cuts := by
  obtain ⟨N, cuts, h0, hlast, hmono, _, hfull, hrem⟩ := p.exists_first_cuts a m s
  exact ⟨N, cuts, h0, hlast, hmono, hfull, hrem⟩

/-- Two decompositions by the first-cut rule have the same full-stage count and cut times. -/
theorem first_stage_decompositions_agree {d : ℕ × ℕ} (p : Path 0 d)
    {a : ℝ} {m : ℕ} {s : ℝ} {N N' : ℕ}
    {cuts : Fin (N + 2) → Fin (d.1 + d.2 + 1)}
    {cuts' : Fin (N' + 2) → Fin (d.1 + d.2 + 1)}
    (hcuts : p.is_first_stage_decomposition a m s cuts)
    (hcuts' : p.is_first_stage_decomposition a m s cuts') :
    N = N' ∧ ∀ (i : Fin (N + 2)) (i' : Fin (N' + 2)), i.val = i'.val → cuts i = cuts' i' := by
  obtain ⟨h0, hlast, _, hfull, hrem⟩ := hcuts
  obtain ⟨h0', hlast', _, hfull', hrem'⟩ := hcuts'
  have agree : ∀ i : ℕ, ∀ hi : i ≤ N, ∀ hi' : i ≤ N',
      cuts ⟨i, by omega⟩ = cuts' ⟨i, by omega⟩ := by
    intro i
    induction i with
    | zero =>
      intro _ _
      exact h0.trans h0'.symm
    | succ i ih =>
      intro hi hi'
      have hprev := ih (by omega) (by omega)
      obtain ⟨hlt, htest, hmin⟩ := hfull ⟨i, by omega⟩
      obtain ⟨hlt', htest', hmin'⟩ := hfull' ⟨i, by omega⟩
      dsimp only at hlt htest hmin hlt' htest' hmin'
      rw [hprev] at hlt htest hmin
      apply le_antisymm
      · apply le_of_not_gt
        intro horder
        exact (p.not_reaches_stage_cut_iff a m s _ _).mpr (hmin _ hlt' horder) htest'
      · apply le_of_not_gt
        intro horder
        exact (p.not_reaches_stage_cut_iff a m s _ _).mpr (hmin' _ hlt horder) htest
  have hN : N = N' := by
    apply le_antisymm
    · apply le_of_not_gt
      intro hlt
      have hprev := agree N' hlt.le le_rfl
      obtain ⟨hnext, htest, _⟩ := hfull ⟨N', hlt⟩
      dsimp only at hnext htest
      rw [hprev] at hnext htest
      exact (p.not_reaches_stage_cut_iff a m s _ _).mpr (hrem' _ hnext) htest
    · apply le_of_not_gt
      intro hlt
      have hprev := agree N le_rfl hlt.le
      obtain ⟨hnext, htest, _⟩ := hfull' ⟨N, hlt⟩
      dsimp only at hnext htest
      rw [← hprev] at hnext htest
      exact (p.not_reaches_stage_cut_iff a m s _ _).mpr (hrem _ hnext) htest
  refine ⟨hN, fun i i' heq => ?_⟩
  by_cases hi : i.val ≤ N
  · have hi' : i.val ≤ N' := by omega
    have hindex : (⟨i.val, by omega⟩ : Fin (N' + 2)) = i' := Fin.ext heq
    simpa only [hindex] using agree i.val hi hi'
  · have hindex : i = Fin.last (N + 1) := Fin.ext (by
      change i.val = N + 1
      have hbound := i.isLt
      omega)
    have hindex' : i' = Fin.last (N' + 1) := Fin.ext (by
      change i'.val = N' + 1
      have hval := congrArg Fin.val hindex
      change i.val = N + 1 at hval
      omega)
    rw [hindex, hindex', hlast, hlast']

/-- For a fixed full-stage count, the first-cut maps agree. -/
theorem first_stage_decomposition_unique {d : ℕ × ℕ} (p : Path 0 d)
    {a : ℝ} {m : ℕ} {s : ℝ} {N : ℕ}
    {cuts cuts' : Fin (N + 2) → Fin (d.1 + d.2 + 1)}
    (hcuts : p.is_first_stage_decomposition a m s cuts)
    (hcuts' : p.is_first_stage_decomposition a m s cuts') : cuts = cuts' :=
  funext fun i => (p.first_stage_decompositions_agree hcuts hcuts').2 i i rfl

end Path

end LPPDifferentiability
