/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Differentiability.Model.Paths.DefectAlgebra
public import LPP_Foundations.Model.Animals.PathSets
import Mathlib.Data.Nat.Find
import Mathlib.Order.Fin.Basic
import Mathlib.Tactic

/-! Least eligible cuts along an actual finite up-right path. -/

public section

namespace LPPDifferentiability

/-- The stage starting at `k` reaches a longitudinal or transverse cutoff at `l`.
The first such `l > k` ends a full stage, as in `eq:cut`. -/
@[expose] def Path.reaches_stage_cut {d : ℕ × ℕ} (p : Path 0 d) (a : ℝ) (m : ℕ) (s : ℝ)
    (k l : Fin (d.1 + d.2 + 1)) : Prop :=
  2 * m ≤ l.val - k.val ∨
    s ≤ |latticeTransverseCoordinate a (p.vertex l) - latticeTransverseCoordinate a (p.vertex k)|

/-- A cut is reached when at least one of the two thresholds is met. -/
theorem Path.reaches_stage_cut_iff {d : ℕ × ℕ} (p : Path 0 d)
    (a : ℝ) (m : ℕ) (s : ℝ) (k l : Fin (d.1 + d.2 + 1)) :
    p.reaches_stage_cut a m s k l ↔
      2 * m ≤ l.val - k.val ∨
        s ≤ |latticeTransverseCoordinate a (p.vertex l) - latticeTransverseCoordinate a (p.vertex k)| :=
  Iff.rfl

/-- Before a stage reaches a cutoff, both its length and transverse displacement are strictly
below their thresholds. -/
theorem Path.not_reaches_stage_cut_iff {d : ℕ × ℕ} (p : Path 0 d)
    (a : ℝ) (m : ℕ) (s : ℝ) (k l : Fin (d.1 + d.2 + 1)) :
    ¬ p.reaches_stage_cut a m s k l ↔
      l.val - k.val < 2 * m ∧
        |latticeTransverseCoordinate a (p.vertex l) - latticeTransverseCoordinate a (p.vertex k)| < s := by
  simp only [reaches_stage_cut_iff, not_or, not_le]

private theorem finite_first_cuts (L : ℕ) (C : Fin (L + 1) → Fin (L + 1) → Prop)
    (k : Fin (L + 1)) :
    ∃ N : ℕ, ∃ c : Fin (N + 2) → Fin (L + 1),
      c 0 = k ∧ c (Fin.last (N + 1)) = Fin.last L ∧ Monotone c ∧
      N ≤ L - k.val ∧
      (∀ i : Fin N, c ⟨i.val, by omega⟩ < c ⟨i.val + 1, by omega⟩ ∧
        C (c ⟨i.val, by omega⟩) (c ⟨i.val + 1, by omega⟩) ∧
        ∀ t, c ⟨i.val, by omega⟩ < t → t < c ⟨i.val + 1, by omega⟩ →
          ¬ C (c ⟨i.val, by omega⟩) t) ∧
      (∀ t, c ⟨N, by omega⟩ < t → ¬ C (c ⟨N, by omega⟩) t) := by
  classical
  suffices ∀ n, ∀ k : Fin (L + 1), L - k.val = n →
      ∃ N : ℕ, ∃ c : Fin (N + 2) → Fin (L + 1),
        c 0 = k ∧ c (Fin.last (N + 1)) = Fin.last L ∧ Monotone c ∧
        N ≤ L - k.val ∧
        (∀ i : Fin N, c ⟨i.val, by omega⟩ < c ⟨i.val + 1, by omega⟩ ∧
          C (c ⟨i.val, by omega⟩) (c ⟨i.val + 1, by omega⟩) ∧
          ∀ t, c ⟨i.val, by omega⟩ < t → t < c ⟨i.val + 1, by omega⟩ →
            ¬ C (c ⟨i.val, by omega⟩) t) ∧
        (∀ t, c ⟨N, by omega⟩ < t → ¬ C (c ⟨N, by omega⟩) t) from
    this _ k rfl
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro k hkn
    by_cases hex : ∃ t : Fin (L + 1), k < t ∧ C k t
    · have hn : ∃ t : ℕ, ∃ ht : t < L + 1, k.val < t ∧ C k ⟨t, ht⟩ := by
        obtain ⟨t, ht, hc⟩ := hex
        exact ⟨t.val, t.isLt, ht, hc⟩
      obtain ⟨ht, hkt, hC⟩ := Nat.find_spec hn
      let t : Fin (L + 1) := ⟨Nat.find hn, ht⟩
      have hmin : ∀ j : Fin (L + 1), k < j → j < t → ¬ C k j := by
        intro j hkj hjt hc
        exact Nat.find_min hn hjt ⟨j.isLt, hkj, hc⟩
      obtain ⟨N, c, hc0, hcl, hmono, hN, hfull, hrem⟩ :=
        ih (L - t.val) (by dsimp [t]; omega) t rfl
      let b : Fin (N + 1 + 2) → Fin (L + 1) := Fin.cases k c
      refine ⟨N + 1, b, rfl, hcl, ?_, ?_, ?_, hrem⟩
      · apply Fin.monotone_iff_le_succ.mpr
        intro i
        refine Fin.cases ?_ (fun j => ?_) i
        · change k ≤ c 0
          rw [hc0]
          exact le_of_lt hkt
        · exact hmono (by change j.val ≤ j.val + 1; omega)
      · dsimp [t] at hN
        omega
      · intro i
        refine Fin.cases ?_ (fun j => ?_) i
        · change k < c 0 ∧ C k (c 0) ∧
            (∀ j, k < j → j < c 0 → ¬ C k j)
          rw [hc0]
          exact ⟨hkt, hC, hmin⟩
        · exact hfull j
    · let c : Fin 2 → Fin (L + 1) := Fin.cases k (fun _ => Fin.last L)
      refine ⟨0, c, rfl, rfl, ?_, by omega, ?_, ?_⟩
      · apply Fin.monotone_iff_le_succ.mpr
        intro i
        have hi : i = 0 := Fin.ext (by omega)
        subst i
        exact Fin.le_last k
      · intro i
        exact Fin.elim0 i
      · intro t hkt hc
        exact hex ⟨t, hkt, hc⟩

/-- Actual first-cut stages, with a possibly empty final remainder. All cuts
and their minimality are produced from the path, rather than supplied. -/
theorem Path.exists_first_cuts {d : ℕ × ℕ} (p : Path 0 d) (a : ℝ) (m : ℕ) (s : ℝ) :
    let transverse (t : Fin (d.1 + d.2 + 1)) := latticeTransverseCoordinate a (p.vertex t)
    ∃ N : ℕ, ∃ cuts : Fin (N + 2) → Fin (d.1 + d.2 + 1),
      cuts 0 = 0 ∧ cuts (Fin.last (N + 1)) = Fin.last (d.1 + d.2) ∧
      Monotone cuts ∧ N ≤ d.1 + d.2 ∧
      (∀ i : Fin N,
        let k := cuts ⟨i.val, by omega⟩
        let l := cuts ⟨i.val + 1, by omega⟩
        k < l ∧ p.reaches_stage_cut a m s k l ∧
        ∀ t, k < t → t < l →
          t.val - k.val < 2 * m ∧ |transverse t - transverse k| < s) ∧
      (∀ t, cuts ⟨N, by omega⟩ < t →
        t.val - (cuts ⟨N, by omega⟩).val < 2 * m ∧
        |transverse t - transverse (cuts ⟨N, by omega⟩)| < s) := by
  obtain ⟨N, cuts, h0, hlast, hmono, hN, hfull, hrem⟩ :=
    finite_first_cuts (d.1 + d.2) (p.reaches_stage_cut a m s) 0
  refine ⟨N, cuts, h0, hlast, hmono, by simpa using hN, ?_, ?_⟩
  · intro i
    obtain ⟨hlt, hc, hmin⟩ := hfull i
    refine ⟨hlt, hc, ?_⟩
    intro t hkt htl
    exact (p.not_reaches_stage_cut_iff a m s _ t).mp (hmin t hkt htl)
  · intro t ht
    exact (p.not_reaches_stage_cut_iff a m s _ t).mp (hrem t ht)

end LPPDifferentiability
