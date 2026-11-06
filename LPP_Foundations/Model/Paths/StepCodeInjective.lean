/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import LPP_Foundations.Model.Paths.StepCode

/-! # The step code determines the path

For fixed start point and displacement, the step code `stepCode` is injective: two paths with the
same step code are equal.
-/

@[expose] public section

namespace LPPDifferentiability

theorem stepCode_injective (u : Lattice) (d : ℕ × ℕ) :
    Function.Injective (@stepCode u d) := by
  classical
  intro p q h
  have hv : p.vertex = q.vertex := by
    funext i
    induction i using Fin.induction with
    | zero => exact p.start.trans q.start.symm
    | succ j ih =>
      have hc := congrFun h j
      dsimp [stepCode] at hc
      by_cases hp : p.vertex j.succ = p.vertex j.castSucc + (1, 0)
      · have hq : q.vertex j.succ = q.vertex j.castSucc + (1, 0) := by
          apply of_decide_eq_true
          rw [← hc]
          exact decide_eq_true hp
        rw [hp, hq, ih]
      · have hq : ¬ q.vertex j.succ = q.vertex j.castSucc + (1, 0) := by
          intro hq
          have ht : decide (p.vertex j.succ = p.vertex j.castSucc + (1, 0)) = true := by
            rw [hc]
            exact decide_eq_true hq
          exact hp (of_decide_eq_true ht)
        rw [(p.step j).resolve_left hp, (q.step j).resolve_left hq, ih]
  cases p
  cases q
  cases hv
  rfl

end LPPDifferentiability
