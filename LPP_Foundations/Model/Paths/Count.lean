/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import LPP_Foundations.Model.Paths.Fintype
public import Mathlib.Data.Finset.Powerset
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.Card
import Lean.Elab.Tactic.Omega

/-! The binomial upper bound for the actual finite up-right path carrier. -/

@[expose] public section

namespace LPPDifferentiability

/-- The indices at which an actual path takes an east step. -/
noncomputable def Path.eastSteps {u : Lattice} {d : ℕ × ℕ} (p : Path u d) :
    Finset (Fin (d.1 + d.2)) :=
  Finset.univ.filter (fun i => stepCode p i = true)

/-- The subset encoding uses precisely the already defined actual step word. -/
@[simp] theorem Path.mem_eastSteps {u : Lattice} {d : ℕ × ℕ} (p : Path u d)
    (i : Fin (d.1 + d.2)) : i ∈ p.eastSteps ↔ stepCode p i = true := by
  classical
  simp only [Path.eastSteps, Finset.mem_filter, Finset.mem_univ, true_and]

/-- The endpoint forces exactly the first displacement's number of east steps. -/
theorem Path.card_eastSteps {u : Lattice} {d : ℕ × ℕ} (p : Path u d) :
    p.eastSteps.card = d.1 := by
  classical
  have hstep (i : Fin (d.1 + d.2)) :
      (if stepCode p i = true then (1 : ℤ) else 0) =
        (p.vertex i.succ).1 - (p.vertex i.castSucc).1 := by
    by_cases h : p.vertex i.succ = p.vertex i.castSucc + (1, 0)
    · have hc : stepCode p i = true := decide_eq_true h
      rw [ite_eq_left hc, h]
      change (1 : ℤ) = (p.vertex i.castSucc).1 + 1 - (p.vertex i.castSucc).1
      omega
    · have hn := (p.step i).resolve_left h
      have hc : ¬ stepCode p i = true := by
        intro ht
        exact h (of_decide_eq_true ht)
      rw [ite_eq_right hc, hn]
      change (0 : ℤ) = (p.vertex i.castSucc).1 + 0 - (p.vertex i.castSucc).1
      omega
  have hsum := Fin.sum_univ_succ (fun i => (p.vertex i).1)
  have hsum' := Fin.sum_univ_castSucc (fun i => (p.vertex i).1)
  have hcount : (p.eastSteps.card : ℤ) = d.1 := by
    rw [Path.eastSteps, Finset.natCast_card_filter]
    simp_rw [hstep]
    rw [Finset.sum_sub_distrib]
    simp only [p.start, p.finish, Prod.fst_add] at hsum hsum'
    omega
  omega

/-- The east-step subset determines all vertices from the fixed starting point. -/
theorem Path.eastSteps_injective (u : Lattice) (d : ℕ × ℕ) :
    Function.Injective (@Path.eastSteps u d) := by
  intro p q h
  apply stepCode_injective u d
  funext i
  have hm : stepCode p i = true ↔ stepCode q i = true := by
    rw [← Path.mem_eastSteps, ← Path.mem_eastSteps, h]
  cases hp : stepCode p i <;> cases hq : stepCode q i <;> simp_all

/-- The number of actual up-right paths is bounded by the binomial allocation count. -/
theorem path_card_le_choose (u : Lattice) (d : ℕ × ℕ) :
    Fintype.card (Path u d) ≤ Nat.choose (d.1 + d.2) d.1 := by
  classical
  let encode : Path u d → ↥((Finset.univ : Finset (Fin (d.1 + d.2))).powersetCard d.1) :=
    fun p => ⟨p.eastSteps, Finset.mem_powersetCard.mpr
      ⟨Finset.subset_univ _, p.card_eastSteps⟩⟩
  have hinj : Function.Injective encode := by
    intro p q h
    exact Path.eastSteps_injective u d (congrArg Subtype.val h)
  have hcard := Fintype.card_le_of_injective encode hinj
  simpa only [Fintype.card_coe, Finset.card_powersetCard, Finset.card_univ,
    Fintype.card_fin] using hcard

end LPPDifferentiability
