/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import LPP_Foundations.Model.LastPassage.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-! A deterministic terminal-excluded LPP bound from an additive edge potential. -/

public section

open LPPDifferentiability
open scoped BigOperators

namespace LPP

/-- The edge potential along a finite vertex sequence telescopes; see GRS
1510.00860v2, Lemma 4.1(a). -/
theorem finite_edge_potential_telescope (n : ℕ)
    (C : Lattice → Lattice → ℝ)
    (hC : ∀ x y z, C x y + C y z = C x z)
    (v : Fin (n + 1) → Lattice) :
    (∑ i : Fin n, C (v i.castSucc) (v i.succ)) =
      C (v 0) (v (Fin.last n)) := by
  induction n with
  | zero =>
      have hzero := hC (v 0) (v 0) (v 0)
      have hCxx : C (v 0) (v 0) = 0 := by linarith
      simp [hCxx]
  | succ n ih =>
      let tail : Fin (n + 1) → Lattice := fun j => v j.succ
      have htail := ih tail
      have htail' :
          (∑ j : Fin n, C (v j.succ.castSucc) (v j.succ.succ)) =
            C (v (0 : Fin (n + 1)).succ) (v (Fin.last (n + 1))) := by
        calc
          (∑ j : Fin n, C (v j.succ.castSucc) (v j.succ.succ)) =
              ∑ j : Fin n, C (tail j.castSucc) (tail j.succ) := by
                apply Finset.sum_congr rfl
                intro j hj
                dsimp [tail]
          _ = C (tail 0) (tail (Fin.last n)) := htail
          _ = C (v (0 : Fin (n + 1)).succ) (v (Fin.last (n + 1))) := by
                congr 2
      calc
        (∑ i : Fin (n + 1), C (v i.castSucc) (v i.succ)) =
            C (v (0 : Fin (n + 2))) (v (0 : Fin (n + 1)).succ) +
              ∑ j : Fin n, C (v j.succ.castSucc) (v j.succ.succ) := by
                simp [Fin.sum_univ_succ]
        _ = C (v (0 : Fin (n + 2))) (v (0 : Fin (n + 1)).succ) +
              C (v (0 : Fin (n + 1)).succ) (v (Fin.last (n + 1))) := by rw [htail']
        _ = C (v (0 : Fin (n + 2))) (v (Fin.last (n + 1))) := hC _ _ _

/-- Bound one path by its additive edge potential and a signed per-step error. -/
private theorem pathWeight_le_additivePotential (C : Lattice → Lattice → ℝ)
    (hC : ∀ x y z, C x y + C y z = C x z)
    (ω : Environment) (c : ℝ)
    (hright : ∀ x, ω x - C x (x + (1, 0)) ≤ c)
    (hup : ∀ x, ω x - C x (x + (0, 1)) ≤ c)
    {u : Lattice} {d : ℕ × ℕ} (p : Path u d) :
    pathWeight ω p ≤
      C u (u + ((d.1 : ℤ), (d.2 : ℤ))) + ((d.1 + d.2 : ℕ) : ℝ) * c := by
  let n := d.1 + d.2
  let v : Fin (n + 1) → Lattice := fun i => p.vertex i
  have hstart : v 0 = u := by
    dsimp [v]
    simpa using p.start
  have hend : v (Fin.last n) = u + ((d.1 : ℤ), (d.2 : ℤ)) := by
    dsimp [v, n]
    simpa using p.finish
  have hstep_bound (i : Fin n) :
      ω (v i.castSucc) ≤ C (v i.castSucc) (v i.succ) + c := by
    dsimp [v]
    rcases p.step i with h | h
    · rw [h]
      linarith [hright (p.vertex i.castSucc)]
    · rw [h]
      linarith [hup (p.vertex i.castSucc)]
  have hsum_bound :
      (∑ i : Fin n, ω (v i.castSucc)) ≤
        ∑ i : Fin n, (C (v i.castSucc) (v i.succ) + c) := by
    apply Finset.sum_le_sum
    intro i hi
    exact hstep_bound i
  have hweight :
      pathWeight ω p = ∑ i : Fin n, ω (v i.castSucc) := by
    rfl
  rw [hweight]
  calc
    (∑ i : Fin n, ω (v i.castSucc)) ≤
        ∑ i : Fin n, (C (v i.castSucc) (v i.succ) + c) := hsum_bound
    _ = (∑ i : Fin n, C (v i.castSucc) (v i.succ)) +
          (∑ _i : Fin n, c) := Finset.sum_add_distrib
    _ = C u (u + ((d.1 : ℤ), (d.2 : ℤ))) +
          ((d.1 + d.2 : ℕ) : ℝ) * c := by
        rw [finite_edge_potential_telescope n C hC v, hstart, hend]
        simp [n, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- Every finite LPP passage value obeys the all-start local edge bound. -/
theorem lastPassage_le_additivePotential_add_steps (C : Lattice → Lattice → ℝ)
    (hC : ∀ x y z, C x y + C y z = C x z)
    (ω : Environment) (c : ℝ)
    (hright : ∀ x, ω x - C x (x + (1, 0)) ≤ c)
    (hup : ∀ x, ω x - C x (x + (0, 1)) ≤ c)
    (u : Lattice) (d : ℕ × ℕ) :
    lastPassage ω u d ≤
      C u (u + ((d.1 : ℤ), (d.2 : ℤ))) + ((d.1 + d.2 : ℕ) : ℝ) * c := by
  obtain ⟨p, hp⟩ := exists_pathWeight_eq_lastPassage ω u d
  rw [← hp]
  exact pathWeight_le_additivePotential C hC ω c hright hup p

end LPP
