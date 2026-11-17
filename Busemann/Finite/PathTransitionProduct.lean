/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Busemann.Finite.PartitionRecursion
public import Busemann.Frozen.Definitions.FiniteEdgeStep
public import Busemann.Frozen.Definitions.FiniteTiltCoordinate
public import LPP_Foundations.Model.Paths.StepCode
import LPP_Foundations.Model.Paths.Count
import LPP_Foundations.Model.Paths.Level
import Mathlib.Tactic

/-! The deterministic transition product underlying the finite Gibbs path law. -/

@[expose] public section

open LPPDifferentiability
open scoped BigOperators

namespace LPP.Busemann

private theorem prod_successive_ratios {n : ℕ} (F : Fin (n + 1) → ℝ)
    (hF : ∀ i, F i ≠ 0) :
    (∏ j : Fin n, F j.succ / F j.castSucc) = F (Fin.last n) / F 0 := by
  rw [Finset.prod_div_distrib]
  have hden : (∏ j : Fin n, F j.castSucc) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun j _ => hF j.castSucc)
  apply (div_eq_div_iff hden (hF 0)).2
  have hfull := (Fin.prod_univ_succ F).symm.trans (Fin.prod_univ_castSucc F)
  simpa only [mul_comm] using hfull

private theorem sum_actual_tilt (h : ℝ × ℝ) {x : Lattice} {d : ℕ × ℕ}
    (p : LPPDifferentiability.Path x d) :
    (∑ j : Fin (d.1 + d.2),
      finiteTiltCoordinate h (if stepCode p j = true then 0 else 1)) =
        h.1 * (d.1 : ℝ) + h.2 * (d.2 : ℝ) := by
  classical
  have heast : (Finset.univ.filter (fun j => stepCode p j = true)).card = d.1 :=
    p.card_eastSteps
  have hnorth : (Finset.univ.filter (fun j => ¬ stepCode p j = true)).card = d.2 := by
    have hcount := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (Fin (d.1 + d.2)))) (fun j => stepCode p j = true)
    simp only [Finset.card_univ, Fintype.card_fin, heast] at hcount
    omega
  have hcoordinate (j : Fin (d.1 + d.2)) :
      finiteTiltCoordinate h (if stepCode p j = true then 0 else 1) =
        if stepCode p j = true then h.1 else h.2 := by
    by_cases hj : stepCode p j = true
    · simp only [hj, ite_true, finiteTiltCoordinate, Fin.val_zero]
    · simp [hj, finiteTiltCoordinate]
  simp_rw [hcoordinate]
  rw [Finset.sum_ite]
  simp only [Finset.sum_const, nsmul_eq_mul, heast, hnorth]
  ring

/-- Along an actual finite path, the corrected departure transition ratios
multiply to its normalized exponential weight. This is the deterministic
path-weight calculation in JR1810.03580v3, Appendix A.1, with the departure-site correction; it makes no probability-law assertion. -/
theorem finite_path_transition_product (ω : Environment) (h : ℝ × ℝ)
    (β : ℝ) (hβ : 0 < β) (x : Lattice) (d : ℕ × ℕ)
    (p : LPPDifferentiability.Path x d) :
    let Z : ℕ → Lattice → ℝ := fun n y =>
      ∑ k : Fin (n + 1), ∑ a : LPPDifferentiability.Path y (k.val, n - k.val),
        Real.exp (β * (pathWeight ω a + h.1 * (k.val : ℝ) +
          h.2 * ((n - k.val : ℕ) : ℝ)))
    let L : ℤ := x.1 + x.2 + ((d.1 + d.2 : ℕ) : ℤ)
    let r : Lattice → ℕ := fun y => (L - y.1 - y.2).toNat
    let q : Lattice → Fin 2 → ℝ := fun y i =>
      Real.exp (β * (ω y + finiteTiltCoordinate h i)) *
        Z (r y - 1) (y + finiteEdgeStep i) / Z (r y) y
    (∏ j : Fin (d.1 + d.2),
      q (p.vertex j.castSucc) (if stepCode p j = true then 0 else 1)) =
        Real.exp (β * (pathWeight ω p + h.1 * (d.1 : ℝ) +
          h.2 * (d.2 : ℝ))) / Z (d.1 + d.2) x := by
  classical
  let Z : ℕ → Lattice → ℝ := fun n y =>
    ∑ k : Fin (n + 1), ∑ a : LPPDifferentiability.Path y (k.val, n - k.val),
      Real.exp (β * (pathWeight ω a + h.1 * (k.val : ℝ) +
        h.2 * ((n - k.val : ℕ) : ℝ)))
  let L : ℤ := x.1 + x.2 + ((d.1 + d.2 : ℕ) : ℤ)
  let r : Lattice → ℕ := fun y => (L - y.1 - y.2).toNat
  let q : Lattice → Fin 2 → ℝ := fun y i =>
    Real.exp (β * (ω y + finiteTiltCoordinate h i)) *
      Z (r y - 1) (y + finiteEdgeStep i) / Z (r y) y
  change (∏ j : Fin (d.1 + d.2),
    q (p.vertex j.castSucc) (if stepCode p j = true then 0 else 1)) = _

  -- The absolute terminal level gives the exact remaining horizon everywhere on p.
  have hr (i : Fin (d.1 + d.2 + 1)) : r (p.vertex i) = d.1 + d.2 - i.val := by
    have hlevel := p.level i
    dsimp only [r, L]
    omega
  have hrpos (j : Fin (d.1 + d.2)) : 0 < r (p.vertex j.castSucc) := by
    rw [hr]
    have hj := j.isLt
    simp only [Fin.val_castSucc]
    omega
  have hrnext (j : Fin (d.1 + d.2)) :
      r (p.vertex j.succ) = r (p.vertex j.castSucc) - 1 := by
    have hpositive := hrpos j
    rw [hr, hr] at *
    simp only [Fin.val_succ, Fin.val_castSucc] at *
    omega

  -- The actual step code selects the actual next vertex, including signed origins.
  have hstep (j : Fin (d.1 + d.2)) :
      p.vertex j.castSucc + finiteEdgeStep (if stepCode p j = true then 0 else 1) =
        p.vertex j.succ := by
    by_cases hc : stepCode p j = true
    · have he : p.vertex j.succ = p.vertex j.castSucc + (1, 0) :=
        of_decide_eq_true hc
      simpa only [hc, ite_true, finiteEdgeStep, Fin.val_zero] using he.symm
    · have he : ¬ p.vertex j.succ = p.vertex j.castSucc + (1, 0) := by
        intro he
        exact hc (decide_eq_true he)
      have hn := (p.step j).resolve_left he
      simpa [hc, finiteEdgeStep] using hn.symm

  -- Positive actual partition values justify all cancellations in the finite telescope.
  let F : Fin (d.1 + d.2 + 1) → ℝ := fun i => Z (r (p.vertex i)) (p.vertex i)
  have hF (i : Fin (d.1 + d.2 + 1)) : F i ≠ 0 := by
    have hpos := (finite_tilted_partition_zero_pos_succ ω h β hβ
      (r (p.vertex i)) (p.vertex i)).2.1
    exact ne_of_gt hpos
  have hfirst : F 0 = Z (d.1 + d.2) x := by
    dsimp only [F]
    rw [hr, p.start]
    simp only [Fin.val_zero, Nat.sub_zero]
  have hlast : F (Fin.last (d.1 + d.2)) = 1 := by
    dsimp only [F]
    rw [hr]
    simp only [Fin.val_last, Nat.sub_self]
    exact (finite_tilted_partition_zero_pos_succ ω h β hβ 0
      (p.vertex (Fin.last (d.1 + d.2)))).1
  have hfactor (j : Fin (d.1 + d.2)) :
      q (p.vertex j.castSucc) (if stepCode p j = true then 0 else 1) =
        Real.exp (β * (ω (p.vertex j.castSucc) +
          finiteTiltCoordinate h (if stepCode p j = true then 0 else 1))) *
            (F j.succ / F j.castSucc) := by
    dsimp only [q, F]
    rw [hstep, hrnext]
    ring

  -- The exponential product is the terminal-excluded path weight and exact tilt counts.
  have hexp :
      (∏ j : Fin (d.1 + d.2), Real.exp (β * (ω (p.vertex j.castSucc) +
        finiteTiltCoordinate h (if stepCode p j = true then 0 else 1)))) =
      Real.exp (β * (pathWeight ω p + h.1 * (d.1 : ℝ) + h.2 * (d.2 : ℝ))) := by
    rw [← Real.exp_sum]
    congr 1
    rw [← Finset.mul_sum, Finset.sum_add_distrib, sum_actual_tilt h p]
    unfold pathWeight
    ring
  calc
    _ = (∏ j : Fin (d.1 + d.2), Real.exp (β * (ω (p.vertex j.castSucc) +
          finiteTiltCoordinate h (if stepCode p j = true then 0 else 1)))) *
        (∏ j : Fin (d.1 + d.2), F j.succ / F j.castSucc) := by
      simp_rw [hfactor]
      exact Finset.prod_mul_distrib
    _ = _ := by
      rw [prod_successive_ratios F hF, hlast, hfirst, hexp]
      ring

end LPP.Busemann
