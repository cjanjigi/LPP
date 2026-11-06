/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import LPP_Foundations.Frozen.Model.LastPassage
public import Mathlib.MeasureTheory.MeasurableSpace.Pi
public import Mathlib.MeasureTheory.Group.Arithmetic
public import Mathlib.MeasureTheory.Order.Lattice
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

/-!
# Measurability of path weights and passage times

For fixed endpoints, each path weight is a finite sum of measurable coordinate maps. The
last-passage value is the finite supremum of those path weights.
-/

@[expose] public section

open scoped BigOperators

namespace LPPDifferentiability

/-- The weight of any fixed path is measurable as a function of the environment. -/
theorem measurable_pathWeight {u : Lattice} {d : ℕ × ℕ} (p : Path u d) :
    Measurable (fun ω : Environment => pathWeight ω p) := by
  classical
  simp only [pathWeight]
  exact Finset.univ.measurable_fun_sum fun i _ =>
    measurable_pi_apply (p.vertex i.castSucc)

/-- Last-passage value is measurable for every fixed start and displacement. -/
theorem measurable_lastPassage (u : Lattice) (d : ℕ × ℕ) :
    Measurable (fun ω : Environment => lastPassage ω u d) := by
  classical
  have hsup :
      Measurable
        (Finset.univ.sup' Finset.univ_nonempty
          (fun p : Path u d => fun ω : Environment => pathWeight ω p)) :=
    Finset.measurable_sup' Finset.univ_nonempty fun p _ => measurable_pathWeight p
  have heq :
      (fun ω : Environment => lastPassage ω u d) =
        Finset.univ.sup' Finset.univ_nonempty
          (fun p : Path u d => fun ω : Environment => pathWeight ω p) := by
    funext ω
    simp [lastPassage, Finset.max'_eq_sup', Finset.sup'_image]
  rw [heq]
  exact hsup

end LPPDifferentiability
