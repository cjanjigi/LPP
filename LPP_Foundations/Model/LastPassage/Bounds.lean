/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import LPP_Foundations.Model.LastPassage.Basic
public import LPP_Foundations.Model.Paths.WeightBounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Deterministic comparison bounds for finite last-passage maxima. -/

@[expose] public section

namespace LPPDifferentiability

/-- Pointwise comparison of environments gives comparison of their passage maxima. -/
theorem lastPassage_mono (ω η : Environment) (u : Lattice) (d : ℕ × ℕ)
    (h : ∀ z, ω z ≤ η z) :
    lastPassage ω u d ≤ lastPassage η u d := by
  obtain ⟨p, hp⟩ := exists_pathWeight_eq_lastPassage ω u d
  calc
    lastPassage ω u d = pathWeight ω p := hp.symm
    _ ≤ pathWeight η p := pathWeight_mono ω η p h
    _ ≤ lastPassage η u d := pathWeight_le_lastPassage η p

/-- The passage maximum of a sum of environments is at most the sum of maxima. -/
theorem lastPassage_add_le (ω η : Environment) (u : Lattice) (d : ℕ × ℕ) :
    lastPassage (ω + η) u d ≤ lastPassage ω u d + lastPassage η u d := by
  obtain ⟨p, hp⟩ := exists_pathWeight_eq_lastPassage (ω + η) u d
  calc
    lastPassage (ω + η) u d = pathWeight (ω + η) p := hp.symm
    _ = pathWeight ω p + pathWeight η p := pathWeight_add ω η p
    _ ≤ lastPassage ω u d + lastPassage η u d :=
      add_le_add (pathWeight_le_lastPassage ω p) (pathWeight_le_lastPassage η p)

/-- A constant environment has the same weight along every path with a given displacement. -/
theorem lastPassage_const (u : Lattice) (d : ℕ × ℕ) (c : ℝ) :
    lastPassage (fun _ : Lattice => c) u d = ((d.1 + d.2 : ℕ) : ℝ) * c := by
  obtain ⟨p, hp⟩ := exists_pathWeight_eq_lastPassage (fun _ : Lattice => c) u d
  calc
    lastPassage (fun _ : Lattice => c) u d = pathWeight (fun _ : Lattice => c) p := hp.symm
    _ = ((d.1 + d.2 : ℕ) : ℝ) * c := pathWeight_const c p

/-- A pointwise upper bound on site weights bounds every last-passage maximum. -/
theorem lastPassage_le_const (ω : Environment) (u : Lattice) (d : ℕ × ℕ)
    (c : ℝ) (h : ∀ z, ω z ≤ c) :
    lastPassage ω u d ≤ ((d.1 + d.2 : ℕ) : ℝ) * c := by
  calc
    lastPassage ω u d ≤ lastPassage (fun _ : Lattice => c) u d :=
      lastPassage_mono ω (fun _ : Lattice => c) u d h
    _ = ((d.1 + d.2 : ℕ) : ℝ) * c := lastPassage_const u d c

/-- A pointwise lower bound on site weights bounds every last-passage maximum below. -/
theorem const_le_lastPassage (ω : Environment) (u : Lattice) (d : ℕ × ℕ)
    (c : ℝ) (h : ∀ z, c ≤ ω z) :
    ((d.1 + d.2 : ℕ) : ℝ) * c ≤ lastPassage ω u d := by
  calc
    ((d.1 + d.2 : ℕ) : ℝ) * c = lastPassage (fun _ : Lattice => c) u d :=
      (lastPassage_const u d c).symm
    _ ≤ lastPassage ω u d := lastPassage_mono (fun _ : Lattice => c) ω u d h

/-- Uniform absolute bounds on site weights give an absolute bound on passage time. -/
theorem lastPassage_abs_le (ω : Environment) (u : Lattice) (d : ℕ × ℕ)
    (B : ℝ) (h : ∀ z, |ω z| ≤ B) :
    |lastPassage ω u d| ≤ ((d.1 + d.2 : ℕ) : ℝ) * B := by
  have hupper : ∀ z, ω z ≤ B := fun z => (abs_le.mp (h z)).2
  have hlower : ∀ z, -B ≤ ω z := fun z => (abs_le.mp (h z)).1
  have hupper' := lastPassage_le_const ω u d B hupper
  have hlower' := const_le_lastPassage ω u d (-B) hlower
  apply abs_le.mpr
  constructor
  · calc
      -(((d.1 + d.2 : ℕ) : ℝ) * B) = ((d.1 + d.2 : ℕ) : ℝ) * (-B) := by ring
      _ ≤ lastPassage ω u d := hlower'
  · exact hupper'

/-- A pointwise perturbation bound controls the change in the passage maximum. -/
theorem lastPassage_sub_abs_le (ω η : Environment) (u : Lattice) (d : ℕ × ℕ)
    (B : ℝ) (h : ∀ z, |ω z - η z| ≤ B) :
    |lastPassage ω u d - lastPassage η u d| ≤ ((d.1 + d.2 : ℕ) : ℝ) * B := by
  have hωη : ∀ z, ω z ≤ (η + fun _ : Lattice => B) z := by
    intro z
    dsimp
    have hz := (abs_le.mp (h z)).2
    linarith
  have hηω : ∀ z, η z ≤ (ω + fun _ : Lattice => B) z := by
    intro z
    dsimp
    have hz := (abs_le.mp (h z)).1
    linarith
  have hup : lastPassage ω u d ≤ lastPassage η u d + ((d.1 + d.2 : ℕ) : ℝ) * B := by
    calc
      lastPassage ω u d ≤ lastPassage (η + fun _ : Lattice => B) u d :=
        lastPassage_mono ω (η + fun _ : Lattice => B) u d hωη
      _ ≤ lastPassage η u d + lastPassage (fun _ : Lattice => B) u d :=
        lastPassage_add_le η (fun _ : Lattice => B) u d
      _ = lastPassage η u d + ((d.1 + d.2 : ℕ) : ℝ) * B := by
        rw [lastPassage_const]
  have hlow : lastPassage η u d ≤ lastPassage ω u d + ((d.1 + d.2 : ℕ) : ℝ) * B := by
    calc
      lastPassage η u d ≤ lastPassage (ω + fun _ : Lattice => B) u d :=
        lastPassage_mono η (ω + fun _ : Lattice => B) u d hηω
      _ ≤ lastPassage ω u d + lastPassage (fun _ : Lattice => B) u d :=
        lastPassage_add_le ω (fun _ : Lattice => B) u d
      _ = lastPassage ω u d + ((d.1 + d.2 : ℕ) : ℝ) * B := by
        rw [lastPassage_const]
  apply abs_le.mpr
  constructor <;> linarith

end LPPDifferentiability
