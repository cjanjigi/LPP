/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import LPP_Foundations.Model.Paths.StepCodeInjective
public import Mathlib.Data.Fintype.OfMap
public import Mathlib.Data.Fintype.Pi

/-!
# Finiteness of the type of paths

A directed path with starting point `u` and displacement `d` is determined by its step code, and
the step code is injective. So the type of such paths is finite; this file records the `Fintype`
instance. -/

@[expose] public section

namespace LPPDifferentiability

noncomputable instance pathFintype (u : Lattice) (d : ℕ × ℕ) : Fintype (Path u d) :=
  Fintype.ofInjective stepCode (stepCode_injective u d)

end LPPDifferentiability
