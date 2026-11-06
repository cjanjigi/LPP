/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import LPP_Foundations.Model.LastPassage.Basic
import LPP_Foundations.Model.LastPassage.Bounds
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Ring

/-!
# Monotonicity of last-passage times after a linear correction

If every site weight is at least `c`, then the last-passage time to the endpoint `d`, minus `c`
times the number of steps to `d`, is nondecreasing in `d`.
-/

@[expose] public section

namespace LPPDifferentiability

/-- A uniform lower bound on site weights makes passage minus that bound times
the displacement length monotone in the endpoint. -/
theorem lastPassage_corrected_monotone_of_lower_bound
    (ω : Environment) (u : Lattice) (c : ℝ)
    (hω : ∀ v, c ≤ ω v) :
    Monotone (fun d : ℕ × ℕ =>
      lastPassage ω u d - ((d.1 + d.2 : ℕ) : ℝ) * c) := by
  intro d e hde
  rcases Prod.le_def.mp hde with ⟨hd₁, hd₂⟩
  let δ : ℕ × ℕ := (e.1 - d.1, e.2 - d.2)
  have hsplit : d + δ = e := by
    apply Prod.ext
    · dsimp [δ]
      exact Nat.add_sub_of_le hd₁
    · dsimp [δ]
      exact Nat.add_sub_of_le hd₂
  have hsuper := lastPassage_superadditive ω u d δ
  rw [hsplit] at hsuper
  have htail := const_le_lastPassage ω
    (u + ((d.1 : ℤ), (d.2 : ℤ))) δ c hω
  have hgain :
      lastPassage ω u d + ((δ.1 + δ.2 : ℕ) : ℝ) * c ≤
        lastPassage ω u e := by
    calc
      _ ≤ lastPassage ω u d +
          lastPassage ω (u + ((d.1 : ℤ), (d.2 : ℤ))) δ :=
        add_le_add le_rfl htail
      _ ≤ lastPassage ω u e := hsuper
  have hlengthNat :
      (d.1 + d.2) + (δ.1 + δ.2) = e.1 + e.2 := by
    dsimp [δ]
    omega
  have hcoeff :
      ((d.1 + d.2 : ℕ) : ℝ) * c + ((δ.1 + δ.2 : ℕ) : ℝ) * c =
        ((e.1 + e.2 : ℕ) : ℝ) * c := by
    calc
      _ = (((d.1 + d.2) + (δ.1 + δ.2) : ℕ) : ℝ) * c := by
        rw [← add_mul, ← Nat.cast_add]
      _ = _ := congrArg (fun n : ℕ => (n : ℝ) * c) hlengthNat
  have hrewrite :
      lastPassage ω u d - ((d.1 + d.2 : ℕ) : ℝ) * c =
        (lastPassage ω u d + ((δ.1 + δ.2 : ℕ) : ℝ) * c) -
          ((e.1 + e.2 : ℕ) : ℝ) * c := by
    rw [← hcoeff]
    ring
  calc
    lastPassage ω u d - ((d.1 + d.2 : ℕ) : ℝ) * c =
        (lastPassage ω u d + ((δ.1 + δ.2 : ℕ) : ℝ) * c) -
          ((e.1 + e.2 : ℕ) : ℝ) * c := hrewrite
    _ ≤ lastPassage ω u e - ((e.1 + e.2 : ℕ) : ℝ) * c :=
      sub_le_sub_right hgain _

end LPPDifferentiability
