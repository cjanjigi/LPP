/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import LPP_Foundations.Model.LastPassage.Translate
public import LPP_Foundations.Model.Translations

/-! Actual finite passage values along natural lattice rays. -/

public section

namespace LPPDifferentiability

/-- Iterating a coordinate translation translates the start of finite passage
by the corresponding multiple of that lattice vector. -/
theorem lastPassage_translate_iterate (ω : Environment) (v : Lattice) (m : ℕ)
    (u : Lattice) (d : ℕ × ℕ) :
    lastPassage (((fun ω : Environment => fun z => ω (v + z))^[m]) ω) u d =
      lastPassage ω (m • v + u) d := by
  have heq : ((fun ω : Environment => fun z => ω (v + z))^[m]) ω =
      (fun z => ω (m • v + z)) :=
    funext (fun z => environment_translate_iterate ω v m z)
  rw [heq, lastPassage_translate]

private theorem ray_cast_smul (a : ℕ × ℕ) (m : ℕ) :
    (((m • a).1 : ℤ), ((m • a).2 : ℤ)) = m • ((a.1 : ℤ), (a.2 : ℤ)) := by
  ext <;> simp

/-- Negated actual passage values form a stationary subadditive cocycle along
any natural displacement, with the actual coordinate translation as shift. -/
theorem neg_lastPassage_ray_cocycle (ω : Environment) (a : ℕ × ℕ) (m n : ℕ) :
    -lastPassage ω 0 ((m + n) • a) ≤
      -lastPassage ω 0 (m • a) +
      -lastPassage (((fun ω : Environment => fun z =>
        ω (((a.1 : ℤ), (a.2 : ℤ)) + z))^[m]) ω) 0 (n • a) := by
  rw [lastPassage_translate_iterate, add_zero]
  have h := neg_le_neg (lastPassage_superadditive ω 0 (m • a) (n • a))
  rw [zero_add, ray_cast_smul, ← add_nsmul, neg_add] at h
  exact h

/-- The zero ray has identically zero passage, including under signed laws. -/
@[simp] theorem neg_lastPassage_zero_ray (ω : Environment) (n : ℕ) :
    -lastPassage ω 0 (n • (0 : ℕ × ℕ)) = 0 := by
  rw [smul_zero]
  change -lastPassage ω 0 (0, 0) = 0
  rw [lastPassage_zero, neg_zero]

end LPPDifferentiability
