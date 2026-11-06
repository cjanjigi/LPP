/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Differentiability.Model.Paths.TransverseStaircase
public import LPP_Foundations.Frozen.Model.Path
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-! # The staircase at a transverse coordinate, starting on any level

For `0 < a < 1`, a real `ρ` and an integer level `I`, the unique site `ẑ(I, ρ)`
on level `I` with transverse coordinate `(1 - a) z₁ - a z₂ ∈ (ρ - 1, ρ]` is
`(⌊ρ + a I⌋, I - ⌊ρ + a I⌋)`. The sites `ẑ(I + k, ρ)` form an admissible path.
This extends `exists_transverse_staircase`, which starts on level `0`, by a lattice
translation through `(0, I)`.
-/

public section

namespace LPPDifferentiability

/-- The staircase at `ρ` from level `I` to level `I + n`: an admissible path starting
at `ẑ(I, ρ)`, whose vertex on level `I + k` is `ẑ(I + k, ρ)`, with transverse
coordinate in `(ρ - 1, ρ]` at every vertex, and with `ẑ(I + k, ρ)` the only site on
level `I + k` having this property. -/
theorem exists_level_transverse_staircase (a ρ : ℝ) (ha₀ : 0 < a) (ha₁ : a < 1)
    (I : ℤ) (n : ℕ) :
    ∃ (i : Fin (n + 1))
      (q : Path (⌊ρ + a * (I : ℝ)⌋, I - ⌊ρ + a * (I : ℝ)⌋) (i.val, n - i.val)),
      (∀ k : Fin (i.val + (n - i.val) + 1),
        q.vertex k =
          (⌊ρ + a * ((I + (k.val : ℤ) : ℤ) : ℝ)⌋,
            (I + (k.val : ℤ)) - ⌊ρ + a * ((I + (k.val : ℤ) : ℤ) : ℝ)⌋)) ∧
      (∀ k : Fin (i.val + (n - i.val) + 1),
        ρ - 1 < (1 - a) * ((q.vertex k).1 : ℝ) - a * ((q.vertex k).2 : ℝ) ∧
          (1 - a) * ((q.vertex k).1 : ℝ) - a * ((q.vertex k).2 : ℝ) ≤ ρ) ∧
      (∀ k : Fin (i.val + (n - i.val) + 1), ∀ z : Lattice,
        z.1 + z.2 = I + (k.val : ℤ) →
        ρ - 1 < (1 - a) * (z.1 : ℝ) - a * (z.2 : ℝ) →
        (1 - a) * (z.1 : ℝ) - a * (z.2 : ℝ) ≤ ρ → z = q.vertex k) := by
  obtain ⟨i, q, hv, hr, hu⟩ := exists_transverse_staircase a (ρ + a * (I : ℝ)) ha₀ ha₁ n
  have hshift (k : ℕ) :
      ρ + a * ((I + (k : ℤ) : ℤ) : ℝ) = ρ + a * (I : ℝ) + a * (k : ℝ) := by
    push_cast
    ring
  have hrshift (z : Lattice) :
      (1 - a) * (z.1 : ℝ) - a * (z.2 : ℝ) =
        (1 - a) * (z.1 : ℝ) - a * ((z.2 - I : ℤ) : ℝ) - a * (I : ℝ) := by
    push_cast
    ring
  let q' : Path (⌊ρ + a * (I : ℝ)⌋, I - ⌊ρ + a * (I : ℝ)⌋) (i.val, n - i.val) :=
    { vertex := fun k => ((0 : ℤ), I) + q.vertex k
      start := by
        rw [q.start]
        apply Prod.ext <;> simp
        omega
      finish := by
        rw [q.finish]
        apply Prod.ext <;> simp
        omega
      step := by
        intro k
        rcases q.step k with h | h
        · exact Or.inl (by rw [h, add_assoc])
        · exact Or.inr (by rw [h, add_assoc]) }
  have hq' (k : Fin (i.val + (n - i.val) + 1)) :
      q'.vertex k =
        (⌊ρ + a * ((I + (k.val : ℤ) : ℤ) : ℝ)⌋,
          (I + (k.val : ℤ)) - ⌊ρ + a * ((I + (k.val : ℤ) : ℤ) : ℝ)⌋) := by
    change ((0 : ℤ), I) + q.vertex k = _
    rw [hv k, hshift]
    apply Prod.ext <;> simp
    omega
  have hrq' (k : Fin (i.val + (n - i.val) + 1)) :
      (1 - a) * ((q'.vertex k).1 : ℝ) - a * ((q'.vertex k).2 : ℝ) =
        (1 - a) * ((q.vertex k).1 : ℝ) - a * ((q.vertex k).2 : ℝ) - a * (I : ℝ) := by
    change (1 - a) * ((((0 : ℤ), I) + q.vertex k).1 : ℝ) -
      a * ((((0 : ℤ), I) + q.vertex k).2 : ℝ) = _
    simp only [Prod.fst_add, Prod.snd_add]
    push_cast
    ring
  refine ⟨i, q', hq', ?_, ?_⟩
  · intro k
    obtain ⟨h₁, h₂⟩ := hr k
    rw [hrq']
    constructor <;> linarith
  · intro k z hz h₁ h₂
    have hz' : (z.1 + (z.2 - I)) = (k.val : ℤ) := by omega
    have hzr : ρ + a * (I : ℝ) - 1 <
        (1 - a) * (z.1 : ℝ) - a * ((z.2 - I : ℤ) : ℝ) := by
      rw [hrshift z] at h₁
      linarith
    have hzr' : (1 - a) * (z.1 : ℝ) - a * ((z.2 - I : ℤ) : ℝ) ≤
        ρ + a * (I : ℝ) := by
      rw [hrshift z] at h₂
      linarith
    have h := hu k (z.1, z.2 - I) hz' hzr hzr'
    have h1 := congrArg Prod.fst h
    have h2 := congrArg Prod.snd h
    change z.1 = (q.vertex k).1 at h1
    change z.2 - I = (q.vertex k).2 at h2
    change z = ((0 : ℤ), I) + q.vertex k
    apply Prod.ext <;> simp <;> omega

end LPPDifferentiability
