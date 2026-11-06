/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import LPP_Foundations.Model.Paths.Level
public import Mathlib.Algebra.Order.Floor.Defs
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-! # The deterministic staircase in the coordinates of a direction

For a direction `(a, 1 - a)` with `0 < a < 1`, the transverse coordinate of a
site `z` is `(1 - a) * z.1 - a * z.2`. On level `k` (that is, `z.1 + z.2 = k`)
it equals `z.1 - a * k`, so the sites on level `k` whose transverse coordinate
lies in `(ρ - 1, ρ]` consist of exactly one site, with first coordinate
`⌊ρ + a * k⌋`. Consecutive such sites differ by one admissible step, so these
sites form a path, the staircase at `ρ`.
-/

public section

namespace LPPDifferentiability

/-- On level `k`, the site `(j, k - j)` has transverse coordinate `j - a * k`. -/
theorem transverse_coordinate_on_level (a : ℝ) (j k : ℤ) :
    (1 - a) * (j : ℝ) - a * ((k - j : ℤ) : ℝ) = (j : ℝ) - a * (k : ℝ) := by
  push_cast
  ring

/-- Among the sites of a level, the one with transverse coordinate in
`(ρ - 1, ρ]` is unique, and its first coordinate is `⌊ρ + a * k⌋`. -/
theorem transverse_interval_iff_floor (a ρ : ℝ) (j k : ℤ) :
    (ρ - 1 < (1 - a) * (j : ℝ) - a * ((k - j : ℤ) : ℝ) ∧
      (1 - a) * (j : ℝ) - a * ((k - j : ℤ) : ℝ) ≤ ρ) ↔ j = ⌊ρ + a * (k : ℝ)⌋ := by
  rw [transverse_coordinate_on_level, eq_comm, Int.floor_eq_iff]
  constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith

private theorem floor_add_step (x a : ℝ) (ha₀ : 0 ≤ a) (ha₁ : a < 1) :
    ⌊x + a⌋ = ⌊x⌋ ∨ ⌊x + a⌋ = ⌊x⌋ + 1 := by
  have h₁ : ⌊x⌋ ≤ ⌊x + a⌋ := Int.floor_le_floor (by linarith)
  have h₂ : ⌊x + a⌋ ≤ ⌊x⌋ + 1 := by
    rw [Int.floor_le_iff]
    have := Int.lt_floor_add_one x
    push_cast
    linarith
  omega

/-- The staircase at `ρ` is an admissible path starting at the level-zero site
with transverse coordinate in `(ρ - 1, ρ]`. Its vertex on level `k` is the unique
site of that level with transverse coordinate in `(ρ - 1, ρ]`, namely
`(⌊ρ + a * k⌋, k - ⌊ρ + a * k⌋)`, and it ends on level `n`. -/
theorem exists_transverse_staircase (a ρ : ℝ) (ha₀ : 0 < a) (ha₁ : a < 1) (n : ℕ) :
    ∃ (i : Fin (n + 1)) (q : Path (⌊ρ⌋, -⌊ρ⌋) (i.val, n - i.val)),
      (∀ k : Fin (i.val + (n - i.val) + 1),
        q.vertex k = (⌊ρ + a * (k.val : ℝ)⌋, (k.val : ℤ) - ⌊ρ + a * (k.val : ℝ)⌋)) ∧
      (∀ k : Fin (i.val + (n - i.val) + 1),
        ρ - 1 < (1 - a) * ((q.vertex k).1 : ℝ) - a * ((q.vertex k).2 : ℝ) ∧
          (1 - a) * ((q.vertex k).1 : ℝ) - a * ((q.vertex k).2 : ℝ) ≤ ρ) ∧
      (∀ k : Fin (i.val + (n - i.val) + 1), ∀ z : Lattice,
        z.1 + z.2 = (k.val : ℤ) →
        ρ - 1 < (1 - a) * (z.1 : ℝ) - a * (z.2 : ℝ) →
        (1 - a) * (z.1 : ℝ) - a * (z.2 : ℝ) ≤ ρ → z = q.vertex k) := by
  have hlow : ⌊ρ⌋ ≤ ⌊ρ + a * (n : ℝ)⌋ :=
    Int.floor_le_floor (by nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)])
  have hhigh : ⌊ρ + a * (n : ℝ)⌋ ≤ ⌊ρ⌋ + n := by
    rw [Int.floor_le_iff]
    have := Int.lt_floor_add_one ρ
    have hn : a * (n : ℝ) ≤ (n : ℝ) := by
      nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    push_cast
    linarith
  let i : ℕ := (⌊ρ + a * (n : ℝ)⌋ - ⌊ρ⌋).toNat
  have hi : (i : ℤ) = ⌊ρ + a * (n : ℝ)⌋ - ⌊ρ⌋ := by
    simp only [i]
    omega
  have hin : i < n + 1 := by omega
  have hlen : i + (n - i) = n := by omega
  let f : ℕ → ℤ := fun k => ⌊ρ + a * (k : ℝ)⌋
  have hstep : ∀ k : ℕ, f (k + 1) = f k ∨ f (k + 1) = f k + 1 := by
    intro k
    have h := floor_add_step (ρ + a * (k : ℝ)) a ha₀.le ha₁
    have : ρ + a * ((k + 1 : ℕ) : ℝ) = ρ + a * (k : ℝ) + a := by
      push_cast
      ring
    simp only [f, this]
    exact h
  let q : Path (⌊ρ⌋, -⌊ρ⌋) (i, n - i) :=
    { vertex := fun k => (f k.val, (k.val : ℤ) - f k.val)
      start := by simp [f]
      finish := by
        apply Prod.ext
        · simp only [Fin.val_last, hlen, f, Prod.fst_add]
          omega
        · simp only [Fin.val_last, hlen, f, Prod.snd_add]
          omega
      step := by
        intro k
        rcases hstep k.val with h | h
        · right
          apply Prod.ext
          · simp only [Fin.val_succ, Fin.val_castSucc, Prod.fst_add]
            omega
          · simp only [Fin.val_succ, Fin.val_castSucc, Prod.snd_add]
            push_cast
            omega
        · left
          apply Prod.ext
          · simp only [Fin.val_succ, Fin.val_castSucc, Prod.fst_add]
            omega
          · simp only [Fin.val_succ, Fin.val_castSucc, Prod.snd_add]
            push_cast
            omega }
  refine ⟨⟨i, hin⟩, q, fun k => rfl, ?_, ?_⟩
  · intro k
    have h := (transverse_interval_iff_floor a ρ (f k.val) k.val).2 rfl
    simpa only [q, f] using h
  · intro k z hz h₁ h₂
    have hz2 : z.2 = (k.val : ℤ) - z.1 := by omega
    have h := (transverse_interval_iff_floor a ρ z.1 k.val).1 (by
      rw [← hz2]
      exact ⟨h₁, h₂⟩)
    apply Prod.ext
    · exact h
    · have h' : z.1 = ⌊ρ + a * (k.val : ℝ)⌋ := by
        simpa only [Int.cast_natCast] using h
      simp only [q, f]
      omega

/-- The staircase at `ρ = 0` starts at the origin and keeps `|r| < 1`. -/
theorem exists_origin_staircase (a : ℝ) (ha₀ : 0 < a) (ha₁ : a < 1) (n : ℕ) :
    ∃ (i : Fin (n + 1)) (q : Path (0 : Lattice) (i.val, n - i.val)),
      ∀ k : Fin (i.val + (n - i.val) + 1),
        |(1 - a) * ((q.vertex k).1 : ℝ) - a * ((q.vertex k).2 : ℝ)| < 1 := by
  have key := exists_transverse_staircase a 0 ha₀ ha₁ n
  have h0 : ((⌊(0 : ℝ)⌋, -⌊(0 : ℝ)⌋) : Lattice) = 0 := by simp
  rw [h0] at key
  obtain ⟨i, q, _, hr, _⟩ := key
  exact ⟨i, q, fun k => abs_lt.2 ⟨by linarith [(hr k).1], by linarith [(hr k).2]⟩⟩

end LPPDifferentiability
