/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Differentiability.Model.Paths.ReachableLevel
import LPP_Foundations.Model.Paths.Geometry
import LPP_Foundations.Model.Paths.HorizontalFirst
import LPP_Foundations.Model.Paths.Level
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Backward reachable level intervals

Starting points of directed paths ending at a fixed lattice point, together with
zero-step, boundary and signed-coordinate consequences.
-/

@[expose] public section

namespace LPPDifferentiability

/-- Backward starting points are indexed without repetition by `Fin (m + 1)`;
they are exactly the signed points below `v` on level `level(v)-m`. -/
theorem backwardReachable_mem_iff (v w : Lattice) (m : ℕ) :
    let starts : Finset Lattice :=
      Finset.univ.image (fun j : Fin (m + 1) =>
        v - ((j.val : ℤ), ((m - j.val : ℕ) : ℤ)))
    w ∈ starts ↔ w ≤ v ∧ w.1 + w.2 + (m : ℤ) = v.1 + v.2 := by
  classical
  change w ∈ Finset.univ.image (fun j : Fin (m + 1) =>
    v - ((j.val : ℤ), ((m - j.val : ℕ) : ℤ))) ↔ _
  constructor
  · intro hw
    rcases Finset.mem_image.mp hw with ⟨j, -, hj⟩
    have hjle : j.val ≤ m := by omega
    constructor
    · rw [← hj]
      change (v - ((j.val : ℤ), ((m - j.val : ℕ) : ℤ))).1 ≤ v.1 ∧
        (v - ((j.val : ℤ), ((m - j.val : ℕ) : ℤ))).2 ≤ v.2
      simp only [Prod.fst_sub, Prod.snd_sub]
      constructor <;> omega
    · rw [← hj]
      simp only [Prod.fst_sub, Prod.snd_sub]
      omega
  · rintro ⟨hle, hlevel⟩
    change w.1 ≤ v.1 ∧ w.2 ≤ v.2 at hle
    rcases hle with ⟨h₁, h₂⟩
    have hd₁ : 0 ≤ v.1 - w.1 := by omega
    have hcast : ((v.1 - w.1).toNat : ℤ) = v.1 - w.1 :=
      Int.toNat_of_nonneg hd₁
    have hsum : (v.1 - w.1) + (v.2 - w.2) = (m : ℤ) := by omega
    have hjle : (v.1 - w.1).toNat ≤ m := by
      have hleZ : ((v.1 - w.1).toNat : ℤ) ≤ (m : ℤ) := by
        rw [hcast]
        omega
      exact_mod_cast hleZ
    let j : Fin (m + 1) := ⟨(v.1 - w.1).toNat, by omega⟩
    have hj₁ : (j.val : ℤ) = v.1 - w.1 := by
      change ((v.1 - w.1).toNat : ℤ) = _
      exact hcast
    have hj₂ : ((m - j.val : ℕ) : ℤ) = v.2 - w.2 := by
      omega
    have hpoint : w = v - ((j.val : ℤ), ((m - j.val : ℕ) : ℤ)) := by
      apply Prod.ext
      · simp only [Prod.fst_sub]
        omega
      · simp only [Prod.snd_sub]
        omega
    apply Finset.mem_image.mpr
    exact ⟨j, Finset.mem_univ _, hpoint.symm⟩

/-- The backward starting-point enumeration has exactly `m + 1` distinct points. -/
theorem backwardReachable_card (v : Lattice) (m : ℕ) :
    let starts : Finset Lattice :=
      Finset.univ.image (fun j : Fin (m + 1) =>
        v - ((j.val : ℤ), ((m - j.val : ℕ) : ℤ)))
    starts.card = m + 1 := by
  classical
  change (Finset.univ.image (fun j : Fin (m + 1) =>
    v - ((j.val : ℤ), ((m - j.val : ℕ) : ℤ)))).card = m + 1
  have hinj : Function.Injective (fun j : Fin (m + 1) =>
      v - ((j.val : ℤ), ((m - j.val : ℕ) : ℤ))) := by
    intro i j hij
    apply Fin.ext
    have hfst := congrArg Prod.fst hij
    simp only [Prod.fst_sub] at hfst
    omega
  rw [Finset.card_image_of_injective Finset.univ hinj]
  simp

/-- The transverse coordinate of a backward starting point, for every real `a`. -/
theorem backwardReachable_transverse (v : Lattice) (m : ℕ)
    (j : Fin (m + 1)) (a : ℝ) :
    (1 - a) * (((v - ((j.val : ℤ), ((m - j.val : ℕ) : ℤ))).1 : ℤ) : ℝ) -
        a * (((v - ((j.val : ℤ), ((m - j.val : ℕ) : ℤ))).2 : ℤ) : ℝ) =
      ((1 - a) * (v.1 : ℝ) - a * (v.2 : ℝ)) + a * (m : ℝ) - (j.val : ℝ) := by
  have hj : j.val ≤ m := by omega
  simp only [Prod.fst_sub, Prod.snd_sub, Int.cast_sub, Int.cast_natCast,
    Nat.cast_sub hj]
  ring

/-- On the earlier level, coordinatewise backward reachability is equivalent
to the closed transverse interval ending at `rho(v)+a*m`. -/
theorem backwardLevelInterval_iff (v w : Lattice) (m : ℕ) (a : ℝ) :
    (w ≤ v ∧ w.1 + w.2 + (m : ℤ) = v.1 + v.2) ↔
      (w.1 + w.2 + (m : ℤ) = v.1 + v.2 ∧
        ((1 - a) * (w.1 : ℝ) - a * (w.2 : ℝ)) ∈
          Set.Icc ((1 - a) * (v.1 : ℝ) - a * (v.2 : ℝ) - (1 - a) * (m : ℝ))
            ((1 - a) * (v.1 : ℝ) - a * (v.2 : ℝ) + a * (m : ℝ))) := by
  have hformula (hlevel : w.1 + w.2 + (m : ℤ) = v.1 + v.2) :
      (1 - a) * (w.1 : ℝ) - a * (w.2 : ℝ) =
        ((1 - a) * (v.1 : ℝ) - a * (v.2 : ℝ)) + a * (m : ℝ) -
          ((v.1 : ℝ) - (w.1 : ℝ)) := by
    have hlevelR : (w.1 : ℝ) + (w.2 : ℝ) + (m : ℝ) =
        (v.1 : ℝ) + (v.2 : ℝ) := by
      exact_mod_cast hlevel
    have hw₂ : (w.2 : ℝ) = (v.1 : ℝ) + (v.2 : ℝ) - (m : ℝ) - (w.1 : ℝ) := by
      linarith [hlevelR]
    rw [hw₂]
    ring
  constructor
  · rintro ⟨hle, hlevel⟩
    change w.1 ≤ v.1 ∧ w.2 ≤ v.2 at hle
    rcases hle with ⟨h₁, h₂⟩
    have hlevelR : (w.1 : ℝ) + (w.2 : ℝ) + (m : ℝ) =
        (v.1 : ℝ) + (v.2 : ℝ) := by
      exact_mod_cast hlevel
    have hd₁ : 0 ≤ (v.1 : ℝ) - (w.1 : ℝ) := by exact_mod_cast (sub_nonneg.mpr h₁)
    have hd₂ : 0 ≤ (v.2 : ℝ) - (w.2 : ℝ) := by exact_mod_cast (sub_nonneg.mpr h₂)
    have hsum : ((v.1 : ℝ) - (w.1 : ℝ)) +
        ((v.2 : ℝ) - (w.2 : ℝ)) = (m : ℝ) := by
      linarith [hlevelR]
    refine ⟨hlevel, ?_⟩
    rw [hformula hlevel]
    constructor <;> linarith
  · rintro ⟨hlevel, hinterval⟩
    have hlevelR : (w.1 : ℝ) + (w.2 : ℝ) + (m : ℝ) =
        (v.1 : ℝ) + (v.2 : ℝ) := by
      exact_mod_cast hlevel
    have hformula' := hformula hlevel
    have hd₁ : 0 ≤ (v.1 : ℝ) - (w.1 : ℝ) := by
      rw [hformula'] at hinterval
      linarith [hinterval.2]
    have hd₁m : (v.1 : ℝ) - (w.1 : ℝ) ≤ (m : ℝ) := by
      rw [hformula'] at hinterval
      linarith [hinterval.1]
    have h₁ : w.1 ≤ v.1 := by
      exact_mod_cast (show (w.1 : ℝ) ≤ (v.1 : ℝ) by linarith)
    have h₂ : w.2 ≤ v.2 := by
      have h₂R : (w.2 : ℝ) ≤ (v.2 : ℝ) := by linarith [hlevelR, hd₁m]
      exact_mod_cast h₂R
    exact ⟨⟨h₁, h₂⟩, hlevel⟩

/-- Filtering the backward enumeration by its closed level interval retains all
of its `m + 1` points. -/
theorem backwardLevelInterval_card (v : Lattice) (m : ℕ) (a : ℝ) :
    let starts : Finset Lattice :=
      Finset.univ.image (fun j : Fin (m + 1) =>
        v - ((j.val : ℤ), ((m - j.val : ℕ) : ℤ)))
    (starts.filter (fun w =>
      w.1 + w.2 + (m : ℤ) = v.1 + v.2 ∧
        ((1 - a) * (w.1 : ℝ) - a * (w.2 : ℝ)) ∈
          Set.Icc ((1 - a) * (v.1 : ℝ) - a * (v.2 : ℝ) - (1 - a) * (m : ℝ))
            ((1 - a) * (v.1 : ℝ) - a * (v.2 : ℝ) + a * (m : ℝ)))).card =
      m + 1 := by
  classical
  change ((Finset.univ.image (fun j : Fin (m + 1) =>
    v - ((j.val : ℤ), ((m - j.val : ℕ) : ℤ)))).filter (fun w =>
      w.1 + w.2 + (m : ℤ) = v.1 + v.2 ∧
        ((1 - a) * (w.1 : ℝ) - a * (w.2 : ℝ)) ∈
          Set.Icc ((1 - a) * (v.1 : ℝ) - a * (v.2 : ℝ) - (1 - a) * (m : ℝ))
            ((1 - a) * (v.1 : ℝ) - a * (v.2 : ℝ) + a * (m : ℝ)))).card = m + 1
  have hfilter :
      ((Finset.univ.image (fun j : Fin (m + 1) =>
        v - ((j.val : ℤ), ((m - j.val : ℕ) : ℤ)))).filter (fun w =>
          w.1 + w.2 + (m : ℤ) = v.1 + v.2 ∧
            ((1 - a) * (w.1 : ℝ) - a * (w.2 : ℝ)) ∈
              Set.Icc ((1 - a) * (v.1 : ℝ) - a * (v.2 : ℝ) - (1 - a) * (m : ℝ))
                ((1 - a) * (v.1 : ℝ) - a * (v.2 : ℝ) + a * (m : ℝ)))) =
      Finset.univ.image (fun j : Fin (m + 1) =>
        v - ((j.val : ℤ), ((m - j.val : ℕ) : ℤ))) := by
    apply Finset.filter_eq_self.mpr
    intro w hw
    exact (backwardLevelInterval_iff v w m a).mp
      ((backwardReachable_mem_iff v w m).mp hw)
  rw [hfilter]
  exact backwardReachable_card v m

/-- Every point in the backward enumeration has an actual horizontal-first
path to `v`, with terminal vertex exactly `v`. -/
theorem exists_path_from_backwardReachable (v : Lattice) (w : Lattice) (m : ℕ)
    (hw : w ∈ Finset.univ.image (fun j : Fin (m + 1) =>
      v - ((j.val : ℤ), ((m - j.val : ℕ) : ℤ)))) :
    ∃ j : Fin (m + 1), ∃ p : Path w (j.val, m - j.val),
      p.vertex (Fin.last (j.val + (m - j.val))) = v := by
  classical
  change w ∈ Finset.univ.image (fun j : Fin (m + 1) =>
    v - ((j.val : ℤ), ((m - j.val : ℕ) : ℤ))) at hw
  rcases Finset.mem_image.mp hw with ⟨j, -, hj⟩
  refine ⟨j, horizontalFirst w (j.val, m - j.val), ?_⟩
  calc
    (horizontalFirst w (j.val, m - j.val)).vertex
        (Fin.last (j.val + (m - j.val))) =
        w + ((j.val : ℤ), ((m - j.val : ℕ) : ℤ)) :=
      (horizontalFirst w (j.val, m - j.val)).finish
    _ = v := by rw [← hj]; simp

/-- The start of an actual length-`m` path ending at `v` lies in the backward
enumeration. -/
theorem Path.start_mem_backwardReachable {w : Lattice} {d : ℕ × ℕ}
    (p : Path w d) (v : Lattice) (m : ℕ)
    (hm : d.1 + d.2 = m)
    (hend : p.vertex (Fin.last (d.1 + d.2)) = v) :
    w ∈ (let starts : Finset Lattice :=
      Finset.univ.image (fun j : Fin (m + 1) =>
        v - ((j.val : ℤ), ((m - j.val : ℕ) : ℤ)))
      starts) := by
  have hbox := Path.vertex_mem_Icc p (Fin.last (d.1 + d.2))
  have hle : w ≤ v := by rw [← hend]; exact hbox.1
  have hlevel := Path.level p (Fin.last (d.1 + d.2))
  simp only [Fin.val_last] at hlevel
  have hlevel' : w.1 + w.2 + (m : ℤ) = v.1 + v.2 := by
    rw [hend] at hlevel
    have hmZ : ((d.1 + d.2 : ℕ) : ℤ) = (m : ℤ) := by exact_mod_cast hm
    omega
  exact (backwardReachable_mem_iff v w m).2 ⟨hle, hlevel'⟩

/-- The zero-step forward enumeration consists only of its signed starting point. -/
theorem forwardReachable_zero (u : Lattice) :
    let endpoints : Finset Lattice :=
      Finset.univ.image (fun j : Fin (0 + 1) =>
        u + ((j.val : ℤ), ((0 - j.val : ℕ) : ℤ)))
    endpoints = {u} := by
  classical
  apply Finset.ext
  intro v
  rw [Finset.mem_singleton]
  have hiff := forwardReachable_mem_iff u v 0
  change v ∈ Finset.univ.image (fun j : Fin (0 + 1) =>
    u + ((j.val : ℤ), ((0 - j.val : ℕ) : ℤ))) ↔ _ at hiff
  rw [hiff]
  change u ≤ v ∧ v.1 + v.2 = u.1 + u.2 + (0 : ℤ) ↔ v = u
  constructor
  · rintro ⟨hle, hlevel⟩
    change u.1 ≤ v.1 ∧ u.2 ≤ v.2 at hle
    rcases hle with ⟨h₁, h₂⟩
    apply Prod.ext <;> omega
  · intro h
    rw [h]
    exact ⟨le_rfl, by omega⟩

/-- The zero-step backward enumeration consists only of its signed endpoint. -/
theorem backwardReachable_zero (v : Lattice) :
    let starts : Finset Lattice :=
      Finset.univ.image (fun j : Fin (0 + 1) =>
        v - ((j.val : ℤ), ((0 - j.val : ℕ) : ℤ)))
    starts = {v} := by
  classical
  apply Finset.ext
  intro w
  rw [Finset.mem_singleton]
  have hiff := backwardReachable_mem_iff v w 0
  change w ∈ Finset.univ.image (fun j : Fin (0 + 1) =>
    v - ((j.val : ℤ), ((0 - j.val : ℕ) : ℤ))) ↔ _ at hiff
  rw [hiff]
  change w ≤ v ∧ w.1 + w.2 + (0 : ℤ) = v.1 + v.2 ↔ w = v
  constructor
  · rintro ⟨hle, hlevel⟩
    change w.1 ≤ v.1 ∧ w.2 ≤ v.2 at hle
    rcases hle with ⟨h₁, h₂⟩
    apply Prod.ext <;> omega
  · intro h
    rw [h]
    exact ⟨le_rfl, by omega⟩

/-- The two forward boundary points are the actual horizontal and vertical
horizontal-first paths, including when `m = 0`. -/
theorem forwardReachable_axis_paths (u : Lattice) (m : ℕ) :
    (∃ j : Fin (m + 1), ∃ p : Path u (j.val, m - j.val),
      p.vertex (Fin.last (j.val + (m - j.val))) = u + ((m : ℤ), 0)) ∧
    (∃ j : Fin (m + 1), ∃ p : Path u (j.val, m - j.val),
      p.vertex (Fin.last (j.val + (m - j.val))) = u + (0, (m : ℤ))) := by
  constructor
  · have hmem : u + ((m : ℤ), 0) ∈ Finset.univ.image (fun j : Fin (m + 1) =>
        u + ((j.val : ℤ), ((m - j.val : ℕ) : ℤ))) := by
      apply (forwardReachable_mem_iff u _ m).2
      constructor
      · change u.1 ≤ _ ∧ u.2 ≤ _
        simp only [Prod.fst_add, Prod.snd_add]
        constructor <;> omega
      · simp only [Prod.fst_add, Prod.snd_add]
        omega
    exact exists_path_to_forwardReachable u (u + ((m : ℤ), 0)) m hmem
  · have hmem : u + (0, (m : ℤ)) ∈ Finset.univ.image (fun j : Fin (m + 1) =>
        u + ((j.val : ℤ), ((m - j.val : ℕ) : ℤ))) := by
      apply (forwardReachable_mem_iff u _ m).2
      constructor
      · change u.1 ≤ _ ∧ u.2 ≤ _
        simp only [Prod.fst_add, Prod.snd_add]
        constructor <;> omega
      · simp only [Prod.fst_add, Prod.snd_add]
        omega
    exact exists_path_to_forwardReachable u (u + (0, (m : ℤ))) m hmem

/-- The two backward boundary points have actual paths ending at `v`, including
when `m = 0`. -/
theorem backwardReachable_axis_paths (v : Lattice) (m : ℕ) :
    (∃ j : Fin (m + 1), ∃ p : Path (v - ((m : ℤ), 0)) (j.val, m - j.val),
      p.vertex (Fin.last (j.val + (m - j.val))) = v) ∧
    (∃ j : Fin (m + 1), ∃ p : Path (v - (0, (m : ℤ))) (j.val, m - j.val),
      p.vertex (Fin.last (j.val + (m - j.val))) = v) := by
  constructor
  · let w := v - ((m : ℤ), 0)
    have hmem : w ∈ Finset.univ.image (fun j : Fin (m + 1) =>
        v - ((j.val : ℤ), ((m - j.val : ℕ) : ℤ))) := by
      apply (backwardReachable_mem_iff v w m).2
      constructor
      · change w.1 ≤ v.1 ∧ w.2 ≤ v.2
        dsimp [w]
        constructor <;> omega
      · dsimp [w]
        ring
    simpa [w] using exists_path_from_backwardReachable v w m hmem
  · let w := v - (0, (m : ℤ))
    have hmem : w ∈ Finset.univ.image (fun j : Fin (m + 1) =>
        v - ((j.val : ℤ), ((m - j.val : ℕ) : ℤ))) := by
      apply (backwardReachable_mem_iff v w m).2
      constructor
      · change w.1 ≤ v.1 ∧ w.2 ≤ v.2
        dsimp [w]
        constructor <;> omega
      · dsimp [w]
        ring
    simpa [w] using exists_path_from_backwardReachable v w m hmem

/-- A forward path consumer with arbitrary signed coordinates; in particular,
the starting point need not lie in the first quadrant. -/
theorem signed_forwardReachable_consumer (x y : ℤ) (m : ℕ) :
    ∃ j : Fin (m + 1), ∃ p : Path (x, y) (j.val, m - j.val),
      p.vertex (Fin.last (j.val + (m - j.val))) = (x + (m : ℤ), y) := by
  have hmem : (x + (m : ℤ), y) ∈ Finset.univ.image (fun j : Fin (m + 1) =>
      (x, y) + ((j.val : ℤ), ((m - j.val : ℕ) : ℤ))) := by
    apply (forwardReachable_mem_iff (x, y) _ m).2
    constructor
    · change x ≤ x + (m : ℤ) ∧ y ≤ y
      exact ⟨by omega, le_rfl⟩
    · change x + (m : ℤ) + y = x + y + (m : ℤ)
      ring
  exact exists_path_to_forwardReachable (x, y) (x + (m : ℤ), y) m hmem

/-- A backward path consumer with arbitrary signed coordinates, including a
signed endpoint and a possibly negative starting point. -/
theorem signed_backwardReachable_consumer (x y : ℤ) (m : ℕ) :
    ∃ j : Fin (m + 1), ∃ p : Path (x - (m : ℤ), y) (j.val, m - j.val),
      p.vertex (Fin.last (j.val + (m - j.val))) = (x, y) := by
  have hmem : (x - (m : ℤ), y) ∈ Finset.univ.image (fun j : Fin (m + 1) =>
      (x, y) - ((j.val : ℤ), ((m - j.val : ℕ) : ℤ))) := by
    apply (backwardReachable_mem_iff (x, y) _ m).2
    constructor
    · change x - (m : ℤ) ≤ x ∧ y ≤ y
      exact ⟨by omega, le_rfl⟩
    · change x - (m : ℤ) + y + (m : ℤ) = x + y
      ring
  exact exists_path_from_backwardReachable (x, y) (x - (m : ℤ), y) m hmem

end LPPDifferentiability
