/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Differentiability.Model.Paths.OrientedCompactness
import Mathlib.Data.Fin.Tuple.Basic
import Lean.Elab.Tactic.Omega

/-!
# Extension of finite oriented endpoint witnesses

The terminal site may be bad. If it is good, appending either forward step
gives an actual witness for the neighboring endpoint.
-/

public section

namespace LPPDifferentiability

private theorem oriented_endpoint_set_extend (G : Set (ℕ × ℕ))
    (w y : ℕ × ℕ)
    (hw : w ∈ {x : ℕ × ℕ | ∃ n : ℕ, ∃ q : Fin (n + 1) → ℕ × ℕ,
      q 0 = (0, 0) ∧ q (Fin.last n) = x ∧
      (∀ i : Fin n,
        q i.succ = q i.castSucc + (1, 0) ∨ q i.succ = q i.castSucc + (0, 1)) ∧
      ∀ i : Fin (n + 1), (i : ℕ) < n → q i ∈ G})
    (hwgood : w ∈ G)
    (hstepEnd : y = w + (1, 0) ∨ y = w + (0, 1)) :
    y ∈ {x : ℕ × ℕ | ∃ n : ℕ, ∃ q : Fin (n + 1) → ℕ × ℕ,
      q 0 = (0, 0) ∧ q (Fin.last n) = x ∧
      (∀ i : Fin n,
        q i.succ = q i.castSucc + (1, 0) ∨ q i.succ = q i.castSucc + (0, 1)) ∧
      ∀ i : Fin (n + 1), (i : ℕ) < n → q i ∈ G} := by
  rcases hw with ⟨n, q, hzero, hlast, hstep, hgood⟩
  have hlastStep : y = q (Fin.last n) + (1, 0) ∨
      y = q (Fin.last n) + (0, 1) := by
    rw [← hlast] at hstepEnd
    exact hstepEnd
  let q' : Fin ((n + 1) + 1) → ℕ × ℕ := Fin.lastCases y q
  refine ⟨n + 1, q', ?_, ?_, ?_, ?_⟩
  · change q' (Fin.castSucc (0 : Fin (n + 1))) = (0, 0)
    simp only [q', Fin.lastCases_castSucc, hzero]
  · simp only [q', Fin.lastCases_last]
  · intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa only [q', Fin.lastCases_last, Fin.succ_last,
        Fin.lastCases_castSucc] using hlastStep
    · simpa only [q', Fin.lastCases_castSucc, Fin.succ_castSucc] using hstep j
  · intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · intro hi
      simp only [Fin.val_last] at hi
      omega
    · intro _
      refine Fin.lastCases ?_ (fun k => ?_) j
      · simpa only [q', Fin.lastCases_castSucc, hlast] using hwgood
      · simpa only [q', Fin.lastCases_castSucc] using hgood k.castSucc k.isLt

/-- The zero-length path witnesses that the origin is in the literal endpoint
set, even when the origin is bad. -/
theorem oriented_endpoint_set_zero (G : Set (ℕ × ℕ)) :
    (0, 0) ∈ {x : ℕ × ℕ | ∃ n : ℕ, ∃ q : Fin (n + 1) → ℕ × ℕ,
      q 0 = (0, 0) ∧ q (Fin.last n) = x ∧
      (∀ i : Fin n,
        q i.succ = q i.castSucc + (1, 0) ∨ q i.succ = q i.castSucc + (0, 1)) ∧
      ∀ i : Fin (n + 1), (i : ℕ) < n → q i ∈ G} := by
  refine ⟨0, fun _ => (0, 0), rfl, rfl, ?_, ?_⟩
  · intro i
    exact Fin.elim0 i
  · intro i hi
    omega

/-- A good endpoint extends by either actual oriented unit step. -/
theorem oriented_endpoint_set_forward_closed (G : Set (ℕ × ℕ))
    (w : ℕ × ℕ)
    (hw : w ∈ {x : ℕ × ℕ | ∃ n : ℕ, ∃ q : Fin (n + 1) → ℕ × ℕ,
      q 0 = (0, 0) ∧ q (Fin.last n) = x ∧
      (∀ i : Fin n,
        q i.succ = q i.castSucc + (1, 0) ∨ q i.succ = q i.castSucc + (0, 1)) ∧
      ∀ i : Fin (n + 1), (i : ℕ) < n → q i ∈ G})
    (hwgood : w ∈ G) :
    w + (1, 0) ∈ {x : ℕ × ℕ | ∃ n : ℕ, ∃ q : Fin (n + 1) → ℕ × ℕ,
      q 0 = (0, 0) ∧ q (Fin.last n) = x ∧
      (∀ i : Fin n,
        q i.succ = q i.castSucc + (1, 0) ∨ q i.succ = q i.castSucc + (0, 1)) ∧
      ∀ i : Fin (n + 1), (i : ℕ) < n → q i ∈ G} ∧
    w + (0, 1) ∈ {x : ℕ × ℕ | ∃ n : ℕ, ∃ q : Fin (n + 1) → ℕ × ℕ,
      q 0 = (0, 0) ∧ q (Fin.last n) = x ∧
      (∀ i : Fin n,
        q i.succ = q i.castSucc + (1, 0) ∨ q i.succ = q i.castSucc + (0, 1)) ∧
      ∀ i : Fin (n + 1), (i : ℕ) < n → q i ∈ G} := by
  exact ⟨oriented_endpoint_set_extend G w (w + (1, 0)) hw hwgood (Or.inl rfl),
    oriented_endpoint_set_extend G w (w + (0, 1)) hw hwgood (Or.inr rfl)⟩

/-- Any endpoint with a missing forward neighbor is bad. -/
theorem oriented_endpoint_set_bad_of_forward_exit (G : Set (ℕ × ℕ))
    (w : ℕ × ℕ)
    (hw : w ∈ {x : ℕ × ℕ | ∃ n : ℕ, ∃ q : Fin (n + 1) → ℕ × ℕ,
      q 0 = (0, 0) ∧ q (Fin.last n) = x ∧
      (∀ i : Fin n,
        q i.succ = q i.castSucc + (1, 0) ∨ q i.succ = q i.castSucc + (0, 1)) ∧
      ∀ i : Fin (n + 1), (i : ℕ) < n → q i ∈ G})
    (hexit : w + (1, 0) ∉ {x : ℕ × ℕ | ∃ n : ℕ, ∃ q : Fin (n + 1) → ℕ × ℕ,
      q 0 = (0, 0) ∧ q (Fin.last n) = x ∧
      (∀ i : Fin n,
        q i.succ = q i.castSucc + (1, 0) ∨ q i.succ = q i.castSucc + (0, 1)) ∧
      ∀ i : Fin (n + 1), (i : ℕ) < n → q i ∈ G} ∨
      w + (0, 1) ∉ {x : ℕ × ℕ | ∃ n : ℕ, ∃ q : Fin (n + 1) → ℕ × ℕ,
      q 0 = (0, 0) ∧ q (Fin.last n) = x ∧
      (∀ i : Fin n,
        q i.succ = q i.castSucc + (1, 0) ∨ q i.succ = q i.castSucc + (0, 1)) ∧
      ∀ i : Fin (n + 1), (i : ℕ) < n → q i ∈ G}) :
    w ∉ G := by
  intro hwgood
  rcases oriented_endpoint_set_forward_closed G w hw hwgood with ⟨h₁, h₂⟩
  rcases hexit with h₁' | h₂'
  · exact h₁' h₁
  · exact h₂' h₂

end LPPDifferentiability
