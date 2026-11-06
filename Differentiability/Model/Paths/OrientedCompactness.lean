/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Mathlib.Data.Set.Basic
public import Mathlib.Algebra.Group.Prod
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Order
import Lean.Elab.Tactic.Omega

/-!
# Compactness of oriented step words

The compact product of two-point step spaces turns arbitrarily long actual
good paths in the natural quadrant into one infinite good path.
-/

public section

namespace LPPDifferentiability

private def wordPosition (w : ℕ → Bool) : ℕ → ℕ × ℕ
  | 0 => (0, 0)
  | n + 1 => wordPosition w n + if w n then (1, 0) else (0, 1)

private theorem continuous_wordPosition (n : ℕ) :
    Continuous (fun w : ℕ → Bool => wordPosition w n) := by
  induction n with
  | zero => exact continuous_const
  | succ n ih =>
    exact (continuous_of_discreteTopology :
      Continuous (fun p : (ℕ × ℕ) × Bool =>
        p.1 + if p.2 then (1, 0) else (0, 1))).comp
      (ih.prodMk (continuous_apply n))

private theorem finite_path_word {n : ℕ} (q : Fin (n + 1) → ℕ × ℕ)
    (hzero : q 0 = (0, 0))
    (hstep : ∀ i : Fin n,
      q i.succ = q i.castSucc + (1, 0) ∨ q i.succ = q i.castSucc + (0, 1)) :
    ∃ w : ℕ → Bool, ∀ i : Fin (n + 1), wordPosition w i = q i := by
  classical
  let w : ℕ → Bool := fun k => if h : k < n then
    decide (q ⟨k + 1, by omega⟩ = q ⟨k, by omega⟩ + (1, 0)) else false
  refine ⟨w, ?_⟩
  have hrec : ∀ k (hk : k ≤ n), wordPosition w k = q ⟨k, by omega⟩ := by
    intro k
    induction k with
    | zero => intro _; exact hzero.symm
    | succ k ih =>
      intro hkn
      have hk : k < n := by omega
      rw [wordPosition, ih (by omega)]
      have hs := hstep ⟨k, hk⟩
      change q ⟨k + 1, by omega⟩ = q ⟨k, by omega⟩ + (1, 0) ∨
        q ⟨k + 1, by omega⟩ = q ⟨k, by omega⟩ + (0, 1) at hs
      by_cases he : q ⟨k + 1, by omega⟩ = q ⟨k, by omega⟩ + (1, 0)
      · have hw : w k = true := by simp [w, hk, he]
        rw [hw]
        exact he.symm
      · have hw : w k = false := by simp [w, hk, he]
        rw [hw]
        exact (hs.resolve_left he).symm
  intro i
  exact hrec i (by omega)

/-- Arbitrarily long finite all-good oriented vertex families have an actual
infinite all-good oriented vertex family. The proof uses closed cylinders in
the compact product of Boolean step spaces. -/
theorem exists_infinite_good_oriented_path (G : Set (ℕ × ℕ))
    (hfinite : ∀ n : ℕ, ∃ q : Fin (n + 1) → ℕ × ℕ,
      q 0 = (0, 0) ∧
      (∀ i : Fin n,
        q i.succ = q i.castSucc + (1, 0) ∨ q i.succ = q i.castSucc + (0, 1)) ∧
      ∀ i, q i ∈ G) :
    ∃ v : ℕ → ℕ × ℕ, v 0 = (0, 0) ∧
      (∀ i, v (i + 1) = v i + (1, 0) ∨ v (i + 1) = v i + (0, 1)) ∧
      ∀ i, v i ∈ G := by
  let C : ℕ → Set (ℕ → Bool) := fun n =>
    {w | ∀ i : Fin (n + 1), wordPosition w i ∈ G}
  have hclosed : ∀ n, IsClosed (C n) := by
    intro n
    simp only [C, Set.ofPred_forall]
    exact isClosed_iInter fun i =>
      (isClosed_discrete G).preimage (continuous_wordPosition i)
  have hnonempty : ∀ n, (C n).Nonempty := by
    intro n
    obtain ⟨q, hzero, hstep, hgood⟩ := hfinite n
    obtain ⟨w, hw⟩ := finite_path_word q hzero hstep
    exact ⟨w, fun i => (hw i).symm ▸ hgood i⟩
  have hdecreasing : ∀ n, C (n + 1) ⊆ C n := by
    intro n w hw i
    exact hw ⟨i, by omega⟩
  obtain ⟨w, hw⟩ :=
    IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed C
      hdecreasing hnonempty (hclosed 0).isCompact hclosed
  have hall : ∀ n, w ∈ C n := Set.mem_iInter.mp hw
  refine ⟨wordPosition w, rfl, ?_, ?_⟩
  · intro i
    cases h : w i with
    | false => exact Or.inr (by simp only [wordPosition, h, Bool.false_eq_true, ↓reduceIte])
    | true => exact Or.inl (by simp only [wordPosition, h, ↓reduceIte])
  · intro i
    exact hall i ⟨i, by omega⟩

end LPPDifferentiability
