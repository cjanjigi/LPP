/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Busemann.Frozen.Definitions.OrderedPassage
public import Busemann.Frozen.Definitions.FiniteEdgeStep
import LPP_Foundations.Model.LastPassage.Outgoing
import Mathlib.Tactic

/-! Endpoint order of the two finite last-passage gradients. -/

@[expose] public section

open LPPDifferentiability LPP.Busemann

namespace LPP

/-- For every start and endpoint pair, the horizontal gradient decreases in
the horizontal endpoint coordinate and increases in the vertical coordinate;
the vertical gradient decreases vertically and increases horizontally. This
is the simultaneous coordinate-extension comparison in GRS1510.00859v2,
Lemma 6.3 and the proof of (6.6). -/
theorem local_gradient_order (ω : Environment) :
    let H : Lattice → ℕ → ℕ → ℝ := fun x a b =>
      lastPassage ω x (a + 1, b) - lastPassage ω (x + (1, 0)) (a, b)
    let V : Lattice → ℕ → ℕ → ℝ := fun x a b =>
      lastPassage ω x (a, b + 1) - lastPassage ω (x + (0, 1)) (a, b)
    ∀ a b x,
      (H x (a + 1) b ≤ H x a b ∧ H x a b ≤ H x a (b + 1)) ∧
      (V x a (b + 1) ≤ V x a b ∧ V x a b ≤ V x (a + 1) b) := by
  let H : Lattice → ℕ → ℕ → ℝ := fun x a b =>
    lastPassage ω x (a + 1, b) - lastPassage ω (x + (1, 0)) (a, b)
  let V : Lattice → ℕ → ℕ → ℝ := fun x a b =>
    lastPassage ω x (a, b + 1) - lastPassage ω (x + (0, 1)) (a, b)
  change ∀ a b x,
    (H x (a + 1) b ≤ H x a b ∧ H x a b ≤ H x a (b + 1)) ∧
    (V x a (b + 1) ≤ V x a b ∧ V x a b ≤ V x (a + 1) b)
  have hmax (A B C : ℝ) : max A B - A = max 0 ((B - C) - (A - C)) := by
    by_cases h : A ≤ B
    · rw [max_eq_right h, max_eq_right (by linarith : 0 ≤ (B - C) - (A - C))]
      ring
    · have h' : B ≤ A := le_of_not_ge h
      rw [max_eq_left h', max_eq_left (by linarith : (B - C) - (A - C) ≤ 0)]
      ring
  have hHaxis (x : Lattice) (a : ℕ) : H x a 0 = ω x := by
    dsimp only [H]
    rw [lastPassage_outgoing_horizontal_succ]
    ring
  have hVaxis (x : Lattice) (b : ℕ) : V x 0 b = ω x := by
    dsimp only [V]
    rw [lastPassage_outgoing_vertical_succ]
    ring
  have hcomm (x : Lattice) : (x + (1, 0)) + (0, 1) = (x + (0, 1)) + (1, 0) := by
    apply Prod.ext <;> simp only [Prod.fst_add, Prod.snd_add] <;> ring
  have hHrec (x : Lattice) (a b : ℕ) : H x a (b + 1) =
      ω x + max 0 (H (x + (0, 1)) a b - V (x + (1, 0)) a b) := by
    dsimp only [H, V]
    rw [lastPassage_outgoing_succ_succ, hcomm]
    have h := hmax (lastPassage ω (x + (1, 0)) (a, b + 1))
      (lastPassage ω (x + (0, 1)) (a + 1, b))
      (lastPassage ω ((x + (0, 1)) + (1, 0)) (a, b))
    linarith only [h]
  have hVrec (x : Lattice) (a b : ℕ) : V x (a + 1) b =
      ω x + max 0 (V (x + (1, 0)) a b - H (x + (0, 1)) a b) := by
    dsimp only [H, V]
    rw [lastPassage_outgoing_succ_succ, hcomm]
    have h := hmax (lastPassage ω (x + (0, 1)) (a + 1, b))
      (lastPassage ω (x + (1, 0)) (a, b + 1))
      (lastPassage ω ((x + (0, 1)) + (1, 0)) (a, b))
    rw [max_comm] at h
    linarith only [h]
  have hmain : ∀ n a b, a + b = n → ∀ x,
      (H x (a + 1) b ≤ H x a b ∧ H x a b ≤ H x a (b + 1)) ∧
      (V x a (b + 1) ≤ V x a b ∧ V x a b ≤ V x (a + 1) b) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro a b hn x
      constructor
      · cases b with
        | zero =>
          simp only [hHaxis, hHrec]
          exact ⟨le_rfl, le_add_of_nonneg_right (le_max_left _ _)⟩
        | succ b =>
          have hN := ih (a + b) (by omega) a b rfl (x + (0, 1))
          have hE := ih (a + b) (by omega) a b rfl (x + (1, 0))
          constructor
          · rw [hHrec, hHrec]
            apply add_le_add le_rfl
            apply max_le_max le_rfl
            linarith only [hN.1.1, hE.2.2]
          · rw [hHrec, hHrec]
            apply add_le_add le_rfl
            apply max_le_max le_rfl
            linarith only [hN.1.2, hE.2.1]
      · cases a with
        | zero =>
          simp only [hVaxis, hVrec]
          exact ⟨le_rfl, le_add_of_nonneg_right (le_max_left _ _)⟩
        | succ a =>
          have hN := ih (a + b) (by omega) a b rfl (x + (0, 1))
          have hE := ih (a + b) (by omega) a b rfl (x + (1, 0))
          constructor
          · rw [hVrec, hVrec]
            apply add_le_add le_rfl
            apply max_le_max le_rfl
            linarith only [hE.2.1, hN.1.2]
          · rw [hVrec, hVrec]
            apply add_le_add le_rfl
            apply max_le_max le_rfl
            linarith only [hE.2.2, hN.1.1]
  intro a b x
  exact hmain (a + b) a b rfl x

-- Iterate the two coordinate-extension inequalities along one antidiagonal.
private theorem finite_chain_order (F : ℕ → ℕ → ℝ)
    (hEast : ∀ a b, F (a + 1) b ≤ F a b)
    (hNorth : ∀ a b, F a b ≤ F a (b + 1)) (a b k : ℕ) :
    F (a + k) b ≤ F a (b + k) := by
  induction k with
  | zero => exact le_rfl
  | succ k ih =>
    calc
      F (a + (k + 1)) b = F ((a + k) + 1) b := by rw [Nat.add_assoc]
      _ ≤ F (a + k) b := hEast (a + k) b
      _ ≤ F a (b + k) := ih
      _ ≤ F a (b + (k + 1)) := by simpa only [Nat.add_assoc] using hNorth a (b + k)

/-- At a common endpoint level, moving the endpoint right decreases the horizontal
passage increment and increases the vertical increment, for arbitrary real weights.
This is the finite comparison of GRS1510.00859v2, Lemma 6.3. -/
theorem passage_difference_antidiagonal_order
    (ω : Environment) (x : Lattice) (i : Fin 2) (v w : Lattice)
    (hv : x ≤ v ∧ x + finiteEdgeStep i ≤ v)
    (hw : x ≤ w ∧ x + finiteEdgeStep i ≤ w)
    (hlevel : v.1 + v.2 = w.1 + w.2) (horder : v.1 ≤ w.1) :
    let Dv : ℝ := orderedPassage ω ⟨(x, v), hv.1⟩ -
      orderedPassage ω ⟨(x + finiteEdgeStep i, v), hv.2⟩
    let Dw : ℝ := orderedPassage ω ⟨(x, w), hw.1⟩ -
      orderedPassage ω ⟨(x + finiteEdgeStep i, w), hw.2⟩
    if i = 0 then Dw ≤ Dv else Dv ≤ Dw := by
  have hlocal := local_gradient_order ω
  fin_cases i
  · have hvE : x + (1, 0) ≤ v := hv.2
    have hwE : x + (1, 0) ≤ w := hw.2
    let a : ℕ := (v.1 - (x.1 + 1)).toNat
    let b : ℕ := (w.2 - x.2).toNat
    let k : ℕ := (w.1 - v.1).toNat
    have ha : (a : ℤ) = v.1 - (x.1 + 1) := Int.toNat_of_nonneg (by
      have h := hvE.1
      simp only [Prod.fst_add] at h
      omega)
    have hb : (b : ℤ) = w.2 - x.2 := Int.toNat_of_nonneg (sub_nonneg.mpr hw.1.2)
    have hk : (k : ℤ) = w.1 - v.1 := Int.toNat_of_nonneg (sub_nonneg.mpr horder)
    have hdv : ((v.1 - x.1).toNat, (v.2 - x.2).toNat) = (a + 1, b + k) := by
      apply Prod.ext <;> (dsimp; omega)
    have hcv : ((v.1 - (x + (1, 0)).1).toNat,
        (v.2 - (x + (1, 0)).2).toNat) = (a, b + k) := by
      apply Prod.ext
      · rfl
      · dsimp
        omega
    have hdw : ((w.1 - x.1).toNat, (w.2 - x.2).toNat) = (a + k + 1, b) := by
      apply Prod.ext
      · dsimp
        omega
      · rfl
    have hcw : ((w.1 - (x + (1, 0)).1).toNat,
        (w.2 - (x + (1, 0)).2).toNat) = (a + k, b) := by
      apply Prod.ext <;> (dsimp; omega)
    change orderedPassage ω ⟨(x, w), hw.1⟩ - orderedPassage ω ⟨(x + (1, 0), w), hwE⟩ ≤
      orderedPassage ω ⟨(x, v), hv.1⟩ - orderedPassage ω ⟨(x + (1, 0), v), hvE⟩
    dsimp only [orderedPassage]
    rw [hdv, hcv, hdw, hcw]
    exact finite_chain_order
      (fun a b => lastPassage ω x (a + 1, b) - lastPassage ω (x + (1, 0)) (a, b))
      (fun a b => (hlocal a b x).1.1) (fun a b => (hlocal a b x).1.2) a b k
  · have hvN : x + (0, 1) ≤ v := hv.2
    have hwN : x + (0, 1) ≤ w := hw.2
    let a : ℕ := (v.1 - x.1).toNat
    let b : ℕ := (w.2 - (x.2 + 1)).toNat
    let k : ℕ := (w.1 - v.1).toNat
    have ha : (a : ℤ) = v.1 - x.1 := Int.toNat_of_nonneg (sub_nonneg.mpr hv.1.1)
    have hb : (b : ℤ) = w.2 - (x.2 + 1) := Int.toNat_of_nonneg (by
      have h := hwN.2
      simp only [Prod.snd_add] at h
      omega)
    have hk : (k : ℤ) = w.1 - v.1 := Int.toNat_of_nonneg (sub_nonneg.mpr horder)
    have hdv : ((v.1 - x.1).toNat, (v.2 - x.2).toNat) = (a, b + k + 1) := by
      apply Prod.ext
      · rfl
      · dsimp
        omega
    have hcv : ((v.1 - (x + (0, 1)).1).toNat,
        (v.2 - (x + (0, 1)).2).toNat) = (a, b + k) := by
      apply Prod.ext <;> (dsimp; omega)
    have hdw : ((w.1 - x.1).toNat, (w.2 - x.2).toNat) = (a + k, b + 1) := by
      apply Prod.ext <;> (dsimp; omega)
    have hcw : ((w.1 - (x + (0, 1)).1).toNat,
        (w.2 - (x + (0, 1)).2).toNat) = (a + k, b) := by
      apply Prod.ext
      · dsimp
        omega
      · rfl
    have h := finite_chain_order
      (fun a b => -(lastPassage ω x (a, b + 1) - lastPassage ω (x + (0, 1)) (a, b)))
      (fun a b => neg_le_neg (hlocal a b x).2.2)
      (fun a b => neg_le_neg (hlocal a b x).2.1) a b k
    change orderedPassage ω ⟨(x, v), hv.1⟩ - orderedPassage ω ⟨(x + (0, 1), v), hvN⟩ ≤
      orderedPassage ω ⟨(x, w), hw.1⟩ - orderedPassage ω ⟨(x + (0, 1), w), hwN⟩
    dsimp only [orderedPassage]
    rw [hdv, hcv, hdw, hcw]
    exact neg_le_neg_iff.mp h

end LPP
