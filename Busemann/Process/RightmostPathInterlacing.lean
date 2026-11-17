/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Busemann.Process.RightmostPaths
public import LPP_Foundations.Model.Paths.HeightOrder
import Mathlib.Logic.Function.Iterate
import Lean.Elab.Tactic.Omega

/-! Interlacing of three deterministic rightmost rays from vertical starts. -/

@[expose] public section

open LPPDifferentiability

namespace LPP.Busemann

/-- If the rays from heights `b` and `c` are disjoint, then the lower ray from
`a` cannot meet the ray from `c` when `a < b < c`. This is the vertical
interlacing step in GRS, arXiv:1510.00860v1, lines 1543–1551. -/
theorem rightmostCocyclePath_disjoint_lower_of_vertical_pair
    (C : Lattice → Lattice → ℝ)
    (a b c : ℕ) (hab : a < b) (hbc : b < c)
    (hDisjoint : ∀ r s : ℕ,
      rightmostCocyclePath C (0, (b : ℤ)) r ≠
        rightmostCocyclePath C (0, (c : ℤ)) s) :
    ∀ r s : ℕ,
      rightmostCocyclePath C (0, (a : ℤ)) r ≠
        rightmostCocyclePath C (0, (c : ℤ)) s := by
  classical
  let ray : ℕ → ℕ → Lattice := fun j n =>
    rightmostCocyclePath C (0, (j : ℤ)) n

  -- Each ray uses the same east-or-north successor at every local time.
  have rayStep (j n : ℕ) :
      ray j (n + 1) = ray j n + (1, 0) ∨
        ray j (n + 1) = ray j n + (0, 1) := by
    simpa only [ray, rightmostCocyclePath, Function.iterate_succ_apply'] using
      rightmostCocycleSuccessor_step C
        (rightmostCocyclePath C (0, (j : ℤ)) n)

  -- The absolute level rises by exactly one at each step.
  have rayLevel (j n : ℕ) :
      (ray j n).1 + (ray j n).2 = (j : ℤ) + (n : ℤ) := by
    induction n with
    | zero => simp [ray, rightmostCocyclePath]
    | succ n ih =>
        rcases rayStep j n with h | h
        · rw [h]
          simp only [Prod.fst_add, Prod.snd_add, Nat.cast_succ]
          omega
        · rw [h]
          simp only [Prod.fst_add, Prod.snd_add, Nat.cast_succ]
          omega

  -- The first coordinate of each ray stays nonnegative.
  have rayFirstNonneg (j n : ℕ) : 0 ≤ (ray j n).1 := by
    induction n with
    | zero => simp [ray, rightmostCocyclePath]
    | succ n ih =>
        rcases rayStep j n with h | h
        · rw [h]
          simp only [Prod.fst_add]
          omega
        · rw [h]
          simp only [Prod.fst_add]
          omega

  -- Restarting one iterate at its current vertex gives the same future ray.
  have pathRestart (x : Lattice) (m n : ℕ) :
      rightmostCocyclePath C (rightmostCocyclePath C x m) n =
        rightmostCocyclePath C x (m + n) := by
    change (rightmostCocycleSuccessor C)^[n]
        ((rightmostCocycleSuccessor C)^[m] x) =
      (rightmostCocycleSuccessor C)^[m + n] x
    rw [Nat.add_comm m n, Function.iterate_add_apply]

  -- Shared finite height order compares any two disjoint vertical rays.
  have heightLtOfAvoidance
      (u v N : ℕ) (huv : u < v) (hvN : v ≤ N)
      (hAvoid : ∀ k : ℕ, k ≤ N - v →
        ray u (v - u + k) ≠ ray v k) :
      (ray u (N - u)).2 < (ray v (N - v)).2 := by
    let p : ℕ → Lattice := fun k => ray u (v - u + k)
    let q : ℕ → Lattice := ray v

    have hpStep (k : ℕ) :
        p (k + 1) = p k + (1, 0) ∨ p (k + 1) = p k + (0, 1) := by
      dsimp only [p]
      simpa only [Nat.add_assoc] using rayStep u (v - u + k)
    have hqStep (k : ℕ) :
        q (k + 1) = q k + (1, 0) ∨ q (k + 1) = q k + (0, 1) := by
      dsimp only [q]
      exact rayStep v k
    have hqZero : q 0 = (0, (v : ℤ)) := by
      simp only [q, ray, rightmostCocyclePath, Function.iterate_zero_apply]
    have hInitialLevel :
        (p 0).1 + (p 0).2 = (q 0).1 + (q 0).2 := by
      change (ray u (v - u)).1 + (ray u (v - u)).2 =
        (ray v 0).1 + (ray v 0).2
      rw [rayLevel u (v - u), rayLevel v 0]
      omega
    have hpFirstNonneg : 0 ≤ (p 0).1 := by
      simpa only [p, Nat.add_zero] using rayFirstNonneg u (v - u)
    have hInitialAvoid : p 0 ≠ q 0 := by
      simpa only [p, q, Nat.add_zero] using hAvoid 0 (by omega)
    have hpLevel : (p 0).1 + (p 0).2 = (v : ℤ) := by
      simpa only [hqZero, zero_add] using hInitialLevel
    have hpHeightNe : (p 0).2 ≠ (v : ℤ) := by
      intro hHeight
      apply hInitialAvoid
      rw [hqZero]
      apply Prod.ext
      · change (p 0).1 = 0
        omega
      · exact hHeight
    have hInitialOrder : (p 0).2 < (q 0).2 := by
      rw [hqZero]
      change (p 0).2 < (v : ℤ)
      omega
    have hFinalOrder :=
      (up_right_paths_strict_height_order_iff_of_disjoint p q (N - v)
        hpStep hqStep hInitialLevel (fun k hk => hAvoid k hk)).mp
        hInitialOrder
    have hIndex : v - u + (N - v) = N - u := by omega
    calc
      (ray u (N - u)).2 = (p (N - v)).2 := by
        dsimp only [p]
        rw [hIndex]
      _ < (q (N - v)).2 := hFinalOrder
      _ = (ray v (N - v)).2 := rfl

  intro r s hMeet
  change ray a r = ray c s at hMeet

  -- A meeting point fixes one common absolute level for all three rays.
  have hMeetingLevel : a + r = c + s := by
    have hPointLevel := congrArg (fun z : Lattice => z.1 + z.2) hMeet
    rw [rayLevel a r, rayLevel c s] at hPointLevel
    omega
  let N : ℕ := a + r
  have hcN : c ≤ N := by
    dsimp [N]
    omega
  have hbN : b ≤ N := by omega

  -- Disjointness keeps the b-ray strictly below the c-ray at level N.
  have hBCheight : (ray b (N - b)).2 < (ray c (N - c)).2 :=
    heightLtOfAvoidance b c N hbc hcN (fun k _ => hDisjoint (c - b + k) k)

  -- If the a- and b-rays avoided each other through N, their order would
  -- contradict the order just obtained from the b- and c-rays.
  have hABmeeting :
      ∃ k : ℕ, k ≤ N - b ∧ ray a (b - a + k) = ray b k := by
    by_contra hNoMeeting
    have hABavoid (k : ℕ) (hk : k ≤ N - b) :
        ray a (b - a + k) ≠ ray b k := by
      intro hEqual
      exact hNoMeeting ⟨k, hk, hEqual⟩
    have hABheight := heightLtOfAvoidance a b N hab hbN hABavoid
    have hACheight : (ray a (N - a)).2 = (ray c (N - c)).2 := by
      have hNa : N - a = r := by
        dsimp [N]
        omega
      have hNc : N - c = s := by
        dsimp [N]
        omega
      rw [hNa, hNc, hMeet]
    omega

  -- The a/b meeting makes their tails identical at the common level N.
  obtain ⟨k, hk, hABmeet⟩ := hABmeeting
  let t : ℕ := N - b - k
  have htB : k + t = N - b := by
    dsimp [t]
    omega
  have htA : b - a + k + t = N - a := by
    dsimp [t]
    omega
  have hABatN : ray a (N - a) = ray b (N - b) := by
    calc
      ray a (N - a) = ray a (b - a + k + t) := by rw [htA]
      _ = rightmostCocyclePath C (ray a (b - a + k)) t := by
        simpa only [ray] using
          (pathRestart (0, (a : ℤ)) (b - a + k) t).symm
      _ = rightmostCocyclePath C (ray b k) t := by rw [hABmeet]
      _ = ray b (k + t) := by
        simpa only [ray] using pathRestart (0, (b : ℤ)) k t
      _ = ray b (N - b) := by rw [htB]
  have hBCmeet : ray b (N - b) = ray c (N - c) := by
    calc
      ray b (N - b) = ray a (N - a) := hABatN.symm
      _ = ray c (N - c) := by
        have hNa : N - a = r := by
          dsimp [N]
          omega
        have hNc : N - c = s := by
          dsimp [N]
          omega
        rw [hNa, hNc, hMeet]
  exact hDisjoint (N - b) (N - c) hBCmeet

end LPP.Busemann
