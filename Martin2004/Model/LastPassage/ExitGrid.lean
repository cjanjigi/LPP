/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Martin2004.Model.LastPassage.ExitPoint
public import LPP_Foundations.Model.LastPassage.Inclusive
public import LPP_Foundations.Model.LastPassage.Locality
public import Martin2004.Model.LastPassage.Stationary
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith

/-! The deterministic exit-grid reduction for the stationary passage time. The exit point of
an optimal path leaves the axes at some site; the axes are cut into `K` pieces by the grid
points `k_r = m r / K` and `l_r = n r / K` (natural division), the boundary sum is replaced by
the sum up to the next grid point, and the bulk piece is started at the previous grid point.
This bound is used to compare stationary passage times with bulk passage times. -/

@[expose] public section

open Set

namespace LPPDifferentiability

/-- Choice of the grid piece: if `0 < a ≤ m`, there is `r < K` with
`m r / K < a ≤ m (r + 1) / K`. Take the least grid index `j` with `a ≤ m j / K`;
it is positive and at most `K`, and `r = j - 1`. -/
private theorem exists_grid_index {m K a : ℕ} (hK : 0 < K) (ha : 0 < a) (ham : a ≤ m) :
    ∃ r : ℕ, r < K ∧ m * r / K < a ∧ a ≤ m * (r + 1) / K := by
  classical
  have hKspec : a ≤ m * K / K := by
    rw [Nat.mul_div_cancel _ hK]
    exact ham
  have hex : ∃ j, a ≤ m * j / K := ⟨K, hKspec⟩
  obtain ⟨j, hjspec, hjmin⟩ : ∃ j, a ≤ m * j / K ∧ ∀ i < j, ¬ a ≤ m * i / K :=
    ⟨Nat.find hex, Nat.find_spec hex, fun i hi => Nat.find_min hex hi⟩
  have hjK : j ≤ K := by
    by_contra hcon
    exact hjmin K (by omega) hKspec
  have hj0 : j ≠ 0 := by
    intro h
    rw [h] at hjspec
    simp at hjspec
    omega
  obtain ⟨r, hr⟩ := Nat.exists_eq_succ_of_ne_zero hj0
  refine ⟨r, by omega, ?_, ?_⟩
  · have h := hjmin r (by omega)
    omega
  · rw [hr] at hjspec
    exact hjspec

/-- The inclusive passage time along the horizontal axis grows with its length when the weights
are nonnegative. -/
private theorem inclusivePassage_horizontal_mono {η : Environment} (hη : ∀ z, 0 ≤ η z)
    (u : Lattice) {a b : ℕ} (h : a ≤ b) :
    inclusivePassage η u (a, 0) ≤ inclusivePassage η u (b, 0) := by
  have e : ∀ n : ℕ, ∑ i : Fin (n + 1), η (u.1 + (i.val : ℤ), u.2) =
      ∑ i ∈ Finset.range (n + 1), η (u.1 + (i : ℤ), u.2) :=
    fun n => (Finset.sum_range (fun i : ℕ => η (u.1 + (i : ℤ), u.2))).symm
  rw [inclusivePassage_horizontal, inclusivePassage_horizontal, e, e]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega))
    (fun i _ _ => hη _)

/-- The inclusive passage time along the vertical axis grows with its length when the weights
are nonnegative. -/
private theorem inclusivePassage_vertical_mono {η : Environment} (hη : ∀ z, 0 ≤ η z)
    (u : Lattice) {a b : ℕ} (h : a ≤ b) :
    inclusivePassage η u (0, a) ≤ inclusivePassage η u (0, b) := by
  have e : ∀ n : ℕ, ∑ j : Fin (n + 1), η (u.1, u.2 + (j.val : ℤ)) =
      ∑ j ∈ Finset.range (n + 1), η (u.1, u.2 + (j : ℤ)) :=
    fun n => (Finset.sum_range (fun j : ℕ => η (u.1, u.2 + (j : ℤ)))).symm
  rw [inclusivePassage_vertical, inclusivePassage_vertical, e, e]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega))
    (fun i _ _ => hη _)

/-- Environments that agree on the endpoint rectangle have the same inclusive passage time. -/
private theorem inclusivePassage_eq_of_eqOn {ω η : Environment} {u : Lattice} {d : ℕ × ℕ}
    (h : EqOn ω η (Icc u (u + ((d.1 : ℤ), (d.2 : ℤ))))) :
    inclusivePassage ω u d = inclusivePassage η u d := by
  have hend : u + ((d.1 : ℤ), (d.2 : ℤ)) ∈ Icc u (u + ((d.1 : ℤ), (d.2 : ℤ))) := by
    refine ⟨?_, le_rfl⟩
    rcases u with ⟨a, b⟩
    exact Prod.le_def.2 ⟨by simp, by simp⟩
  unfold inclusivePassage
  rw [lastPassage_eq_of_eqOn h, h hend]

/-- For `0 < ρ < 1` and nonnegative weights the stationary weights are nonnegative. -/
private theorem stationaryEnvironment_nonneg {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    {ω : Environment} (hω : ∀ z, 0 ≤ ω z) (z : Lattice) : 0 ≤ stationaryEnvironment ρ ω z := by
  unfold stationaryEnvironment stationaryRate
  apply div_nonneg (hω z)
  split_ifs
  · linarith
  · exact hρ0.le
  · exact zero_le_one

/-- Horizontal exit, after the grid is chosen: the exit `(k + 1, 0)` lies in the grid piece
`kr < k + 1 ≤ kr'`. -/
private theorem horizontal_exit_bound {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    {ω : Environment} (hω : ∀ z, 0 ≤ ω z) {m n k kr kr' : ℕ} (hkr : kr ≤ k) (hk : k ≤ m)
    (hkr' : k + 1 ≤ kr')
    (h : inclusivePassage (stationaryEnvironment ρ ω) 0 (m + 1, n + 1) ≤
      inclusivePassage (stationaryEnvironment ρ ω) 0 (k + 1, 0) +
        inclusivePassage (stationaryEnvironment ρ ω) (((k : ℤ) + 1, 1) : Lattice) (m - k, n)) :
    stationaryPassage ρ ω (m + 1) (n + 1) ≤
      inclusivePassage (stationaryEnvironment ρ ω) 0 (kr', 0) +
        inclusivePassage ω ((((kr : ℕ) : ℤ) + 1, 1) : Lattice) (m + 1 - kr - 1, n + 1 - 1) := by
  have hS := stationaryEnvironment_nonneg hρ0 hρ1 hω
  have hb := inclusivePassage_horizontal_mono hS (0 : Lattice) hkr'
  have hbulk : inclusivePassage (stationaryEnvironment ρ ω) (((k : ℤ) + 1, 1) : Lattice)
        (m - k, n) = inclusivePassage ω (((k : ℤ) + 1, 1) : Lattice) (m - k, n) := by
    apply inclusivePassage_eq_of_eqOn
    rintro ⟨a, b⟩ hz
    have ha : (k : ℤ) + 1 ≤ a := hz.1.1
    have hb' : (1 : ℤ) ≤ b := hz.1.2
    exact stationaryEnvironment_bulk ρ ω a b (by omega) (by omega)
  have hearly := inclusivePassage_le_of_earlier_start hω
    ((((kr : ℕ) : ℤ) + 1, 1) : Lattice) (k - kr, 0) (m - k, n)
  have e1 : ((((kr : ℕ) : ℤ) + 1, 1) : Lattice) +
      ((((k - kr, 0) : ℕ × ℕ).1 : ℤ), (((k - kr, 0) : ℕ × ℕ).2 : ℤ)) = ((k : ℤ) + 1, 1) := by
    refine Prod.ext ?_ ?_
    · simp; omega
    · simp
  have e2 : ((k - kr, 0) : ℕ × ℕ) + (m - k, n) = (m + 1 - kr - 1, n + 1 - 1) := by
    refine Prod.ext ?_ ?_
    · simp; omega
    · simp
  rw [e1, e2] at hearly
  unfold stationaryPassage
  linarith

/-- Vertical exit, after the grid is chosen: the exit `(0, l + 1)` lies in the grid piece
`lr < l + 1 ≤ lr'`. -/
private theorem vertical_exit_bound {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    {ω : Environment} (hω : ∀ z, 0 ≤ ω z) {m n l lr lr' : ℕ} (hlr : lr ≤ l) (hl : l ≤ n)
    (hlr' : l + 1 ≤ lr')
    (h : inclusivePassage (stationaryEnvironment ρ ω) 0 (m + 1, n + 1) ≤
      inclusivePassage (stationaryEnvironment ρ ω) 0 (0, l + 1) +
        inclusivePassage (stationaryEnvironment ρ ω) ((1, (l : ℤ) + 1) : Lattice) (m, n - l)) :
    stationaryPassage ρ ω (m + 1) (n + 1) ≤
      inclusivePassage (stationaryEnvironment ρ ω) 0 (0, lr') +
        inclusivePassage ω ((1, ((lr : ℕ) : ℤ) + 1) : Lattice) (m + 1 - 1, n + 1 - lr - 1) := by
  have hS := stationaryEnvironment_nonneg hρ0 hρ1 hω
  have hb := inclusivePassage_vertical_mono hS (0 : Lattice) hlr'
  have hbulk : inclusivePassage (stationaryEnvironment ρ ω) ((1, (l : ℤ) + 1) : Lattice)
        (m, n - l) = inclusivePassage ω ((1, (l : ℤ) + 1) : Lattice) (m, n - l) := by
    apply inclusivePassage_eq_of_eqOn
    rintro ⟨a, b⟩ hz
    have ha : (1 : ℤ) ≤ a := hz.1.1
    have hb' : (l : ℤ) + 1 ≤ b := hz.1.2
    exact stationaryEnvironment_bulk ρ ω a b (by omega) (by omega)
  have hearly := inclusivePassage_le_of_earlier_start hω
    ((1, ((lr : ℕ) : ℤ) + 1) : Lattice) (0, l - lr) (m, n - l)
  have e1 : ((1, ((lr : ℕ) : ℤ) + 1) : Lattice) +
      ((((0, l - lr) : ℕ × ℕ).1 : ℤ), (((0, l - lr) : ℕ × ℕ).2 : ℤ)) = (1, (l : ℤ) + 1) := by
    refine Prod.ext ?_ ?_
    · simp
    · simp; omega
  have e2 : ((0, l - lr) : ℕ × ℕ) + (m, n - l) = (m + 1 - 1, n + 1 - lr - 1) := by
    refine Prod.ext ?_ ?_
    · simp
    · simp; omega
  rw [e1, e2] at hearly
  unfold stationaryPassage
  linarith

/-- Deterministic reduction. With nonnegative weights and grid points
`k_r = m r / K`, `l_r = n r / K` (natural division), the stationary passage time `G(m, n)` is at
most one of the `2K` grid terms: a boundary sum up to the next grid point plus the bulk passage
time from just after the previous grid point. The proof takes the exit point of
`inclusivePassage_le_exit`, picks the grid piece that contains it, enlarges the boundary sum to
the end of that piece, and starts the bulk piece earlier. -/
theorem stationaryPassage_le_exitGridTerm {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    {ω : Environment} (hω : ∀ z, 0 ≤ ω z) {m n K : ℕ} (hm : 0 < m) (hn : 0 < n)
    (hK : 0 < K) :
    ∃ r : Fin K,
      stationaryPassage ρ ω m n ≤
          inclusivePassage (stationaryEnvironment ρ ω) 0 (m * ((r : ℕ) + 1) / K, 0) +
            inclusivePassage ω ((((m * (r : ℕ) / K : ℕ) : ℤ) + 1, 1) : Lattice)
              (m - m * (r : ℕ) / K - 1, n - 1) ∨
      stationaryPassage ρ ω m n ≤
          inclusivePassage (stationaryEnvironment ρ ω) 0 (0, n * ((r : ℕ) + 1) / K) +
            inclusivePassage ω ((1, ((n * (r : ℕ) / K : ℕ) : ℤ) + 1) : Lattice)
              (m - 1, n - n * (r : ℕ) / K - 1) := by
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
  rcases inclusivePassage_le_exit (stationaryEnvironment ρ ω) m' n' with
    ⟨k, hk, h⟩ | ⟨l, hl, h⟩
  · obtain ⟨r, hrK, hr1, hr2⟩ :=
      exists_grid_index (m := m' + 1) (a := k + 1) hK (by omega) (by omega)
    exact ⟨⟨r, hrK⟩, Or.inl
      (horizontal_exit_bound hρ0 hρ1 hω (kr := (m' + 1) * r / K)
        (kr' := (m' + 1) * (r + 1) / K) (by omega) hk hr2 h)⟩
  · obtain ⟨r, hrK, hr1, hr2⟩ :=
      exists_grid_index (m := n' + 1) (a := l + 1) hK (by omega) (by omega)
    exact ⟨⟨r, hrK⟩, Or.inr
      (vertical_exit_bound hρ0 hρ1 hω (lr := (n' + 1) * r / K)
        (lr' := (n' + 1) * (r + 1) / K) (by omega) hl hr2 h)⟩

end LPPDifferentiability
