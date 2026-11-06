/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import LPP_Foundations.Model.LastPassage.Inclusive
public import LPP_Foundations.Model.LastPassage.Locality
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Order.MinMax
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! The deterministic part of the stationary corner model: site rates, the stationary
environment (each weight divided by the rate of its site), the stationary passage time `G`,
its horizontal and vertical increments, the two cell recursions for the increments, the
boundary values, the column-plus-row telescoping and the comparison with the passage time
of the original environment from `(1, 1)`.

Martin (2004), Theorem 2.4, uses the exact exponential shape formula in its
proof. This file supplies the stationary construction and its deterministic
identities; the proof states the formula but does not develop this construction.
Nothing here uses probability. -/

@[expose] public section

open scoped BigOperators

namespace LPPDifferentiability

/-- Rates of the stationary model: `1 - ρ` on the positive horizontal axis, `ρ` on
the positive vertical axis, and `1` at every other site (the corner and the bulk). -/
noncomputable def stationaryRate (ρ : ℝ) (z : Lattice) : ℝ :=
  if 0 < z.1 ∧ z.2 = 0 then 1 - ρ else if z.1 = 0 ∧ 0 < z.2 then ρ else 1

/-- The stationary environment built from an environment `ω` (the i.i.d. `Exp(1)`
one in the application) by dividing each weight by the rate of its site. It equals `ω` off
the two positive axes. -/
noncomputable def stationaryEnvironment (ρ : ℝ) (ω : Environment) : Environment :=
  fun z => ω z / stationaryRate ρ z

/-- The stationary passage time `G(m, n)`: the inclusive passage time from the origin
to `(m, n)` in the stationary environment. -/
noncomputable def stationaryPassage (ρ : ℝ) (ω : Environment) (m n : ℕ) : ℝ :=
  inclusivePassage (stationaryEnvironment ρ ω) 0 (m, n)

/-- Horizontal increment `I(i + 1, n) = G(i + 1, n) - G(i, n)`. -/
noncomputable def stationaryHorizontalIncrement (ρ : ℝ) (ω : Environment) (i n : ℕ) : ℝ :=
  stationaryPassage ρ ω (i + 1) n - stationaryPassage ρ ω i n

/-- Vertical increment `J(i, n + 1) = G(i, n + 1) - G(i, n)`. -/
noncomputable def stationaryVerticalIncrement (ρ : ℝ) (ω : Environment) (i n : ℕ) : ℝ :=
  stationaryPassage ρ ω i (n + 1) - stationaryPassage ρ ω i n

/-- The stationary environment at a site is the weight divided by the rate. -/
private theorem stationaryEnvironment_apply (ρ : ℝ) (ω : Environment) (z : Lattice) :
    stationaryEnvironment ρ ω z = ω z / stationaryRate ρ z := rfl

/-- The rate is `1` at the corner. -/
private theorem stationaryRate_corner (ρ : ℝ) : stationaryRate ρ (0, 0) = 1 := by
  simp [stationaryRate]

/-- The rate on the positive horizontal axis is `1 - ρ`. -/
private theorem stationaryRate_horizontal (ρ : ℝ) (a : ℤ) (ha : 0 < a) :
    stationaryRate ρ (a, 0) = 1 - ρ := by
  simp [stationaryRate, ha]

/-- The rate on the positive vertical axis is `ρ`. -/
private theorem stationaryRate_vertical (ρ : ℝ) (b : ℤ) (hb : 0 < b) :
    stationaryRate ρ (0, b) = ρ := by
  simp [stationaryRate, hb]

/-- The rate in the bulk is `1`. -/
private theorem stationaryRate_bulk (ρ : ℝ) (a b : ℤ) (ha : 0 < a) (hb : 0 < b) :
    stationaryRate ρ (a, b) = 1 := by
  simp [stationaryRate, ha.ne', hb.ne']

/-- The stationary weight at a bulk site is the original weight. -/
theorem stationaryEnvironment_bulk (ρ : ℝ) (ω : Environment) (a b : ℤ) (ha : 0 < a)
    (hb : 0 < b) : stationaryEnvironment ρ ω (a, b) = ω (a, b) := by
  rw [stationaryEnvironment_apply, stationaryRate_bulk ρ a b ha hb, div_one]

/-- The stationary weight on the positive horizontal axis. -/
private theorem stationaryEnvironment_horizontal (ρ : ℝ) (ω : Environment) (i : ℕ) :
    stationaryEnvironment ρ ω ((i : ℤ) + 1, 0) = ω ((i : ℤ) + 1, 0) / (1 - ρ) := by
  have hi : (0 : ℤ) < (i : ℤ) + 1 := by omega
  rw [stationaryEnvironment_apply, stationaryRate_horizontal ρ ((i : ℤ) + 1) hi]

/-- The stationary weight on the positive vertical axis. -/
private theorem stationaryEnvironment_vertical (ρ : ℝ) (ω : Environment) (n : ℕ) :
    stationaryEnvironment ρ ω (0, (n : ℤ) + 1) = ω (0, (n : ℤ) + 1) / ρ := by
  have hn : (0 : ℤ) < (n : ℤ) + 1 := by omega
  rw [stationaryEnvironment_apply, stationaryRate_vertical ρ ((n : ℤ) + 1) hn]

/-- Corner recursion for `G`: the last vertex before `(i + 1, n + 1)` is `(i, n + 1)` or
`(i + 1, n)`, and the weight at `(i + 1, n + 1)` is the original weight (the bulk rate is
`1`). -/
private theorem stationaryPassage_succ_succ (ρ : ℝ) (ω : Environment) (i n : ℕ) :
    stationaryPassage ρ ω (i + 1) (n + 1) =
      ω ((i : ℤ) + 1, (n : ℤ) + 1) +
        max (stationaryPassage ρ ω i (n + 1)) (stationaryPassage ρ ω (i + 1) n) := by
  have h : lastPassage (stationaryEnvironment ρ ω) 0 (i + 1, n + 1) =
      max (inclusivePassage (stationaryEnvironment ρ ω) 0 (i, n + 1))
        (inclusivePassage (stationaryEnvironment ρ ω) 0 (i + 1, n)) :=
    lastPassage_succ_succ (stationaryEnvironment ρ ω) 0 (i, n)
  have hl : inclusivePassage (stationaryEnvironment ρ ω) 0 (i + 1, n + 1) =
      lastPassage (stationaryEnvironment ρ ω) 0 (i + 1, n + 1) +
        stationaryEnvironment ρ ω
          ((0 : Lattice) + (((i + 1 : ℕ) : ℤ), ((n + 1 : ℕ) : ℤ))) := rfl
  have e : (0 : Lattice) + (((i + 1 : ℕ) : ℤ), ((n + 1 : ℕ) : ℤ)) =
      ((i : ℤ) + 1, (n : ℤ) + 1) := by
    ext <;> simp
  have hi : (0 : ℤ) < (i : ℤ) + 1 := by omega
  have hn : (0 : ℤ) < (n : ℤ) + 1 := by omega
  have hw : stationaryEnvironment ρ ω
      ((0 : Lattice) + (((i + 1 : ℕ) : ℤ), ((n + 1 : ℕ) : ℤ))) =
        ω ((i : ℤ) + 1, (n : ℤ) + 1) := by
    rw [e]
    exact stationaryEnvironment_bulk ρ ω _ _ hi hn
  show inclusivePassage (stationaryEnvironment ρ ω) 0 (i + 1, n + 1) =
    ω ((i : ℤ) + 1, (n : ℤ) + 1) +
      max (inclusivePassage (stationaryEnvironment ρ ω) 0 (i, n + 1))
        (inclusivePassage (stationaryEnvironment ρ ω) 0 (i + 1, n))
  rw [hl, h, hw]
  ring

/-- Real-number identity behind the horizontal cell recursion. -/
private theorem cell_horizontal_arith (a b g c : ℝ) :
    c + max b a - b = c + max (a - g - (b - g)) 0 := by
  rcases le_total a b with h | h
  · have h2 : a - g - (b - g) ≤ 0 := by linarith
    rw [max_eq_left h, max_eq_right h2]
    ring
  · have h2 : 0 ≤ a - g - (b - g) := by linarith
    rw [max_eq_right h, max_eq_left h2]
    ring

/-- Real-number identity behind the vertical cell recursion. -/
private theorem cell_vertical_arith (a b g c : ℝ) :
    c + max b a - a = c + max (b - g - (a - g)) 0 := by
  rcases le_total a b with h | h
  · have h2 : 0 ≤ b - g - (a - g) := by linarith
    rw [max_eq_left h, max_eq_left h2]
    ring
  · have h2 : b - g - (a - g) ≤ 0 := by linarith
    rw [max_eq_right h, max_eq_right h2]
    ring

/-- Cell identity (horizontal output). The horizontal increment one row up is the
bulk weight plus the positive part of the horizontal increment minus the vertical
increment below. This is the one-cell Burke map. -/
theorem stationaryHorizontalIncrement_succ (ρ : ℝ) (ω : Environment) (i n : ℕ) :
    stationaryHorizontalIncrement ρ ω i (n + 1) =
      ω ((i : ℤ) + 1, (n : ℤ) + 1) +
        max (stationaryHorizontalIncrement ρ ω i n - stationaryVerticalIncrement ρ ω i n) 0 := by
  unfold stationaryHorizontalIncrement stationaryVerticalIncrement
  rw [stationaryPassage_succ_succ ρ ω i n]
  exact cell_horizontal_arith (stationaryPassage ρ ω (i + 1) n)
    (stationaryPassage ρ ω i (n + 1)) (stationaryPassage ρ ω i n) _

/-- Cell identity (vertical output). The vertical increment one column to the right
is the bulk weight plus the positive part of the vertical increment minus the horizontal
increment. -/
theorem stationaryVerticalIncrement_succ (ρ : ℝ) (ω : Environment) (i n : ℕ) :
    stationaryVerticalIncrement ρ ω (i + 1) n =
      ω ((i : ℤ) + 1, (n : ℤ) + 1) +
        max (stationaryVerticalIncrement ρ ω i n - stationaryHorizontalIncrement ρ ω i n) 0 := by
  unfold stationaryHorizontalIncrement stationaryVerticalIncrement
  rw [stationaryPassage_succ_succ ρ ω i n]
  exact cell_vertical_arith (stationaryPassage ρ ω (i + 1) n)
    (stationaryPassage ρ ω i (n + 1)) (stationaryPassage ρ ω i n) _

/-- The corner value `G(0, 0)` is the weight at the origin (the rate there is `1`). -/
private theorem stationaryPassage_zero_zero (ρ : ℝ) (ω : Environment) :
    stationaryPassage ρ ω 0 0 = ω 0 := by
  unfold stationaryPassage
  rw [inclusivePassage_horizontal]
  simp [stationaryEnvironment_apply, stationaryRate_corner]
  rfl

/-- Along the horizontal axis, `G(i + 1, 0)` adds the weight of the site `(i + 1, 0)`. -/
private theorem stationaryPassage_succ_zero (ρ : ℝ) (ω : Environment) (i : ℕ) :
    stationaryPassage ρ ω (i + 1) 0 =
      stationaryPassage ρ ω i 0 + stationaryEnvironment ρ ω ((i : ℤ) + 1, 0) := by
  unfold stationaryPassage
  rw [inclusivePassage_horizontal, inclusivePassage_horizontal,
    Fin.sum_univ_castSucc (n := i + 1)]
  simp only [Fin.val_castSucc]
  congr 1
  congr 1
  ext <;> simp

/-- Along the vertical axis, `G(0, n + 1)` adds the weight of the site `(0, n + 1)`. -/
private theorem stationaryPassage_zero_succ (ρ : ℝ) (ω : Environment) (n : ℕ) :
    stationaryPassage ρ ω 0 (n + 1) =
      stationaryPassage ρ ω 0 n + stationaryEnvironment ρ ω (0, (n : ℤ) + 1) := by
  unfold stationaryPassage
  rw [inclusivePassage_vertical, inclusivePassage_vertical,
    Fin.sum_univ_castSucc (n := n + 1)]
  simp only [Fin.val_castSucc]
  congr 1
  congr 1
  ext <;> simp

/-- Boundary increments. On the two axes the increments are the stationary
weights: the weight divided by `1 - ρ` on the horizontal axis and by `ρ` on the vertical
axis. -/
theorem stationaryIncrement_boundary (ρ : ℝ) (ω : Environment) (i n : ℕ) :
    stationaryHorizontalIncrement ρ ω i 0 = ω ((i : ℤ) + 1, 0) / (1 - ρ) ∧
    stationaryVerticalIncrement ρ ω 0 n = ω (0, (n : ℤ) + 1) / ρ := by
  constructor
  · unfold stationaryHorizontalIncrement
    rw [stationaryPassage_succ_zero, stationaryEnvironment_horizontal]
    ring
  · unfold stationaryVerticalIncrement
    rw [stationaryPassage_zero_succ, stationaryEnvironment_vertical]
    ring

/-- The left column: `G(0, n)` is the origin weight plus the `n` stationary weights above
it, each divided by `ρ`. -/
private theorem stationaryPassage_zero_left (ρ : ℝ) (ω : Environment) (n : ℕ) :
    stationaryPassage ρ ω 0 n = ω 0 + ∑ j : Fin n, ω (0, (j.val : ℤ) + 1) / ρ := by
  induction n with
  | zero => simp [stationaryPassage_zero_zero]
  | succ n ih =>
    rw [stationaryPassage_zero_succ, ih, Fin.sum_univ_castSucc, stationaryEnvironment_vertical]
    simp only [Fin.val_castSucc, Fin.val_last]
    ring

/-- Telescoping. `G(m, n)` is the left column plus the horizontal increments of
row `n`. -/
theorem stationaryPassage_eq_column_add_row (ρ : ℝ) (ω : Environment) (m n : ℕ) :
    stationaryPassage ρ ω m n =
      ω 0 + ∑ j : Fin n, ω (0, (j.val : ℤ) + 1) / ρ +
        ∑ i : Fin m, stationaryHorizontalIncrement ρ ω i n := by
  induction m with
  | zero => simp [stationaryPassage_zero_left]
  | succ m ih =>
    have hH : stationaryHorizontalIncrement ρ ω m n =
        stationaryPassage ρ ω (m + 1) n - stationaryPassage ρ ω m n := rfl
    rw [Fin.sum_univ_castSucc (n := m)]
    simp only [Fin.val_castSucc, Fin.val_last]
    rw [hH]
    linarith

/-- Every rate is positive when `0 < ρ < 1`. -/
private theorem stationaryRate_pos {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (z : Lattice) :
    0 < stationaryRate ρ z := by
  unfold stationaryRate
  split_ifs
  · linarith
  · exact hρ0
  · exact one_pos

/-- Comparison. With nonnegative weights the bulk passage time from `(1, 1)` is at
most the stationary passage time: the stationary environment agrees with `ω` on the bulk, a
path from the origin can be prefixed to any path from `(1, 1)`, and the endpoint weight is
nonnegative. -/
theorem lastPassage_le_stationaryPassage {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    {ω : Environment} (hω : ∀ z, 0 ≤ ω z) (m n : ℕ) :
    lastPassage ω (1, 1) (m, n) ≤ stationaryPassage ρ ω (m + 1) (n + 1) := by
  have hnn : ∀ z, 0 ≤ stationaryEnvironment ρ ω z := by
    intro z
    rw [stationaryEnvironment_apply]
    exact div_nonneg (hω z) (stationaryRate_pos hρ0 hρ1 z).le
  have hbulk : Set.EqOn ω (stationaryEnvironment ρ ω)
      (Set.Icc ((1 : ℤ), (1 : ℤ)) (((1 : ℤ), (1 : ℤ)) + ((m : ℤ), (n : ℤ)))) := by
    rintro ⟨a, b⟩ hz
    have ha : (1 : ℤ) ≤ a := hz.1.1
    have hb : (1 : ℤ) ≤ b := hz.1.2
    exact (stationaryEnvironment_bulk ρ ω a b (by omega) (by omega)).symm
  have h1 : lastPassage ω (1, 1) (m, n) = lastPassage (stationaryEnvironment ρ ω) (1, 1) (m, n) :=
    lastPassage_eq_of_eqOn (u := ((1 : ℤ), (1 : ℤ))) (d := (m, n)) hbulk
  have h2 : inclusivePassage (stationaryEnvironment ρ ω) (1, 1) (m, n) ≤
      inclusivePassage (stationaryEnvironment ρ ω) 0 (m + 1, n + 1) := by
    have h := inclusivePassage_le_of_earlier_start hnn (0 : Lattice) ((1, 1) : ℕ × ℕ) (m, n)
    have e1 : (0 : Lattice) + ((((1, 1) : ℕ × ℕ).1 : ℤ), (((1, 1) : ℕ × ℕ).2 : ℤ)) = (1, 1) := by
      ext <;> simp
    have e2 : ((1, 1) : ℕ × ℕ) + (m, n) = (m + 1, n + 1) := by
      ext <;> simp [Nat.add_comm]
    rw [e1, e2] at h
    exact h
  have h3 : lastPassage (stationaryEnvironment ρ ω) (1, 1) (m, n) ≤
      inclusivePassage (stationaryEnvironment ρ ω) (1, 1) (m, n) := by
    unfold inclusivePassage
    exact le_add_of_nonneg_right (hnn _)
  exact h1.le.trans (h3.trans h2)

end LPPDifferentiability
