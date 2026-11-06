/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Martin2004.Model.ColumnPassage
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.Order.Interval.Finset.Fin

@[expose] public section

/-!
# Deterministic stationary-column comparison

Martin (2004), Lemma 4.1, gives an expected one-site-per-column passage-time bound. This file
supplies the stationary-column recursion and deterministic comparison used by this formalization;
its one-cell conservation identity is proved here. It contains no probability.

The model sweeps the columns from left to right and each column from bottom to top. A cell receives
the vertical increment `J` of the column on its left, the horizontal increment `I` coming from
below, and the site weight `w`. It returns the vertical increment `max (J + w - I) 0` of the new
column and the horizontal increment `max (I - J) w` passed upward (`columnBurkeCell`). The
stationary passage time is the sum of the bottom increments and the final vertical increments
(`stationaryColumnPassage`).

The main result is `columnPassage_le_stationaryColumnPassage`: if the left boundary increments are
nonnegative, then `columnPassage` is at most the stationary passage time, whatever the weights and
the bottom increments are. Its proof uses only one-cell conservation
(`columnBurkeCell_conservation`) and induction on the columns.

Measurability of the final increments is included (`measurable_stationaryColumns`), so that later
modules can integrate against product laws.
-/

open MeasureTheory

namespace LPPDifferentiability

/-- One cell of the stationary column model. Input `(J, I, w)`: the vertical increment `J` of the
column on the left, the horizontal increment `I` entering from below, and the cell weight `w`.
Output `(J', I')`: `J' = max (J + w - I) 0` is the vertical increment of the new column and
`I' = max (I - J) w` the horizontal increment leaving at the top. -/
noncomputable def columnBurkeCell (x : ℝ × ℝ × ℝ) : ℝ × ℝ :=
  (max (x.1 + x.2.2 - x.2.1) 0, max (x.2.1 - x.1) x.2.2)

/-- Conservation in one cell: `J' + I = J + I'` (both equal `max I (J + w)`).
This conservation identity is used by the stationary-column comparison developed in this file. -/
theorem columnBurkeCell_conservation (x : ℝ × ℝ × ℝ) :
    (columnBurkeCell x).1 + x.2.1 = x.1 + (columnBurkeCell x).2 := by
  obtain ⟨J, I, w⟩ := x
  simp only [columnBurkeCell]
  rw [max_def, max_def]
  split_ifs <;> linarith

/-- Pass a scalar through `M` cells in order. Cell `k` receives the entry `a k`, the current scalar
and the weight `c k`, and returns a new entry and the next scalar. The result is the `M` new
entries and the last scalar. -/
noncomputable def cellSweep {α β γ : Type*} (f : α × β × γ → α × β) :
    (M : ℕ) → (Fin M → α) → β → (Fin M → γ) → (Fin M → α) × β
  | 0, _, b, _ => (fun i : Fin 0 => i.elim0, b)
  | M + 1, a, b, c =>
      let x := f (a 0, b, c 0)
      let out := cellSweep f M (Fin.tail a) x.2 (Fin.tail c)
      (Fin.cons x.1 out.1, out.2)

/-- A sweep through no cells returns no entries and leaves the scalar unchanged. -/
theorem cellSweep_zero {α β γ : Type*} (f : α × β × γ → α × β) (a : Fin 0 → α) (b : β)
    (c : Fin 0 → γ) : cellSweep f 0 a b c = (fun i : Fin 0 => i.elim0, b) :=
  rfl

/-- A sweep through `M + 1` cells: the first cell acts, and its scalar output starts the sweep
through the remaining `M` cells. -/
theorem cellSweep_succ {α β γ : Type*} (f : α × β × γ → α × β) (M : ℕ) (a : Fin (M + 1) → α)
    (b : β) (c : Fin (M + 1) → γ) :
    cellSweep f (M + 1) a b c =
      (Fin.cons (f (a 0, b, c 0)).1
          (cellSweep f M (Fin.tail a) (f (a 0, b, c 0)).2 (Fin.tail c)).1,
        (cellSweep f M (Fin.tail a) (f (a 0, b, c 0)).2 (Fin.tail c)).2) :=
  rfl

/-- The vertical increments of the stationary model after `m` columns. `I i` is the horizontal
increment entering column `i` from below, `J` the vertical increments of the left boundary, and
`W i j` the weight of site `(i, j)`. Columns are swept from left to right. -/
noncomputable def stationaryColumns (n : ℕ) :
    (m : ℕ) → (Fin m → ℝ) → (Fin (n + 1) → ℝ) → (Fin m → Fin (n + 1) → ℝ) → Fin (n + 1) → ℝ
  | 0, _, J, _ => J
  | m + 1, I, J, W =>
      stationaryColumns n m (Fin.tail I) (cellSweep columnBurkeCell (n + 1) J (I 0) (W 0)).1
        (Fin.tail W)

/-- With no columns the vertical increments are those of the left boundary. -/
theorem stationaryColumns_zero (n : ℕ) (I : Fin 0 → ℝ) (J : Fin (n + 1) → ℝ)
    (W : Fin 0 → Fin (n + 1) → ℝ) : stationaryColumns n 0 I J W = J :=
  rfl

/-- With `m + 1` columns: sweep the first column, then continue with the remaining `m` columns,
whose left boundary is the output of that sweep. -/
theorem stationaryColumns_succ (n m : ℕ) (I : Fin (m + 1) → ℝ) (J : Fin (n + 1) → ℝ)
    (W : Fin (m + 1) → Fin (n + 1) → ℝ) :
    stationaryColumns n (m + 1) I J W =
      stationaryColumns n m (Fin.tail I)
        (cellSweep columnBurkeCell (n + 1) J (I 0) (W 0)).1 (Fin.tail W) :=
  rfl

/-- The stationary passage time to the top of column `m`: the bottom boundary increments plus
the vertical increments of the last column. -/
noncomputable def stationaryColumnPassage (m n : ℕ) (I : Fin m → ℝ) (J : Fin (n + 1) → ℝ)
    (W : Fin m → Fin (n + 1) → ℝ) : ℝ :=
  ∑ i : Fin m, I i + ∑ j : Fin (n + 1), stationaryColumns n m I J W j

/-- New vertical increments are nonnegative (each is a `max` with `0`). -/
theorem cellSweep_columnBurkeCell_fst_nonneg (N : ℕ) (J : Fin N → ℝ) (I : ℝ) (w : Fin N → ℝ)
    (l : Fin N) : 0 ≤ (cellSweep columnBurkeCell N J I w).1 l := by
  induction N generalizing I with
  | zero => exact l.elim0
  | succ N ih =>
    rw [cellSweep_succ]
    induction l using Fin.cases with
    | zero =>
      simp only [Fin.cons_zero, columnBurkeCell]
      exact le_max_right _ _
    | succ l =>
      simp only [Fin.cons_succ]
      exact ih _ _ _ l

/-- A sum over the initial segment up to `0` has one term. -/
private theorem sum_Iic_zero {N : ℕ} (f : Fin (N + 1) → ℝ) :
    ∑ l ∈ Finset.Iic (0 : Fin (N + 1)), f l = f 0 := by
  have h : Finset.Iic (0 : Fin (N + 1)) = {0} := by
    ext l
    simp
  rw [h, Finset.sum_singleton]

/-- A sum over the initial segment up to `k.succ` splits into the term at `0` and a sum over the
initial segment up to `k` of the shifted function. -/
private theorem sum_Iic_succ {N : ℕ} (f : Fin (N + 1) → ℝ) (k : Fin N) :
    ∑ l ∈ Finset.Iic k.succ, f l = f 0 + ∑ l ∈ Finset.Iic k, f l.succ := by
  have h : ∀ {n : ℕ} (g : Fin n → ℝ) (j : Fin n),
      ∑ l ∈ Finset.Iic j, g l = ∑ l, if l ≤ j then g l else 0 := by
    intro n g j
    rw [← Finset.sum_filter]
    congr 1
    ext l
    simp
  rw [h, h, Fin.sum_univ_succ]
  simp [Fin.succ_le_succ_iff]

/-- One column: the stationary height of the new column at height `k`, which is
`I` plus the new increments up to `k`, is at least the old height at `k` plus the weight `w k`. -/
theorem cellSweep_columnBurkeCell_prefix (N : ℕ) (J : Fin N → ℝ) (I : ℝ) (w : Fin N → ℝ)
    (k : Fin N) :
    ∑ l ∈ Finset.Iic k, J l + w k ≤
      I + ∑ l ∈ Finset.Iic k, (cellSweep columnBurkeCell N J I w).1 l := by
  induction N generalizing I with
  | zero => exact k.elim0
  | succ N ih =>
    have hcons := columnBurkeCell_conservation (J 0, I, w 0)
    have hmax : J 0 + w 0 - I ≤ (columnBurkeCell (J 0, I, w 0)).1 := le_max_left _ _
    rw [cellSweep_succ]
    induction k using Fin.cases with
    | zero =>
      simp only [sum_Iic_zero, Fin.cons_zero]
      linarith
    | succ k =>
      have hrec := ih (Fin.tail J) (columnBurkeCell (J 0, I, w 0)).2 (Fin.tail w) k
      simp only [sum_Iic_succ, Fin.cons_zero, Fin.cons_succ]
      simp only [Fin.tail] at hrec
      dsimp only at hcons
      linarith

/-- The generalized induction behind the comparison. For every nondecreasing
height sequence `y` and every height `k` not above any `y i`, the left boundary up to `k` plus the
weights along `y` is at most the stationary passage time. The left boundary must be nonnegative;
no sign condition on `I` or `W` is needed. -/
private theorem prefix_add_sum_le_stationaryColumnPassage (n : ℕ) :
    ∀ (m : ℕ) (I : Fin m → ℝ) (J : Fin (n + 1) → ℝ), (∀ j, 0 ≤ J j) →
      ∀ (W : Fin m → Fin (n + 1) → ℝ) (y : Fin m → Fin (n + 1)), Monotone y →
      ∀ k : Fin (n + 1), (∀ i, k ≤ y i) →
        ∑ l ∈ Finset.Iic k, J l + ∑ i, W i (y i) ≤
          ∑ i, I i + ∑ j, stationaryColumns n m I J W j := by
  intro m
  induction m with
  | zero =>
    intro I J hJ W y _ k _
    simp only [Finset.univ_eq_empty, Finset.sum_empty, add_zero, zero_add,
      stationaryColumns_zero]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun j _ _ => hJ j
  | succ m ih =>
    intro I J hJ W y hy k hk
    have hnn := cellSweep_columnBurkeCell_fst_nonneg (n + 1) J (I 0) (W 0)
    have hcol := cellSweep_columnBurkeCell_prefix (n + 1) J (I 0) (W 0) (y 0)
    have hmono : ∑ l ∈ Finset.Iic k, J l ≤ ∑ l ∈ Finset.Iic (y 0), J l :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.Iic_subset_Iic.mpr (hk 0))
        fun j _ _ => hJ j
    have hrec : ∑ l ∈ Finset.Iic (y 0),
          (cellSweep columnBurkeCell (n + 1) J (I 0) (W 0)).1 l +
        ∑ i : Fin m, W i.succ (y i.succ) ≤
        ∑ i : Fin m, I i.succ + ∑ j,
          stationaryColumns n m (Fin.tail I)
            (cellSweep columnBurkeCell (n + 1) J (I 0) (W 0)).1 (Fin.tail W) j :=
      ih (Fin.tail I) _ hnn (Fin.tail W) (fun i => y i.succ)
        (fun a b hab => hy (Fin.succ_le_succ_iff.mpr hab)) (y 0)
        fun i => hy (Fin.zero_le _)
    rw [Fin.sum_univ_succ (fun i => W i (y i)), Fin.sum_univ_succ I, stationaryColumns_succ]
    linarith

/-- Comparison: with a nonnegative left boundary, the column passage time is at
most the stationary passage time built on the same weights. No sign condition on the weights or
on the bottom boundary is needed. This is the deterministic half of the domination used for
Martin (2004), Lemma 4.1. -/
theorem columnPassage_le_stationaryColumnPassage (ω : Environment) (m n : ℕ)
    (I : Fin m → ℝ) {J : Fin (n + 1) → ℝ} (hJ : ∀ j, 0 ≤ J j) :
    columnPassage ω m n ≤
      stationaryColumnPassage m n I J (fun i j => ω (((i : ℕ) : ℤ), ((j : ℕ) : ℤ))) := by
  refine columnPassage_le_of_forall fun y hy => ?_
  have h := prefix_add_sum_le_stationaryColumnPassage n m I J hJ
    (fun i j => ω (((i : ℕ) : ℤ), ((j : ℕ) : ℤ))) y hy 0 fun i => Fin.zero_le _
  have h0 : 0 ≤ ∑ l ∈ Finset.Iic (0 : Fin (n + 1)), J l :=
    Finset.sum_nonneg fun j _ => hJ j
  unfold stationaryColumnPassage
  linarith

/-- Dropping the first coordinate of a tuple is measurable. -/
theorem measurable_fin_tail {α : Type*} [MeasurableSpace α] (M : ℕ) :
    Measurable (Fin.tail : (Fin (M + 1) → α) → Fin M → α) :=
  measurable_pi_iff.mpr fun i => measurable_pi_apply i.succ

/-- Adding a first coordinate to a tuple is measurable. -/
theorem measurable_fin_cons {α : Type*} [MeasurableSpace α] (M : ℕ) :
    Measurable fun p : α × (Fin M → α) => (Fin.cons p.1 p.2 : Fin (M + 1) → α) := by
  refine measurable_pi_iff.mpr fun i => ?_
  induction i using Fin.cases with
  | zero => simpa using measurable_fst
  | succ i =>
    simp only [Fin.cons_succ]
    exact (measurable_pi_apply i).comp measurable_snd

/-- Sweeping a measurable cell map over `M` cells is measurable in the entries, the starting
scalar and the weights. -/
theorem measurable_cellSweep {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace γ] {f : α × β × γ → α × β} (hf : Measurable f) (M : ℕ) :
    Measurable fun x : (Fin M → α) × β × (Fin M → γ) => cellSweep f M x.1 x.2.1 x.2.2 := by
  induction M with
  | zero => exact measurable_const.prodMk (measurable_fst.comp measurable_snd)
  | succ M ih =>
    have hcell : Measurable fun x : (Fin (M + 1) → α) × β × (Fin (M + 1) → γ) =>
        f (x.1 0, x.2.1, x.2.2 0) :=
      hf.comp (((measurable_pi_apply 0).comp measurable_fst).prodMk
        ((measurable_fst.comp measurable_snd).prodMk
          ((measurable_pi_apply 0).comp (measurable_snd.comp measurable_snd))))
    have hout : Measurable fun x : (Fin (M + 1) → α) × β × (Fin (M + 1) → γ) =>
        cellSweep f M (Fin.tail x.1) (f (x.1 0, x.2.1, x.2.2 0)).2 (Fin.tail x.2.2) :=
      ih.comp (((measurable_fin_tail M).comp measurable_fst).prodMk
        (hcell.snd.prodMk ((measurable_fin_tail M).comp (measurable_snd.comp measurable_snd))))
    exact ((measurable_fin_cons M).comp (hcell.fst.prodMk hout.fst)).prodMk hout.snd

/-- The final vertical increments are a measurable function of the inputs. This is bookkeeping, not
a step of Martin's text: it lets later modules integrate against product laws. -/
theorem measurable_stationaryColumns (m n : ℕ) :
    Measurable fun x : (Fin m → ℝ) × (Fin (n + 1) → ℝ) × (Fin m → Fin (n + 1) → ℝ) =>
      stationaryColumns n m x.1 x.2.1 x.2.2 := by
  have hcell : Measurable columnBurkeCell := by
    unfold columnBurkeCell
    fun_prop
  induction m with
  | zero => exact measurable_fst.comp measurable_snd
  | succ m ih =>
    have hin : Measurable fun x : (Fin (m + 1) → ℝ) × (Fin (n + 1) → ℝ) ×
        (Fin (m + 1) → Fin (n + 1) → ℝ) => (x.2.1, x.1 0, x.2.2 0) := by
      fun_prop
    have hsweep : Measurable fun x : (Fin (m + 1) → ℝ) × (Fin (n + 1) → ℝ) ×
        (Fin (m + 1) → Fin (n + 1) → ℝ) =>
        (cellSweep columnBurkeCell (n + 1) x.2.1 (x.1 0) (x.2.2 0)).1 :=
      ((measurable_cellSweep hcell (n + 1)).comp hin).fst
    have hg : Measurable fun x : (Fin (m + 1) → ℝ) × (Fin (n + 1) → ℝ) ×
        (Fin (m + 1) → Fin (n + 1) → ℝ) =>
        (Fin.tail x.1, (cellSweep columnBurkeCell (n + 1) x.2.1 (x.1 0) (x.2.2 0)).1,
          Fin.tail x.2.2) :=
      ((measurable_fin_tail m).comp measurable_fst).prodMk
        (hsweep.prodMk ((measurable_fin_tail m).comp (measurable_snd.comp measurable_snd)))
    simp only [stationaryColumns_succ]
    exact ih.comp hg

end LPPDifferentiability
