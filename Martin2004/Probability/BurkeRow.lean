/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Martin2004.Probability.BurkeCell
public import Mathlib.MeasureTheory.Constructions.Pi
import Martin2004.Probability.CellSweep

/-!
# The Burke property along one row of the exponential corner growth model

The row lemma, the second half of the Burke argument behind the exponential shape. Martin (2004)
uses the exponential shape in the proof of Theorem 2.4.

A row of `M` cells is passed from left to right. Cell `i` receives the horizontal increment
`a i`, the vertical increment `v` coming from the cell on its left, and a bulk weight `c i`. It
sends out the horizontal increment `c i + max (a i - v) 0` and the vertical increment
`c i + max (v - a i) 0`. The row map `stationaryRowMap` returns the `M` new horizontal increments
and the last vertical increment.

The main theorem `map_stationaryRowMap` says: if the `M` horizontal inputs are independent
`Exp(1 - ρ)`, the vertical input is an independent `Exp(ρ)` and the `M` bulk weights are
independent `Exp(1)`, then the outputs are again independent, with laws `Exp(1 - ρ)` for the
`M` horizontal values and `Exp(ρ)` for the last vertical value.

Proof (induction on `M`). For `M + 1` cells the first cell
`(a 0, b, c 0)` has the Burke cell law and is independent of the tails `(tail a, tail c)`. By the
pair form of the Burke theorem the two values leaving the first cell are independent
`Exp(1 - ρ)` and `Exp(ρ)`, and still independent of the tails. The vertical value leaving the
first cell, with the tails, is exactly an input of the row of `M` cells, so the induction
hypothesis applies; the horizontal value leaving the first cell is consed onto its output.
Every regrouping of a product is a measure preserving bijection.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace LPPDifferentiability

/-! ## Measurability of the maps involved -/

/-- The Burke map is measurable. -/
theorem measurable_burkeMap : Measurable burkeMap := by
  have hx : Measurable (fun p : ℝ × ℝ × ℝ => p.1) := measurable_fst
  have hy : Measurable (fun p : ℝ × ℝ × ℝ => p.2.1) := measurable_fst.comp measurable_snd
  have hw : Measurable (fun p : ℝ × ℝ × ℝ => p.2.2) := measurable_snd.comp measurable_snd
  show Measurable fun p : ℝ × ℝ × ℝ =>
    (p.2.2 + max (p.1 - p.2.1) 0, p.2.2 + max (p.2.1 - p.1) 0, min p.1 p.2.1)
  exact (hw.add ((hx.sub hy).max measurable_const)).prodMk
    ((hw.add ((hy.sub hx).max measurable_const)).prodMk (hx.min hy))

/-- One row of cells: incoming horizontal increments `a`, incoming
vertical increment `b`, bulk weights `c`; returns the outgoing horizontal
increments and the last vertical increment. -/
noncomputable def stationaryRowMap :
    (M : ℕ) → (Fin M → ℝ) → ℝ → (Fin M → ℝ) → (Fin M → ℝ) × ℝ
  | 0, _, b, _ => (fun i => i.elim0, b)
  | M + 1, a, b, c =>
      let out := stationaryRowMap M (Fin.tail a) (c 0 + max (b - a 0) 0) (Fin.tail c)
      (Fin.cons (c 0 + max (a 0 - b) 0) out.1, out.2)

/-- Dropping the first entry of a tuple is measurable. -/
private theorem measurable_tail (M : ℕ) :
    Measurable (Fin.tail : (Fin (M + 1) → ℝ) → Fin M → ℝ) :=
  measurable_pi_iff.2 fun j => measurable_pi_apply j.succ

/-- Putting a new first entry in front of a tuple is measurable. -/
private theorem measurable_cons (M : ℕ) :
    Measurable fun p : ℝ × (Fin M → ℝ) => (Fin.cons p.1 p.2 : Fin (M + 1) → ℝ) := by
  refine measurable_pi_iff.2 fun i => ?_
  induction i using Fin.cases with
  | zero => simp only [Fin.cons_zero]; exact measurable_fst
  | succ j => simp only [Fin.cons_succ]; exact (measurable_pi_apply j).comp measurable_snd

/-- The row map, as a function of the triple `(a, b, c)`, is measurable. This is needed to
push product measures forward along it. -/
theorem measurable_stationaryRowMap (M : ℕ) :
    Measurable fun p : (Fin M → ℝ) × ℝ × (Fin M → ℝ) => stationaryRowMap M p.1 p.2.1 p.2.2 := by
  induction M with
  | zero => exact measurable_const.prodMk (measurable_fst.comp measurable_snd)
  | succ M ih =>
    have ha0 : Measurable fun p : (Fin (M + 1) → ℝ) × ℝ × (Fin (M + 1) → ℝ) => p.1 0 :=
      (measurable_pi_apply 0).comp measurable_fst
    have hb : Measurable fun p : (Fin (M + 1) → ℝ) × ℝ × (Fin (M + 1) → ℝ) => p.2.1 :=
      measurable_fst.comp measurable_snd
    have hc0 : Measurable fun p : (Fin (M + 1) → ℝ) × ℝ × (Fin (M + 1) → ℝ) => p.2.2 0 :=
      (measurable_pi_apply 0).comp (measurable_snd.comp measurable_snd)
    have hta : Measurable fun p : (Fin (M + 1) → ℝ) × ℝ × (Fin (M + 1) → ℝ) => Fin.tail p.1 :=
      (measurable_tail M).comp measurable_fst
    have htc : Measurable fun p : (Fin (M + 1) → ℝ) × ℝ × (Fin (M + 1) → ℝ) =>
        Fin.tail p.2.2 :=
      (measurable_tail M).comp (measurable_snd.comp measurable_snd)
    have hx : Measurable fun p : (Fin (M + 1) → ℝ) × ℝ × (Fin (M + 1) → ℝ) =>
        p.2.2 0 + max (p.1 0 - p.2.1) 0 :=
      hc0.add ((ha0.sub hb).max measurable_const)
    have hy : Measurable fun p : (Fin (M + 1) → ℝ) × ℝ × (Fin (M + 1) → ℝ) =>
        p.2.2 0 + max (p.2.1 - p.1 0) 0 :=
      hc0.add ((hb.sub ha0).max measurable_const)
    have hR : Measurable fun p : (Fin (M + 1) → ℝ) × ℝ × (Fin (M + 1) → ℝ) =>
        stationaryRowMap M (Fin.tail p.1) (p.2.2 0 + max (p.2.1 - p.1 0) 0) (Fin.tail p.2.2) :=
      ih.comp (hta.prodMk (hy.prodMk htc))
    exact ((measurable_cons M).comp (hx.prodMk (measurable_fst.comp hR))).prodMk
      (measurable_snd.comp hR)

/-! ## Splitting a product over `Fin (M + 1)` -/

/-- The first entry and the remaining entries of an i.i.d. tuple are independent, with the
original law on the first entry and the i.i.d. law on the tail. -/
private theorem measurePreserving_headTail (μ : Measure ℝ) [SigmaFinite μ] (M : ℕ) :
    MeasurePreserving (fun a : Fin (M + 1) → ℝ => (a 0, Fin.tail a))
      (Measure.pi fun _ : Fin (M + 1) => μ) (μ.prod (Measure.pi fun _ : Fin M => μ)) := by
  have h := measurePreserving_piFinSuccAbove (fun _ : Fin (M + 1) => μ) 0
  refine h.congr ((measurable_pi_apply 0).prodMk (measurable_tail M)) (ae_of_all _ fun a => ?_)
  rfl

/-- Putting an independent entry in front of an i.i.d. tuple gives an i.i.d. tuple. -/
private theorem measurePreserving_cons (μ : Measure ℝ) [SigmaFinite μ] (M : ℕ) :
    MeasurePreserving (fun p : ℝ × (Fin M → ℝ) => (Fin.cons p.1 p.2 : Fin (M + 1) → ℝ))
      (μ.prod (Measure.pi fun _ : Fin M => μ)) (Measure.pi fun _ : Fin (M + 1) => μ) := by
  have hht := measurePreserving_headTail μ M
  refine ⟨measurable_cons M, ?_⟩
  rw [← hht.map_eq, Measure.map_map (measurable_cons M) hht.measurable]
  have hid : ((fun p : ℝ × (Fin M → ℝ) => (Fin.cons p.1 p.2 : Fin (M + 1) → ℝ)) ∘
      fun a : Fin (M + 1) → ℝ => (a 0, Fin.tail a)) = id :=
    funext fun a => Fin.cons_self_tail a
  rw [hid, Measure.map_id]

/-! ## The four stages of the induction step -/

/-- First stage. The first cell `(a 0, b, c 0)` has the Burke cell law and is independent of the
tails `(tail a, tail c)`. -/
private theorem measurePreserving_firstCell (E ν E1 : Measure ℝ) [SigmaFinite E]
    [SigmaFinite ν] [SigmaFinite E1] (M : ℕ) :
    MeasurePreserving
      (fun p : (Fin (M + 1) → ℝ) × ℝ × (Fin (M + 1) → ℝ) =>
        ((p.1 0, p.2.1, p.2.2 0), Fin.tail p.1, Fin.tail p.2.2))
      ((Measure.pi fun _ : Fin (M + 1) => E).prod (ν.prod (Measure.pi fun _ : Fin (M + 1) => E1)))
      ((E.prod (ν.prod E1)).prod
        ((Measure.pi fun _ : Fin M => E).prod (Measure.pi fun _ : Fin M => E1))) := by
  have h1 := (measurePreserving_headTail E M).prod
    ((MeasurePreserving.id ν).prod (measurePreserving_headTail E1 M))
  have h2 := (MeasurePreserving.id (E.prod (Measure.pi fun _ : Fin M => E))).prod
    (measurePreserving_sweep_assoc_symm ν E1 (Measure.pi fun _ : Fin M => E1))
  have h3 := measurePreserving_sweep_shuffle E (Measure.pi fun _ : Fin M => E) (ν.prod E1)
    (Measure.pi fun _ : Fin M => E1)
  exact h3.comp (h2.comp h1)

/-- Second stage. The Burke pair map on the first cell. The two values leaving it are independent
`Exp(1 - ρ)` and `Exp(ρ)`, and independent of the tails. The result is regrouped as
(new horizontal value, (tail of `a`, (new vertical value, tail of `c`))). -/
private theorem measurePreserving_secondStage {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (M : ℕ) :
    MeasurePreserving
      (fun q : (ℝ × ℝ × ℝ) × (Fin M → ℝ) × (Fin M → ℝ) =>
        ((burkeMap q.1).1, q.2.1, (burkeMap q.1).2.1, q.2.2))
      ((burkeLaw ρ).prod
        ((Measure.pi fun _ : Fin M => expMeasure (1 - ρ)).prod
          (Measure.pi fun _ : Fin M => expMeasure 1)))
      ((expMeasure (1 - ρ)).prod
        ((Measure.pi fun _ : Fin M => expMeasure (1 - ρ)).prod
          ((expMeasure ρ).prod (Measure.pi fun _ : Fin M => expMeasure 1)))) := by
  have : SFinite (burkeLaw ρ) :=
    inferInstanceAs (SFinite ((expMeasure (1 - ρ)).prod ((expMeasure ρ).prod (expMeasure 1))))
  have hpair : MeasurePreserving (fun p : ℝ × ℝ × ℝ => ((burkeMap p).1, (burkeMap p).2.1))
      (burkeLaw ρ) ((expMeasure (1 - ρ)).prod (expMeasure ρ)) :=
    ⟨(measurable_fst.comp measurable_burkeMap).prodMk
        ((measurable_fst.comp measurable_snd).comp measurable_burkeMap),
      map_burkePair_burkeLaw hρ0 hρ1⟩
  have h1 := hpair.prod (MeasurePreserving.id ((Measure.pi fun _ : Fin M => expMeasure (1 - ρ)).prod
    (Measure.pi fun _ : Fin M => expMeasure 1)))
  have h2 := measurePreserving_sweep_regroup (expMeasure (1 - ρ)) (expMeasure ρ)
    (Measure.pi fun _ : Fin M => expMeasure (1 - ρ)) (Measure.pi fun _ : Fin M => expMeasure 1)
  exact h2.comp h1

/-- Fourth stage. Consing the new first horizontal value onto the output of the remaining row and
regrouping gives an i.i.d. tuple of length `M + 1` next to the last vertical value. -/
private theorem measurePreserving_lastStage (E ν : Measure ℝ) [SigmaFinite E] [SigmaFinite ν]
    (M : ℕ) :
    MeasurePreserving
      (fun q : ℝ × (Fin M → ℝ) × ℝ => ((Fin.cons q.1 q.2.1 : Fin (M + 1) → ℝ), q.2.2))
      (E.prod ((Measure.pi fun _ : Fin M => E).prod ν))
      ((Measure.pi fun _ : Fin (M + 1) => E).prod ν) := by
  have h1 := measurePreserving_sweep_assoc_symm E (Measure.pi fun _ : Fin M => E) ν
  have h2 := (measurePreserving_cons E M).prod (MeasurePreserving.id ν)
  exact h2.comp h1

/-! ## The row lemma -/

/-- The row lemma. With i.i.d. Exp(1 - rho) inputs `a`, an independent
Exp(rho) input `b` and i.i.d. Exp(1) bulk weights, the outputs are i.i.d.
Exp(1 - rho) together with an independent Exp(rho). -/
theorem map_stationaryRowMap {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (M : ℕ) :
    (((Measure.pi fun _ : Fin M => expMeasure (1 - ρ)).prod
        ((expMeasure ρ).prod (Measure.pi fun _ : Fin M => expMeasure 1))).map
      (fun p => stationaryRowMap M p.1 p.2.1 p.2.2)) =
      (Measure.pi fun _ : Fin M => expMeasure (1 - ρ)).prod (expMeasure ρ) := by
  induction M with
  | zero =>
    -- no cells: the row map sends `(a, b, c)` to `(empty tuple, b)`
    have hpi : ∀ μ : Measure ℝ, (Measure.pi fun _ : Fin 0 => μ) =
        Measure.dirac (fun i : Fin 0 => (i.elim0 : ℝ)) :=
      fun μ => Measure.pi_of_empty _ _
    rw [hpi (expMeasure (1 - ρ)), hpi (expMeasure 1)]
    have hfst : MeasurePreserving (Prod.fst : ℝ × (Fin 0 → ℝ) → ℝ)
        ((expMeasure ρ).prod (Measure.dirac (fun i : Fin 0 => (i.elim0 : ℝ)))) (expMeasure ρ) :=
      measurePreserving_fst
    have hsnd : MeasurePreserving
        (Prod.snd : (Fin 0 → ℝ) × ℝ × (Fin 0 → ℝ) → ℝ × (Fin 0 → ℝ))
        ((Measure.dirac (fun i : Fin 0 => (i.elim0 : ℝ))).prod
          ((expMeasure ρ).prod (Measure.dirac (fun i : Fin 0 => (i.elim0 : ℝ)))))
        ((expMeasure ρ).prod (Measure.dirac (fun i : Fin 0 => (i.elim0 : ℝ)))) :=
      measurePreserving_snd
    have hmk : MeasurePreserving (Prod.mk (fun i : Fin 0 => (i.elim0 : ℝ)) : ℝ → (Fin 0 → ℝ) × ℝ)
        (expMeasure ρ) ((Measure.dirac (fun i : Fin 0 => (i.elim0 : ℝ))).prod (expMeasure ρ)) :=
      ⟨measurable_prodMk_left, by rw [Measure.dirac_prod]⟩
    exact (hmk.comp (hfst.comp hsnd)).map_eq
  | succ M ih =>
    have h1 := measurePreserving_firstCell (expMeasure (1 - ρ)) (expMeasure ρ) (expMeasure 1) M
    have h2 := measurePreserving_secondStage hρ0 hρ1 M
    have hrow : MeasurePreserving
        (fun p : (Fin M → ℝ) × ℝ × (Fin M → ℝ) => stationaryRowMap M p.1 p.2.1 p.2.2)
        ((Measure.pi fun _ : Fin M => expMeasure (1 - ρ)).prod
          ((expMeasure ρ).prod (Measure.pi fun _ : Fin M => expMeasure 1)))
        ((Measure.pi fun _ : Fin M => expMeasure (1 - ρ)).prod (expMeasure ρ)) :=
      ⟨measurable_stationaryRowMap M, ih⟩
    have h3 := (MeasurePreserving.id (expMeasure (1 - ρ))).prod hrow
    have h4 := measurePreserving_lastStage (expMeasure (1 - ρ)) (expMeasure ρ) M
    have hF := h4.comp (h3.comp (h2.comp h1))
    refine (hF.congr (measurable_stationaryRowMap (M + 1)) (ae_of_all _ fun p => ?_)).map_eq
    rfl

end LPPDifferentiability
