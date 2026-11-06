/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Martin2004.Model.StationaryColumns
public import Mathlib.MeasureTheory.Constructions.Pi

/-!
# Sweeping a cell map over a row of independent cells

The argument follows Martin (2004), Lemma 4.1, through the stationary comparison of
Seppäläinen (1998), Section 6. It is the sweep step for the stationary column model.

`cellSweep f M` (in `Model/StationaryColumns.lean`) passes a scalar through `M` cells. Cell `k`
receives the entry `a k`, the current scalar and the weight `c k`, and the cell map `f` returns the
new entry and the next scalar.

The main theorem `map_cellSweep` says: suppose the cell map `f` sends the law `E x (nu x E1)` of
(entry, scalar, weight) to `E x nu`, meaning the new entry has law `E` and the new scalar has law
`nu`, independently. Then for `M` cells whose entries are independent with law `E`, whose scalar
has law `nu` and whose weights are independent with law `E1`, the `M` new entries are again
independent with law `E` and independent of the last scalar, which has law `nu`.

The proof repeats the four stages of the exponential row lemma `map_stationaryRowMap`
(`Probability/BurkeRow.lean`), with the hypothesis on `f` in place of the Burke theorem, and with
arbitrary measurable spaces in place of the real line. Induction on `M`: split off the first cell,
apply the hypothesis to it, apply the induction hypothesis to the remaining cells, and put the new
first entry back in front. Every regrouping of a product is a measure preserving bijection.
-/

@[expose] public section

open MeasureTheory

namespace LPPDifferentiability

/-! ## Regrouping products of measures -/

section Regrouping

variable {α β γ δ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
  [MeasurableSpace δ]

/-- Regrouping `x × (y × z)` as `(x × y) × z` preserves the product measure. -/
theorem measurePreserving_sweep_assoc_symm (μ : Measure α) (ν : Measure β)
    (τ : Measure γ) [SFinite ν] [SFinite τ] :
    MeasurePreserving (fun p : α × β × γ => ((p.1, p.2.1), p.2.2))
      (μ.prod (ν.prod τ)) ((μ.prod ν).prod τ) := by
  have h := MeasurePreserving.symm MeasurableEquiv.prodAssoc (measurePreserving_prodAssoc μ ν τ)
  exact h

/-- Exchanging the last two factors of `(x × y) × z` preserves the product measure. -/
theorem measurePreserving_sweep_swap_right (μ : Measure α) (ν : Measure β)
    (τ : Measure γ) [SFinite μ] [SFinite ν] [SFinite τ] :
    MeasurePreserving (fun p : (α × β) × γ => ((p.1.1, p.2), p.1.2))
      ((μ.prod ν).prod τ) ((μ.prod τ).prod ν) := by
  have h1 := measurePreserving_prodAssoc μ ν τ
  have h2 : MeasurePreserving (Prod.map (id : α → α) (Prod.swap : β × γ → γ × β))
      (μ.prod (ν.prod τ)) (μ.prod (τ.prod ν)) :=
    (MeasurePreserving.id μ).prod Measure.measurePreserving_swap
  have h3 := measurePreserving_sweep_assoc_symm μ τ ν
  exact h3.comp (h2.comp h1)

/-- Exchanging the second and third factors of `(x × y) × (z × w)` preserves the product
measure. -/
theorem measurePreserving_sweep_shuffle (μ : Measure α) (ν : Measure β)
    (τ : Measure γ) (σ : Measure δ) [SFinite μ] [SFinite ν] [SFinite τ] [SFinite σ] :
    MeasurePreserving (fun p : (α × β) × γ × δ => ((p.1.1, p.2.1), p.1.2, p.2.2))
      ((μ.prod ν).prod (τ.prod σ)) ((μ.prod τ).prod (ν.prod σ)) := by
  have h1 := measurePreserving_sweep_assoc_symm (μ.prod ν) τ σ
  have h2 : MeasurePreserving
      (Prod.map (fun q : (α × β) × γ => ((q.1.1, q.2), q.1.2)) (id : δ → δ))
      (((μ.prod ν).prod τ).prod σ) (((μ.prod τ).prod ν).prod σ) :=
    (measurePreserving_sweep_swap_right μ ν τ).prod (MeasurePreserving.id σ)
  have h3 := measurePreserving_prodAssoc (μ.prod τ) ν σ
  exact h3.comp (h2.comp h1)

/-- The regrouping `((x, y), (z, w)) ↦ (x, (z, (y, w)))` preserves the product measure. -/
theorem measurePreserving_sweep_regroup (μ : Measure α) (ν : Measure β)
    (τ : Measure γ) (σ : Measure δ) [SFinite μ] [SFinite ν] [SFinite τ] [SFinite σ] :
    MeasurePreserving (fun p : (α × β) × γ × δ => (p.1.1, p.2.1, p.1.2, p.2.2))
      ((μ.prod ν).prod (τ.prod σ)) (μ.prod (τ.prod (ν.prod σ))) := by
  have h := (measurePreserving_prodAssoc μ τ (ν.prod σ)).comp
    (measurePreserving_sweep_shuffle μ ν τ σ)
  exact h

end Regrouping

/-! ## Splitting a product over `Fin (M + 1)` -/

/-- The first entry and the remaining entries of an i.i.d. tuple are independent, with the
original law on the first entry and the i.i.d. law on the tail. -/
theorem measurePreserving_sweep_headTail {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [SigmaFinite μ] (M : ℕ) :
    MeasurePreserving (fun a : Fin (M + 1) → α => (a 0, Fin.tail a))
      (Measure.pi fun _ : Fin (M + 1) => μ) (μ.prod (Measure.pi fun _ : Fin M => μ)) := by
  have h := measurePreserving_piFinSuccAbove (fun _ : Fin (M + 1) => μ) 0
  refine h.congr ((measurable_pi_apply 0).prodMk (measurable_fin_tail M))
    (ae_of_all _ fun a => ?_)
  rfl

/-- Putting an independent entry in front of an i.i.d. tuple gives an i.i.d. tuple. -/
private theorem measurePreserving_sweep_cons {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [SigmaFinite μ] (M : ℕ) :
    MeasurePreserving (fun p : α × (Fin M → α) => (Fin.cons p.1 p.2 : Fin (M + 1) → α))
      (μ.prod (Measure.pi fun _ : Fin M => μ)) (Measure.pi fun _ : Fin (M + 1) => μ) := by
  have hht := measurePreserving_sweep_headTail μ M
  refine ⟨measurable_fin_cons M, ?_⟩
  rw [← hht.map_eq, Measure.map_map (measurable_fin_cons M) hht.measurable]
  have hid : ((fun p : α × (Fin M → α) => (Fin.cons p.1 p.2 : Fin (M + 1) → α)) ∘
      fun a : Fin (M + 1) → α => (a 0, Fin.tail a)) = id :=
    funext fun a => Fin.cons_self_tail a
  rw [hid, Measure.map_id]

/-! ## The four stages of the induction step -/

section Stages

variable {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]

/-- First stage. The first cell `(a 0, b, c 0)` has the product law `E × (ν × E₁)` and is
independent of the tails `(tail a, tail c)`. -/
private theorem measurePreserving_sweep_firstCell (E : Measure α) (ν : Measure β)
    (E₁ : Measure γ) [SigmaFinite E] [SigmaFinite ν] [SigmaFinite E₁] (M : ℕ) :
    MeasurePreserving
      (fun p : (Fin (M + 1) → α) × β × (Fin (M + 1) → γ) =>
        ((p.1 0, p.2.1, p.2.2 0), Fin.tail p.1, Fin.tail p.2.2))
      ((Measure.pi fun _ : Fin (M + 1) => E).prod (ν.prod (Measure.pi fun _ : Fin (M + 1) => E₁)))
      ((E.prod (ν.prod E₁)).prod
        ((Measure.pi fun _ : Fin M => E).prod (Measure.pi fun _ : Fin M => E₁))) := by
  have h1 := (measurePreserving_sweep_headTail E M).prod
    ((MeasurePreserving.id ν).prod (measurePreserving_sweep_headTail E₁ M))
  have h2 := (MeasurePreserving.id (E.prod (Measure.pi fun _ : Fin M => E))).prod
    (measurePreserving_sweep_assoc_symm ν E₁ (Measure.pi fun _ : Fin M => E₁))
  have h3 := measurePreserving_sweep_shuffle E (Measure.pi fun _ : Fin M => E) (ν.prod E₁)
    (Measure.pi fun _ : Fin M => E₁)
  exact h3.comp (h2.comp h1)

/-- Second stage. The cell map on the first cell. By the hypothesis `hlaw`, the two values
leaving the first cell are independent with laws `E` and `ν`, and still independent of the
tails. The result is regrouped as (new entry, (tail of `a`, (new scalar, tail of `c`))). -/
private theorem measurePreserving_sweep_secondStage (E : Measure α) (ν : Measure β)
    (E₁ : Measure γ) [SigmaFinite E] [SigmaFinite ν] [SigmaFinite E₁]
    {f : α × β × γ → α × β} (hf : Measurable f)
    (hlaw : (E.prod (ν.prod E₁)).map f = E.prod ν) (M : ℕ) :
    MeasurePreserving
      (fun q : (α × β × γ) × (Fin M → α) × (Fin M → γ) =>
        ((f q.1).1, q.2.1, (f q.1).2, q.2.2))
      ((E.prod (ν.prod E₁)).prod
        ((Measure.pi fun _ : Fin M => E).prod (Measure.pi fun _ : Fin M => E₁)))
      (E.prod ((Measure.pi fun _ : Fin M => E).prod
        (ν.prod (Measure.pi fun _ : Fin M => E₁)))) := by
  have hcell : MeasurePreserving f (E.prod (ν.prod E₁)) (E.prod ν) := ⟨hf, hlaw⟩
  have h1 := hcell.prod (MeasurePreserving.id ((Measure.pi fun _ : Fin M => E).prod
    (Measure.pi fun _ : Fin M => E₁)))
  have h2 := measurePreserving_sweep_regroup E ν (Measure.pi fun _ : Fin M => E)
    (Measure.pi fun _ : Fin M => E₁)
  exact h2.comp h1

/-- Fourth stage. Consing the new first entry onto the output of the remaining cells and regrouping
gives an i.i.d. tuple of length `M + 1` next to the last scalar. -/
private theorem measurePreserving_sweep_lastStage (E : Measure α) (ν : Measure β)
    [SigmaFinite E] [SigmaFinite ν] (M : ℕ) :
    MeasurePreserving
      (fun q : α × (Fin M → α) × β => ((Fin.cons q.1 q.2.1 : Fin (M + 1) → α), q.2.2))
      (E.prod ((Measure.pi fun _ : Fin M => E).prod ν))
      ((Measure.pi fun _ : Fin (M + 1) => E).prod ν) := by
  have h1 := measurePreserving_sweep_assoc_symm E (Measure.pi fun _ : Fin M => E) ν
  have h2 := (measurePreserving_sweep_cons E M).prod (MeasurePreserving.id ν)
  exact h2.comp h1

end Stages

/-! ## The sweep lemma -/

/-- Sweep lemma. If the measurable cell map `f` sends `E × (ν × E₁)` to `E × ν`, then
sweeping it over `M` cells sends `(pi E) × (ν × pi E₁)` to `(pi E) × ν`: with independent entries
of law `E`, an independent starting scalar of law `ν` and independent weights of law `E₁`, the new
entries are independent with law `E` and independent of the last scalar, which has law `ν`. -/
theorem map_cellSweep {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace γ] (E : Measure α) (ν : Measure β) (E₁ : Measure γ)
    [IsProbabilityMeasure E] [IsProbabilityMeasure ν] [IsProbabilityMeasure E₁]
    {f : α × β × γ → α × β} (hf : Measurable f)
    (hlaw : (E.prod (ν.prod E₁)).map f = E.prod ν) (M : ℕ) :
    ((Measure.pi fun _ : Fin M => E).prod (ν.prod (Measure.pi fun _ : Fin M => E₁))).map
        (fun x => cellSweep f M x.1 x.2.1 x.2.2) =
      (Measure.pi fun _ : Fin M => E).prod ν := by
  induction M with
  | zero =>
    -- no cells: the sweep sends `(a, b, c)` to `(empty tuple, b)`
    have hpiα : (Measure.pi fun _ : Fin 0 => E) =
        Measure.dirac (fun i : Fin 0 => (i.elim0 : α)) :=
      Measure.pi_of_empty _ _
    have hpiγ : (Measure.pi fun _ : Fin 0 => E₁) =
        Measure.dirac (fun i : Fin 0 => (i.elim0 : γ)) :=
      Measure.pi_of_empty _ _
    rw [hpiα, hpiγ]
    have hfst : MeasurePreserving (Prod.fst : β × (Fin 0 → γ) → β)
        (ν.prod (Measure.dirac (fun i : Fin 0 => (i.elim0 : γ)))) ν :=
      measurePreserving_fst
    have hsnd : MeasurePreserving
        (Prod.snd : (Fin 0 → α) × β × (Fin 0 → γ) → β × (Fin 0 → γ))
        ((Measure.dirac (fun i : Fin 0 => (i.elim0 : α))).prod
          (ν.prod (Measure.dirac (fun i : Fin 0 => (i.elim0 : γ)))))
        (ν.prod (Measure.dirac (fun i : Fin 0 => (i.elim0 : γ)))) :=
      measurePreserving_snd
    have hmk : MeasurePreserving (Prod.mk (fun i : Fin 0 => (i.elim0 : α)) : β → (Fin 0 → α) × β)
        ν ((Measure.dirac (fun i : Fin 0 => (i.elim0 : α))).prod ν) :=
      ⟨measurable_prodMk_left, by rw [Measure.dirac_prod]⟩
    exact (hmk.comp (hfst.comp hsnd)).map_eq
  | succ M ih =>
    have h1 := measurePreserving_sweep_firstCell E ν E₁ M
    have h2 := measurePreserving_sweep_secondStage E ν E₁ hf hlaw M
    have hrow : MeasurePreserving
        (fun p : (Fin M → α) × β × (Fin M → γ) => cellSweep f M p.1 p.2.1 p.2.2)
        ((Measure.pi fun _ : Fin M => E).prod (ν.prod (Measure.pi fun _ : Fin M => E₁)))
        ((Measure.pi fun _ : Fin M => E).prod ν) :=
      ⟨measurable_cellSweep hf M, ih⟩
    have h3 := (MeasurePreserving.id E).prod hrow
    have h4 := measurePreserving_sweep_lastStage E ν M
    have hF := h4.comp (h3.comp (h2.comp h1))
    refine (hF.congr (measurable_cellSweep hf (M + 1)) (ae_of_all _ fun p => ?_)).map_eq
    rfl

end LPPDifferentiability
