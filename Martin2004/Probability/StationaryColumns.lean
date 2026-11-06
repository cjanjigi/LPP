/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Martin2004.Probability.CellSweep
public import Martin2004.Probability.ColumnBurkeCell
public import Martin2004.Probability.ColumnLaws

@[expose] public section

/-!
# The stationary column model: stationarity and mean

This file defines the stationary column model and proves its stationarity and mean identities. The
input laws and the relation among their parameters are stated with the theorems below.

The stationary column model (`Model/StationaryColumns.lean`) sweeps `m` columns of `n + 1` cells.
Column `i` starts with the bottom increment `I i`; the left boundary column has vertical increments
`J`; the cell weights are `W i j`. This module puts a law on these inputs and proves two facts.

* `stationaryColumnLaw p ρ θ m n`: the bottom increments are independent `Ber(ρ)`, the left
  column is independent `Geom(θ)` (`P(k) = (1 - θ) θ ^ k`), the weights are independent `Ber(p)`,
  and the three groups are independent.
* `map_stationaryColumns`: if `ρ θ (1 - p) = p (1 - ρ)` and `θ < 1`, the vertical
  increments after `m` columns are again independent `Geom(θ)`. The proof is an induction over the
  columns. One column is one sweep of the Burke cell (`map_cellSweep` with `map_columnBurkeCell`),
  and the discarded top scalar is independent of the new column.
* `integrable_and_integral_stationaryColumnPassage`: the stationary passage time is
  integrable with mean `m ρ + (n + 1) θ / (1 - θ)`, by linearity and the previous law.
-/

open MeasureTheory ProbabilityTheory unitInterval

namespace LPPDifferentiability

/-- The law of the inputs of the stationary column model for `m` columns of `n + 1` cells, in the
order (bottom increments `I`, left column `J`, weights `W`): the bottom increments are
independent `Ber(ρ)`, the left column is independent `Geom(θ)` and the weights are independent
`Ber(p)`, with the three groups independent. -/
noncomputable def stationaryColumnLaw (p ρ θ : unitInterval) (m n : ℕ) :
    Measure ((Fin m → ℝ) × (Fin (n + 1) → ℝ) × (Fin m → Fin (n + 1) → ℝ)) :=
  (Measure.pi fun _ : Fin m => bernoulliMeasure (1 : ℝ) 0 ρ).prod
    ((Measure.pi fun _ : Fin (n + 1) => geometricCountLaw θ).prod
      (Measure.pi fun _ : Fin m => Measure.pi fun _ : Fin (n + 1) => bernoulliMeasure (1 : ℝ) 0 p))

/-- Unfolding lemma for `stationaryColumnLaw`. -/
theorem stationaryColumnLaw_def (p ρ θ : unitInterval) (m n : ℕ) :
    stationaryColumnLaw p ρ θ m n =
      (Measure.pi fun _ : Fin m => bernoulliMeasure (1 : ℝ) 0 ρ).prod
        ((Measure.pi fun _ : Fin (n + 1) => geometricCountLaw θ).prod
          (Measure.pi fun _ : Fin m =>
            Measure.pi fun _ : Fin (n + 1) => bernoulliMeasure (1 : ℝ) 0 p)) :=
  rfl

/-- The law of the inputs is a probability measure. -/
instance isProbabilityMeasure_stationaryColumnLaw (p ρ θ : unitInterval) (m n : ℕ) :
    IsProbabilityMeasure (stationaryColumnLaw p ρ θ m n) := by
  unfold stationaryColumnLaw
  infer_instance

/-! ## Regrouping products of measures -/

section Regrouping

variable {α β γ δ ε : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
  [MeasurableSpace δ] [MeasurableSpace ε]

/-- Exchanging the first two factors of `x × (y × z)` gives `y × (x × z)` and preserves the
product measure. -/
private theorem measurePreserving_columns_swap_inner (ν : Measure β) (τ : Measure γ)
    (κ : Measure δ) [SFinite ν] [SFinite τ] [SFinite κ] :
    MeasurePreserving (fun p : β × γ × δ => (p.2.1, p.1, p.2.2))
      (ν.prod (τ.prod κ)) (τ.prod (ν.prod κ)) := by
  have h1 := measurePreserving_sweep_assoc_symm ν τ κ
  have h2 : MeasurePreserving (Prod.map (Prod.swap : β × γ → γ × β) (id : δ → δ))
      ((ν.prod τ).prod κ) ((τ.prod ν).prod κ) :=
    Measure.measurePreserving_swap.prod (MeasurePreserving.id κ)
  have h3 := measurePreserving_prodAssoc τ ν κ
  exact h3.comp (h2.comp h1)

/-- The regrouping `((a, b), (c, (d, e))) ↦ ((c, (a, d)), (b, e))` preserves the product
measure. -/
private theorem measurePreserving_columns_regroup (A : Measure α) (B : Measure β) (C : Measure γ)
    (D : Measure δ) (E : Measure ε) [SFinite A] [SFinite B] [SFinite C] [SFinite D] [SFinite E] :
    MeasurePreserving
      (fun q : (α × β) × γ × δ × ε => ((q.2.1, q.1.1, q.2.2.1), q.1.2, q.2.2.2))
      ((A.prod B).prod (C.prod (D.prod E))) ((C.prod (A.prod D)).prod (B.prod E)) := by
  have s1 := measurePreserving_sweep_shuffle A B C (D.prod E)
  have s2 : MeasurePreserving
      (Prod.map (id : α × γ → α × γ) (fun p : β × δ × ε => (p.2.1, p.1, p.2.2)))
      ((A.prod C).prod (B.prod (D.prod E))) ((A.prod C).prod (D.prod (B.prod E))) :=
    (MeasurePreserving.id (A.prod C)).prod (measurePreserving_columns_swap_inner B D E)
  have s3 := measurePreserving_sweep_shuffle A C D (B.prod E)
  have s4 := measurePreserving_sweep_assoc_symm (A.prod D) C (B.prod E)
  have s5 : MeasurePreserving
      (Prod.map (Prod.swap : (α × δ) × γ → γ × α × δ) (id : β × ε → β × ε))
      (((A.prod D).prod C).prod (B.prod E)) ((C.prod (A.prod D)).prod (B.prod E)) :=
    Measure.measurePreserving_swap.prod (MeasurePreserving.id (B.prod E))
  exact s5.comp (s4.comp (s3.comp (s2.comp s1)))

/-- Forgetting the second coordinate of the first factor, and regrouping, sends
`((g, e), (a, b))` to `(a, (g, b))` and preserves the product measure when `E` is a probability
measure. -/
private theorem measurePreserving_columns_drop (G : Measure α) (E : Measure β) (A : Measure γ)
    (B : Measure δ) [SFinite G] [IsProbabilityMeasure E] [SFinite A] [SFinite B] :
    MeasurePreserving (fun q : (α × β) × γ × δ => (q.2.1, q.1.1, q.2.2))
      ((G.prod E).prod (A.prod B)) (A.prod (G.prod B)) := by
  have d1 : MeasurePreserving (Prod.map (Prod.fst : α × β → α) (id : γ × δ → γ × δ))
      ((G.prod E).prod (A.prod B)) (G.prod (A.prod B)) :=
    measurePreserving_fst.prod (MeasurePreserving.id (A.prod B))
  have d2 := measurePreserving_sweep_assoc_symm G A B
  have d3 : MeasurePreserving (Prod.map (Prod.swap : α × γ → γ × α) (id : δ → δ))
      ((G.prod A).prod B) ((A.prod G).prod B) :=
    Measure.measurePreserving_swap.prod (MeasurePreserving.id B)
  have d4 := measurePreserving_prodAssoc A G B
  exact d4.comp (d3.comp (d2.comp d1))

end Regrouping

/-! ## One column of the stationary model -/

/-- Splitting off the first column: the inputs `(I, J, W)` for `m + 1` columns become the first
bottom increment and first weight column next to the left column, `(J, (I 0, W 0))`, and the
independent remaining inputs `(tail I, tail W)`. -/
private theorem measurePreserving_columns_split {α β γ : Type*} [MeasurableSpace α]
    [MeasurableSpace β] [MeasurableSpace γ] (E : Measure α) (G : Measure β) (Λ : Measure γ)
    [SigmaFinite E] [SigmaFinite G] [SigmaFinite Λ] (m : ℕ) :
    MeasurePreserving
      (fun x : (Fin (m + 1) → α) × β × (Fin (m + 1) → γ) =>
        ((x.2.1, x.1 0, x.2.2 0), Fin.tail x.1, Fin.tail x.2.2))
      ((Measure.pi fun _ : Fin (m + 1) => E).prod (G.prod (Measure.pi fun _ : Fin (m + 1) => Λ)))
      ((G.prod (E.prod Λ)).prod
        ((Measure.pi fun _ : Fin m => E).prod (Measure.pi fun _ : Fin m => Λ))) := by
  have h1 := (measurePreserving_sweep_headTail E m).prod
    ((MeasurePreserving.id G).prod (measurePreserving_sweep_headTail Λ m))
  have h2 := measurePreserving_columns_regroup E (Measure.pi fun _ : Fin m => E) G Λ
    (Measure.pi fun _ : Fin m => Λ)
  exact h2.comp h1

/-- **One column preserves the stationary law.** Sweeping the first column through the Burke cell
and discarding the top increment sends the input law for `m + 1` columns to the input law for `m`
columns: the new left column is again `Geom(θ)` and independent of the remaining inputs. -/
private theorem measurePreserving_stationaryColumns_step {p ρ θ : unitInterval}
    (hθ : (θ : ℝ) < 1) (hrel : (ρ : ℝ) * θ * (1 - p) = p * (1 - ρ)) (m n : ℕ) :
    MeasurePreserving
      (fun x : (Fin (m + 1) → ℝ) × (Fin (n + 1) → ℝ) × (Fin (m + 1) → Fin (n + 1) → ℝ) =>
        (Fin.tail x.1, (cellSweep columnBurkeCell (n + 1) x.2.1 (x.1 0) (x.2.2 0)).1,
          Fin.tail x.2.2))
      (stationaryColumnLaw p ρ θ (m + 1) n) (stationaryColumnLaw p ρ θ m n) := by
  unfold stationaryColumnLaw
  -- stage 1: split off the first column
  have h1 := measurePreserving_columns_split (bernoulliMeasure (1 : ℝ) 0 ρ)
    (Measure.pi fun _ : Fin (n + 1) => geometricCountLaw θ)
    (Measure.pi fun _ : Fin (n + 1) => bernoulliMeasure (1 : ℝ) 0 p) m
  -- stage 2: sweep the first column (the Burke cell preserves `Geom ⊗ Ber`)
  have hsweep : MeasurePreserving
      (fun y : (Fin (n + 1) → ℝ) × ℝ × (Fin (n + 1) → ℝ) =>
        cellSweep columnBurkeCell (n + 1) y.1 y.2.1 y.2.2)
      ((Measure.pi fun _ : Fin (n + 1) => geometricCountLaw θ).prod
        ((bernoulliMeasure (1 : ℝ) 0 ρ).prod
          (Measure.pi fun _ : Fin (n + 1) => bernoulliMeasure (1 : ℝ) 0 p)))
      ((Measure.pi fun _ : Fin (n + 1) => geometricCountLaw θ).prod
        (bernoulliMeasure (1 : ℝ) 0 ρ)) :=
    ⟨measurable_cellSweep measurable_columnBurkeCell (n + 1),
      map_cellSweep (geometricCountLaw θ) (bernoulliMeasure (1 : ℝ) 0 ρ)
        (bernoulliMeasure (1 : ℝ) 0 p) measurable_columnBurkeCell (map_columnBurkeCell hθ hrel)
        (n + 1)⟩
  have h2 := hsweep.prod (MeasurePreserving.id
    ((Measure.pi fun _ : Fin m => bernoulliMeasure (1 : ℝ) 0 ρ).prod
      (Measure.pi fun _ : Fin m =>
        Measure.pi fun _ : Fin (n + 1) => bernoulliMeasure (1 : ℝ) 0 p)))
  -- stage 3: discard the independent top increment
  have h3 := measurePreserving_columns_drop (Measure.pi fun _ : Fin (n + 1) => geometricCountLaw θ)
    (bernoulliMeasure (1 : ℝ) 0 ρ) (Measure.pi fun _ : Fin m => bernoulliMeasure (1 : ℝ) 0 ρ)
    (Measure.pi fun _ : Fin m =>
      Measure.pi fun _ : Fin (n + 1) => bernoulliMeasure (1 : ℝ) 0 p)
  exact h3.comp (h2.comp h1)

/-! ## Stationarity -/

/-- **Stationarity.** Let the bottom increments be independent `Ber(ρ)`, the left column
independent `Geom(θ)` and the weights independent `Ber(p)`, all independent, with
`ρ θ (1 - p) = p (1 - ρ)` and `θ < 1`. Then after `m` columns the vertical increments of the
stationary column model are again independent `Geom(θ)`. -/
theorem map_stationaryColumns {p ρ θ : unitInterval} (hθ : (θ : ℝ) < 1)
    (hrel : (ρ : ℝ) * θ * (1 - p) = p * (1 - ρ)) (m n : ℕ) :
    (stationaryColumnLaw p ρ θ m n).map (fun x => stationaryColumns n m x.1 x.2.1 x.2.2) =
      Measure.pi fun _ : Fin (n + 1) => geometricCountLaw θ := by
  induction m with
  | zero =>
    -- no columns: the output is the left boundary
    have hsnd : MeasurePreserving
        (Prod.snd : (Fin 0 → ℝ) × (Fin (n + 1) → ℝ) × (Fin 0 → Fin (n + 1) → ℝ) →
          (Fin (n + 1) → ℝ) × (Fin 0 → Fin (n + 1) → ℝ))
        (stationaryColumnLaw p ρ θ 0 n)
        ((Measure.pi fun _ : Fin (n + 1) => geometricCountLaw θ).prod
          (Measure.pi fun _ : Fin 0 =>
            Measure.pi fun _ : Fin (n + 1) => bernoulliMeasure (1 : ℝ) 0 p)) := by
      unfold stationaryColumnLaw
      exact measurePreserving_snd
    have hfst : MeasurePreserving
        (Prod.fst : (Fin (n + 1) → ℝ) × (Fin 0 → Fin (n + 1) → ℝ) → Fin (n + 1) → ℝ)
        ((Measure.pi fun _ : Fin (n + 1) => geometricCountLaw θ).prod
          (Measure.pi fun _ : Fin 0 =>
            Measure.pi fun _ : Fin (n + 1) => bernoulliMeasure (1 : ℝ) 0 p))
        (Measure.pi fun _ : Fin (n + 1) => geometricCountLaw θ) :=
      measurePreserving_fst
    exact (hfst.comp hsnd).map_eq
  | succ m ih =>
    have hG : MeasurePreserving
        (fun x : (Fin m → ℝ) × (Fin (n + 1) → ℝ) × (Fin m → Fin (n + 1) → ℝ) =>
          stationaryColumns n m x.1 x.2.1 x.2.2)
        (stationaryColumnLaw p ρ θ m n) (Measure.pi fun _ : Fin (n + 1) => geometricCountLaw θ) :=
      ⟨measurable_stationaryColumns m n, ih⟩
    exact (hG.comp (measurePreserving_stationaryColumns_step hθ hrel m n)).map_eq

/-! ## Mean -/

/-- Integrability of the identity transfers along a measure preserving map into the real line. -/
private theorem integrable_of_measurePreserving_id {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {ν : Measure ℝ} {f : α → ℝ} (hf : MeasurePreserving f μ ν)
    (hν : Integrable (fun t : ℝ => t) ν) : Integrable f μ :=
  hf.integrable_comp_of_integrable hν

/-- The integral of a function with a given law on the real line is the mean of that law. -/
private theorem integral_eq_of_measurePreserving_id {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {ν : Measure ℝ} {f : α → ℝ} (hf : MeasurePreserving f μ ν) :
    ∫ x, f x ∂μ = ∫ t : ℝ, t ∂ν := by
  rw [← hf.map_eq]
  exact (integral_map hf.measurable.aemeasurable (f := fun t : ℝ => t)
    measurable_id'.aestronglyMeasurable).symm

/-- **Mean of the stationary passage time.** Under the Burke relation
`ρ θ (1 - p) = p (1 - ρ)` with `θ < 1`, the stationary passage time of `m` columns of `n + 1`
cells is integrable and has mean `m ρ + (n + 1) θ / (1 - θ)`: each of the `m` bottom increments has
mean `ρ`, and each of the `n + 1` final vertical increments has mean `θ / (1 - θ)` by
`map_stationaryColumns`. -/
theorem integrable_and_integral_stationaryColumnPassage {p ρ θ : unitInterval}
    (hθ : (θ : ℝ) < 1) (hrel : (ρ : ℝ) * θ * (1 - p) = p * (1 - ρ)) (m n : ℕ) :
    Integrable (fun x => stationaryColumnPassage m n x.1 x.2.1 x.2.2)
        (stationaryColumnLaw p ρ θ m n) ∧
      ∫ x, stationaryColumnPassage m n x.1 x.2.1 x.2.2 ∂stationaryColumnLaw p ρ θ m n =
        (m : ℝ) * ρ + ((n : ℝ) + 1) * ((θ : ℝ) / (1 - θ)) := by
  -- each bottom increment has law `Ber(ρ)`
  have hfst : MeasurePreserving
      (Prod.fst : (Fin m → ℝ) × (Fin (n + 1) → ℝ) × (Fin m → Fin (n + 1) → ℝ) → Fin m → ℝ)
      (stationaryColumnLaw p ρ θ m n) (Measure.pi fun _ : Fin m => bernoulliMeasure (1 : ℝ) 0 ρ) := by
    unfold stationaryColumnLaw
    exact measurePreserving_fst
  have hI : ∀ i : Fin m, MeasurePreserving
      (fun x : (Fin m → ℝ) × (Fin (n + 1) → ℝ) × (Fin m → Fin (n + 1) → ℝ) => x.1 i)
      (stationaryColumnLaw p ρ θ m n) (bernoulliMeasure (1 : ℝ) 0 ρ) := fun i =>
    (measurePreserving_eval (fun _ : Fin m => bernoulliMeasure (1 : ℝ) 0 ρ) i).comp hfst
  have hIint : ∀ i : Fin m, ∫ x, x.1 i ∂stationaryColumnLaw p ρ θ m n = (ρ : ℝ) := fun i => by
    rw [integral_eq_of_measurePreserving_id (hI i),
      integral_bernoulliMeasure (1 : ℝ) 0 ρ (fun t : ℝ => t)]
    simp
  have hIi : ∀ i : Fin m,
      Integrable (fun x : (Fin m → ℝ) × (Fin (n + 1) → ℝ) × (Fin m → Fin (n + 1) → ℝ) => x.1 i)
        (stationaryColumnLaw p ρ θ m n) := fun i =>
    integrable_of_measurePreserving_id (hI i)
      (integrable_bernoulliMeasure (1 : ℝ) 0 ρ (fun t : ℝ => t))
  -- each final vertical increment has law `Geom(θ)`, by stationarity
  have hGmp : MeasurePreserving
      (fun x : (Fin m → ℝ) × (Fin (n + 1) → ℝ) × (Fin m → Fin (n + 1) → ℝ) =>
        stationaryColumns n m x.1 x.2.1 x.2.2)
      (stationaryColumnLaw p ρ θ m n) (Measure.pi fun _ : Fin (n + 1) => geometricCountLaw θ) :=
    ⟨measurable_stationaryColumns m n, map_stationaryColumns hθ hrel m n⟩
  have hG : ∀ j : Fin (n + 1), MeasurePreserving
      (fun x : (Fin m → ℝ) × (Fin (n + 1) → ℝ) × (Fin m → Fin (n + 1) → ℝ) =>
        stationaryColumns n m x.1 x.2.1 x.2.2 j)
      (stationaryColumnLaw p ρ θ m n) (geometricCountLaw θ) := fun j =>
    (measurePreserving_eval (fun _ : Fin (n + 1) => geometricCountLaw θ) j).comp hGmp
  have hGint : ∀ j : Fin (n + 1),
      ∫ x, stationaryColumns n m x.1 x.2.1 x.2.2 j ∂stationaryColumnLaw p ρ θ m n =
        (θ : ℝ) / (1 - θ) := fun j => by
    rw [integral_eq_of_measurePreserving_id (hG j)]
    exact (integrable_and_integral_id_geometricCountLaw hθ).2
  have hGi : ∀ j : Fin (n + 1),
      Integrable
        (fun x : (Fin m → ℝ) × (Fin (n + 1) → ℝ) × (Fin m → Fin (n + 1) → ℝ) =>
          stationaryColumns n m x.1 x.2.1 x.2.2 j) (stationaryColumnLaw p ρ θ m n) := fun j =>
    integrable_of_measurePreserving_id (hG j)
      (integrable_and_integral_id_geometricCountLaw hθ).1
  -- linearity
  have hfun : ∀ x : (Fin m → ℝ) × (Fin (n + 1) → ℝ) × (Fin m → Fin (n + 1) → ℝ),
      stationaryColumnPassage m n x.1 x.2.1 x.2.2 =
        (∑ i : Fin m, x.1 i) + ∑ j : Fin (n + 1), stationaryColumns n m x.1 x.2.1 x.2.2 j :=
    fun _ => rfl
  have hsumI : Integrable (fun x : (Fin m → ℝ) × (Fin (n + 1) → ℝ) × (Fin m → Fin (n + 1) → ℝ) =>
      ∑ i : Fin m, x.1 i) (stationaryColumnLaw p ρ θ m n) :=
    integrable_finsetSum _ fun i _ => hIi i
  have hsumG : Integrable (fun x : (Fin m → ℝ) × (Fin (n + 1) → ℝ) × (Fin m → Fin (n + 1) → ℝ) =>
      ∑ j : Fin (n + 1), stationaryColumns n m x.1 x.2.1 x.2.2 j)
      (stationaryColumnLaw p ρ θ m n) :=
    integrable_finsetSum _ fun j _ => hGi j
  have hmeanI : ∫ x, ∑ i : Fin m, x.1 i ∂stationaryColumnLaw p ρ θ m n = (m : ℝ) * ρ := by
    rw [integral_finsetSum _ fun i _ => hIi i]
    simp [hIint]
  have hmeanG : ∫ x, ∑ j : Fin (n + 1), stationaryColumns n m x.1 x.2.1 x.2.2 j
      ∂stationaryColumnLaw p ρ θ m n = ((n : ℝ) + 1) * ((θ : ℝ) / (1 - θ)) := by
    rw [integral_finsetSum _ fun j _ => hGi j]
    simp [hGint]
  simp only [hfun]
  exact ⟨hsumI.add hsumG, by rw [integral_add hsumI hsumG, hmeanI, hmeanG]⟩

end LPPDifferentiability
