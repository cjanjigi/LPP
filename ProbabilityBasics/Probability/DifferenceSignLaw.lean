/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Mathlib.Probability.Independence.Basic
public import Mathlib.Probability.IdentDistrib
public import Mathlib.MeasureTheory.Constructions.Pi

/-!
# Deterministic sign changes of independent-copy differences

A finite independent family may have different laws at its different coordinates.
Its two independent copies give a product of coordinate-pair laws. Swapping any
chosen pairs preserves that whole law and negates exactly the chosen differences.
No centering, moment, or identical-marginal hypothesis is needed.
-/

public section

open MeasureTheory ProbabilityTheory

namespace LPPDifferentiability

/-- The full original finite vector has the product of its actual marginal laws. -/
theorem map_independent_finite_vector {ι Ω : Type*} [Fintype ι] [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (Z : ι → Ω → ℝ)
    (hZ : ∀ i, Measurable (Z i)) (hInd : iIndepFun Z P) :
    P.map (fun ω i => Z i ω) = Measure.pi (fun i => P.map (Z i)) :=
  hInd.map_fun_eq_pi_map (fun i => (hZ i).aemeasurable)

/-- Rearranging the two actual vector copies gives the full product of pair laws. -/
theorem map_independent_copy_pairs {ι Ω : Type*} [Fintype ι] [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (Z : ι → Ω → ℝ)
    (hZ : ∀ i, Measurable (Z i)) (hInd : iIndepFun Z P) :
    (P.prod P).map (fun ω i => (Z i ω.1, Z i ω.2)) =
      Measure.pi (fun i => (P.map (Z i)).prod (P.map (Z i))) := by
  let V : Ω → ι → ℝ := fun ω i => Z i ω
  have hV : Measurable V := measurable_pi_iff.mpr hZ
  have hVL : P.map V = Measure.pi (fun i => P.map (Z i)) :=
    map_independent_finite_vector P Z hZ hInd
  have : ∀ i, IsFiniteMeasure (P.map (Z i)) :=
    fun i => Measure.isFiniteMeasure_map P (Z i)
  let e := MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ ι
  have he := measurePreserving_arrowProdEquivProdArrow ℝ ℝ ι
    (fun i => P.map (Z i)) (fun i => P.map (Z i))
  have hcopies : (P.prod P).map (Prod.map V V) =
      (Measure.pi (fun i => P.map (Z i))).prod
        (Measure.pi (fun i => P.map (Z i))) := by
    rw [← Measure.map_prod_map P P hV hV, hVL]
  calc
    _ = ((P.prod P).map (Prod.map V V)).map e.symm :=
      (Measure.map_map e.symm.measurable (hV.prodMap hV)).symm
    _ = _ := by
      rw [hcopies]
      exact (he.symm e).map_eq

/-- Subtraction after a literal pair swap is multiplication by the chosen sign. -/
theorem difference_pair_swap (b : Bool) (x : ℝ × ℝ) :
    (if b then x else x.swap).1 - (if b then x else x.swap).2 =
      (if b then (1 : ℝ) else -1) * (x.1 - x.2) := by
  cases b
  · simp only [Bool.false_eq_true, ite_false, Prod.fst_swap, Prod.snd_swap, neg_one_mul,
      neg_sub]
  · simp only [ite_true, one_mul]

/-- Independent coordinate pairs permit arbitrary deterministic swaps simultaneously. -/
theorem measurePreserving_pi_pair_swap {ι : Type*} [Fintype ι]
    (ν : ι → Measure ℝ) [∀ i, IsFiniteMeasure (ν i)] (ε : ι → Bool) :
    MeasurePreserving
      (fun x : ι → ℝ × ℝ => fun i => if ε i then x i else (x i).swap)
      (Measure.pi (fun i => (ν i).prod (ν i)))
      (Measure.pi (fun i => (ν i).prod (ν i))) := by
  refine measurePreserving_pi (fun i => (ν i).prod (ν i))
    (fun i => (ν i).prod (ν i))
    (f := fun (i : ι) (x : ℝ × ℝ) => if ε i then x else x.swap) ?_
  intro i
  cases h : ε i
  · simpa only [h, Bool.false_eq_true, ite_false] using
      (Measure.measurePreserving_swap : MeasurePreserving Prod.swap ((ν i).prod (ν i))
        ((ν i).prod (ν i)))
  · simp only [ite_true]
    exact ⟨measurable_id, Measure.map_id⟩

/-- The whole vector of independent-copy differences is unchanged in law by any
fixed choice of coordinate signs. Original coordinates need not have equal laws. -/
theorem map_independent_copy_difference_sign {ι Ω : Type*} [Fintype ι]
    [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ι → Ω → ℝ) (hZ : ∀ i, Measurable (Z i)) (hInd : iIndepFun Z P)
    (ε : ι → Bool) :
    (P.prod P).map (fun ω i => Z i ω.1 - Z i ω.2) =
      (P.prod P).map
        (fun ω i => (if ε i then (1 : ℝ) else -1) * (Z i ω.1 - Z i ω.2)) := by
  let Q := Measure.pi (fun i => (P.map (Z i)).prod (P.map (Z i)))
  let F : Ω × Ω → ι → ℝ × ℝ := fun ω i => (Z i ω.1, Z i ω.2)
  let D : (ι → ℝ × ℝ) → ι → ℝ := fun x i => (x i).1 - (x i).2
  let S : (ι → ℝ × ℝ) → ι → ℝ × ℝ :=
    fun x i => if ε i then x i else (x i).swap
  have hF : Measurable F := measurable_pi_iff.mpr fun i =>
    ((hZ i).comp measurable_fst).prodMk ((hZ i).comp measurable_snd)
  have hD : Measurable D := measurable_pi_iff.mpr fun i =>
    (measurable_fst.comp (measurable_pi_apply i)).sub
      (measurable_snd.comp (measurable_pi_apply i))
  have hFL : (P.prod P).map F = Q := map_independent_copy_pairs P Z hZ hInd
  have : ∀ i, IsFiniteMeasure (P.map (Z i)) :=
    fun i => Measure.isFiniteMeasure_map P (Z i)
  have hS : MeasurePreserving S Q Q :=
    measurePreserving_pi_pair_swap (fun i => P.map (Z i)) ε
  have hidentity : (D ∘ S) ∘ F =
      (fun ω i => (if ε i then (1 : ℝ) else -1) * (Z i ω.1 - Z i ω.2)) := by
    funext ω i
    exact difference_pair_swap (ε i) (F ω i)
  calc
    _ = Q.map D := by rw [← hFL, Measure.map_map hD hF]; rfl
    _ = (Q.map S).map D := by rw [hS.map_eq]
    _ = ((P.prod P).map F).map (D ∘ S) := by
      rw [hFL, Measure.map_map hD hS.measurable]
    _ = _ := by
      rw [Measure.map_map (hD.comp hS.measurable) hF, hidentity]

/-- Identical distribution of the actual full finite vectors, for measurable
composition by downstream consumers. -/
theorem identDistrib_independent_copy_difference_sign {ι Ω : Type*} [Fintype ι]
    [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ι → Ω → ℝ) (hZ : ∀ i, Measurable (Z i)) (hInd : iIndepFun Z P)
    (ε : ι → Bool) :
    IdentDistrib (fun ω : Ω × Ω => fun i => Z i ω.1 - Z i ω.2)
      (fun ω : Ω × Ω => fun i =>
        (if ε i then (1 : ℝ) else -1) * (Z i ω.1 - Z i ω.2))
      (P.prod P) (P.prod P) where
  aemeasurable_fst := (measurable_pi_iff.mpr fun i =>
    ((hZ i).comp measurable_fst).sub ((hZ i).comp measurable_snd)).aemeasurable
  aemeasurable_snd := (measurable_pi_iff.mpr fun i =>
    measurable_const.mul
      (((hZ i).comp measurable_fst).sub ((hZ i).comp measurable_snd))).aemeasurable
  map_eq := map_independent_copy_difference_sign P Z hZ hInd ε

end LPPDifferentiability
