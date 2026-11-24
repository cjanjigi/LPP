/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, and Timo Seppäläinen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Differentiability.FinalDraft.SelectedGridPaths.Streams
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions
public import Mathlib.MeasureTheory.MeasurableSpace.Instances
import Differentiability.Model.StaircaseFamilyIndex
import Mathlib.Data.Nat.Find

/-! # Measurability of the streams used by the selected grid paths -/

public section

open MeasureTheory Set
open scoped Classical

namespace LPPDifferentiability.SelectedGridPaths

open StairGeometry

local notation "Mask" => Lattice → Bool

/-- Countable tests of the mask can be imposed simultaneously. This is used
for the path selection in Appendix B, item U5 of the final draft. -/
theorem measurableSet_mask_forall {ι : Type*} [Countable ι] {p : ι → Mask → Prop}
    (hp : ∀ i, MeasurableSet {b | p i b}) :
    MeasurableSet {b | ∀ i, p i b} := by
  rw [show {b | ∀ i, p i b} = ⋂ i, {b | p i b} by ext b; exact mem_iInter.symm]
  exact MeasurableSet.iInter hp

/-- At a fixed path index the geometric eligibility test is independent of the mask. -/
theorem measurableSet_mask_imp {p : Prop} {s : Mask → Prop}
    (hs : MeasurableSet {b | s b}) : MeasurableSet {b | p → s b} := by
  by_cases hp : p
  · simpa only [hp, true_implies] using hs
  · simp only [hp, false_implies, Set.ofPred_true, MeasurableSet.univ]

private theorem measurableSet_mask_value (z : Lattice) (v : Bool) :
    MeasurableSet {b : Mask | b z = v} :=
  show MeasurableSet ((fun b : Mask => b z) ⁻¹' {v}) from
    (measurable_pi_apply z) (measurableSet_singleton v)

private theorem measurableSet_forwardTrapped_at (z : Lattice) :
    MeasurableSet {b : Mask | z ∈ forwardTrapped (maskEnvironment b) 0} := by
  simpa only [forwardTrapped, mem_ofPred_eq, reachSet, neg_zero, maskEnvironment_nonneg_iff]
    using measurableSet_reach_finite z

private theorem measurableSet_backwardBlocked_at (z : Lattice) :
    MeasurableSet {b : Mask | z ∈ backwardBlocked (maskEnvironment b) 0} := by
  have hneg (b : Mask) : maskEnvironment b z < 0 ↔ b z = true := by
    cases hz : b z <;> simp [maskEnvironment, hz]
  have hb : MeasurableSet {b : Mask | (reachBackSet (maskEnvironment b) 0 z).Finite} := by
    simpa only [reachBackSet, neg_zero, maskEnvironment_nonneg_iff] using measurableSet_reachBack_finite z
  rw [show {b : Mask | z ∈ backwardBlocked (maskEnvironment b) 0} =
      {b : Mask | b z = true} ∪ {b : Mask | (reachBackSet (maskEnvironment b) 0 z).Finite} by
    ext b
    simp only [backwardBlocked, neg_zero, hneg, mem_ofPred_eq, mem_union]]
  exact (measurableSet_mask_value z true).union hb

/-- Testing a mask-dependent site in a mask-dependent event uses the
countable partition by its lattice value (Appendix B, item U5). -/
theorem measurableSet_mask_at_site {x : Mask → Lattice} (hx : Measurable x)
    {p : Lattice → Mask → Prop} (hp : ∀ z, MeasurableSet {b | p z b}) :
    MeasurableSet {b | p (x b) b} := by
  rw [show {b | p (x b) b} = ⋃ z : Lattice, {b | x b = z} ∩ {b | p z b} by
    ext b
    simp only [mem_ofPred_eq, mem_iUnion, mem_inter_iff]
    exact ⟨fun h => ⟨x b, rfl, h⟩, by rintro ⟨z, rfl, h⟩; exact h⟩]
  exact MeasurableSet.iUnion fun z => (hx (measurableSet_singleton z)).inter (hp z)

/-- The test for a nontrapped vertex is measurable even when the vertex is
chosen from the mask (Appendix B, item U5). -/
theorem measurableSet_not_trapped_at_site {x : Mask → Lattice} (hx : Measurable x) :
    MeasurableSet {b | x b ∉ forwardTrapped (maskEnvironment b) 0} :=
  measurableSet_mask_at_site hx (fun z => (measurableSet_forwardTrapped_at z).compl)

/-- Evaluating the mask at a measurable selected site is a measurable test
(Appendix B, item U5). -/
theorem measurableSet_mask_false_at_site {x : Mask → Lattice} (hx : Measurable x) :
    MeasurableSet {b : Mask | b (x b) = false} :=
  measurableSet_mask_at_site hx (fun z => measurableSet_mask_value z false)

private theorem measurable_forwardStream (a : ℝ) (u : Lattice) (n : ℕ) :
    Measurable (fun b : Mask => forwardStream b a u n) :=
  measurable_greedy_vertex u a (fun b => forwardTrapped (maskEnvironment b) 0)
    measurableSet_forwardTrapped_at n

private theorem measurable_backwardStream (a : ℝ) (u : Lattice) (n : ℕ) :
    Measurable (fun b : Mask => backwardStream b a u n) :=
  (Measurable.of_discrete (f := fun x : Lattice => -x)).comp
    (measurable_greedy_vertex (-u) a (fun b => {z | -z ∈ backwardBlocked (maskEnvironment b) 0})
      (fun z => measurableSet_backwardBlocked_at (-z)) n)

/-- Each indexed vertex of the staircase through a fixed site is measurable
in the whole mask (Appendix B, items U1 and U5). -/
theorem measurable_gammaPoint (a : ℝ) (u : Lattice) (I : ℤ) :
    Measurable (fun b : Mask => gammaPoint b a u I) := by
  rcases le_total (lev u) I with h | h
  · simpa only [gammaPoint_eq_forward _ _ _ _ h] using
      measurable_forwardStream a u (I - lev u).toNat
  · simpa only [gammaPoint_eq_backward _ _ _ _ h] using
      measurable_backwardStream a u (lev u - I).toNat

/-- Each vertex of a staircase segment is measurable in the mask
(Appendix B, items U1 and U5). -/
theorem measurable_gammaStream (a : ℝ) (u : Lattice) (I : ℤ) (n : ℕ) :
    Measurable (fun b : Mask => gammaStream b a u I n) :=
  measurable_gammaPoint a u (I + (n : ℤ))

/-- Coverage of a level by the selected staircase is a measurable condition
on the mask (Appendix B, items U1 and U5). -/
theorem measurableSet_gammaDefined (Q : Set Lattice) (a : ℝ) (u : Lattice) (I : ℤ) :
    MeasurableSet {b : Mask | gammaDefined Q b a u I} := by
  have hQ : MeasurableSet Q := (Set.to_countable Q).measurableSet
  have hF : MeasurableSet {b : Mask | ∀ s ≤ (I - lev u).toNat, forwardStream b a u s ∈ Q} :=
    measurableSet_mask_forall fun s => measurableSet_mask_imp ((measurable_forwardStream a u s) hQ)
  have hB : MeasurableSet {b : Mask | ∀ s ≤ (lev u - I).toNat, backwardStream b a u s ∈ Q} :=
    measurableSet_mask_forall fun s => measurableSet_mask_imp ((measurable_backwardStream a u s) hQ)
  change MeasurableSet
    (({b : Mask | lev u ≤ I} ∩ ({b : Mask | u ∈ forwardTrapped (maskEnvironment b) 0}ᶜ ∩
      {b : Mask | ∀ s ≤ (I - lev u).toNat, forwardStream b a u s ∈ Q})) ∪
     ({b : Mask | I ≤ lev u} ∩ ({b : Mask | u ∈ backwardBlocked (maskEnvironment b) 0}ᶜ ∩
      {b : Mask | ∀ s ≤ (lev u - I).toNat, backwardStream b a u s ∈ Q})))
  exact ((MeasurableSet.const _).inter ((measurableSet_forwardTrapped_at u).compl.inter hF)).union
    ((MeasurableSet.const _).inter ((measurableSet_backwardBlocked_at u).compl.inter hB))

/-- Measurability of the test that the prescribed arrival box is free of very
bad sites (Appendix B, items U3 and U5). -/
theorem measurableSet_mask_boxFree (L : ℕ) (v : Lattice) :
    MeasurableSet {b : Mask | boxFree (maskEnvironment b) 0 L v} := by
  unfold boxFree
  simp only [neg_zero, maskEnvironment_nonneg_iff]
  exact measurableSet_mask_forall fun z =>
    measurableSet_mask_imp (measurableSet_mask_imp (measurableSet_mask_imp
      (measurableSet_mask_imp (measurableSet_mask_value z false))))

private theorem measurable_arrivalStream (L : ℕ) (z v : Lattice) (s : ℕ) :
    Measurable (fun b : Mask => arrivalStream b L z v s) := by
  let n := (lev v - lev z).toNat
  let q : ℝ := ((v.1 - z.1 : ℤ) : ℝ) / n
  by_cases hs : s ≤ n - L
  · simpa only [arrivalStream, ite_eq_left hs, n, q] using measurable_forwardStream q z s
  · let f (p : Lattice) :=
      p + (Int.ofNat (min (s - (n - L)) ((v.1 - p.1).toNat)),
        Int.ofNat (s - (n - L) - (v.1 - p.1).toNat))
    have h : Measurable (fun b : Mask => f (forwardStream b q z (n - L))) :=
      (Measurable.of_discrete (f := f)).comp (measurable_forwardStream q z (n - L))
    simpa only [arrivalStream, ite_eq_right hs, f, q, n] using h

/-- Arrival vertices are measurable when the starting staircase point is
selected from the same mask (Appendix B, items U4 and U5). -/
theorem measurable_arrivalStream_at {x : Mask → Lattice} (hx : Measurable x)
    (L : ℕ) (v : Lattice) (s : ℕ) :
    Measurable (fun b : Mask => arrivalStream b L (x b) v s) := by
  intro A hA
  exact measurableSet_mask_at_site hx (fun z => measurable_arrivalStream L z v s hA)

/-- Each vertex of the stream from the trimmed crossing end is measurable
(Appendix B, items U4 and U5). -/
theorem measurable_mergeStream (a : ℝ) (Δ₀ : ℕ) (u v : Lattice) (Λ : ℤ) (s : ℕ) :
    Measurable (fun b : Mask => mergeStream b a Δ₀ u v Λ s) :=
  measurable_forwardStream _ _ _

/-- The event that the two streams first meet at the indicated index is
measurable in the actual mask (Appendix B, items U4 and U5). -/
theorem measurableSet_firstMeeting_eq_some (Q : Set Lattice) (a : ℝ) (Δ₀ : ℕ)
    (u v : Lattice) (Λ : ℤ) (i : ℕ) :
    MeasurableSet {b : Mask | firstMeeting Q b a Δ₀ u v Λ = some i} := by
  let eligible (b : Mask) (s : ℕ) := s ≤ (Λ - lev v).toNat ∧
    gammaDefined Q b a u (lev v + (s : ℤ)) ∧
      mergeStream b a Δ₀ u v Λ s = gammaStream b a u (lev v) s
  have htest (s : ℕ) : MeasurableSet {b : Mask | eligible b s} :=
    (MeasurableSet.const _).inter ((measurableSet_gammaDefined Q a u (lev v + (s : ℤ))).inter
      (measurableSet_eq_fun (measurable_mergeStream a Δ₀ u v Λ s)
        (measurable_gammaStream a u (lev v) s)))
  have heq : {b : Mask | firstMeeting Q b a Δ₀ u v Λ = some i} =
      {b : Mask | eligible b i ∧ ∀ s < i, ¬ eligible b s} := by
    ext b
    change (if h : ∃ s, eligible b s then some (Nat.find h) else none) = some i ↔
      eligible b i ∧ ∀ s < i, ¬ eligible b s
    by_cases h : ∃ s, eligible b s
    · rw [dite_eq_left h, Option.some.injEq, Nat.find_eq_iff h]
    · simp only [dite_eq_right h, reduceCtorEq, false_iff]
      exact fun hh => h ⟨i, hh.1⟩
  rw [heq]
  exact (htest i).inter
    (measurableSet_mask_forall fun s => measurableSet_mask_imp (htest s).compl)

end LPPDifferentiability.SelectedGridPaths
