/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import LPP_Foundations.Probability.EnvironmentLaw
public import LPP_Foundations.Model.Animals.PathSets
public import ProbabilityBasics.Frozen.Foundations.BK.BKInequalityFamilyInfinitePi
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real

/-! # The BK inequality for path events

Disjoint occurrence of the events "some listed path of slot `j` has weight above its
threshold `a j i`", for finitely many slots, has probability at most the product of the
probabilities of the single events. The path-event bound follows from the
countable-product, real-coordinate extension of the van den Berg-Kesten
inequality (van den Berg and Kesten (1985), Theorem 3.3), through
`ProbabilityBasics.BK.bk_inequality_family_infinitePi`:

1. each event is measurable and increasing in the environment;
2. the event with pairwise disjoint collected sites lies inside the disjoint occurrence of
   the events, with the collected sites of the chosen paths as witnesses;
3. the environment law is the infinite product of the site law.
-/

public section

open MeasureTheory
open scoped ENNReal

namespace LPPDifferentiability

namespace PathEventBK

/-- The event that some listed path of one slot has weight above its threshold. -/
private def slotEvent {I : Type*} {u : I → Lattice} {d : I → ℕ × ℕ}
    (p : ∀ i, Path (u i) (d i)) (a : I → ℝ) : Set Environment :=
  {ω | ∃ i : I, a i < pathWeight ω (p i)}

/-- Path weight is a measurable function of the environment (a finite sum of coordinates). -/
private theorem measurable_pathWeight {u : Lattice} {d : ℕ × ℕ} (p : Path u d) :
    Measurable fun ω : Environment => pathWeight ω p :=
  Finset.measurable_sum _ fun i _ => measurable_pi_apply (p.vertex i.castSucc)

/-- Step 1 (measurability): a slot event is a finite union of strict superlevel sets of
measurable functions. -/
private theorem measurableSet_slotEvent {I : Type*} [Finite I] {u : I → Lattice}
    {d : I → ℕ × ℕ} (p : ∀ i, Path (u i) (d i)) (a : I → ℝ) :
    MeasurableSet (slotEvent p a) := by
  have hcountable : Countable I := Finite.to_countable
  have h : slotEvent p a = ⋃ i, {ω : Environment | a i < pathWeight ω (p i)} := by
    ext ω
    exact (Set.mem_iUnion (x := ω)
      (s := fun i => {ω : Environment | a i < pathWeight ω (p i)})).symm
  rw [h]
  exact MeasurableSet.iUnion fun i =>
    measurableSet_lt measurable_const (measurable_pathWeight (p i))

/-- Step 1 (monotonicity): path weights, being sums of coordinates, grow with the
environment, so a slot event is an upper set. -/
private theorem isUpperSet_slotEvent {I : Type*} {u : I → Lattice} {d : I → ℕ × ℕ}
    (p : ∀ i, Path (u i) (d i)) (a : I → ℝ) : IsUpperSet (slotEvent p a) := by
  intro ω ω' hle hω
  obtain ⟨i, hi⟩ := hω
  refine ⟨i, lt_of_lt_of_le hi ?_⟩
  exact Finset.sum_le_sum fun k _ => hle _

/-- Step 2 (the witness): the weight of a path is unchanged by any change of the
environment away from its collected sites. -/
private theorem pathWeight_congr_on_collectedSites {u : Lattice} {d : ℕ × ℕ} (p : Path u d)
    {ω ω' : Environment} (h : ∀ z ∈ p.collectedSites, ω' z = ω z) :
    pathWeight ω' p = pathWeight ω p := by
  rw [Path.pathWeight_eq_sum_collectedSites, Path.pathWeight_eq_sum_collectedSites]
  exact Finset.sum_congr rfl h

end PathEventBK

open PathEventBK in
/-- **BK inequality for path events.** For finitely many slots `j`, each with finitely many
listed paths `p j i` and thresholds `a j i`, the environments for which one can choose a
path in every slot above its threshold, with pairwise disjoint collected sites, have
probability at most the product over the slots of the probabilities that some listed path of
that slot is above its threshold. This is the countable-product, real-coordinate
extension of the van den Berg-Kesten inequality (van den Berg and Kesten (1985),
Theorem 3.3) for path events; it follows from
`ProbabilityBasics.BK.bk_inequality_family_infinitePi`. -/
theorem path_event_bk (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (q : ℕ) (I : Fin q → Type*) [∀ j, Fintype (I j)]
    (u : ∀ j, I j → Lattice) (d : ∀ j, I j → ℕ × ℕ)
    (p : ∀ j i, Path (u j i) (d j i)) (a : ∀ j, I j → ℝ) :
    environmentLaw μ {ω | ∃ i : ∀ j, I j,
      (∀ j, a j (i j) < pathWeight ω (p j (i j))) ∧
      Pairwise (fun j k => Disjoint (p j (i j)).collectedSites
        (p k (i k)).collectedSites)} ≤
      ∏ j : Fin q, environmentLaw μ {ω | ∃ i : I j, a j i < pathWeight ω (p j i)} := by
  -- The events `A j` of the inequality, one for each slot.
  let A : Fin q → Set Environment := fun j => slotEvent (p j) (a j)
  have hAm : ∀ j, MeasurableSet (A j) := fun j => measurableSet_slotEvent (p j) (a j)
  have hA : ∀ j, IsUpperSet (A j) := fun j => isUpperSet_slotEvent (p j) (a j)
  -- The left-hand event lies inside the disjoint occurrence of the `A j`.
  have hsub : {ω : Environment | ∃ i : ∀ j, I j,
      (∀ j, a j (i j) < pathWeight ω (p j (i j))) ∧
      Pairwise (fun j k => Disjoint (p j (i j)).collectedSites
        (p k (i k)).collectedSites)} ⊆ ProbabilityBasics.BK.disjointOccurrence A := by
    rintro ω ⟨i, hi, hdisj⟩
    refine ⟨fun j => (p j (i j)).collectedSites, hdisj, fun j ω' hω' => ?_⟩
    refine ⟨i j, ?_⟩
    rw [pathWeight_congr_on_collectedSites (p j (i j)) hω']
    exact hi j
  -- The environment law is the infinite product of the site law.
  have hlaw : ∀ S : Set Environment,
      environmentLaw μ S = Measure.infinitePi (fun _ : Lattice => μ) S := fun _ => rfl
  calc environmentLaw μ _
      ≤ environmentLaw μ (ProbabilityBasics.BK.disjointOccurrence A) := measure_mono hsub
    _ = Measure.infinitePi (fun _ : Lattice => μ) (ProbabilityBasics.BK.disjointOccurrence A) :=
        hlaw _
    _ ≤ ∏ j, Measure.infinitePi (fun _ : Lattice => μ) (A j) :=
        ProbabilityBasics.BK.bk_inequality_family_infinitePi (E := fun _ : Lattice => ℝ)
          (fun _ => μ) hAm hA
    _ = ∏ j : Fin q, environmentLaw μ {ω | ∃ i : I j, a j i < pathWeight ω (p j i)} := by
        simp only [hlaw]; rfl

end LPPDifferentiability
