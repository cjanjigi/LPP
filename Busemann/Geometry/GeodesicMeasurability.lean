/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Busemann.Geometry.LocallyRightmostGeodesic
public import LPP_Foundations.Probability.PassageMeasurable
import Mathlib.Tactic

/-! Joint Borel graphs for locally-rightmost paths and their shared-level order. -/

@[expose] public section
open MeasureTheory LPPDifferentiability

namespace LPP.Busemann

-- Fix the random segment root BEFORE quantifying over its finite path type.
private theorem locallyRightmost_countable_iff
    (ω : LPPDifferentiability.Environment) (u : Lattice) (γ : ℕ → Lattice) :
    IsLocallyRightmostGeodesic ω u γ ↔
      γ 0 = u ∧
      (∀ n : ℕ,
        γ (n + 1) = γ n + ((1 : ℤ), (0 : ℤ)) ∨
          γ (n + 1) = γ n + ((0 : ℤ), (1 : ℤ))) ∧
      ∀ m N : ℕ, 0 < N →
        ∃ (v : Lattice) (d : ℕ × ℕ) (p : LPPDifferentiability.Path v d),
          γ m = v ∧ d.1 + d.2 = N ∧
          (∀ i : Fin (d.1 + d.2 + 1), p.vertex i = γ (m + i.val)) ∧
          pathWeight ω p = lastPassage ω v d ∧
          ∀ q : LPPDifferentiability.Path v d,
            pathWeight ω q = lastPassage ω v d →
            ∀ i : Fin (d.1 + d.2 + 1),
              (q.vertex i).1 ≤ (p.vertex i).1 ∧ (p.vertex i).2 ≤ (q.vertex i).2 := by
  unfold IsLocallyRightmostGeodesic
  constructor
  · rintro ⟨hStart, hStep, hSegment⟩
    refine ⟨hStart, hStep, ?_⟩
    intro m N hN
    obtain ⟨d, p, hLength, hTrace, hMax, hGreatest⟩ := hSegment m N hN
    exact ⟨γ m, d, p, rfl, hLength, hTrace, hMax, hGreatest⟩
  · rintro ⟨hStart, hStep, hSegment⟩
    refine ⟨hStart, hStep, ?_⟩
    intro m N hN
    obtain ⟨v, d, p, hRoot, hLength, hTrace, hMax, hGreatest⟩ := hSegment m N hN
    subst v
    exact ⟨d, p, hLength, hTrace, hMax, hGreatest⟩

-- All quantified paths here have FIXED root and displacement and form a finite type.
private theorem measurableSet_fixed_geodesic_segment
    (m N : ℕ) (v : Lattice) (d : ℕ × ℕ) (p : LPPDifferentiability.Path v d) :
    MeasurableSet {a : LPPDifferentiability.Environment × (Lattice × (ℕ → Lattice)) |
      a.2.2 m = v ∧ d.1 + d.2 = N ∧
      (∀ i : Fin (d.1 + d.2 + 1), p.vertex i = a.2.2 (m + i.val)) ∧
      pathWeight a.1 p = lastPassage a.1 v d ∧
      ∀ q : LPPDifferentiability.Path v d,
        pathWeight a.1 q = lastPassage a.1 v d →
        ∀ i : Fin (d.1 + d.2 + 1),
          (q.vertex i).1 ≤ (p.vertex i).1 ∧ (p.vertex i).2 ≤ (q.vertex i).2} := by
  classical
  have hVertex (k : ℕ) : Measurable
      (fun a : LPPDifferentiability.Environment × (Lattice × (ℕ → Lattice)) => a.2.2 k) :=
    (measurable_pi_apply k).comp measurable_snd.snd
  have hRoot : MeasurableSet
      {a : LPPDifferentiability.Environment × (Lattice × (ℕ → Lattice)) | a.2.2 m = v} :=
    measurableSet_eq_fun (hVertex m) measurable_const
  have hTrace : MeasurableSet
      {a : LPPDifferentiability.Environment × (Lattice × (ℕ → Lattice)) |
        ∀ i : Fin (d.1 + d.2 + 1), p.vertex i = a.2.2 (m + i.val)} := by
    simp only [Set.ofPred_forall]
    exact MeasurableSet.iInter fun i =>
      measurableSet_eq_fun measurable_const (hVertex (m + i.val))
  have hLast : Measurable
      (fun a : LPPDifferentiability.Environment × (Lattice × (ℕ → Lattice)) =>
        lastPassage a.1 v d) := (measurable_lastPassage v d).comp measurable_fst
  have hMax : MeasurableSet
      {a : LPPDifferentiability.Environment × (Lattice × (ℕ → Lattice)) |
        pathWeight a.1 p = lastPassage a.1 v d} :=
    measurableSet_eq_fun ((measurable_pathWeight p).comp measurable_fst) hLast
  have hGreatest : MeasurableSet
      {a : LPPDifferentiability.Environment × (Lattice × (ℕ → Lattice)) |
        ∀ q : LPPDifferentiability.Path v d,
          pathWeight a.1 q = lastPassage a.1 v d →
          ∀ i : Fin (d.1 + d.2 + 1),
            (q.vertex i).1 ≤ (p.vertex i).1 ∧ (p.vertex i).2 ≤ (q.vertex i).2} := by
    simp only [Set.ofPred_forall]
    apply MeasurableSet.iInter
    intro q
    exact (measurableSet_eq_fun ((measurable_pathWeight q).comp measurable_fst) hLast).imp
      (MeasurableSet.const _)
  exact hRoot.inter ((MeasurableSet.const _).inter (hTrace.inter (hMax.inter hGreatest)))

/-- The locally-rightmost membership graph is jointly Borel in the environment,
root and whole raw sequence. Strong Existence, lines 725–842,
uses this measurable geodesic interface in its conditional-law construction. -/
theorem measurableSet_isLocallyRightmostGeodesic :
    MeasurableSet {p : LPPDifferentiability.Environment × (Lattice × (ℕ → Lattice)) |
      IsLocallyRightmostGeodesic p.1 p.2.1 p.2.2} := by
  classical
  have hVertex (k : ℕ) : Measurable
      (fun a : LPPDifferentiability.Environment × (Lattice × (ℕ → Lattice)) => a.2.2 k) :=
    (measurable_pi_apply k).comp measurable_snd.snd
  have hStart : MeasurableSet
      {a : LPPDifferentiability.Environment × (Lattice × (ℕ → Lattice)) |
        a.2.2 0 = a.2.1} := measurableSet_eq_fun (hVertex 0) measurable_snd.fst
  have hStep (n : ℕ) : MeasurableSet
      {a : LPPDifferentiability.Environment × (Lattice × (ℕ → Lattice)) |
        a.2.2 (n + 1) = a.2.2 n + ((1 : ℤ), (0 : ℤ)) ∨
          a.2.2 (n + 1) = a.2.2 n + ((0 : ℤ), (1 : ℤ))} :=
    (measurableSet_eq_fun (hVertex (n + 1)) ((hVertex n).add measurable_const)).union
      (measurableSet_eq_fun (hVertex (n + 1)) ((hVertex n).add measurable_const))
  have hSteps : MeasurableSet
      {a : LPPDifferentiability.Environment × (Lattice × (ℕ → Lattice)) |
        ∀ n : ℕ, a.2.2 (n + 1) = a.2.2 n + ((1 : ℤ), (0 : ℤ)) ∨
          a.2.2 (n + 1) = a.2.2 n + ((0 : ℤ), (1 : ℤ))} := by
    simp only [Set.ofPred_forall]
    exact MeasurableSet.iInter hStep
  -- Keep set builders explicit when constructing their countable intersections.
  have hSegments : MeasurableSet
      {a : LPPDifferentiability.Environment × (Lattice × (ℕ → Lattice)) |
        ∀ m N : ℕ, 0 < N →
          ∃ (v : Lattice) (d : ℕ × ℕ) (p : LPPDifferentiability.Path v d),
            a.2.2 m = v ∧ d.1 + d.2 = N ∧
            (∀ i : Fin (d.1 + d.2 + 1), p.vertex i = a.2.2 (m + i.val)) ∧
            pathWeight a.1 p = lastPassage a.1 v d ∧
            ∀ q : LPPDifferentiability.Path v d,
              pathWeight a.1 q = lastPassage a.1 v d →
              ∀ i : Fin (d.1 + d.2 + 1),
                (q.vertex i).1 ≤ (p.vertex i).1 ∧ (p.vertex i).2 ≤ (q.vertex i).2} := by
    simp only [Set.ofPred_forall]
    refine MeasurableSet.iInter fun m => MeasurableSet.iInter fun N => ?_
    have hExists : MeasurableSet
        {a : LPPDifferentiability.Environment × (Lattice × (ℕ → Lattice)) |
          ∃ (v : Lattice) (d : ℕ × ℕ) (p : LPPDifferentiability.Path v d),
            a.2.2 m = v ∧ d.1 + d.2 = N ∧
            (∀ i : Fin (d.1 + d.2 + 1), p.vertex i = a.2.2 (m + i.val)) ∧
            pathWeight a.1 p = lastPassage a.1 v d ∧
            ∀ q : LPPDifferentiability.Path v d,
              pathWeight a.1 q = lastPassage a.1 v d →
              ∀ i : Fin (d.1 + d.2 + 1),
                (q.vertex i).1 ≤ (p.vertex i).1 ∧ (p.vertex i).2 ≤ (q.vertex i).2} := by
      simp only [Set.ofPred_exists]
      exact MeasurableSet.iUnion fun v => MeasurableSet.iUnion fun d =>
        MeasurableSet.iUnion fun p => measurableSet_fixed_geodesic_segment m N v d p
    exact MeasurableSet.iInter (fun _ : 0 < N => hExists)
  -- This set equality uses the proved dependent-root equivalence, not a projection theorem.
  convert hStart.inter (hSteps.inter hSegments) using 1
  ext a
  exact locallyRightmost_countable_iff a.1 a.2.1 a.2.2

/-- Shared signed absolute-level southeast comparison is a measurable relation
on all raw sequences. Strong Existence, lines 171–175 and
725–842; no path validity, global ordering or measurable selection is assumed. -/
theorem measurableSet_pathSoutheastLE :
    MeasurableSet {p : (ℕ → Lattice) × (ℕ → Lattice) | pathSoutheastLE p.1 p.2} := by
  have hLeft (k : ℕ) : Measurable
      (fun p : (ℕ → Lattice) × (ℕ → Lattice) => p.1 k) :=
    (measurable_pi_apply k).comp measurable_fst
  have hRight (k : ℕ) : Measurable
      (fun p : (ℕ → Lattice) × (ℕ → Lattice) => p.2 k) :=
    (measurable_pi_apply k).comp measurable_snd
  unfold pathSoutheastLE
  simp only [Set.ofPred_forall]
  apply MeasurableSet.iInter
  intro m
  apply MeasurableSet.iInter
  intro n
  have hClock : MeasurableSet
      {p : (ℕ → Lattice) × (ℕ → Lattice) |
        (p.1 0).1 + (p.1 0).2 + (m : ℤ) =
          (p.2 0).1 + (p.2 0).2 + (n : ℤ)} :=
    measurableSet_eq_fun (((hLeft 0).fst.add (hLeft 0).snd).add measurable_const)
      (((hRight 0).fst.add (hRight 0).snd).add measurable_const)
  exact hClock.imp
    ((measurableSet_le (hLeft m).fst (hRight n).fst).inter
      (measurableSet_le (hRight n).snd (hLeft m).snd))

end LPP.Busemann
