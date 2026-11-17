/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Busemann.Process.CoordinatePathSum
public import Busemann.Frozen.Definitions.ProcessShift
public import Busemann.Frozen.Definitions.RandomCocycle
public import Busemann.Frozen.Definitions.Recovery
import Busemann.Process.Shifts
import LPP_Foundations.Model.LatticeEdgeTranslation
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Tactic

/-! Countably many actual cocycles from simultaneous elementary edge constraints. -/

@[expose] public section

open MeasureTheory LPPDifferentiability
open scoped BigOperators

namespace LPP.Busemann

/-- The literal signed coordinate sums extend an integrable countable edge array
on one measurable shift-invariant full event. This is the extension step in
JR1810.03580v3, proof of Theorem 4.8 after (4.19); no stationarity is assumed. -/
theorem countable_coordinate_cocycles (P : Measure ProcessSample) [IsProbabilityMeasure P]
    (hInt : ∀ j x i, Integrable (fun s : ProcessSample => s.2 j x i) P)
    (hField : ∀ᵐ s ∂P,
      (∀ j x, s.2 j x 0 + s.2 j (x + (1, 0)) 1 =
        s.2 j x 1 + s.2 j (x + (0, 1)) 0) ∧
      (∀ j x, min (s.2 j x 0) (s.2 j x 1) = s.1 x)) :
    let S : (ℤ → ℝ) → ℤ → ℤ → ℝ := fun f a b =>
      if a ≤ b then ∑ k ∈ Finset.Ico a b, f k else -(∑ k ∈ Finset.Ico b a, f k)
    let R : ℕ → Lattice → Lattice → ProcessSample → ℝ := fun j x y s =>
      S (fun k => s.2 j (k, x.2) 0) x.1 y.1 +
        S (fun k => s.2 j (y.1, k) 1) x.2 y.2
    Measurable (fun q : ℕ × Lattice × Lattice × ProcessSample =>
      R q.1 q.2.1 q.2.2.1 q.2.2.2) ∧
    (∀ j x y, Integrable (R j x y) P) ∧
    (∀ s j x, R j x (x + (1, 0)) s = s.2 j x 0 ∧
      R j x (x + (0, 1)) s = s.2 j x 1) ∧
    ∃ C : Set ProcessSample,
      C = {s | (∀ j x, s.2 j x 0 + s.2 j (x + (1, 0)) 1 =
          s.2 j x 1 + s.2 j (x + (0, 1)) 0) ∧
        (∀ j x, min (s.2 j x 0) (s.2 j x 1) = s.1 x)} ∧
      MeasurableSet C ∧ P C = 1 ∧
      (∀ z s, processShift z s ∈ C ↔ s ∈ C) ∧
      (∀ s ∈ C, ∀ j,
        (∀ x y z, R j (x + z) (y + z) s = R j x y (processShift z s)) ∧
        (∀ x y z, R j x y s + R j y z s = R j x z s) ∧
        recovers_environment s.1 (fun x y => R j x y s)) ∧
      (∀ j, is_shift_covariant_cocycle P processShift (R j)) := by
  classical
  let S : (ℤ → ℝ) → ℤ → ℤ → ℝ := fun f a b =>
    if a ≤ b then ∑ k ∈ Finset.Ico a b, f k else -(∑ k ∈ Finset.Ico b a, f k)
  let R : ℕ → Lattice → Lattice → ProcessSample → ℝ := fun j x y s =>
    S (fun k => s.2 j (k, x.2) 0) x.1 y.1 +
      S (fun k => s.2 j (y.1, k) 1) x.2 y.2
  change Measurable (fun q : ℕ × Lattice × Lattice × ProcessSample =>
      R q.1 q.2.1 q.2.2.1 q.2.2.2) ∧ _
  have hReg := coordinate_path_sum_regularities P hInt

  -- One literal event imposes every raw square and every raw recovery identity.
  let C : Set ProcessSample :=
    {s | (∀ j x, s.2 j x 0 + s.2 j (x + (1, 0)) 1 =
        s.2 j x 1 + s.2 j (x + (0, 1)) 0) ∧
      (∀ j x, min (s.2 j x 0) (s.2 j x 1) = s.1 x)}
  have hcoord (j : ℕ) (x : Lattice) (i : Fin 2) :
      Measurable (fun s : ProcessSample => s.2 j x i) :=
    (measurable_pi_apply i).comp
      ((measurable_pi_apply x).comp ((measurable_pi_apply j).comp measurable_snd))
  have hEnv (x : Lattice) : Measurable (fun s : ProcessSample => s.1 x) :=
    (measurable_pi_apply x).comp measurable_fst
  have hCurlMeas : MeasurableSet {s : ProcessSample |
      ∀ j x, s.2 j x 0 + s.2 j (x + (1, 0)) 1 =
        s.2 j x 1 + s.2 j (x + (0, 1)) 0} := by
    simp only [Set.ofPred_forall]
    exact MeasurableSet.iInter fun j => MeasurableSet.iInter fun x =>
      measurableSet_eq_fun ((hcoord j x 0).add (hcoord j (x + (1, 0)) 1))
        ((hcoord j x 1).add (hcoord j (x + (0, 1)) 0))
  have hRecoveryMeas : MeasurableSet {s : ProcessSample |
      ∀ j x, min (s.2 j x 0) (s.2 j x 1) = s.1 x} := by
    simp only [Set.ofPred_forall]
    exact MeasurableSet.iInter fun j => MeasurableSet.iInter fun x =>
      measurableSet_eq_fun ((hcoord j x 0).min (hcoord j x 1)) (hEnv x)
  have hCMeas : MeasurableSet C := hCurlMeas.inter hRecoveryMeas
  have hCAE : ∀ᵐ s ∂P, s ∈ C := hField
  have hCProb : P C = 1 := (mem_ae_iff_prob_eq_one hCMeas).mp hCAE

  -- Translation only reindexes the raw constraints; inverse translation gives equivalence.
  have hCforward (z : Lattice) (s : ProcessSample) (hs : s ∈ C) :
      processShift z s ∈ C := by
    constructor
    · intro j x
      simpa only [processShift, add_assoc] using hs.1 j (z + x)
    · intro j x
      simpa only [processShift, environmentTranslationEquiv_apply] using hs.2 j (z + x)
  have hCInvariant (z : Lattice) (s : ProcessSample) :
      processShift z s ∈ C ↔ s ∈ C := by
    constructor
    · intro hs
      have hback := hCforward (-z) (processShift z s) hs
      rwa [processShift_neg_processShift] at hback
    · exact hCforward z s

  -- The deterministic extension supplies all-pair additivity and covariance.
  have hGood (s : ProcessSample) (hs : s ∈ C) (j : ℕ) :
      (∀ x y z, R j (x + z) (y + z) s = R j x y (processShift z s)) ∧
      (∀ x y z, R j x y s + R j y z s = R j x z s) ∧
      recovers_environment s.1 (fun x y => R j x y s) := by
    have hdet := lattice_edge_extension_sum_additive_translation (s.2 j) (hs.1 j)
    constructor
    · intro x y z
      have ht := hdet.2 z x y
      change R j x y (processShift z s) = R j (z + x) (z + y) s at ht
      simpa only [add_comm] using ht.symm
    constructor
    · exact hdet.1
    · intro x
      have he : R j x (x + (1, 0)) s = s.2 j x 0 := (hReg.2.2 s j x).1
      have hn : R j x (x + (0, 1)) s = s.2 j x 1 := (hReg.2.2 s j x).2
      change min (R j x (x + (1, 0)) s) (R j x (x + (0, 1)) s) = s.1 x
      rw [he, hn]
      exact hs.2 j x

  -- Specialize joint regularity and use this same full event for the exact random predicate.
  have hCocycle (j : ℕ) : is_shift_covariant_cocycle P processShift (R j) := by
    have hMap : Measurable (fun q : (Lattice × Lattice) × ProcessSample =>
        (j, q.1.1, q.1.2, q.2)) := by fun_prop
    refine ⟨hReg.1.comp hMap, ?_, ?_⟩
    · intro x y z
      filter_upwards [hCAE] with s hs
      exact (hGood s hs j).1 x y z
    · filter_upwards [hCAE] with s hs
      exact (hGood s hs j).2.1
  exact ⟨hReg.1, hReg.2.1, hReg.2.2, C, rfl, hCMeas, hCProb,
    hCInvariant, hGood, hCocycle⟩

end LPP.Busemann
