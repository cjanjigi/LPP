/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Differentiability.FinalDraft.WitnessMultiplicity.Cuts
public import Differentiability.FinalDraft.WitnessMultiplicity.Maximum
public import LPP_Foundations.Probability.EnvironmentLaw
public import Mathlib.MeasureTheory.Measure.Real
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Differentiability.Model.Paths.StageSplitWitnesses
import Differentiability.Model.StageItinerarySteps
import Differentiability.Probability.LongPathWitnessBound
import Mathlib.Tactic.Linarith

/-! The maximizing families from all stages combine into one disjoint family.
The long-path estimate applies to this family and therefore to the exact total count. -/

public section

open MeasureTheory
open scoped BigOperators

namespace LPPDifferentiability

/-- Maximal families for the stages, including the final remainder, have disjoint
collected sites across the entire path. -/
theorem Path.exists_total_witness_family {d : ℕ × ℕ} (p : Path 0 d) (ω : Environment)
    (a : ℝ) (m : ℕ) (s η G0 dl dr K : ℝ)
    (hm : 0 < m) (hs : 0 < s) (hη : 0 < η) {N : ℕ}
    (cuts : Fin (N + 2) → Fin (d.1 + d.2 + 1))
    (hcuts : p.is_first_stage_decomposition a m s cuts) :
    let capacity := fun i : Fin (N + 1) =>
      p.stageWitnessMultiplicity ω a m s η G0 dl dr K hm hs hη
        (cuts i.castSucc) (cuts i.succ) (hcuts.2.2.1 i.castSucc_le_succ)
    ∃ (time : (Σ i : Fin (N + 1), Fin (capacity i)) → ℕ)
      (start : (Σ i : Fin (N + 1), Fin (capacity i)) → Lattice)
      (disp : (Σ i : Fin (N + 1), Fin (capacity i)) → ℕ × ℕ)
      (q : (j : Σ i : Fin (N + 1), Fin (capacity i)) → Path (start j) (disp j)),
      (∀ j, (cuts j.1.castSucc).val ≤ time j ∧
        time j + ((disp j).1 + (disp j).2) ≤ (cuts j.1.succ).val ∧
        p.is_segment_at (time j) (q j) ∧
        (q j).is_stage_block_witness ω a m s η G0 dl dr K
          (p.stageBlockIndex a m s (cuts j.1.castSucc))) ∧
      (∀ j j', j ≠ j' → Disjoint (q j).collectedSites (q j').collectedSites) := by
  classical
  intro capacity
  have hw (i : Fin (N + 1)) :
      p.has_stage_witness_family ω a m s η G0 dl dr K (cuts i.castSucc) (cuts i.succ) (capacity i) :=
    p.has_stage_witness_family_multiplicity ω a m s η G0 dl dr K hm hs hη
      (cuts i.castSucc) (cuts i.succ) (hcuts.2.2.1 i.castSucc_le_succ)
  simp only [Path.has_stage_witness_family] at hw
  choose time start disp q hmem hdisj using hw
  refine ⟨fun j => time j.1 j.2, fun j => start j.1 j.2, fun j => disp j.1 j.2,
    fun j => q j.1 j.2, fun j => hmem j.1 j.2, ?_⟩
  rintro ⟨i, j⟩ ⟨i', j'⟩ hne
  change Disjoint (q i j).collectedSites (q i' j').collectedSites
  have earlier_disjoint (i i' : Fin (N + 1)) (hlt : i < i')
      (j : Fin (capacity i)) (j' : Fin (capacity i')) :
      Disjoint (q i j).collectedSites (q i' j').collectedSites := by
    have horder : i.succ ≤ i'.castSucc := by
      change i.val + 1 ≤ i'.val
      exact Nat.succ_le_of_lt hlt
    have hmiddle : (cuts i.succ).val ≤ (cuts i'.castSucc).val := hcuts.2.2.1 horder
    have hsep := (hmem i j).2.1.trans (hmiddle.trans (hmem i' j').1)
    exact p.segment_collectedSites_disjoint (q i j) (q i' j') (time i j) (time i' j')
      (hmem i j).2.2.1 (hmem i' j').2.2.1 hsep
  rcases lt_trichotomy i i' with hlt | heq | hgt
  · exact earlier_disjoint i i' hlt j j'
  · subst i'
    exact hdisj i j j' (fun h => hne (congrArg (Sigma.mk i) h))
  · exact (earlier_disjoint i' i hgt j' j).symm

/-- Proposition `prop:longpaths`, using the sum of the actual maximal counts.
The almost-sure bound is strict with the natural-number floor `N / 32`. -/
theorem totalWitnessMultiplicity_lt_eventually_ae (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (a : ℝ) (ha : 0 < a) (ha1 : a < 1) (m : ℕ) (hm : 0 < m) (s : ℝ) (hs : 2 ≤ s)
    (η G0 dl dr K q0 : ℝ) (hη : 0 < η) (hq0 : 0 < q0)
    (hsmall : 60 * (2 * q0) ^ (1 / 32 : ℝ) ≤ 1 / 2)
    (hrare : ∀ b : Lattice, (environmentLaw μ).real {ω : Environment |
      ∃ (u : Lattice) (e : ℕ × ℕ) (q : Path u e),
        q.is_stage_block_witness ω a m s η G0 dl dr K b} ≤ 2 * q0) :
    ∀ᵐ ω ∂environmentLaw μ, ∃ N0 : ℕ, ∀ (d : ℕ × ℕ) (p : Path 0 d) (N : ℕ), N0 ≤ N →
      ∀ (cuts : Fin (N + 2) → Fin (d.1 + d.2 + 1))
        (hcuts : p.is_first_stage_decomposition a m s cuts),
      p.totalWitnessMultiplicity ω a m s η G0 dl dr K hm (by linarith) hη cuts hcuts < N / 32 := by
  have hlong := long_path_disjoint_witnesses_ae μ a s m η G0 dl dr K q0 hq0 hsmall hrare
  filter_upwards [hlong] with ω hω
  obtain ⟨N0, hbound⟩ := hω
  refine ⟨N0, fun d p N hN cuts hcuts => ?_⟩
  obtain ⟨N', cuts', hgeometry⟩ := p.exists_first_cuts_blocks_indices a ha ha1 m hm s hs
  have hcuts' : p.is_first_stage_decomposition a m s cuts' :=
    ⟨hgeometry.1, hgeometry.2.1, hgeometry.2.2.1,
      hgeometry.2.2.2.2.1, hgeometry.2.2.2.2.2.1⟩
  obtain ⟨hcount, hsame⟩ := p.first_stage_decompositions_agree hcuts hcuts'
  subst N'
  have heq : cuts' = cuts := funext fun i => (hsame i i rfl).symm
  subst cuts'
  obtain ⟨time, start, disp, q, hmem, hdisj⟩ :=
    p.exists_total_witness_family ω a m s η G0 dl dr K hm (by linarith) hη cuts hcuts
  exact hbound d p N hN cuts hgeometry _ time start disp q hmem hdisj

end LPPDifferentiability
