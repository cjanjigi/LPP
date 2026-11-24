/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Differentiability.FinalDraft.WitnessMultiplicity.Definitions
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-! The maximal stage count is attained and dominates every disjoint witness family. -/

public section

namespace LPPDifferentiability

namespace Path

/-- A witness has a positive number of collected vertices. -/
theorem length_pos_of_is_stage_block_witness {u : Lattice} {e : ℕ × ℕ}
    (q : Path u e) {ω : Environment} {a : ℝ} {m : ℕ} {s η G0 dl dr K : ℝ} {b : Lattice}
    (hm : 0 < m) (hs : 0 < s) (hη : 0 < η)
    (hw : q.is_stage_block_witness ω a m s η G0 dl dr K b) : 0 < e.1 + e.2 := by
  rcases hw with ⟨_, hdefect⟩ | ⟨_, hlen, _, _⟩
  · by_contra! hlen
    have he : e = (0, 0) := Prod.ext (by omega) (by omega)
    subst e
    norm_num [Path.minimumSupportDefect, Path.supportDefect, supportingFunctional,
      transverseCoordinate, pathWeight] at hdefect
    linarith only [hdefect, mul_pos hη hs]
  · rwa [hlen]

/-- The empty family is valid in every stage. -/
theorem has_stage_witness_family_zero {d : ℕ × ℕ} (p : Path 0 d) (ω : Environment)
    (a : ℝ) (m : ℕ) (s η G0 dl dr K : ℝ) (k l : Fin (d.1 + d.2 + 1)) :
    p.has_stage_witness_family ω a m s η G0 dl dr K k l 0 := by
  refine ⟨Fin.elim0, Fin.elim0, Fin.elim0, (fun j => Fin.elim0 j), ?_, ?_⟩
  · intro j
    exact Fin.elim0 j
  · intro j
    exact Fin.elim0 j

/-- The first collected time of each witness gives an injection into the stage times. -/
theorem le_stage_length_of_has_stage_witness_family {d : ℕ × ℕ} (p : Path 0 d)
    {ω : Environment} {a : ℝ} {m : ℕ} {s η G0 dl dr K : ℝ}
    {k l : Fin (d.1 + d.2 + 1)} {M : ℕ}
    (hm : 0 < m) (hs : 0 < s) (hη : 0 < η)
    (hfamily : p.has_stage_witness_family ω a m s η G0 dl dr K k l M) :
    M ≤ l.val - k.val := by
  obtain ⟨time, start, disp, q, hmem, hdisj⟩ := hfamily
  have hlen (j : Fin M) : 0 < (disp j).1 + (disp j).2 :=
    (q j).length_pos_of_is_stage_block_witness hm hs hη (hmem j).2.2.2
  let f (j : Fin M) : Fin (l.val - k.val) :=
    ⟨time j - k.val, by
      have hstart := (hmem j).1
      have hend := (hmem j).2.1
      have hpos := hlen j
      omega⟩
  have hsite (j : Fin M) (t : Fin (d.1 + d.2 + 1)) (ht : t.val = time j) :
      p.vertex t ∈ (q j).collectedSites := by
    refine ((q j).mem_collectedSites_iff _).2 ⟨⟨0, hlen j⟩, ?_⟩
    exact (hmem j).2.2.1.2 _ t (by change t.val = time j + 0; omega)
  have hf : Function.Injective f := by
    intro i j heq
    have hdiff := congrArg Fin.val heq
    change time i - k.val = time j - k.val at hdiff
    have hi := (hmem i).1
    have hj := (hmem j).1
    have htime : time i = time j := by omega
    have hfit := (hmem i).2.2.1.1
    let t : Fin (d.1 + d.2 + 1) := ⟨time i, by omega⟩
    by_contra hne
    exact Finset.disjoint_left.mp (hdisj i j hne)
      (hsite i t rfl) (hsite j t htime)
  simpa only [Fintype.card_fin] using Fintype.card_le_of_injective f hf

/-- A disjoint family attains the maximal stage count. -/
theorem has_stage_witness_family_multiplicity {d : ℕ × ℕ} (p : Path 0 d)
    (ω : Environment) (a : ℝ) (m : ℕ) (s η G0 dl dr K : ℝ)
    (hm : 0 < m) (hs : 0 < s) (hη : 0 < η) (k l : Fin (d.1 + d.2 + 1)) (hkl : k ≤ l) :
    p.has_stage_witness_family ω a m s η G0 dl dr K k l
      (p.stageWitnessMultiplicity ω a m s η G0 dl dr K hm hs hη k l hkl) := by
  classical
  unfold stageWitnessMultiplicity
  exact Nat.findGreatest_spec (Nat.zero_le _)
    (p.has_stage_witness_family_zero ω a m s η G0 dl dr K k l)

/-- Every disjoint witness family has size at most the maximal stage count. -/
theorem le_stageWitnessMultiplicity_of_has_stage_witness_family {d : ℕ × ℕ} (p : Path 0 d)
    {ω : Environment} {a : ℝ} {m : ℕ} {s η G0 dl dr K : ℝ}
    {k l : Fin (d.1 + d.2 + 1)} {M : ℕ}
    (hm : 0 < m) (hs : 0 < s) (hη : 0 < η) (hkl : k ≤ l)
    (hf : p.has_stage_witness_family ω a m s η G0 dl dr K k l M) :
    M ≤ p.stageWitnessMultiplicity ω a m s η G0 dl dr K hm hs hη k l hkl := by
  classical
  unfold stageWitnessMultiplicity
  exact Nat.le_findGreatest (p.le_stage_length_of_has_stage_witness_family hm hs hη hf) hf

/-- The stage count never exceeds its length. -/
theorem stageWitnessMultiplicity_le_length {d : ℕ × ℕ} (p : Path 0 d)
    (ω : Environment) (a : ℝ) (m : ℕ) (s η G0 dl dr K : ℝ)
    (hm : 0 < m) (hs : 0 < s) (hη : 0 < η) (k l : Fin (d.1 + d.2 + 1)) (hkl : k ≤ l) :
    p.stageWitnessMultiplicity ω a m s η G0 dl dr K hm hs hη k l hkl ≤ l.val - k.val :=
  p.le_stage_length_of_has_stage_witness_family hm hs hη
    (p.has_stage_witness_family_multiplicity ω a m s η G0 dl dr K hm hs hη k l hkl)

/-- A length-zero stage, including an empty remainder, contributes zero. -/
theorem stageWitnessMultiplicity_eq_zero_of_same_time {d : ℕ × ℕ} (p : Path 0 d)
    (ω : Environment) (a : ℝ) (m : ℕ) (s η G0 dl dr K : ℝ)
    (hm : 0 < m) (hs : 0 < s) (hη : 0 < η) (k : Fin (d.1 + d.2 + 1)) :
    p.stageWitnessMultiplicity ω a m s η G0 dl dr K hm hs hη k k le_rfl = 0 :=
  Nat.eq_zero_of_le_zero (by
    simpa only [Nat.sub_self] using
      p.stageWitnessMultiplicity_le_length ω a m s η G0 dl dr K hm hs hη k k le_rfl)

end Path

end LPPDifferentiability
