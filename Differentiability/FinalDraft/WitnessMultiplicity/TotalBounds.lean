/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Differentiability.FinalDraft.WitnessMultiplicity.Cuts
public import Differentiability.FinalDraft.WitnessMultiplicity.Maximum
import Differentiability.Model.Paths.StageDefectTotal
import Differentiability.Probability.StageExcessItinerary
import Mathlib.Data.Sigma.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-! Whole-path weight bounds using the sum of maximum stage witness counts. -/

public section

open scoped BigOperators

namespace LPPDifferentiability

namespace Path

private theorem total_weight_le_with_cutoff {d : ℕ × ℕ} (p : Path 0 d) (ω : Environment)
    (a : ℝ) (ha : 0 < a) (ha1 : a < 1) (m : ℕ) (hm : 0 < m) (s : ℝ) (hs : 2 ≤ s)
    (η G0 dl dr K M0 : ℝ) (hη : 0 < η) (hc : 2 * η ≤ (dl - dr) / 2)
    (hstep : |G0| + |(dl + dr) / 2| + M0 ≤ η * s / 2)
    (hK : 3 * η * s + |(dl + dr) / 2| * (2 * s + 2) < K * s)
    {N : ℕ} (cuts : Fin (N + 2) → Fin (d.1 + d.2 + 1))
    (hcuts : p.is_first_stage_decomposition a m s cuts) :
    pathWeight ω p ≤ averageSupportingFunctional a G0 dl dr ((d.1 : ℝ), (d.2 : ℝ)) -
      ((N : ℝ) - 1) * η * s + 4 * η * s *
        (p.totalWitnessMultiplicity ω a m s η G0 dl dr K hm (by linarith) hη cuts hcuts : ℝ) +
      ∑ z ∈ p.collectedSites, max (ω z - M0) 0 := by
  obtain ⟨N', cuts', hc', capacity, time, start, disp, q, hmem, hdisj, hbound⟩ :=
    p.total_defect_disjoint_witnesses ω a ha ha1 m hm s hs η G0 dl dr K M0 hη hc hstep hK
  have hcuts' : p.is_first_stage_decomposition a m s cuts' :=
    ⟨hc'.1, hc'.2.1, hc'.2.2.1, hc'.2.2.2.2.1, hc'.2.2.2.2.2.1⟩
  obtain ⟨hN, hsame⟩ := p.first_stage_decompositions_agree hcuts hcuts'
  subst N'
  have heq : cuts' = cuts := funext fun i => (hsame i i rfl).symm
  subst cuts'
  have hcap (i : Fin (N + 1)) :
      capacity i ≤ p.stageWitnessMultiplicity ω a m s η G0 dl dr K hm (by linarith) hη
        (cuts i.castSucc) (cuts i.succ) (hcuts.2.2.1 i.castSucc_le_succ) := by
    apply p.le_stageWitnessMultiplicity_of_has_stage_witness_family
    refine ⟨fun j => time ⟨i, j⟩, fun j => start ⟨i, j⟩, fun j => disp ⟨i, j⟩,
      fun j => q ⟨i, j⟩, fun j => hmem ⟨i, j⟩, ?_⟩
    intro j j' hne
    exact hdisj ⟨i, j⟩ ⟨i, j'⟩ (fun h => hne (eq_of_heq (Sigma.mk.inj_iff.mp h).2))
  have htotal : ∑ i, capacity i ≤
      p.totalWitnessMultiplicity ω a m s η G0 dl dr K hm (by linarith) hη cuts hcuts :=
    Finset.sum_le_sum fun i _ => hcap i
  have hcast := (Nat.cast_le (α := ℝ)).mpr htotal
  have hcoeff := mul_le_mul_of_nonneg_left hcast (show 0 ≤ 4 * η * s by positivity)
  change _ ≤ averageSupportingFunctional a G0 dl dr ((d.1 : ℝ), (d.2 : ℝ)) -
    pathWeight ω p at hbound
  linarith only [hbound, hcoeff]

/-- The whole-path bounded-weight conclusion of `lem:fulldefect`. -/
theorem total_weight_le {d : ℕ × ℕ} (p : Path 0 d) (ω : Environment)
    (a : ℝ) (ha : 0 < a) (ha1 : a < 1) (m : ℕ) (hm : 0 < m) (s : ℝ) (hs : 2 ≤ s)
    (η G0 dl dr K M : ℝ) (hη : 0 < η) (hc : 2 * η ≤ (dl - dr) / 2) (hbounded : ∀ z, ω z ≤ M)
    (hstep : |G0| + |(dl + dr) / 2| + M ≤ η * s / 2)
    (hK : 3 * η * s + |(dl + dr) / 2| * (2 * s + 2) < K * s)
    {N : ℕ} (cuts : Fin (N + 2) → Fin (d.1 + d.2 + 1))
    (hcuts : p.is_first_stage_decomposition a m s cuts) :
    pathWeight ω p ≤ averageSupportingFunctional a G0 dl dr ((d.1 : ℝ), (d.2 : ℝ)) -
      ((N : ℝ) - 1) * η * s + 4 * η * s *
        (p.totalWitnessMultiplicity ω a m s η G0 dl dr K hm (by linarith) hη cuts hcuts : ℝ) := by
  have hexcess (z : Lattice) : max (ω z - M) 0 = 0 := max_eq_right (sub_nonpos.mpr (hbounded z))
  simpa only [hexcess, Finset.sum_const_zero, add_zero] using
    p.total_weight_le_with_cutoff ω a ha ha1 m hm s hs η G0 dl dr K M hη hc hstep hK cuts hcuts

/-- The whole-path inequality of `lem:multiplicity-general`.
The block set is the image of the actual itinerary, so each visited block is counted once. -/
theorem total_weight_le_with_block_excess {d : ℕ × ℕ} (p : Path 0 d) (ω : Environment)
    (a : ℝ) (ha : 0 < a) (ha1 : a < 1) (m : ℕ) (hm : 0 < m) (s : ℝ) (hs : 2 ≤ s)
    (η G0 dl dr K : ℝ) (hη : 0 < η) (hc : 2 * η ≤ (dl - dr) / 2)
    (hscale : |G0| + |(dl + dr) / 2| ≤ η * s / 4)
    (hK : 3 * η * s + |(dl + dr) / 2| * (2 * s + 2) < K * s)
    (Q : Finset Lattice) (hQ : ∀ z, z ∈ Q ↔
      0 ≤ z.1 + z.2 ∧ z.1 + z.2 ≤ 3 * (m : ℤ) ∧ |latticeTransverseCoordinate a z| ≤ 4 * s + 1)
    {N : ℕ} (cuts : Fin (N + 2) → Fin (d.1 + d.2 + 1))
    (hcuts : p.is_first_stage_decomposition a m s cuts) :
    let A := Finset.univ.image (fun i : Fin (N + 1) => p.stageBlockIndex a m s (cuts i.castSucc))
    let Z := fun b : Lattice =>
      ∑ z ∈ Q.map ⟨fun w => Path.stageBlockOrigin a m s b + w, fun _ _ h => add_left_cancel h⟩,
        max (ω z - η * s / 4) 0
    pathWeight ω p ≤ averageSupportingFunctional a G0 dl dr ((d.1 : ℝ), (d.2 : ℝ)) -
      ((N : ℝ) - 1) * η * s + 4 * η * s *
        (p.totalWitnessMultiplicity ω a m s η G0 dl dr K hm (by linarith) hη cuts hcuts : ℝ) +
      ∑ b ∈ A, Z b := by
  intro A Z
  obtain ⟨N', cuts', hc', _, hexcess⟩ :=
    Path.exists_first_stage_index_image_excess_le ω p a ha ha1 m hm s hs η Q hQ
  have hcuts' : p.is_first_stage_decomposition a m s cuts' :=
    ⟨hc'.1, hc'.2.1, hc'.2.2.1, hc'.2.2.2.2.1, hc'.2.2.2.2.2.1⟩
  obtain ⟨hN, hsame⟩ := p.first_stage_decompositions_agree hcuts hcuts'
  subst N'
  have heq : cuts' = cuts := funext fun i => (hsame i i rfl).symm
  subst cuts'
  have habove : ∑ z ∈ p.collectedSites, max (ω z - η * s / 4) 0 ≤ ∑ b ∈ A, Z b := hexcess
  exact (p.total_weight_le_with_cutoff ω a ha ha1 m hm s hs η G0 dl dr K (η * s / 4) hη hc
    (by linarith only [hscale]) hK cuts hcuts).trans (add_le_add (le_refl _) habove)

end Path

end LPPDifferentiability
