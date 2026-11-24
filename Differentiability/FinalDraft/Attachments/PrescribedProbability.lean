/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Differentiability.FinalDraft.Attachments.Net
public import LPP_Foundations.Statements.ShapeDefinitions
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Differentiability.FinalDraft.Attachments.UniformEstimate
import Mathlib.Tactic

/-! The all-scale attachment estimate for the prescribed nets in the final draft. -/

public section

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace LPPDifferentiability

private theorem attachment_disp_length {u v : Lattice} {d : ℕ × ℕ} {m : ℕ}
    (hend : u + ((d.1 : ℤ), (d.2 : ℤ)) = v) (hlen : d.1 + d.2 = m) :
    |(v - u).1| + |(v - u).2| = (m : ℤ) := by
  rw [← hend]
  have heq : u + ((d.1 : ℤ), (d.2 : ℤ)) - u = ((d.1 : ℤ), (d.2 : ℤ)) := by abel
  rw [heq]
  change |(d.1 : ℤ)| + |(d.2 : ℤ)| = (m : ℤ)
  rw [abs_of_nonneg (Int.natCast_nonneg _), abs_of_nonneg (Int.natCast_nonneg _)]
  omega

/-- For every prescribed net above or below a level interval, a single
probability bound tending to one guarantees a path with the required weight
and displacement from each interval site. See the final draft,
Lemma `lem:attach-general`. -/
theorem prescribed_attachment_probability
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (_hpos : LPPStatements.HasSqrtUpperTail μ) (hneg : LPPStatements.HasNegativePartMomentAbove μ 1)
    (theta D eta kappa : ℝ)
    (hθ : 0 < theta) (hθhalf : theta ≤ 1 / 2) (hD : 1 ≤ D)
    (heta : 0 < eta) (hkappa : 0 < kappa) (hkappa16 : kappa ≤ 1 / 16)
    (hkappaBudget : kappa ≤ eta / (16 * (∫ x, max (-x) 0 ∂μ) + 16)) :
    ∃ p_att : ℝ → ℝ, Tendsto p_att atTop (𝓝 1) ∧
      ∀ (s : ℝ), 4 ≤ s →
        0 ≤ p_att s ∧ p_att s ≤ 1 ∧
        ∀ a : ℝ, 0 < a → a < 1 → min a (1 - a) = theta →
        ∀ (I : ℤ) (lo hi : ℝ), lo ≤ hi → hi - lo ≤ D * s →
        let m := Nat.ceil (kappa * s)
        (∀ N : Finset Lattice,
          (∃ (M : ℕ) (v : Fin (M + 1) → Lattice), Finset.univ.image v = N ∧
            IsLevelAttachmentNet a m (I + (m : ℤ))
              (lo - a * (m : ℝ)) (hi + (1 - a) * (m : ℝ)) v) →
          ∃ A : Set Environment, MeasurableSet A ∧ p_att s ≤ (environmentLaw μ).real A ∧
            ∀ ω ∈ A, ∀ u : Lattice, u.1 + u.2 = I →
              attachmentTransverse a u ∈ Icc lo hi →
              ∃ v ∈ N, ∃ (d : ℕ × ℕ) (q : Path u d),
                q.vertex (Fin.last (d.1 + d.2)) = v ∧ -eta * s / 4 ≤ pathWeight ω q ∧
                |(v - u).1| + |(v - u).2| = (m : ℤ) ∧
                |attachmentTransverse a (v - u)| ≤ (m : ℝ)) ∧
        (∀ N : Finset Lattice,
          (∃ (M : ℕ) (v : Fin (M + 1) → Lattice), Finset.univ.image v = N ∧
            IsLevelAttachmentNet a m (I - (m : ℤ))
              (lo - (1 - a) * (m : ℝ)) (hi + a * (m : ℝ)) v) →
          ∃ A : Set Environment, MeasurableSet A ∧ p_att s ≤ (environmentLaw μ).real A ∧
            ∀ ω ∈ A, ∀ u : Lattice, u.1 + u.2 = I →
              attachmentTransverse a u ∈ Icc lo hi →
              ∃ v ∈ N, ∃ (d : ℕ × ℕ) (q : Path v d),
                q.vertex (Fin.last (d.1 + d.2)) = u ∧ -eta * s / 4 ≤ pathWeight ω q ∧
                |(u - v).1| + |(u - v).2| = (m : ℤ) ∧
                |attachmentTransverse a (u - v)| ≤ (m : ℝ)) := by
  classical
  rcases hneg with ⟨p, hp, hmoment⟩
  obtain ⟨p_att, hp_att, hlarge⟩ := exists_uniform_prescribed_attachment_events
    μ p theta D eta kappa hp hθ hθhalf hD heta hkappa hkappa16 hmoment hkappaBudget
  obtain ⟨S, hS⟩ := eventually_atTop.mp hlarge
  -- Below the common cutoff the source uses probability zero.
  let P (s : ℝ) := if S ≤ s then p_att s else 0
  have hP : Tendsto P atTop (𝓝 1) :=
    hp_att.congr' ((eventually_ge_atTop S).mono fun s hs => (ite_eq_left hs).symm)
  refine ⟨P, hP, ?_⟩
  intro s _hs
  by_cases h : S ≤ s
  · have hbig := hS s h
    refine ⟨by simpa only [P, ite_eq_left h] using hbig.1,
      by simpa only [P, ite_eq_left h] using hbig.2.1, ?_⟩
    intro a ha ha1 htheta I lo hi hlohi hwidth
    have hpaths := hbig.2.2 a ha ha1 htheta I lo hi hlohi hwidth
    constructor
    · rintro N ⟨M, v, rfl, hnet⟩
      obtain ⟨A, hA, hprob, hp⟩ := hpaths.1 M v hnet
      refine ⟨A, hA, by simpa only [P, ite_eq_left h] using hprob, ?_⟩
      intro ω hω u hu hcoord
      obtain ⟨j, d, hd, q, hend, hw, hr⟩ := hp ω hω u hu hcoord
      exact ⟨v j, Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩,
        d, q, hend, hw, attachment_disp_length (q.finish.symm.trans hend) hd, hr⟩
    · rintro N ⟨M, v, rfl, hnet⟩
      obtain ⟨A, hA, hprob, hp⟩ := hpaths.2 M v hnet
      refine ⟨A, hA, by simpa only [P, ite_eq_left h] using hprob, ?_⟩
      intro ω hω u hu hcoord
      obtain ⟨j, d, hd, q, hend, hw, hr⟩ := hp ω hω u hu hcoord
      exact ⟨v j, Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩,
        d, q, hend, hw, attachment_disp_length (q.finish.symm.trans hend) hd, hr⟩
  · refine ⟨by simp only [P, ite_eq_right h, le_refl], by simp only [P, ite_eq_right h, zero_le_one], ?_⟩
    intro a ha ha1 ht I lo hi hlohi hwidth
    constructor
    · intro N _hnet
      exact ⟨∅, MeasurableSet.empty, by simp only [P, ite_eq_right h, measureReal_empty, le_refl],
        fun _ hω => hω.elim⟩
    · intro N _hnet
      exact ⟨∅, MeasurableSet.empty, by simp only [P, ite_eq_right h, measureReal_empty, le_refl],
        fun _ hω => hω.elim⟩

end LPPDifferentiability
