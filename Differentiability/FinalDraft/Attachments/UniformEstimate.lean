/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Differentiability.FinalDraft.Attachments.ForwardEvent
public import Differentiability.FinalDraft.Attachments.BackwardEvent
import Differentiability.Probability.HeavyAttachmentScaleParameters
import Mathlib.Tactic

/-! The uniform large-scale estimate for the prescribed nets of Lemma B.3. -/

public section

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace LPPDifferentiability

/-- At large scales a single success probability works in both directions
and for every interval and prescribed net with the same `theta`. -/
theorem exists_uniform_prescribed_attachment_events
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (p theta D eta kappa : ℝ)
    (hp : 1 < p) (hθ : 0 < theta) (hθhalf : theta ≤ 1 / 2) (hD : 1 ≤ D)
    (heta : 0 < eta) (hkappa : 0 < kappa) (hkappa16 : kappa ≤ 1 / 16)
    (hmoment : (∫⁻ x, ENNReal.ofReal ((max (-x) 0)^p) ∂μ) < ∞)
    (hkappaBudget : kappa ≤ eta / (16 * (∫ x, max (-x) 0 ∂μ) + 16)) :
    ∃ p_att : ℝ → ℝ, Tendsto p_att atTop (𝓝 1) ∧
      ∀ᶠ s : ℝ in atTop,
        0 ≤ p_att s ∧ p_att s ≤ 1 ∧
        ∀ a : ℝ, 0 < a → a < 1 → min a (1 - a) = theta →
        ∀ (I : ℤ) (lo hi : ℝ), lo ≤ hi → hi - lo ≤ D * s →
        let m := Nat.ceil (kappa * s)
        (∀ (M : ℕ) (v : Fin (M + 1) → Lattice),
          IsLevelAttachmentNet a m (I + (m : ℤ))
            (lo - a * (m : ℝ)) (hi + (1 - a) * (m : ℝ)) v →
          ∃ A : Set Environment, MeasurableSet A ∧ p_att s ≤ (environmentLaw μ).real A ∧
            ∀ ω ∈ A, ∀ u : Lattice, u.1 + u.2 = I →
              attachmentTransverse a u ∈ Icc lo hi →
              ∃ (j : Fin (M + 1)) (d : ℕ × ℕ), d.1 + d.2 = m ∧
                ∃ q : Path u d, q.vertex (Fin.last (d.1 + d.2)) = v j ∧
                  -eta * s / 4 ≤ pathWeight ω q ∧
                  |attachmentTransverse a (v j - u)| ≤ (m : ℝ)) ∧
        (∀ (M : ℕ) (v : Fin (M + 1) → Lattice),
          IsLevelAttachmentNet a m (I - (m : ℤ))
            (lo - (1 - a) * (m : ℝ)) (hi + a * (m : ℝ)) v →
          ∃ A : Set Environment, MeasurableSet A ∧ p_att s ≤ (environmentLaw μ).real A ∧
            ∀ ω ∈ A, ∀ u : Lattice, u.1 + u.2 = I →
              attachmentTransverse a u ∈ Icc lo hi →
              ∃ (j : Fin (M + 1)) (d : ℕ × ℕ), d.1 + d.2 = m ∧
                ∃ q : Path (v j) d, q.vertex (Fin.last (d.1 + d.2)) = u ∧
                  -eta * s / 4 ≤ pathWeight ω q ∧
                  |attachmentTransverse a (u - v j)| ≤ (m : ℝ)) := by
  have htheta : theta ∈ Ioo (0 : ℝ) 1 := ⟨hθ, by linarith only [hθhalf]⟩
  have hmin : min theta (1 - theta) = theta := min_eq_left (by linarith only [hθhalf])
  obtain ⟨K, hK, _, hF, hFnonneg, hcuts⟩ :=
    exists_heavy_attachment_scale_parameters μ p theta D eta kappa hp htheta hD heta
      hkappa hkappa16 hmoment hkappaBudget
  let C₁ : ℝ := ∫ x, max (-x) 0 ∂μ
  let Cₚ : ℝ := ∫ x, (max (-x) 0)^p ∂μ
  let L := 4 * K + 4
  let B := 8 * D / (min theta (1 - theta) * kappa) + 2
  let C := Cₚ * (64 * (K : ℝ) / eta)^p
  let ε := (p - 1) / (2 * p)
  let m (s : ℝ) := Nat.ceil (kappa * s)
  let T (s : ℝ) := eta * s / (64 * (K : ℝ))
  let b (s : ℝ) := s^(1 - ε)
  let t (s : ℝ) := eta * s / 16
  let F (s : ℝ) :=
    (48 * D * s^2 * (C * s^(-p))^2 + (D * s + 1 + B * ((L + 1 : ℕ) : ℝ)^2) * (C * s^(-p)) +
      (D * s + 1) * (((((2 * K + 5) * (m s + 1) : ℕ) : ℝ) * (C * s^(-p)))^K)) +
    (D * s + 1) * ((2 * (m s : ℝ) * Cₚ * (b s)^(-p))^K +
      Real.exp (-(t s)^2 / (2 * b s * (2 * C₁ * (m s : ℝ) + t s / 3))))
  change Tendsto F atTop (𝓝 0) at hF
  change ∀ s, 0 < s → 0 ≤ F s at hFnonneg
  let p_att (s : ℝ) := max 0 (1 - F s)
  have hp_att : Tendsto p_att atTop (𝓝 1) := by
    have h := (tendsto_const_nhds (x := (0 : ℝ))).max
      ((tendsto_const_nhds (x := (1 : ℝ))).sub hF)
    simpa only [sub_zero, max_eq_right (by norm_num : (0 : ℝ) ≤ 1)] using h
  refine ⟨p_att, hp_att, ?_⟩
  filter_upwards [hcuts] with s hcut
  rcases hcut with ⟨hs, _, _, hcutTube, hcutBox, _, hmS, hmass, htail, hbudget⟩
  have hspos : 0 < s := by linarith only [hs]
  have hKpos : (0 : ℝ) < K := by exact_mod_cast (show 0 < K by omega)
  have hT : 0 < T s := by dsimp only [T]; positivity
  have hb : 0 < b s := Real.rpow_pos_of_pos hspos _
  have ht : 0 < t s := by dsimp only [t]; positivity
  refine ⟨le_max_left _ _, max_le (by norm_num) (by linarith only [hFnonneg s hspos]), ?_⟩
  intro a ha ha1 hminA I lo hi hlohi hwidth
  have hBA : 8 * D / (min a (1 - a) * kappa) + 2 = B := by
    dsimp only [B]
    rw [hminA, hmin]
  have hB : 0 ≤ B := by
    dsimp only [B]
    rw [hmin]
    positivity
  have hcast : 4 * K + 5 = L + 1 := rfl
  have hFbound : attachmentFailureBound μ D s B (m s) K (T s) p (b s) (t s) ≤ F s := by
    let pT := μ.real (Iio (-(T s)))
    have hpT : 0 ≤ pT := measureReal_nonneg
    have hbound : pT ≤ C * s^(-p) := htail
    dsimp only [attachmentFailureBound, F]
    rw [show (4 * K + 5 : ℕ) = L + 1 by exact hcast]
    have hDs : 0 ≤ D * s + 1 := by positivity
    have hpair : 0 ≤ 48 * D * s^2 := by positivity
    have hbox : 0 ≤ D * s + 1 + B * ((L + 1 : ℕ) : ℝ)^2 := by positivity
    have hcount : (0 : ℝ) ≤ (((2 * K + 5) * (m s + 1) : ℕ) : ℝ) := Nat.cast_nonneg _
    exact add_le_add
      (add_le_add (add_le_add
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hpT hbound 2) hpair)
        (mul_le_mul_of_nonneg_left hbound hbox))
        (mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (mul_nonneg hcount hpT)
            (mul_le_mul_of_nonneg_left hbound hcount) K) hDs)) (le_refl _)
  have hlower : p_att s ≤ max 0 (1 - attachmentFailureBound μ D s B (m s) K
      (T s) p (b s) (t s)) := max_le_max_left _ (sub_le_sub_left hFbound 1)
  have hfloor : -eta * s / 4 ≤ -2 * C₁ * (m s : ℝ) - (K - 1 : ℕ) * T s - t s := by
    change 2 * C₁ * (m s : ℝ) + ((K - 1 : ℕ) : ℝ) * T s + t s ≤ eta * s / 4 at hbudget
    linarith only [hbudget]
  constructor
  · intro M v hnet
    obtain ⟨A, hA, hprob, hpaths⟩ :=
      exists_forward_prescribed_attachment_event μ (T s) p (b s) (t s) hp hT hmass hb ht hmoment
        a D s kappa lo hi I K M v ha ha1 hD hs hkappa hkappa16 hlohi hwidth hK hcutTube hcutBox hmS hnet
    rw [hBA] at hprob
    refine ⟨A, hA, hlower.trans hprob, ?_⟩
    intro ω hω u hu hcoord
    obtain ⟨j, d, hd, q, hend, hweight, htransverse⟩ := hpaths ω hω u hu hcoord
    exact ⟨j, d, hd, q, hend, hfloor.trans hweight, htransverse⟩
  · intro M v hnet
    obtain ⟨A, hA, hprob, hpaths⟩ :=
      exists_backward_prescribed_attachment_event μ (T s) p (b s) (t s) hp hT hmass hb ht hmoment
        a D s kappa lo hi I K M v ha ha1 hD hs hkappa hkappa16 hlohi hwidth hK hcutTube hcutBox hmS hnet
    rw [hBA] at hprob
    refine ⟨A, hA, hlower.trans hprob, ?_⟩
    intro ω hω u hu hcoord
    obtain ⟨j, d, hd, q, hend, hweight, htransverse⟩ := hpaths ω hω u hu hcoord
    exact ⟨j, d, hd, q, hend, hfloor.trans hweight, htransverse⟩

end LPPDifferentiability
