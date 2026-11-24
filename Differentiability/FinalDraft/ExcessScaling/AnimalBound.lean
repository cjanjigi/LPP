/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Differentiability.Probability.ExcessAnimalBound
public import Differentiability.FinalDraft.ExcessScaling.BlockTail
import Mathlib.Tactic

/-! Excess over the source's connected block sets at general aspect ratios. -/

public section

open MeasureTheory Filter Set
open scoped Topology BigOperators ENNReal

namespace LPPDifferentiability

/-- The enlarged source block in the Appendix B one-step bound, equation `eq:Bprime`, has at most
`44 * s ^ (1 + γ)` sites when its length parameter is at most `s ^ γ`. -/
theorem exists_excess_block_base_of_aspect_ratio (a s γ : ℝ) (m : ℕ)
    (hs : 3 ≤ s) (hm : 1 ≤ m) (hms : (m : ℝ) ≤ s ^ γ) :
    ∃ Q : Finset Lattice,
      (∀ z, z ∈ Q ↔ 0 ≤ z.1 + z.2 ∧ z.1 + z.2 ≤ 3 * (m : ℤ) ∧
        |(1 - a) * (z.1 : ℝ) - a * (z.2 : ℝ)| ≤ 4 * s + 1) ∧
      (Q.card : ℝ) ≤ (3 * (m : ℝ) + 1) * (8 * s + 3) ∧
      (3 * (m : ℝ) + 1) * (8 * s + 3) ≤ 44 * s ^ (1 + γ) := by
  obtain ⟨Q, hQ, hcard⟩ := exists_finset_signed_level_tube a (4 * s + 1)
    (fun _ => 0) 0 (3 * m) (by linarith only [hs])
  refine ⟨Q, ?_, ?_, ?_⟩
  · intro z
    simpa only [zero_add, Nat.cast_mul, Nat.cast_ofNat, sub_zero] using hQ z
  · convert hcard using 1
    push_cast
    ring
  · have hs0 : 0 < s := by linarith only [hs]
    have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
    have hlen : 3 * (m : ℝ) + 1 ≤ 4 * s ^ γ := by linarith only [hm1, hms]
    have hwidth : 8 * s + 3 ≤ 11 * s := by linarith only [hs]
    calc
      _ ≤ (4 * s ^ γ) * (11 * s) := mul_le_mul hlen hwidth (by positivity) (by positivity)
      _ = _ := by rw [Real.rpow_add hs0, Real.rpow_one]; ring

/-- The actual block excess in subsection `sub:ub_mom-chat` has the two-power bound uniformly over
all admissible animals, with the same rooted radius-two animals and environment
as in Lemma `lem:excess` and its tail estimate. This applies when the block length parameter is
`m ≤ ℓ ≤ s ^ γ`. The constant is independent of the block, the direction, the
scale and the animal. -/
theorem exists_excess_animal_bound_of_aspect_ratio
    (μ : Measure ℝ) [IsProbabilityMeasure μ] {p η : ℝ}
    (hp : 2 < p) (hη : 0 < η)
    (hmoment : (∫⁻ x, ENNReal.ofReal ((max x 0) ^ p) ∂μ) < ∞) :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ (a s γ : ℝ), 3 ≤ s → ∀ m : ℕ,
      1 ≤ m → (m : ℝ) ≤ s ^ γ → ∃ Q : Finset Lattice,
      (∀ z, z ∈ Q ↔ 0 ≤ z.1 + z.2 ∧ z.1 + z.2 ≤ 3 * (m : ℤ) ∧
        |(1 - a) * (z.1 : ℝ) - a * (z.2 : ℝ)| ≤ 4 * s + 1) ∧
      (Q.card : ℝ) ≤ (3 * (m : ℝ) + 1) * (8 * s + 3) ∧
      (3 * (m : ℝ) + 1) * (8 * s + 3) ≤ 44 * s ^ (1 + γ) ∧
      ∀ᵐ ω ∂environmentLaw μ,
        let v : Lattice → Lattice := fun b =>
          let j : ℤ := ⌊(b.2 : ℝ) * s + a * ((b.1 * m : ℤ) : ℝ)⌋
          (j, b.1 * m - j)
        let Z : Lattice → ℝ := fun b =>
          ∑ z ∈ Q.map ⟨fun w => v b + w, fun _ _ h => add_left_cancel h⟩,
            max (ω z - η * s / 4) 0
        (limsup (fun N : ℕ =>
          ⨆ A : {A : Finset Lattice // (0 : Lattice) ∈ A ∧ A.card ≤ N + 1 ∧
            ((SimpleGraph.fromRel (fun x y : Lattice =>
              |x.1 - y.1| ≤ 2 ∧ |x.2 - y.2| ≤ 2)).induce (↑A : Set Lattice)).Connected},
            (((∑ b ∈ A.val, Z b) / (N : ℝ) : ℝ) : EReal)) atTop ≤
              ((C₀ * (s ^ ((1 + γ) / p) + s ^ (2 + γ - p)) : ℝ) : EReal)) ∧
        ∀ᶠ N : ℕ in atTop,
          ∀ A : Finset Lattice, (0 : Lattice) ∈ A → A.card ≤ N + 1 →
            ((SimpleGraph.fromRel (fun x y : Lattice =>
              |x.1 - y.1| ≤ 2 ∧ |x.2 - y.2| ≤ 2)).induce (↑A : Set Lattice)).Connected →
            (∑ b ∈ A, Z b) ≤ C₀ * (N : ℝ) * (s ^ ((1 + γ) / p) + s ^ (2 + γ - p)) := by
  classical
  obtain ⟨C, hC, hclass⟩ := exists_excess_class_eventually_bound
  obtain ⟨K, hK, htail⟩ := exists_excess_sum_integrated_sqrt_tail_bound_of_aspect_ratio
    μ hp hη hmoment
  refine ⟨160 * C * K, by positivity, ?_⟩
  intro a s γ hs m hm hms
  obtain ⟨Q, hQ, hcard, hcardBound⟩ := exists_excess_block_base_of_aspect_ratio a s γ m hs hm hms
  refine ⟨Q, hQ, hcard, hcardBound, ?_⟩
  let F : ℝ := s ^ ((1 + γ) / p) + s ^ (2 + γ - p)
  let M : ℝ := η * s / 4
  let T : ℝ≥0∞ := ∫⁻ t in Ioi (0 : ℝ), (environmentLaw μ)
    {ω : Environment | t < ∑ z ∈ Q, max (ω z - M) 0} ^ (1 / 2 : ℝ)
  have hs0 : 0 < s := by linarith only [hs]
  have hF : 0 < F := by dsimp [F]; positivity
  have htailBound : T ≤ ENNReal.ofReal (K * F) := htail γ s hs Q (hcard.trans hcardBound)
  have htailFinite : T < ∞ := htailBound.trans_lt ENNReal.ofReal_lt_top
  have htailReal : T.toReal ≤ K * F := by
    have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top htailBound
    simpa only [ENNReal.toReal_ofReal (mul_nonneg hK.le hF.le)] using h

  -- The residue-class estimate controls all of the admissible animals on
  -- one event for each of the forty signed classes.
  let v : Lattice → Lattice := fun b =>
    let j : ℤ := ⌊(b.2 : ℝ) * s + a * ((b.1 * m : ℤ) : ℝ)⌋
    (j, b.1 * m - j)
  let Z (ω : Environment) (b : Lattice) : ℝ :=
    ∑ z ∈ Q.map ⟨fun w => v b + w, fun _ _ h => add_left_cancel h⟩, max (ω z - M) 0
  have hclasses : ∀ r : Fin 4 × Fin 10, ∀ᵐ ω ∂environmentLaw μ,
      ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
        ∀ A : Finset Lattice, (0 : Lattice) ∈ A → A.card ≤ N + 1 →
          ((SimpleGraph.fromRel (fun x y : Lattice =>
            |x.1 - y.1| ≤ 2 ∧ |x.2 - y.2| ≤ 2)).induce (↑A : Set Lattice)).Connected →
          (∑ b ∈ A.filter (fun b => b.1 % 4 = (r.1.val : ℤ) ∧
            b.2 % 10 = (r.2.val : ℤ)), Z ω b) / (N : ℝ) < 2 * C * T.toReal + ε :=
    fun r => hclass μ a s M m Q hQ hs hm htailFinite r.1 r.2
  filter_upwards [ae_all_iff.mpr hclasses] with ω hω
  let B : ℝ := 80 * C * K * F

  -- Sum the residue-class bounds using the exact partition of the animal.
  have huniform : ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
      ∀ A : Finset Lattice, (0 : Lattice) ∈ A → A.card ≤ N + 1 →
        ((SimpleGraph.fromRel (fun x y : Lattice =>
          |x.1 - y.1| ≤ 2 ∧ |x.2 - y.2| ≤ 2)).induce (↑A : Set Lattice)).Connected →
        (∑ b ∈ A, Z ω b) / (N : ℝ) < B + ε := by
    intro ε hε
    have hεsmall : 0 < ε / 80 := by positivity
    have hfiniteClasses : ∀ᶠ N : ℕ in atTop, ∀ r : Fin 4 × Fin 10,
        ∀ A : Finset Lattice, (0 : Lattice) ∈ A → A.card ≤ N + 1 →
          ((SimpleGraph.fromRel (fun x y : Lattice =>
            |x.1 - y.1| ≤ 2 ∧ |x.2 - y.2| ≤ 2)).induce (↑A : Set Lattice)).Connected →
          (∑ b ∈ A.filter (fun b => b.1 % 4 = (r.1.val : ℤ) ∧
            b.2 % 10 = (r.2.val : ℤ)), Z ω b) / (N : ℝ) < 2 * C * T.toReal + ε / 80 :=
      eventually_all.mpr fun r => hω r (ε / 80) hεsmall
    filter_upwards [hfiniteClasses] with N hN
    intro A hzero hsize hconn
    have hsum := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin 4 × Fin 10)))
      (fun r _ => (hN r A hzero hsize hconn).le)
    rw [← Finset.sum_div, sum_excess_residue_classes] at hsum
    have hcount : (∑ _r : Fin 4 × Fin 10, (2 * C * T.toReal + ε / 80)) =
        80 * C * T.toReal + ε / 2 := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod,
        Fintype.card_fin, Nat.reduceMul, nsmul_eq_mul]
      ring
    rw [hcount] at hsum
    have hscaled : 80 * C * T.toReal ≤ B := by
      calc
        _ ≤ 80 * C * (K * F) := mul_le_mul_of_nonneg_left htailReal (by positivity)
        _ = _ := by dsimp [B]; ring
    linarith only [hsum, hscaled, hε]

  -- Doubling the limsup bound gives one constant for the eventual sum bound.
  have hB : 0 < B := by dsimp [B]; positivity
  have hCeq : 160 * C * K * F = B + B := by dsimp [B]; ring
  change (_ ≤ ((160 * C * K * F : ℝ) : EReal)) ∧ _
  constructor
  · have hlim := (limsup_iSup_radiusTwoAnimal_le_iff (Z ω) B).mpr huniform
    exact hlim.trans (EReal.coe_le_coe_iff.mpr (by rw [hCeq]; linarith only [hB]))
  · filter_upwards [huniform B hB, eventually_ge_atTop (1 : ℕ)] with N hN hN1
    intro A hzero hcardA hconn
    have hN0 : 0 < (N : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hN1)
    have hle := (div_lt_iff₀ hN0).mp (hN A hzero hcardA hconn)
    change (∑ b ∈ A, Z ω b) ≤ 160 * C * K * (N : ℝ) * F
    calc
      _ ≤ (B + B) * (N : ℝ) := hle.le
      _ = _ := by rw [← hCeq]; ring

end LPPDifferentiability
