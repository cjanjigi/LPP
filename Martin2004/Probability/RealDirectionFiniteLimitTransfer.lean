/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Martin2004.Probability.RandomPhaseLiggett
import Mathlib.Tactic

/-!
# Real direction, finite case: transfer from a random phase to phase 0

Martin (2004), Proposition 2.1 gives no argument for directions whose multiples have changing
fractional parts. Here a limit is taken at a random phase and then transferred back to phase 0 by a
bounded comparison. This file holds the transfer step.

* The phase entries `T(⌊n x + θ⌋)` are integrable on the product of the phase law and the
  environment law, and a phase in the unit square lies in the square almost surely.
* The pathwise floor sandwich of `FloorPhaseSandwich`, with the box maximum replaced by the box
  sum of absolute weights. Its mean does not depend on the site.
* If `T(⌊n x + θ⌋)/n` converges almost surely at one phase, so does `T(⌊n x⌋)/n`, to the same limit.
* If `T(⌊n x + θ⌋)/n` converges to a constant `c` in L1 on the product space, then
  `T(⌊n x⌋)/n` converges to `c` in L1.
-/

public section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology

namespace LPPDifferentiability

/-- Almost every phase of the uniform law on the unit square lies in the square. Used by every
step that needs `0 ≤ θ < 1`. -/
theorem ae_phase_in_unit_square :
    ∀ᵐ θ ∂((volume.restrict (Ico (0 : ℝ) 1)).prod (volume.restrict (Ico (0 : ℝ) 1))),
      θ.1 ∈ Ico (0 : ℝ) 1 ∧ θ.2 ∈ Ico (0 : ℝ) 1 := by
  have hU : ∀ᵐ t ∂(volume.restrict (Ico (0 : ℝ) 1)), t ∈ Ico (0 : ℝ) 1 :=
    ae_restrict_mem measurableSet_Ico
  exact (measurePreserving_fst.quasiMeasurePreserving.ae hU).and
    (measurePreserving_snd.quasiMeasurePreserving.ae hU)

/-- Step count for the floor sandwich. For a direction `x` in the closed quadrant there are naturals
`j ≥ 1` and `D` with `j x_i ≥ 1` wherever `x_i > 0` and `j x_i ≤ D`. -/
theorem exists_floor_step_count (x : ℝ × ℝ) (hx1 : 0 ≤ x.1) (hx2 : 0 ≤ x.2) :
    ∃ j D : ℕ, 0 < j ∧ (x.1 = 0 ∨ 1 ≤ (j : ℝ) * x.1) ∧ (x.2 = 0 ∨ 1 ≤ (j : ℝ) * x.2) ∧
      (j : ℝ) * x.1 ≤ D ∧ (j : ℝ) * x.2 ≤ D := by
  obtain ⟨k1, hk1⟩ := exists_nat_ge (1 / x.1)
  obtain ⟨k2, hk2⟩ := exists_nat_ge (1 / x.2)
  have hstep (y : ℝ) (hy : 0 ≤ y) (k j : ℕ) (hk : 1 / y ≤ k) (hkj : k ≤ j) :
      y = 0 ∨ 1 ≤ (j : ℝ) * y := by
    rcases hy.eq_or_lt with h0 | hpos
    · exact Or.inl h0.symm
    · refine Or.inr ?_
      have h1 : 1 ≤ (k : ℝ) * y := by
        have := (div_le_iff₀ hpos).mp hk
        linarith
      exact h1.trans (mul_le_mul_of_nonneg_right (by exact_mod_cast hkj) hy)
  obtain ⟨D, hD⟩ := exists_nat_ge (((k1 + k2 + 1 : ℕ) : ℝ) * x.1 + ((k1 + k2 + 1 : ℕ) : ℝ) * x.2)
  have hj1 : 0 ≤ ((k1 + k2 + 1 : ℕ) : ℝ) * x.1 := mul_nonneg (Nat.cast_nonneg _) hx1
  have hj2 : 0 ≤ ((k1 + k2 + 1 : ℕ) : ℝ) * x.2 := mul_nonneg (Nat.cast_nonneg _) hx2
  exact ⟨k1 + k2 + 1, D, Nat.succ_pos _, hstep x.1 hx1 k1 _ hk1 (by omega),
    hstep x.2 hx2 k2 _ hk2 (by omega), by linarith, by linarith⟩

/-- Each phase entry `ω ↦ T(0, ⌊n x + θ⌋)` is integrable on the product of the phase law and the
environment law. It is measurable because the endpoint takes countably many values, and it is
dominated by a phase-independent sum of absolute weights over a box. -/
theorem integrable_phase_passage (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : Integrable (fun t : ℝ => t) μ) (x : ℝ × ℝ) (hx1 : 0 ≤ x.1) (hx2 : 0 ≤ x.2) (n : ℕ) :
    Integrable (fun p : (ℝ × ℝ) × Environment => lastPassage p.2 0
        (⌊(n : ℝ) * x.1 + p.1.1⌋₊, ⌊(n : ℝ) * x.2 + p.1.2⌋₊))
      (((volume.restrict (Ico (0 : ℝ) 1)).prod (volume.restrict (Ico (0 : ℝ) 1))).prod
        (environmentLaw μ)) := by
  have hF : Measurable
      (fun q : (ℕ × ℕ) × Environment => lastPassage q.2 0 q.1) :=
    measurable_from_prod_countable_right fun e => measurable_lastPassage 0 e
  have hend : Measurable (fun p : (ℝ × ℝ) × Environment =>
      (⌊(n : ℝ) * x.1 + p.1.1⌋₊, ⌊(n : ℝ) * x.2 + p.1.2⌋₊)) :=
    ((Nat.measurable_floor.comp ((measurable_fst.comp measurable_fst).const_add _)).prodMk
      (Nat.measurable_floor.comp ((measurable_snd.comp measurable_fst).const_add _)))
  have hmeas := hF.comp (hend.prodMk measurable_snd)
  set N : ℕ × ℕ := (⌊(n : ℝ) * x.1⌋₊ + 1, ⌊(n : ℝ) * x.2⌋₊ + 1) with hN
  set G : Environment → ℝ := fun ω => ((N.1 + N.2 : ℕ) : ℝ) *
    ∑ z ∈ Finset.Icc ((0 : ℤ), (0 : ℤ)) ((N.1 : ℤ), (N.2 : ℤ)), |ω z| with hG
  have hGi : Integrable G (environmentLaw μ) :=
    (integrable_finsetSum _ fun z _ => (integrable_environment_eval μ hμ z).abs).const_mul _
  have hGP : Integrable (fun p : (ℝ × ℝ) × Environment => G p.2)
      (((volume.restrict (Ico (0 : ℝ) 1)).prod (volume.restrict (Ico (0 : ℝ) 1))).prod
        (environmentLaw μ)) :=
    hGi.comp_snd _
  refine hGP.mono' hmeas.aestronglyMeasurable ?_
  filter_upwards [measurePreserving_fst.quasiMeasurePreserving.ae ae_phase_in_unit_square] with p hp
  rw [Real.norm_eq_abs]
  exact abs_lastPassage_le_box_sum p.2 _ N
    (floor_add_phase_le_floor_add_one _ _ (mul_nonneg (Nat.cast_nonneg _) hx1) hp.1.2)
    (floor_add_phase_le_floor_add_one _ _ (mul_nonneg (Nat.cast_nonneg _) hx2) hp.2.2)


/-- The pathwise sandwich, with the box maximum replaced by the sum `S` of the absolute weights over
the offsets `{-D..1}²` around `b = ⌊(m + j) x⌋`. For every phase `θ` in the unit square,
`T(⌊m x + θ⌋) - 2 D S ≤ T(⌊(m + j) x⌋) ≤ T(⌊(m + j) x + θ⌋) + 2 S`. It is
`lastPassage_phase_sandwich` with `M = S`. -/
theorem lastPassage_phase_sandwich_box_sum (ω : Environment) (x θ : ℝ × ℝ) (j m D : ℕ)
    (S : ℝ)
    (hS : S = ∑ o ∈ Finset.Icc ((-(D : ℤ)), (-(D : ℤ))) ((1 : ℤ), (1 : ℤ)),
      |ω (((⌊((m + j : ℕ) : ℝ) * x.1⌋₊ : ℤ), (⌊((m + j : ℕ) : ℝ) * x.2⌋₊ : ℤ)) + o)|)
    (hx1 : 0 ≤ x.1) (hx2 : 0 ≤ x.2)
    (hθ1 : 0 ≤ θ.1 ∧ θ.1 < 1) (hθ2 : 0 ≤ θ.2 ∧ θ.2 < 1)
    (hj1 : x.1 = 0 ∨ 1 ≤ (j : ℝ) * x.1) (hj2 : x.2 = 0 ∨ 1 ≤ (j : ℝ) * x.2)
    (hD1 : (j : ℝ) * x.1 ≤ D) (hD2 : (j : ℝ) * x.2 ≤ D) :
    lastPassage ω 0 (⌊(m : ℝ) * x.1 + θ.1⌋₊, ⌊(m : ℝ) * x.2 + θ.2⌋₊) - 2 * D * S ≤
        lastPassage ω 0 (⌊((m + j : ℕ) : ℝ) * x.1⌋₊, ⌊((m + j : ℕ) : ℝ) * x.2⌋₊) ∧
      lastPassage ω 0 (⌊((m + j : ℕ) : ℝ) * x.1⌋₊, ⌊((m + j : ℕ) : ℝ) * x.2⌋₊) ≤
        lastPassage ω 0 (⌊((m + j : ℕ) : ℝ) * x.1 + θ.1⌋₊,
          ⌊((m + j : ℕ) : ℝ) * x.2 + θ.2⌋₊) + 2 * S := by
  set b : Lattice := ((⌊((m + j : ℕ) : ℝ) * x.1⌋₊ : ℤ), (⌊((m + j : ℕ) : ℝ) * x.2⌋₊ : ℤ)) with hb
  refine lastPassage_phase_sandwich ω x θ j m D S b hb hx1 hx2 hθ1 hθ2 hj1 hj2 hD1 hD2 ?_
  intro z h1 h2 h3 h4
  have hmem : z - b ∈ Finset.Icc ((-(D : ℤ)), (-(D : ℤ))) ((1 : ℤ), (1 : ℤ)) := by
    rw [Finset.mem_Icc, Prod.le_def, Prod.le_def]
    simp only [Prod.fst_sub, Prod.snd_sub]
    omega
  have h := Finset.single_le_sum (f := fun o => |ω (b + o)|) (fun _ _ => abs_nonneg _) hmem
  rw [add_sub_cancel] at h
  rw [hS]
  exact h


/-- Box sums of absolute weights around the points `⌊n x⌋` are sublinear almost surely. It follows
from `ae_box_max_div_tendsto_zero`, since the sum is at most the number of offsets times the
maximum. -/
theorem ae_box_sum_div_tendsto_zero (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : Integrable (fun t : ℝ => t) μ) (x : ℝ × ℝ) (A B : ℕ) :
    ∀ᵐ ω ∂environmentLaw μ,
      Tendsto (fun n : ℕ => (∑ o ∈ Finset.Icc ((-(A : ℤ)), (-(A : ℤ))) ((B : ℤ), (B : ℤ)),
        |ω (((⌊(n : ℝ) * x.1⌋₊ : ℤ), (⌊(n : ℝ) * x.2⌋₊ : ℤ)) + o)|) / (n : ℝ))
        atTop (𝓝 0) := by
  have hO : (Finset.Icc ((-(A : ℤ)), (-(A : ℤ))) ((B : ℤ), (B : ℤ))).Nonempty :=
    ⟨0, by
      rw [Finset.mem_Icc, Prod.le_def, Prod.le_def]
      simp only [Prod.fst_zero, Prod.snd_zero, neg_nonpos]
      exact ⟨⟨Int.natCast_nonneg _, Int.natCast_nonneg _⟩, Int.natCast_nonneg _, Int.natCast_nonneg _⟩⟩
  have hmax := ae_box_max_div_tendsto_zero μ hμ
    (fun n => ((⌊(n : ℝ) * x.1⌋₊ : ℤ), (⌊(n : ℝ) * x.2⌋₊ : ℤ))) _ hO
  filter_upwards [hmax] with ω hω
  have hc := hω.const_mul
    ((Finset.Icc ((-(A : ℤ)), (-(A : ℤ))) ((B : ℤ), (B : ℤ))).card : ℝ)
  rw [mul_zero] at hc
  refine squeeze_zero (fun n => ?_) (fun n => ?_) hc
  · exact div_nonneg (Finset.sum_nonneg fun _ _ => abs_nonneg _) (Nat.cast_nonneg n)
  · rw [← mul_div_assoc]
    refine div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg n)
    have := Finset.sum_le_card_nsmul
      (Finset.Icc ((-(A : ℤ)), (-(A : ℤ))) ((B : ℤ), (B : ℤ)))
      (fun o => |ω (((⌊(n : ℝ) * x.1⌋₊ : ℤ), (⌊(n : ℝ) * x.2⌋₊ : ℤ)) + o)|)
      ((Finset.Icc ((-(A : ℤ)), (-(A : ℤ))) ((B : ℤ), (B : ℤ))).sup' hO
        (fun o => |ω (((⌊(n : ℝ) * x.1⌋₊ : ℤ), (⌊(n : ℝ) * x.2⌋₊ : ℤ)) + o)|))
      (fun o ho => Finset.le_sup' (fun o => |ω (((⌊(n : ℝ) * x.1⌋₊ : ℤ),
        (⌊(n : ℝ) * x.2⌋₊ : ℤ)) + o)|) ho)
    simpa [nsmul_eq_mul] using this

/-- Transfer from a random phase to phase 0, almost-sure part. If at one phase `θ` in the unit
square `T(⌊n x + θ⌋)/n` tends to `y(ω)` for almost every environment `ω`, then `T(⌊n x⌋)/n` tends to
the same `y(ω)` almost surely. Index shift `n = m + j` and the sandwich. -/
theorem ae_tendsto_floor_of_phase_tendsto (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : Integrable (fun t : ℝ => t) μ) (x : ℝ × ℝ) (hx1 : 0 ≤ x.1) (hx2 : 0 ≤ x.2)
    (θ : ℝ × ℝ) (hθ1 : θ.1 ∈ Ico (0 : ℝ) 1) (hθ2 : θ.2 ∈ Ico (0 : ℝ) 1)
    (y : Environment → ℝ)
    (h : ∀ᵐ ω ∂environmentLaw μ,
      Tendsto (fun n : ℕ => lastPassage ω 0
        (⌊(n : ℝ) * x.1 + θ.1⌋₊, ⌊(n : ℝ) * x.2 + θ.2⌋₊) / (n : ℝ)) atTop (𝓝 (y ω))) :
    ∀ᵐ ω ∂environmentLaw μ,
      Tendsto (fun n : ℕ => lastPassage ω 0 (⌊(n : ℝ) * x.1⌋₊, ⌊(n : ℝ) * x.2⌋₊) / (n : ℝ))
        atTop (𝓝 (y ω)) := by
  obtain ⟨j, D, hj, hj1, hj2, hD1, hD2⟩ := exists_floor_step_count x hx1 hx2
  filter_upwards [h, ae_box_sum_div_tendsto_zero μ hμ x D 1] with ω hω hS
  have hjpos : (0 : ℝ) < j := by exact_mod_cast hj
  -- the three sequences, shifted by `j`
  have hX0 : Tendsto (fun m : ℕ => lastPassage ω 0
      (⌊(m : ℝ) * x.1 + θ.1⌋₊, ⌊(m : ℝ) * x.2 + θ.2⌋₊) / (m : ℝ)) atTop (𝓝 (y ω)) := hω
  have hXj : Tendsto (fun m : ℕ => lastPassage ω 0
      (⌊((m + j : ℕ) : ℝ) * x.1 + θ.1⌋₊, ⌊((m + j : ℕ) : ℝ) * x.2 + θ.2⌋₊) /
        ((m + j : ℕ) : ℝ)) atTop (𝓝 (y ω)) :=
    (tendsto_add_atTop_iff_nat (f := fun n : ℕ => lastPassage ω 0
      (⌊(n : ℝ) * x.1 + θ.1⌋₊, ⌊(n : ℝ) * x.2 + θ.2⌋₊) / (n : ℝ)) j).mpr hω
  have hSj : Tendsto (fun m : ℕ => (∑ o ∈ Finset.Icc ((-(D : ℤ)), (-(D : ℤ))) ((1 : ℤ), (1 : ℤ)),
      |ω (((⌊((m + j : ℕ) : ℝ) * x.1⌋₊ : ℤ), (⌊((m + j : ℕ) : ℝ) * x.2⌋₊ : ℤ)) + o)|) /
        ((m + j : ℕ) : ℝ)) atTop (𝓝 0) :=
    (tendsto_add_atTop_iff_nat (f := fun n : ℕ => (∑ o ∈ Finset.Icc ((-(D : ℤ)), (-(D : ℤ)))
      ((1 : ℤ), (1 : ℤ)),
      |ω (((⌊(n : ℝ) * x.1⌋₊ : ℤ), (⌊(n : ℝ) * x.2⌋₊ : ℤ)) + o)|) / (n : ℝ)) j).mpr hS
  have hratio : Tendsto (fun m : ℕ => (m : ℝ) / ((m + j : ℕ) : ℝ)) atTop (𝓝 1) := by
    have := tendsto_natCast_div_add_atTop (𝕜 := ℝ) (j : ℝ)
    simpa using this
  have hl : Tendsto (fun m : ℕ => (lastPassage ω 0
      (⌊(m : ℝ) * x.1 + θ.1⌋₊, ⌊(m : ℝ) * x.2 + θ.2⌋₊) - 2 * D *
        (∑ o ∈ Finset.Icc ((-(D : ℤ)), (-(D : ℤ))) ((1 : ℤ), (1 : ℤ)),
      |ω (((⌊((m + j : ℕ) : ℝ) * x.1⌋₊ : ℤ), (⌊((m + j : ℕ) : ℝ) * x.2⌋₊ : ℤ)) + o)|)) /
        ((m + j : ℕ) : ℝ)) atTop (𝓝 (y ω)) := by
    have h1 := (hX0.mul hratio).sub (hSj.const_mul (2 * (D : ℝ)))
    rw [mul_one, mul_zero, sub_zero] at h1
    refine h1.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with m hm
    have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
    have hN : ((m + j : ℕ) : ℝ) ≠ 0 := by positivity
    field_simp
  have hr : Tendsto (fun m : ℕ => lastPassage ω 0
      (⌊((m + j : ℕ) : ℝ) * x.1 + θ.1⌋₊, ⌊((m + j : ℕ) : ℝ) * x.2 + θ.2⌋₊) /
        ((m + j : ℕ) : ℝ) + 2 * ((∑ o ∈ Finset.Icc ((-(D : ℤ)), (-(D : ℤ))) ((1 : ℤ), (1 : ℤ)),
      |ω (((⌊((m + j : ℕ) : ℝ) * x.1⌋₊ : ℤ), (⌊((m + j : ℕ) : ℝ) * x.2⌋₊ : ℤ)) + o)|) /
        ((m + j : ℕ) : ℝ))) atTop (𝓝 (y ω)) := by
    have h1 := hXj.add (hSj.const_mul 2)
    rwa [mul_zero, add_zero] at h1
  have hu : Tendsto (fun m : ℕ => lastPassage ω 0
      (⌊((m + j : ℕ) : ℝ) * x.1⌋₊, ⌊((m + j : ℕ) : ℝ) * x.2⌋₊) / ((m + j : ℕ) : ℝ))
      atTop (𝓝 (y ω)) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le hl hr (fun m => ?_) (fun m => ?_)
    · exact div_le_div_of_nonneg_right
        (lastPassage_phase_sandwich_box_sum ω x θ j m D _ rfl hx1 hx2 hθ1 hθ2 hj1 hj2 hD1 hD2).1
        (Nat.cast_nonneg _)
    · refine le_trans (div_le_div_of_nonneg_right
        (lastPassage_phase_sandwich_box_sum ω x θ j m D _ rfl hx1 hx2 hθ1 hθ2 hj1 hj2 hD1 hD2).2
        (Nat.cast_nonneg _)) (le_of_eq ?_)
      rw [add_div, mul_div_assoc]
  exact (tendsto_add_atTop_iff_nat (f := fun n : ℕ => lastPassage ω 0
    (⌊(n : ℝ) * x.1⌋₊, ⌊(n : ℝ) * x.2⌋₊) / (n : ℝ)) j).mp hu


/-- Pure real inequality behind the L1 transfer: if `A - 2 D S ≤ T ≤ B + 2 S`, then
`|T/N - c| ≤ |A/N - c| + |B/N - c| + (2 D + 2) S/N`. -/
private theorem abs_sub_le_of_sandwich (T A B S c N D : ℝ) (hN : 0 < N) (hS : 0 ≤ S)
    (hD : 0 ≤ D) (h1 : A - 2 * D * S ≤ T) (h2 : T ≤ B + 2 * S) :
    |T / N - c| ≤ |A / N - c| + |B / N - c| + (2 * D + 2) * (S / N) := by
  have hSN : 0 ≤ S / N := div_nonneg hS hN.le
  have e1 : (A - 2 * D * S) / N = A / N - 2 * D * (S / N) := by ring
  have e2 : (B + 2 * S) / N = B / N + 2 * (S / N) := by ring
  have l1 : A / N - 2 * D * (S / N) ≤ T / N := e1 ▸ div_le_div_of_nonneg_right h1 hN.le
  have l2 : T / N ≤ B / N + 2 * (S / N) := e2 ▸ div_le_div_of_nonneg_right h2 hN.le
  have hDS : 0 ≤ D * (S / N) := mul_nonneg hD hSN
  rw [abs_le]
  constructor
  · nlinarith [neg_abs_le (A / N - c), abs_nonneg (B / N - c)]
  · nlinarith [le_abs_self (B / N - c), abs_nonneg (A / N - c)]

/-- Rescaling the lower term of the sandwich: the index `m` divided by `m + j` instead of `m`
costs at most `j |c| / (m + j)`. -/
private theorem abs_rescale_le (X c : ℝ) (m j : ℕ) (hm : 0 < m) :
    |X / ((m + j : ℕ) : ℝ) - c| ≤ |X / (m : ℝ) - c| + (j : ℝ) * |c| / ((m + j : ℕ) : ℝ) := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hN : (0 : ℝ) < ((m + j : ℕ) : ℝ) := by positivity
  have hr : (m : ℝ) / ((m + j : ℕ) : ℝ) ≤ 1 := by
    rw [div_le_one hN]; push_cast; linarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)]
  have hr0 : 0 ≤ (m : ℝ) / ((m + j : ℕ) : ℝ) := by positivity
  have hid : X / ((m + j : ℕ) : ℝ) - c =
      ((m : ℝ) / ((m + j : ℕ) : ℝ)) * (X / (m : ℝ) - c) -
        ((j : ℝ) / ((m + j : ℕ) : ℝ)) * c := by
    push_cast
    field_simp
    ring
  rw [hid]
  calc |((m : ℝ) / ((m + j : ℕ) : ℝ)) * (X / (m : ℝ) - c) -
        ((j : ℝ) / ((m + j : ℕ) : ℝ)) * c|
      ≤ |((m : ℝ) / ((m + j : ℕ) : ℝ)) * (X / (m : ℝ) - c)| +
        |((j : ℝ) / ((m + j : ℕ) : ℝ)) * c| := abs_sub _ _
    _ ≤ |X / (m : ℝ) - c| + (j : ℝ) * |c| / ((m + j : ℕ) : ℝ) := by
      rw [abs_mul, abs_mul, abs_of_nonneg hr0, abs_of_nonneg (by positivity :
        (0 : ℝ) ≤ (j : ℝ) / ((m + j : ℕ) : ℝ))]
      have h1 := mul_le_mul_of_nonneg_right hr (abs_nonneg (X / (m : ℝ) - c))
      have h2 : (j : ℝ) / ((m + j : ℕ) : ℝ) * |c| = (j : ℝ) * |c| / ((m + j : ℕ) : ℝ) := by ring
      linarith

/-- The mean of one weight in absolute value does not depend on the site. -/
private theorem integral_abs_environment_eval (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (z : Lattice) : ∫ ω : Environment, |ω z| ∂environmentLaw μ = ∫ t : ℝ, |t| ∂μ := by
  have h := integral_map (μ := environmentLaw μ) (measurable_environment_eval z).aemeasurable
    (f := fun t : ℝ => |t|) continuous_abs.aestronglyMeasurable
  rw [environmentLaw_map_eval] at h
  exact h.symm


/-- Transfer from a random phase to phase 0, L1 part. If on the product of the phase law and the
environment law `∫ |T(⌊n x + θ⌋)/n - c| → 0`, then `∫ |T(⌊n x⌋)/n - c| → 0` for the environment law.
The proof integrates the pathwise sandwich; the mean of the box sum is a constant, so the error from
the box maximum is `O(1/n)`. -/
theorem tendsto_integral_abs_floor_of_phase (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : Integrable (fun t : ℝ => t) μ) (x : ℝ × ℝ) (hx1 : 0 ≤ x.1) (hx2 : 0 ≤ x.2) (c : ℝ)
    (hL1 : Tendsto (fun n : ℕ => ∫ p, |lastPassage p.2 0
        (⌊(n : ℝ) * x.1 + p.1.1⌋₊, ⌊(n : ℝ) * x.2 + p.1.2⌋₊) / (n : ℝ) - c|
        ∂(((volume.restrict (Ico (0 : ℝ) 1)).prod (volume.restrict (Ico (0 : ℝ) 1))).prod
          (environmentLaw μ))) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => ∫ ω, |lastPassage ω 0 (⌊(n : ℝ) * x.1⌋₊, ⌊(n : ℝ) * x.2⌋₊) / (n : ℝ) - c|
      ∂environmentLaw μ) atTop (𝓝 0) := by
  obtain ⟨j, D, hj, hj1, hj2, hD1, hD2⟩ := exists_floor_step_count x hx1 hx2
  set P : Measure ((ℝ × ℝ) × Environment) :=
    ((volume.restrict (Ico (0 : ℝ) 1)).prod (volume.restrict (Ico (0 : ℝ) 1))).prod
      (environmentLaw μ) with hP
  obtain ⟨X, hX⟩ : ∃ X : ℕ → (ℝ × ℝ) × Environment → ℝ, ∀ n p, X n p = lastPassage p.2 0
      (⌊(n : ℝ) * x.1 + p.1.1⌋₊, ⌊(n : ℝ) * x.2 + p.1.2⌋₊) := ⟨_, fun _ _ => rfl⟩
  obtain ⟨T, hT⟩ : ∃ T : ℕ → Environment → ℝ, ∀ n ω, T n ω =
      lastPassage ω 0 (⌊(n : ℝ) * x.1⌋₊, ⌊(n : ℝ) * x.2⌋₊) := ⟨_, fun _ _ => rfl⟩
  obtain ⟨S, hS⟩ : ∃ S : ℕ → Environment → ℝ, ∀ N ω, S N ω =
      ∑ o ∈ Finset.Icc ((-(D : ℤ)), (-(D : ℤ))) ((1 : ℤ), (1 : ℤ)),
        |ω (((⌊(N : ℝ) * x.1⌋₊ : ℤ), (⌊(N : ℝ) * x.2⌋₊ : ℤ)) + o)| := ⟨_, fun _ _ => rfl⟩
  have hXi : ∀ n, Integrable (X n) P := fun n =>
    (integrable_phase_passage μ hμ x hx1 hx2 n).congr
      (Filter.Eventually.of_forall fun p => (hX n p).symm)
  have hTi : ∀ n, Integrable (T n) (environmentLaw μ) := fun n =>
    (integrable_lastPassage μ hμ 0 _).congr (Filter.Eventually.of_forall fun ω => (hT n ω).symm)
  have hSi : ∀ N, Integrable (S N) (environmentLaw μ) := fun N =>
    (integrable_finsetSum _ fun o _ => (integrable_environment_eval μ hμ _).abs).congr
      (Filter.Eventually.of_forall fun ω => (hS N ω).symm)
  have hS0 : ∀ N ω, 0 ≤ S N ω := fun N ω => by
    rw [hS]; exact Finset.sum_nonneg fun _ _ => abs_nonneg _
  obtain ⟨Cb, hCb⟩ : ∃ Cb : ℝ, ∀ N, ∫ ω, S N ω ∂environmentLaw μ = Cb :=
    ⟨∑ o ∈ Finset.Icc ((-(D : ℤ)), (-(D : ℤ))) ((1 : ℤ), (1 : ℤ)), ∫ t : ℝ, |t| ∂μ, fun N => by
      simp_rw [hS]
      rw [integral_finsetSum _ fun o _ => (integrable_environment_eval μ hμ _).abs]
      exact Finset.sum_congr rfl fun o _ => integral_abs_environment_eval μ _⟩
  have hsnd : ∀ f : Environment → ℝ, AEStronglyMeasurable f (environmentLaw μ) →
      ∫ p, f p.2 ∂P = ∫ ω, f ω ∂environmentLaw μ := fun f hf => by
    have hmap : Measure.map Prod.snd P = environmentLaw μ := measurePreserving_snd.map_eq
    have h := integral_map (μ := P) measurable_snd.aemeasurable (f := f) (by rwa [hmap])
    rw [hmap] at h
    exact h.symm
  -- the integral bound for one index `m`, with `N = m + j`
  have hbound : ∀ m : ℕ, ∫ ω, |T (m + j) ω / ((m + j : ℕ) : ℝ) - c| ∂environmentLaw μ ≤
      (∫ p, |X m p / ((m + j : ℕ) : ℝ) - c| ∂P) +
      (∫ p, |X (m + j) p / ((m + j : ℕ) : ℝ) - c| ∂P) +
      (2 * D + 2) * (Cb / ((m + j : ℕ) : ℝ)) := by
    intro m
    have hN : (0 : ℝ) < ((m + j : ℕ) : ℝ) := by positivity
    have hpt : ∀ᵐ p ∂P, |T (m + j) p.2 / ((m + j : ℕ) : ℝ) - c| ≤
        |X m p / ((m + j : ℕ) : ℝ) - c| + |X (m + j) p / ((m + j : ℕ) : ℝ) - c| +
        (2 * D + 2) * (S (m + j) p.2 / ((m + j : ℕ) : ℝ)) := by
      filter_upwards [measurePreserving_fst.quasiMeasurePreserving.ae
        ae_phase_in_unit_square] with p hp
      obtain ⟨h1, h2⟩ := lastPassage_phase_sandwich_box_sum p.2 x p.1 j m D (S (m + j) p.2)
        (hS _ _) hx1 hx2 hp.1 hp.2 hj1 hj2 hD1 hD2
      rw [← hX, ← hT] at h1 h2
      exact abs_sub_le_of_sandwich _ _ _ _ c _ D hN (hS0 _ _) (Nat.cast_nonneg D) h1 h2
    have hI1 : Integrable (fun p => |X m p / ((m + j : ℕ) : ℝ) - c|) P :=
      (((hXi m).div_const _).sub (integrable_const c)).abs
    have hI2 : Integrable (fun p => |X (m + j) p / ((m + j : ℕ) : ℝ) - c|) P :=
      (((hXi (m + j)).div_const _).sub (integrable_const c)).abs
    have hI12 : Integrable (fun p => |X m p / ((m + j : ℕ) : ℝ) - c| +
        |X (m + j) p / ((m + j : ℕ) : ℝ) - c|) P := hI1.add hI2
    have hI3 : Integrable (fun p : (ℝ × ℝ) × Environment =>
        (2 * (D : ℝ) + 2) * (S (m + j) p.2 / ((m + j : ℕ) : ℝ))) P :=
      (((hSi (m + j)).comp_snd _).div_const _).const_mul _
    have hI0 : Integrable (fun ω => |T (m + j) ω / ((m + j : ℕ) : ℝ) - c|) (environmentLaw μ) :=
      (((hTi (m + j)).div_const _).sub (integrable_const c)).abs
    calc ∫ ω, |T (m + j) ω / ((m + j : ℕ) : ℝ) - c| ∂environmentLaw μ
        = ∫ p, |T (m + j) p.2 / ((m + j : ℕ) : ℝ) - c| ∂P :=
          (hsnd _ hI0.aestronglyMeasurable).symm
      _ ≤ ∫ p, (|X m p / ((m + j : ℕ) : ℝ) - c| + |X (m + j) p / ((m + j : ℕ) : ℝ) - c| +
          (2 * D + 2) * (S (m + j) p.2 / ((m + j : ℕ) : ℝ))) ∂P :=
          integral_mono_ae (hI0.comp_snd _) (hI12.add hI3) hpt
      _ = (∫ p, |X m p / ((m + j : ℕ) : ℝ) - c| ∂P) +
          (∫ p, |X (m + j) p / ((m + j : ℕ) : ℝ) - c| ∂P) +
          (2 * D + 2) * (Cb / ((m + j : ℕ) : ℝ)) := by
        rw [integral_add hI12 hI3, integral_add hI1 hI2, integral_const_mul,
          hsnd (fun ω => S (m + j) ω / ((m + j : ℕ) : ℝ))
            (((hSi (m + j)).div_const _).aestronglyMeasurable),
          integral_div, hCb]
  have hrescale : ∀ m : ℕ, 0 < m → ∫ p, |X m p / ((m + j : ℕ) : ℝ) - c| ∂P ≤
      (∫ p, |X m p / (m : ℝ) - c| ∂P) + (j : ℝ) * |c| / ((m + j : ℕ) : ℝ) := by
    intro m hm
    have hI : Integrable (fun p => |X m p / (m : ℝ) - c|) P :=
      (((hXi m).div_const _).sub (integrable_const c)).abs
    have hJ : Integrable (fun p => |X m p / ((m + j : ℕ) : ℝ) - c|) P :=
      (((hXi m).div_const _).sub (integrable_const c)).abs
    have hK : Integrable (fun p => |X m p / (m : ℝ) - c| + (j : ℝ) * |c| / ((m + j : ℕ) : ℝ)) P :=
      hI.add (integrable_const _)
    have hmono := integral_mono hJ hK
      (fun p => abs_rescale_le (X m p) c m j hm)
    rw [integral_add hI (integrable_const _), integral_const] at hmono
    simpa using hmono
  have ha : Tendsto (fun m : ℕ => ∫ p, |X m p / (m : ℝ) - c| ∂P) atTop (𝓝 0) := by
    simpa only [hX] using hL1
  have hb : Tendsto (fun m : ℕ => ∫ p, |X (m + j) p / ((m + j : ℕ) : ℝ) - c| ∂P) atTop (𝓝 0) :=
    (tendsto_add_atTop_iff_nat (f := fun n : ℕ => ∫ p, |X n p / (n : ℝ) - c| ∂P) j).mpr ha
  have hc1 : Tendsto (fun m : ℕ => (j : ℝ) * |c| / ((m + j : ℕ) : ℝ)) atTop (𝓝 0) :=
    (tendsto_const_div_atTop_nhds_zero_nat ((j : ℝ) * |c|)).comp (tendsto_add_atTop_nat j)
  have hc2 : Tendsto (fun m : ℕ => (2 * (D : ℝ) + 2) * (Cb / ((m + j : ℕ) : ℝ))) atTop (𝓝 0) := by
    have h := ((tendsto_const_div_atTop_nhds_zero_nat Cb).comp
      (tendsto_add_atTop_nat j)).const_mul (2 * (D : ℝ) + 2)
    rwa [mul_zero] at h
  have hsum := (((ha.add hc1).add hb).add hc2)
  simp only [add_zero] at hsum
  have hlim : Tendsto (fun m : ℕ => ∫ ω, |T (m + j) ω / ((m + j : ℕ) : ℝ) - c|
      ∂environmentLaw μ) atTop (𝓝 0) := by
    refine squeeze_zero' (Filter.Eventually.of_forall fun m => integral_nonneg fun ω =>
      abs_nonneg _) ?_ hsum
    filter_upwards [eventually_gt_atTop 0] with m hm
    have h1 := hbound m
    have h2 := hrescale m hm
    linarith
  have hfin : Tendsto (fun n : ℕ => ∫ ω, |T n ω / (n : ℝ) - c| ∂environmentLaw μ) atTop (𝓝 0) :=
    (tendsto_add_atTop_iff_nat (f := fun n : ℕ => ∫ ω, |T n ω / (n : ℝ) - c|
      ∂environmentLaw μ) j).mp hlim
  simpa only [hT] using hfin


end LPPDifferentiability
