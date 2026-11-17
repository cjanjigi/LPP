/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LPP_Foundations.Frozen.Model.EnvironmentLaw
public import Mathlib.Data.EReal.Basic
public import Mathlib.Order.LiminfLimsup
public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import LPP_Foundations.Model.Animals.SignedSegment
import LPP_Foundations.Model.Animals.Maximum
import Martin2004.Probability.GreedyAnimalAlmostSureBound
import Martin2004.Probability.UniformTruncationApproximation
import ProbabilityBasics.Probability.AbsoluteMomentTail
import ProbabilityBasics.Probability.AbsoluteMomentLowerTail
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

/-! Uniform short coordinate-ray weights on the full signed lattice window. -/

@[expose] public section

open MeasureTheory Filter Set
open scoped BigOperators ENNReal Topology

namespace LPPDifferentiability

private theorem coordinate_segment_sum_le_animal
    (w : Environment) (hw : ∀ z, 0 ≤ w z) (x : Lattice) (i : Fin 2)
    (m N : ℕ) (hN : x.1.natAbs + x.2.natAbs + m + 1 ≤ N) :
    (∑ k ∈ Finset.range (m + 1), w (x + (k : ℤ) •
      (if i = 0 then ((1 : ℤ), (0 : ℤ)) else ((0 : ℤ), (1 : ℤ))))) ≤
      animalMaximum N (by omega) w := by
  classical
  let f : ℕ → Lattice := fun k => x + (k : ℤ) •
    (if i = 0 then ((1 : ℤ), (0 : ℤ)) else ((0 : ℤ), (1 : ℤ)))
  have hf : Function.Injective f := by
    intro a b hab
    by_cases hi : i = 0
    · have hc : (a : ℤ) = (b : ℤ) := by
        simpa [f, hi] using congrArg Prod.fst hab
      exact_mod_cast hc
    · have hc : (a : ℤ) = (b : ℤ) := by
        simpa [f, hi] using congrArg Prod.snd hab
      exact_mod_cast hc
  obtain ⟨A, hA, hseg⟩ := exists_animalFamily_containing_signed_coordinate_segment x i m N hN
  let B := (Finset.range (m + 1)).image f
  have hsub : B ⊆ A := by
    intro z hz
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hz
    exact hseg k (by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hk)
  calc
    _ = animalWeight w B := by
      change (∑ k ∈ Finset.range (m + 1), w (f k)) =
        ∑ z ∈ (Finset.range (m + 1)).image f, w z
      exact (Finset.sum_image hf.injOn).symm
    _ ≤ animalWeight w A :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun z _ _ => hw z)
    _ ≤ animalMaximum N (by omega) w := animalWeight_le_animalMaximum N (by omega) w hA

private theorem abs_weight_le_cutoff_remainders (t K : ℝ) :
    |t| ≤ K + max (t - K) 0 + max (-t - K) 0 := by
  rcases le_total 0 t with ht | ht
  · rw [abs_of_nonneg ht]
    linarith only [le_max_left (t - K) 0, le_max_right (-t - K) 0]
  · rw [abs_of_nonpos ht]
    linarith only [le_max_right (t - K) 0, le_max_left (-t - K) 0]

private theorem abs_segment_le_animal_remainders
    (ω : Environment) (K : ℝ) (x : Lattice) (i : Fin 2) (m N : ℕ)
    (hN : x.1.natAbs + x.2.natAbs + m + 1 ≤ N) :
    (∑ k ∈ Finset.range (m + 1), |ω (x + (k : ℤ) •
      (if i = 0 then ((1 : ℤ), (0 : ℤ)) else ((0 : ℤ), (1 : ℤ))))|) ≤
      ((m + 1 : ℕ) : ℝ) * K +
        animalMaximum N (by omega) (fun z => max (ω z - K) 0) +
        animalMaximum N (by omega) (fun z => max (-ω z - K) 0) := by
  let f : ℕ → Lattice := fun k => x + (k : ℤ) •
    (if i = 0 then ((1 : ℤ), (0 : ℤ)) else ((0 : ℤ), (1 : ℤ)))
  have hs : (∑ k ∈ Finset.range (m + 1), |ω (f k)|) ≤
      ∑ k ∈ Finset.range (m + 1),
        (K + max (ω (f k) - K) 0 + max (-ω (f k) - K) 0) :=
    Finset.sum_le_sum (fun k _ => abs_weight_le_cutoff_remainders (ω (f k)) K)
  have hs' : (∑ k ∈ Finset.range (m + 1), |ω (f k)|) ≤
      ((m + 1 : ℕ) : ℝ) * K +
        (∑ k ∈ Finset.range (m + 1), max (ω (f k) - K) 0) +
        ∑ k ∈ Finset.range (m + 1), max (-ω (f k) - K) 0 := by
    simpa only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul] using hs
  have hp := coordinate_segment_sum_le_animal (fun z => max (ω z - K) 0)
    (fun z => le_max_right _ _) x i m N hN
  have hn := coordinate_segment_sum_le_animal (fun z => max (-ω z - K) 0)
    (fun z => le_max_right _ _) x i m N hN
  dsimp only [f] at hs'
  linarith only [hs', hp, hn]

private theorem eventually_rescaled_animal_rate
    (w : Environment) (a : ℝ) (ha : 0 ≤ a)
    (hbound : ∀ ε : ℝ, 0 < ε → ∀ᶠ j : ℕ in atTop,
      animalMaximum (j + 1) (by omega) w / ((j + 1 : ℕ) : ℝ) < a + ε)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,
      animalMaximum (4 * (n + 1)) (by omega) w / (n : ℝ) ≤ 8 * (a + ε) := by
  obtain ⟨j0, hj0⟩ := eventually_atTop.mp (hbound ε hε)
  filter_upwards [eventually_ge_atTop (max j0 1)] with n hn
  let N := 4 * (n + 1)
  have hN : 1 ≤ N := by dsimp [N]; omega
  have hnpos : 0 < (n : ℝ) := Nat.cast_pos.mpr (by omega)
  have hNpos : 0 < (N : ℝ) := Nat.cast_pos.mpr (by omega)
  have hraw := hj0 (N - 1) (by dsimp [N]; omega)
  have heq : N - 1 + 1 = N := by omega
  have hraw' : animalMaximum N hN w / (N : ℝ) < a + ε := by
    simpa only [heq] using hraw
  have hNbound : (N : ℝ) ≤ 8 * (n : ℝ) := by
    exact_mod_cast (show N ≤ 8 * n by dsimp [N]; omega)
  apply (div_le_iff₀ hnpos).2
  calc
    _ ≤ (a + ε) * (N : ℝ) := ((div_lt_iff₀ hNpos).1 hraw').le
    _ ≤ (a + ε) * (8 * (n : ℝ)) :=
      mul_le_mul_of_nonneg_left hNbound (add_nonneg ha hε.le)
    _ = (8 * (a + ε)) * (n : ℝ) := by ring

/-- Under the original absolute real moment above two, all short inclusive unit
rays in the signed radius-2n window have small normalized absolute weight.
This is the animal/truncation auxiliary input for JR1810.03580v3,
Appendix B; it makes no stationary cocycle or Appendix B closure assertion. -/
theorem ae_uniform_short_weight_segments_of_absolute_moment
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hmoment : ∃ p : ℝ, 2 < p ∧
      (∫⁻ t, ENNReal.ofReal (|t| ^ p) ∂μ) < ∞) :
    ∀ᵐ ω ∂environmentLaw μ,
      let W : Fin 2 → ℝ → ℕ → EReal := fun i δ n =>
        ⨆ x : {x : Lattice // x.1.natAbs + x.2.natAbs ≤ 2 * n},
          (((∑ k ∈ Finset.range (⌊(n : ℝ) * δ⌋₊ + 1),
            |ω (x.1 + (k : ℤ) •
              (if i = 0 then ((1 : ℤ), (0 : ℤ)) else ((0 : ℤ), (1 : ℤ))))|) /
                (n : ℝ) : ℝ) : EReal)
      ∀ η : ℝ, 0 < η → ∃ δ0 : ℝ, 0 < δ0 ∧ δ0 ≤ 1 ∧
        ∀ δ : ℝ, 0 < δ → δ ≤ δ0 → ∀ i : Fin 2,
          limsup (W i δ) atTop ≤ (η : EReal) := by
  classical
  obtain ⟨p, hp, hmoment⟩ := hmoment
  have hpos :=
    (ProbabilityBasics.negative_moment_and_positive_tail_of_absolute_moment μ hp hmoment).2
  have hneg :=
    ProbabilityBasics.integrated_sqrt_lower_tail_lt_top_of_absolute_moment μ hp hmoment
  obtain ⟨C, hC, hAnimal⟩ := exists_animalMaximum_limsup_and_eventually_bound
  let rp : ℕ → Environment → Environment := fun K ω z => max (ω z - (K : ℝ)) 0
  let rn : ℕ → Environment → Environment := fun K ω z => max (-ω z - (K : ℝ)) 0
  let tp : ℕ → ℝ := fun K => (∫⁻ t in Ioi (0 : ℝ),
    ((μ.map (fun v : ℝ => max (v - (K : ℝ)) 0)) (Ioi t)) ^ (1 / 2 : ℝ)).toReal
  let tn : ℕ → ℝ := fun K => (∫⁻ t in Ioi (0 : ℝ),
    ((μ.map (fun v : ℝ => max (-v - (K : ℝ)) 0)) (Ioi t)) ^ (1 / 2 : ℝ)).toReal
  have hpEvent (K : ℕ) : ∀ᵐ ω ∂environmentLaw μ,
      ∀ ε : ℝ, 0 < ε → ∀ᶠ j : ℕ in atTop,
        animalMaximum (j + 1) (by omega) (rp K ω) / ((j + 1 : ℕ) : ℝ) < C * tp K + ε := by
    let μK := μ.map (fun v : ℝ => max (v - (K : ℝ)) 0)
    have hm : Measurable (fun v : ℝ => max (v - (K : ℝ)) 0) := by fun_prop
    let : IsProbabilityMeasure μK :=
      (Measure.isProbabilityMeasure_map_iff hm.aemeasurable).2 inferInstance
    have hb := hAnimal μK (positive_remainder_sqrt_tail_lt_top μ hpos (K : ℝ) (Nat.cast_nonneg K))
    have hmap : MeasurePreserving (rp K) (environmentLaw μ) (environmentLaw μK) :=
      ⟨measurable_coordinatewise_environment_map _ hm,
        environmentLaw_map_positive_remainder μ (K : ℝ)⟩
    filter_upwards [hmap.quasiMeasurePreserving.ae hb] with ω hω
    exact hω.2
  have hnEvent (K : ℕ) : ∀ᵐ ω ∂environmentLaw μ,
      ∀ ε : ℝ, 0 < ε → ∀ᶠ j : ℕ in atTop,
        animalMaximum (j + 1) (by omega) (rn K ω) / ((j + 1 : ℕ) : ℝ) < C * tn K + ε := by
    let μK := μ.map (fun v : ℝ => max (-v - (K : ℝ)) 0)
    have hm : Measurable (fun v : ℝ => max (-v - (K : ℝ)) 0) := by fun_prop
    let : IsProbabilityMeasure μK :=
      (Measure.isProbabilityMeasure_map_iff hm.aemeasurable).2 inferInstance
    have hb := hAnimal μK (negative_remainder_sqrt_tail_lt_top μ hneg (K : ℝ) (Nat.cast_nonneg K))
    have hmap : MeasurePreserving (rn K) (environmentLaw μ) (environmentLaw μK) :=
      ⟨measurable_coordinatewise_environment_map _ hm,
        environmentLaw_map_negative_remainder μ (K : ℝ)⟩
    filter_upwards [hmap.quasiMeasurePreserving.ae hb] with ω hω
    exact hω.2
  -- This is the only intersection: natural cutoffs, with both remainder laws.
  have hAll := ae_all_iff.2 (fun K : ℕ => (hpEvent K).and (hnEvent K))
  filter_upwards [hAll] with ω hω
  let W : Fin 2 → ℝ → ℕ → EReal := fun i δ n =>
    ⨆ x : {x : Lattice // x.1.natAbs + x.2.natAbs ≤ 2 * n},
      (((∑ k ∈ Finset.range (⌊(n : ℝ) * δ⌋₊ + 1),
        |ω (x.1 + (k : ℤ) •
          (if i = 0 then ((1 : ℤ), (0 : ℤ)) else ((0 : ℤ), (1 : ℤ))))|) /
            (n : ℝ) : ℝ) : EReal)
  change ∀ η : ℝ, 0 < η → ∃ δ0 : ℝ, 0 < δ0 ∧ δ0 ≤ 1 ∧
    ∀ δ : ℝ, 0 < δ → δ ≤ δ0 → ∀ i : Fin 2,
      limsup (W i δ) atTop ≤ (η : EReal)
  intro η hη
  have hη64 : 0 < η / 64 := by linarith only [hη]
  obtain ⟨L0, _, hsmall⟩ := exists_remainder_sqrt_tail_cutoff μ hpos hneg C (η / 64) hη64
  let K : ℕ := ⌈L0⌉₊
  have htp : C * tp K < η / 64 := (hsmall (K : ℝ) (Nat.le_ceil L0)).1
  have htn : C * tn K < η / 64 := (hsmall (K : ℝ) (Nat.le_ceil L0)).2
  have hpRate := eventually_rescaled_animal_rate (rp K ω) (C * tp K)
    (mul_nonneg hC.le ENNReal.toReal_nonneg) (hω K).1 (η / 64) hη64
  have hnRate := eventually_rescaled_animal_rate (rn K ω) (C * tn K)
    (mul_nonneg hC.le ENNReal.toReal_nonneg) (hω K).2 (η / 64) hη64
  have hKover : ∀ᶠ n : ℕ in atTop, (K : ℝ) / (n : ℝ) < η / 4 :=
    (tendsto_const_div_atTop_nhds_zero_nat (K : ℝ)).eventually
      (gt_mem_nhds (by linarith only [hη]))
  let δ0 : ℝ := min 1 (η / (4 * ((K : ℝ) + 1)))
  have hδ0pos : 0 < δ0 := lt_min (by norm_num) (div_pos hη (by positivity))
  refine ⟨δ0, hδ0pos, min_le_left _ _, ?_⟩
  intro δ hδ hδ0 i
  have hδOne : δ ≤ 1 := hδ0.trans (min_le_left _ _)
  have hδSmall : δ ≤ η / (4 * ((K : ℝ) + 1)) := hδ0.trans (min_le_right _ _)
  have hδMul : δ * (4 * ((K : ℝ) + 1)) ≤ η :=
    (le_div_iff₀ (by positivity)).1 hδSmall
  have hKδ : (K : ℝ) * δ ≤ η / 4 := by nlinarith only [hδMul, hδ]
  apply limsup_le_of_le (by isBoundedDefault)
  filter_upwards [hpRate, hnRate, hKover, eventually_ge_atTop (1 : ℕ)] with n hpr hnr hkn hn
  have hnpos : 0 < (n : ℝ) := Nat.cast_pos.mpr (by omega)
  have hpr' : animalMaximum (4 * (n + 1)) (by omega) (rp K ω) / (n : ℝ) ≤ η / 4 := by
    linarith only [hpr, htp]
  have hnr' : animalMaximum (4 * (n + 1)) (by omega) (rn K ω) / (n : ℝ) ≤ η / 4 := by
    linarith only [hnr, htn]
  dsimp only [W]
  apply iSup_le
  intro x
  let m : ℕ := ⌊(n : ℝ) * δ⌋₊
  have hm : m ≤ n := Nat.floor_le_of_le (mul_le_of_le_one_right (Nat.cast_nonneg n) hδOne)
  have hcapacity : x.1.1.natAbs + x.1.2.natAbs + m + 1 ≤ 4 * (n + 1) := by
    have hx := x.2
    omega
  have hseg := abs_segment_le_animal_remainders ω (K : ℝ) x.1 i m (4 * (n + 1)) hcapacity
  have hfloor : (m : ℝ) ≤ (n : ℝ) * δ := Nat.floor_le (mul_nonneg (Nat.cast_nonneg n) hδ.le)
  have hm1 : ((m + 1 : ℕ) : ℝ) ≤ (n : ℝ) * δ + 1 := by
    push_cast
    linarith only [hfloor]
  have hconstant : ((m + 1 : ℕ) : ℝ) * (K : ℝ) / (n : ℝ) ≤
      (K : ℝ) * δ + (K : ℝ) / (n : ℝ) := by
    calc
      _ ≤ (((n : ℝ) * δ + 1) * (K : ℝ)) / (n : ℝ) :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hm1 (Nat.cast_nonneg K)) hnpos.le
      _ = (K : ℝ) * δ + (K : ℝ) / (n : ℝ) := by field_simp [ne_of_gt hnpos]
  have hdiv := div_le_div_of_nonneg_right hseg hnpos.le
  rw [add_div, add_div] at hdiv
  change _ ≤ ((m + 1 : ℕ) : ℝ) * (K : ℝ) / (n : ℝ) +
    animalMaximum (4 * (n + 1)) (by omega) (rp K ω) / (n : ℝ) +
    animalMaximum (4 * (n + 1)) (by omega) (rn K ω) / (n : ℝ) at hdiv
  have hreal : (∑ k ∈ Finset.range (m + 1), |ω (x.1 + (k : ℤ) •
      (if i = 0 then ((1 : ℤ), (0 : ℤ)) else ((0 : ℤ), (1 : ℤ))))|) / (n : ℝ) ≤ η := by
    linarith only [hdiv, hconstant, hpr', hnr', hKδ, hkn]
  exact_mod_cast hreal

end LPPDifferentiability
