/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Martin2004.Probability.DiagonalAnimalCenteredMean
public import ProbabilityBasics.Probability.L1LowerLimit
public import ProbabilityBasics.Analysis.CenteredBlockLimit
import ProbabilityBasics.Analysis.FloorBlockRatio
import Martin2004.Probability.DiagonalAnimalBilateralBlocks
import Martin2004.Probability.DiagonalAnimalConvergence

/-!
# Centered animal lower-limit and integral-error assembly

The helpers and final theorem keep the actual diagonal animal maximum. The
source application discharges the conditional mean and L1 helpers with the
forward, bilateral block, and finite floor comparison theorems.
The final result retains the same forward C and q. It makes no centered
almost-sure convergence or upper-limit assertion.
-/

public section

open MeasureTheory Filter Set
open scoped Topology ENNReal BigOperators

namespace LPPDifferentiability

/-- A nonnegative marginal makes every site of the actual environment
nonnegative on one common full-measure set. -/
theorem ae_forall_environment_nonneg (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hnonneg : ∀ᵐ x ∂μ, 0 ≤ x) :
    ∀ᵐ ω : Environment ∂environmentLaw μ, ∀ v, 0 ≤ ω v := by
  apply ae_all_iff.mpr
  intro v
  have hmap : MeasurePreserving (fun ω : Environment => ω v) (environmentLaw μ) μ :=
    ⟨measurable_environment_eval v, environmentLaw_map_eval μ v⟩
  exact hmap.quasiMeasurePreserving.ae hnonneg

/-- Nonnegative marginals give nonnegative actual centered normalized maxima. -/
theorem ae_nonneg_diagonalAnimalCenteredRate (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hnonneg : ∀ᵐ x ∂μ, 0 ≤ x) (n : ℕ) :
    ∀ᵐ ω ∂environmentLaw μ, 0 ≤ diagonalAnimalCenteredRate n ω := by
  filter_upwards [ae_forall_environment_nonneg μ hnonneg] with ω hω
  exact div_nonneg
    (diagonalAnimalMaximum_nonneg_of_forall_nonneg _ _ _ ω hω)
    (Nat.cast_nonneg _)

/-- The source's nonnegative marginal and finite positive square-root tail
supply the actual finite first moment. -/
theorem integrable_id_of_nonneg_positive_sqrt_tail
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hnonneg : ∀ᵐ x ∂μ, 0 ≤ x)
    (hpos : (∫⁻ t in Ioi (0 : ℝ), (μ (Ioi t)) ^ (1 / 2 : ℝ)) < ∞) :
    Integrable (fun x : ℝ => x) μ := by
  apply (integrable_positivePart_of_positive_sqrt_tail μ hpos).congr
  filter_upwards [hnonneg] with x hx
  exact max_eq_left hx

/-- Conditional integral-error transfer: the actual centered lower limit and
origin mean limit suffice for L1 convergence. All moment and nonnegativity
facts are derived from the displayed source marginal and tail assumptions. -/
theorem tendsto_integral_abs_diagonalAnimalCenteredRate_sub_of_lower_and_origin_mean
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hnonneg : ∀ᵐ x ∂μ, 0 ≤ x)
    (hpos : (∫⁻ t in Ioi (0 : ℝ), (μ (Ioi t)) ^ (1 / 2 : ℝ)) < ∞)
    {q : ℝ} (hq : 0 ≤ q)
    (hlower : ∀ᵐ ω ∂environmentLaw μ, (q : EReal) ≤
      liminf (fun n => (diagonalAnimalCenteredRate n ω : EReal)) atTop)
    (hmean : Tendsto (fun n : ℕ => ∫ ω : Environment,
      diagonalAnimalMaximum 0 ((n + 1 : ℕ) : ℤ) (by omega) ω /
        (n + 1 : ℕ) ∂environmentLaw μ) atTop (𝓝 q)) :
    Tendsto (fun n => ∫ ω, |diagonalAnimalCenteredRate n ω - q| ∂environmentLaw μ)
      atTop (𝓝 0) := by
  exact tendsto_integral_abs_sub_of_ae_le_liminf
    (integrable_diagonalAnimalCenteredRate μ
      (integrable_id_of_nonneg_positive_sqrt_tail μ hnonneg hpos))
    (ae_nonneg_diagonalAnimalCenteredRate μ hnonneg) hq hlower
    (tendsto_integral_diagonalAnimalCenteredRate_of_origin μ hmean)


/-- The source tail estimate gives a genuine finite upper bound on the set of
positive origin expected rates. -/
theorem bddAbove_diagonalAnimalExpectedRates
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hnonneg : ∀ᵐ x ∂μ, 0 ≤ x)
    (hpos : (∫⁻ t in Ioi (0 : ℝ), (μ (Ioi t)) ^ (1 / 2 : ℝ)) < ∞) :
    BddAbove (range (fun n : ℕ =>
      (∫ ω : Environment, diagonalAnimalMaximum 0 ((n + 1 : ℕ) : ℤ)
        (by omega) ω ∂environmentLaw μ) / (n + 1 : ℕ))) := by
  obtain ⟨C, _, hmean⟩ := exists_positive_diagonalAnimalMaximum_mean_bound
  refine ⟨C * (∫⁻ t in Ioi (0 : ℝ), (μ (Ioi t)) ^ (1 / 2 : ℝ)).toReal, ?_⟩
  rintro c ⟨n, rfl⟩
  have heq : (∫ ω : Environment,
      diagonalAnimalMaximum 0 ((n + 1 : ℕ) : ℤ) (by omega) ω ∂environmentLaw μ) =
      (∫ ω : Environment,
      diagonalAnimalMaximum 0 ((n + 1 : ℕ) : ℤ) (by omega)
        (fun v => max (ω v) 0) ∂environmentLaw μ) := by
    apply integral_congr_ae
    filter_upwards [ae_forall_environment_nonneg μ hnonneg] with ω hω
    have hfield : (fun v => max (ω v) 0) = ω := funext fun v => max_eq_left (hω v)
    rw [hfield]
  have hbound := ((hmean μ (n + 1) (by omega)).2 hpos).2
  apply (div_le_iff₀ (by exact_mod_cast Nat.succ_pos n : (0 : ℝ) < (n + 1 : ℕ))).2
  rw [heq]
  calc
    _ ≤ C * (n + 1 : ℕ) *
        (∫⁻ t in Ioi (0 : ℝ), (μ (Ioi t)) ^ (1 / 2 : ℝ)).toReal := hbound
    _ = _ := by ring


/-- The actual proper floor blocks give a finite lower comparison for the
centered normalized maximum. The radius is positive even when n is zero. -/
theorem diagonalAnimal_floor_block_sum_le_centeredRate
    (ω : Environment) (hω : ∀ v, 0 ≤ ω v)
    (n k : ℕ) (hk : 0 < k) (hkn : k ≤ n + 1) :
    (∑ j ∈ Finset.range (2 * ((n + 1) / k)),
      diagonalAnimalMaximum
        ((-(((n + 1) / k : ℕ) : ℤ) + (j : ℤ)) * (k : ℤ))
        ((-(((n + 1) / k : ℕ) : ℤ) + (j : ℤ) + 1) * (k : ℤ))
        (by
          have hkZ : (0 : ℤ) < (k : ℤ) := by exact_mod_cast hk
          exact mul_lt_mul_of_pos_right (by omega) hkZ) ω) /
        (2 * (n + 1 : ℕ) : ℕ) ≤ diagonalAnimalCenteredRate n ω := by
  have hbound := centered_interval_floor_block_sum_le
    (fun a b hab => diagonalAnimalMaximum a b hab ω)
    (fun a b hab => diagonalAnimalMaximum_nonneg_of_forall_nonneg a b hab ω hω)
    (fun a b c hab hbc => diagonalAnimalMaximum_superadditive hab hbc ω)
    (n + 1) k hkn hk
  exact div_le_div_of_nonneg_right hbound (Nat.cast_nonneg _)

/-- For every proper positive block size, the actual bilateral block theorem
and finite floor comparison give its expected per-length rate as a centered
extended lower bound. The finite first moment is the only moment premise. -/
theorem ae_diagonalAnimalExpectedRate_le_centered_liminf
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : Integrable (fun x : ℝ => x) μ) (hnonneg : ∀ᵐ x ∂μ, 0 ≤ x)
    (k : ℕ) (hk : 0 < k) :
    ∀ᵐ ω ∂environmentLaw μ,
      (((∫ η : Environment, diagonalAnimalMaximum 0 (k : ℤ) (by omega) η
          ∂environmentLaw μ) / (k : ℝ) : ℝ) : EReal) ≤
        liminf (fun n => (diagonalAnimalCenteredRate n ω : EReal)) atTop := by
  have hblocks := (diagonalAnimalBilateralBlockAverage_tendsto μ hμ k hk).1
  have hf : diagonalAnimalBlock k hk 0 =
      (fun η : Environment => diagonalAnimalMaximum 0 (k : ℤ) (by omega) η) := by
    funext η
    exact diagonalAnimalBlock_zero k hk η
  rw [hf] at hblocks
  filter_upwards [ae_forall_environment_nonneg μ hnonneg, hblocks] with ω hω hblock
  have hscaled := (tendsto_nat_div_block_ratio_mul_comp hk (hblock.div_const (k : ℝ))).comp
    (tendsto_add_atTop_nat 1)
  apply le_liminf_ereal_of_tendsto_eventually_le hscaled
  filter_upwards [eventually_ge_atTop k] with n hn
  have hkn : k ≤ n + 1 := by omega
  have hr : 0 < (n + 1) / k := (Nat.div_pos_iff).2 ⟨hk, hkn⟩
  have hfinite := diagonalAnimal_floor_block_sum_le_centeredRate ω hω n k hk hkn
  dsimp only [Function.comp_apply]
  rw [diagonalAnimalBilateralBlockAverage_eq_range]
  have halgebra := block_average_scale_eq
    (∑ j ∈ Finset.range (2 * ((n + 1) / k)),
      diagonalAnimalBlock k hk (-(((n + 1) / k : ℕ) : ℤ) + (j : ℤ)) ω)
    ((n + 1) / k) k (n + 1) hr hk (by omega)
  rw [halgebra]
  simpa only [diagonalAnimalBlock, Nat.cast_mul, Nat.cast_ofNat] using hfinite

/-- Countably many actual positive block sizes give the lower bound by their
finite expected-rate supremum. Boundedness is derived from the source tail
estimate before the real supremum is used. -/
theorem ae_sSup_diagonalAnimalExpectedRates_le_centered_liminf
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hnonneg : ∀ᵐ x ∂μ, 0 ≤ x)
    (hpos : (∫⁻ t in Ioi (0 : ℝ), (μ (Ioi t)) ^ (1 / 2 : ℝ)) < ∞) :
    ∀ᵐ ω ∂environmentLaw μ,
      ((sSup (range (fun n : ℕ =>
        (∫ η : Environment, diagonalAnimalMaximum 0 ((n + 1 : ℕ) : ℤ) (by omega) η
          ∂environmentLaw μ) / (n + 1 : ℕ))) : ℝ) : EReal) ≤
        liminf (fun n => (diagonalAnimalCenteredRate n ω : EReal)) atTop := by
  have hμ := integrable_id_of_nonneg_positive_sqrt_tail μ hnonneg hpos
  have hblocks : ∀ j : ℕ, ∀ᵐ ω ∂environmentLaw μ,
      (((∫ η : Environment, diagonalAnimalMaximum 0 ((j + 1 : ℕ) : ℤ) (by omega) η
          ∂environmentLaw μ) / (j + 1 : ℕ) : ℝ) : EReal) ≤
        liminf (fun n => (diagonalAnimalCenteredRate n ω : EReal)) atTop :=
    fun j => ae_diagonalAnimalExpectedRate_le_centered_liminf μ hμ hnonneg (j + 1) (by omega)
  filter_upwards [ae_all_iff.mpr hblocks] with ω hω
  apply coe_sSup_le_liminf_ereal (range_nonempty _)
    (bddAbove_diagonalAnimalExpectedRates μ hnonneg hpos)
  rintro c ⟨j, rfl⟩
  exact hω j

/-- One universal constant and the same forward rate give the centered lower
limit, expected limit, and L1 convergence under the source assumptions alone.
All forward conclusions are retained to make the common witness explicit.
No centered almost-sure upper bound or centered almost-sure convergence is
asserted. -/
theorem exists_diagonalAnimalMaximum_forward_and_centered_lower_convergence :
    ∃ C : ℝ, 0 < C ∧ ∀ (μ : Measure ℝ) [IsProbabilityMeasure μ],
      (∀ᵐ x ∂μ, 0 ≤ x) →
      (∫⁻ t in Ioi (0 : ℝ), (μ (Ioi t)) ^ (1 / 2 : ℝ)) < ∞ →
      ∃ q : ℝ, 0 ≤ q ∧
        q ≤ C * (∫⁻ t in Ioi (0 : ℝ), (μ (Ioi t)) ^ (1 / 2 : ℝ)).toReal ∧
        Tendsto (fun n : ℕ =>
          (∫ ω, diagonalAnimalMaximum 0 ((n + 1 : ℕ) : ℤ) (by omega) ω
            ∂environmentLaw μ) / ((n + 1 : ℕ) : ℝ)) atTop (𝓝 q) ∧
        q = sSup (range (fun n : ℕ =>
          (∫ ω, diagonalAnimalMaximum 0 ((n + 1 : ℕ) : ℤ) (by omega) ω
            ∂environmentLaw μ) / ((n + 1 : ℕ) : ℝ))) ∧
        (∀ᵐ ω ∂environmentLaw μ, Tendsto (fun n : ℕ =>
          diagonalAnimalMaximum 0 ((n + 1 : ℕ) : ℤ) (by omega) ω /
            ((n + 1 : ℕ) : ℝ)) atTop (𝓝 q)) ∧
        Tendsto (fun n : ℕ => ∫ ω,
          |diagonalAnimalMaximum 0 ((n + 1 : ℕ) : ℤ) (by omega) ω /
            ((n + 1 : ℕ) : ℝ) - q| ∂environmentLaw μ) atTop (𝓝 0) ∧
        (∀ᵐ ω ∂environmentLaw μ, (q : EReal) ≤
          liminf (fun n => (diagonalAnimalCenteredRate n ω : EReal)) atTop) ∧
        Tendsto (fun n => ∫ ω, diagonalAnimalCenteredRate n ω ∂environmentLaw μ)
          atTop (𝓝 q) ∧
        Tendsto (fun n => ∫ ω, |diagonalAnimalCenteredRate n ω - q| ∂environmentLaw μ)
          atTop (𝓝 0) := by
  obtain ⟨C, hC, hforward⟩ := exists_diagonalAnimalMaximum_forward_convergence
  refine ⟨C, hC, ?_⟩
  intro μ _ hnonneg hpos
  obtain ⟨q, hq, hqbound, hmean, hsup, hae, hL1⟩ := hforward μ hnonneg hpos
  have hlower := ae_sSup_diagonalAnimalExpectedRates_le_centered_liminf μ hnonneg hpos
  rw [← hsup] at hlower
  have hmean' : Tendsto (fun n : ℕ => ∫ ω : Environment,
      diagonalAnimalMaximum 0 ((n + 1 : ℕ) : ℤ) (by omega) ω /
        (n + 1 : ℕ) ∂environmentLaw μ) atTop (𝓝 q) := by
    simpa only [integral_div] using hmean
  exact ⟨q, hq, hqbound, hmean, hsup, hae, hL1, hlower,
    tendsto_integral_diagonalAnimalCenteredRate_of_origin μ hmean',
    tendsto_integral_abs_diagonalAnimalCenteredRate_sub_of_lower_and_origin_mean
      μ hnonneg hpos hq hlower hmean'⟩

end LPPDifferentiability
