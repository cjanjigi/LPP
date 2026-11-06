/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Differentiability.Probability.ExcessFourthMoment
public import ProbabilityBasics.Probability.FourthMomentSqrtTail
import Mathlib.Tactic

/-!
# Integrated tails of finite excess sums

This file bounds the integrated square-root tail of a finite sum of truncated weights, uniformly
over sets of bounded size and with the right power of the scale `s`. The bound comes from the
fourth moment estimate of `ExcessFourthMoment` and the square-root tail bound of
`FourthMomentSqrtTail`.
-/

public section
open MeasureTheory Set
open scoped BigOperators ENNReal

namespace LPPDifferentiability

/-- One positive constant `C`, depending only on the `p`-th moment of `μ` and on `eta`, controls
the integrated tail of every finite excess sum over a set of at most `44 s^4` sites. -/
theorem exists_excess_sum_integrated_sqrt_tail_bound
    (μ : Measure ℝ) [IsProbabilityMeasure μ] {p eta : ℝ}
    (hp : 4 < p) (heta : 0 < eta)
    (hmoment : (∫⁻ x, ENNReal.ofReal ((max x 0)^p) ∂μ) < ∞) :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℝ, 3 ≤ s → ∀ S : Finset Lattice,
      (S.card : ℝ) ≤ 44*s^4 →
      (∫⁻ t in Ioi (0 : ℝ),
        (environmentLaw μ) {ω : Environment |
          t < ∑ z ∈ S, max (ω z - eta*s/4) 0}^(1/2 : ℝ)) ≤
        ENNReal.ofReal (C*s^(2-p/4)) := by
  let Cp : ℝ := ∫ x : ℝ, (max x 0)^p ∂μ
  let A : ℝ := 44*Cp*(eta/4)^(4-p)
  let B : ℝ := (44*Cp*(eta/4)^(1-p))^4
  let K : ℝ := 34*(A+B)
  let C : ℝ := 1 + 2*K^(1/4 : ℝ)
  have hCp0 : 0 ≤ Cp := by
    dsimp [Cp]
    exact integral_nonneg fun x => Real.rpow_nonneg (le_max_right x 0) p
  have hA0 : 0 ≤ A := by
    dsimp [A]
    positivity
  have hB0 : 0 ≤ B := by
    dsimp [B]
    positivity
  have hK0 : 0 ≤ K := by
    dsimp [K]
    positivity
  have hCpos : 0 < C := by
    dsimp [C]
    positivity
  refine ⟨C, hCpos, ?_⟩
  intro s hs S hcard
  have hs0 : 0 < s := by linarith
  have hs1 : 1 ≤ s := by linarith
  have hexponent : 20-4*p ≤ 8-p := by linarith
  have hscaleExponent : s^(20-4*p) ≤ s^(8-p) :=
    Real.rpow_le_rpow_of_exponent_le hs1 hexponent
  let M : ℝ := eta*s/4
  let φ : ℝ → ℝ := fun x => max (x-M) 0
  let Z : Environment → ℝ := fun ω => ∑ z ∈ S, φ (ω z)
  have hM : 0 < M := by
    dsimp [M]
    positivity
  have hφMeas : Measurable φ := (measurable_id.sub_const M).max measurable_const
  have hφ0 (x : ℝ) : 0 ≤ φ x := le_max_right _ _
  have hZMeas : Measurable Z := by
    dsimp [Z]
    fun_prop
  have hZ0 (ω : Environment) : 0 ≤ Z ω := by
    dsimp [Z]
    exact Finset.sum_nonneg fun z _ => hφ0 (ω z)
  have hp0 : 0 < p := lt_trans (by norm_num) hp
  have hφ4 : Integrable (fun x : ℝ => φ x^(4 : ℝ)) μ := by
    simpa only [φ] using integrable_truncated_positive_rpow μ hp0
      (by norm_num : (0 : ℝ) < 4) hp.le hM hmoment
  have hφMem : MemLp φ 4 μ := by
    apply (integrable_norm_rpow_iff hφMeas.aestronglyMeasurable
      (by norm_num : (4 : ℝ≥0∞) ≠ 0) (by norm_num : (4 : ℝ≥0∞) ≠ ∞)).mp
    simpa only [ENNReal.toReal_ofNat, Real.norm_eq_abs,
      abs_of_nonneg (hφ0 _)] using hφ4
  have hcoord (z : Lattice) : MeasurePreserving (fun ω : Environment => ω z)
      (environmentLaw μ) μ := ⟨measurable_environment_eval z, environmentLaw_map_eval μ z⟩
  have hφMemZ (z : Lattice) : MemLp (fun ω : Environment => φ (ω z)) 4
      (environmentLaw μ) := hφMem.comp_measurePreserving (hcoord z)
  have hZMem : MemLp Z 4 (environmentLaw μ) := by
    dsimp [Z]
    exact memLp_finsetSum S fun z _ => hφMemZ z
  have hZ4 : Integrable (fun ω : Environment => Z ω^4) (environmentLaw μ) := by
    have hn := (hZMem.mono_exponent (by norm_num : (4 : ℝ≥0∞) ≤ 4)).integrable_norm_pow'
    apply (integrable_norm_iff (hZMem.aestronglyMeasurable.pow 4)).mp
    simpa only [Pi.pow_apply, norm_pow] using hn
  have hS34 : (∫ ω : Environment, Z ω^4 ∂environmentLaw μ) ≤
      34*((S.card : ℝ)*Cp*M^(4-p)+((S.card : ℝ)*Cp*M^(1-p))^4) := by
    dsimp [Z, φ, M, Cp]
    exact excess_fourth_moment_le μ hp hM hmoment S
  have hZlower : (∫ ω : Environment, Z ω^4 ∂environmentLaw μ) ≤ K*s^(8-p) := by
    have hfirst : (S.card : ℝ)*Cp*M^(4-p) ≤ A*s^(8-p) := by
      have hraw := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hcard hCp0)
        (Real.rpow_nonneg (le_of_lt hM) (4-p))
      have hMpower : M^(4-p) = (eta/4)^(4-p)*s^(4-p) := by
        dsimp [M]
        rw [show eta*s/4 = (eta/4)*s by ring,
          Real.mul_rpow (by positivity) (le_of_lt hs0)]
      calc
        _ ≤ (44*s^4)*Cp*M^(4-p) := hraw
        _ = A*s^(8-p) := by
          dsimp [A]
          rw [hMpower, show s^4 = s^(4 : ℝ) by simp]
          rw [show 8-p = 4+(4-p) by ring, Real.rpow_add hs0]
          ring
    have hsecondInner : (S.card : ℝ)*Cp*M^(1-p) ≤
        (44*Cp*(eta/4)^(1-p))*s^(5-p) := by
      have hraw := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hcard hCp0)
        (Real.rpow_nonneg (le_of_lt hM) (1-p))
      have hMpower : M^(1-p) = (eta/4)^(1-p)*s^(1-p) := by
        dsimp [M]
        rw [show eta*s/4 = (eta/4)*s by ring,
          Real.mul_rpow (by positivity) (le_of_lt hs0)]
      calc
        _ ≤ (44*s^4)*Cp*M^(1-p) := hraw
        _ = (44*Cp*(eta/4)^(1-p))*s^(5-p) := by
          rw [hMpower, show s^4 = s^(4 : ℝ) by simp,
            show 5-p = 4+(1-p) by ring, Real.rpow_add hs0]
          ring
    have hsecond : ((S.card : ℝ)*Cp*M^(1-p))^4 ≤ B*s^(20-4*p) := by
      have hpow := pow_le_pow_left₀
        (by positivity : 0 ≤ (S.card : ℝ)*Cp*M^(1-p)) hsecondInner 4
      have hspow : (s^(5-p))^4 = s^(20-4*p) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (le_of_lt hs0)]
        congr 1
        ring
      calc
        _ ≤ ((44*Cp*(eta/4)^(1-p))*s^(5-p))^4 := hpow
        _ = B*s^(20-4*p) := by
          rw [mul_pow, hspow]
    have hterms : A*s^(8-p)+B*s^(20-4*p) ≤ (A+B)*s^(8-p) := by
      calc
        _ ≤ A*s^(8-p)+B*s^(8-p) :=
          add_le_add le_rfl (mul_le_mul_of_nonneg_left hscaleExponent hB0)
        _ = (A+B)*s^(8-p) := by ring
    calc
      _ ≤ 34*((S.card : ℝ)*Cp*M^(4-p)+((S.card : ℝ)*Cp*M^(1-p))^4) := hS34
      _ ≤ 34*(A*s^(8-p)+B*s^(20-4*p)) := by
        apply mul_le_mul_of_nonneg_left (add_le_add hfirst hsecond)
        norm_num
      _ ≤ 34*((A+B)*s^(8-p)) := mul_le_mul_of_nonneg_left hterms (by norm_num)
      _ = K*s^(8-p) := by simp only [K, mul_assoc]
  let ν : Measure ℝ := (environmentLaw μ).map Z
  have : IsProbabilityMeasure ν := by
    dsimp [ν]
    infer_instance
  have hνMoment : (∫⁻ x, ENNReal.ofReal ((max x 0)^4) ∂ν) < ∞ := by
    have hG : Measurable (fun x : ℝ => ENNReal.ofReal ((max x 0)^4)) := by
      fun_prop
    change (∫⁻ x, ENNReal.ofReal ((max x 0)^4)
      ∂((environmentLaw μ).map Z)) < ∞
    rw [lintegral_map hG hZMeas]
    have heq : (fun ω : Environment => ENNReal.ofReal ((max (Z ω) 0)^4)) =ᵐ[
        environmentLaw μ] (fun ω => ENNReal.ofReal (Z ω^4)) := by
      filter_upwards with ω
      rw [max_eq_left (hZ0 ω)]
    rw [lintegral_congr_ae heq]
    exact hZ4.lintegral_lt_top
  have hmapMoment : (∫ x : ℝ, (max x 0)^4 ∂ν) =
      ∫ ω : Environment, (max (Z ω) 0)^4 ∂environmentLaw μ := by
    change (∫ x : ℝ, (max x 0)^4 ∂((environmentLaw μ).map Z)) = _
    exact integral_map hZMeas.aemeasurable (by fun_prop)
  have hmapMoment' : (∫ x : ℝ, (max x 0)^4 ∂ν) =
      ∫ ω : Environment, Z ω^4 ∂environmentLaw μ := by
    calc
      _ = ∫ ω : Environment, (max (Z ω) 0)^4 ∂environmentLaw μ := hmapMoment
      _ = _ := by
        apply integral_congr_ae
        filter_upwards with ω
        rw [max_eq_left (hZ0 ω)]
  have htailEq (t : ℝ) : ν (Ioi t) = (environmentLaw μ)
      {ω : Environment | t < ∑ z ∈ S, max (ω z-eta*s/4) 0} := by
    change ((environmentLaw μ).map Z) (Ioi t) = _
    rw [Measure.map_apply hZMeas measurableSet_Ioi]
    rfl
  have hgeneric := integrated_sqrt_positive_tail_le_two_fourth_root ν hνMoment
  have hactual : (∫⁻ t in Ioi (0 : ℝ),
      (environmentLaw μ) {ω : Environment | t < ∑ z ∈ S, max (ω z-eta*s/4) 0}^
        (1/2 : ℝ)) ≤ ENNReal.ofReal (2*(∫ x : ℝ, (max x 0)^4 ∂ν)^(1/4 : ℝ)) := by
    simpa only [htailEq] using hgeneric
  rw [hmapMoment'] at hactual
  have hX0 : 0 ≤ ∫ ω : Environment, Z ω^4 ∂environmentLaw μ :=
    integral_nonneg fun ω => by positivity
  have hroot : (∫ ω : Environment, Z ω^4 ∂environmentLaw μ)^(1/4 : ℝ) ≤
      K^(1/4 : ℝ)*s^(2-p/4) := by
    calc
      _ ≤ (K*s^(8-p))^(1/4 : ℝ) :=
        Real.rpow_le_rpow hX0 hZlower (by norm_num : (0 : ℝ) ≤ 1/4)
      _ = K^(1/4 : ℝ)*s^(2-p/4) := by
        rw [Real.mul_rpow hK0 (Real.rpow_nonneg (le_of_lt hs0) _),
          ← Real.rpow_mul (le_of_lt hs0)]
        congr 2
        ring
  have hscalePos : 0 < s^(2-p/4) := Real.rpow_pos_of_pos hs0 _
  have hcoef : 2*K^(1/4 : ℝ) ≤ C := by
    dsimp [C]
    have : 0 ≤ K^(1/4 : ℝ) := Real.rpow_nonneg hK0 _
    linarith
  have hfinalReal : 2*(∫ ω : Environment, Z ω^4 ∂environmentLaw μ)^(1/4 : ℝ) ≤
      C*s^(2-p/4) := by
    calc
      _ ≤ 2*(K^(1/4 : ℝ)*s^(2-p/4)) :=
        mul_le_mul_of_nonneg_left hroot (by norm_num)
      _ = (2*K^(1/4 : ℝ))*s^(2-p/4) := by ring
      _ ≤ C*s^(2-p/4) := mul_le_mul_of_nonneg_right hcoef (le_of_lt hscalePos)
  exact hactual.trans (ENNReal.ofReal_le_ofReal hfinalReal)

end LPPDifferentiability
