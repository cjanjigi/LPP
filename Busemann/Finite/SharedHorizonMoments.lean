/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Busemann.Finite.ExpectedPressure
public import Busemann.Finite.SharedHorizonMean
import Busemann.Finite.NegativeTails
import Busemann.Finite.Measurability
import LPP_Foundations.Probability.MartinFirstMoment
import ProbabilityBasics.Probability.AbsoluteMomentLowerTail
import Mathlib.Topology.Order.LiminfLimsup
import Mathlib.Tactic

/-! Mean and uniform absolute-mean control for the actual shared-horizon edge. -/

@[expose] public section

open MeasureTheory Filter LPPDifferentiability
open scoped ENNReal Topology

namespace LPP.Busemann

private theorem tendsto_signed_shifted_ratio (f : ℕ → ℝ) (m : ℤ)
    (hf : Tendsto (fun k : ℕ => f k / (k : ℝ)) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => f (((n : ℤ) + 1 - m).toNat) / ((n : ℝ) + 1))
      atTop (𝓝 0) := by
  let K : ℕ → ℕ := fun n => ((n : ℤ) + 1 - m).toNat
  have hK : Tendsto K atTop atTop := by
    apply tendsto_atTop.2
    intro b
    filter_upwards [eventually_ge_atTop (b + m.natAbs + 1)] with n hn
    have hm : m ≤ (m.natAbs : ℤ) := Int.le_natAbs
    have hnonneg : 0 ≤ (n : ℤ) + 1 - m := by omega
    have hcast := Int.toNat_of_nonneg hnonneg
    dsimp only [K]
    omega
  have hdiv (c : ℝ) : Tendsto (fun n : ℕ => c / ((n : ℝ) + 1)) atTop (𝓝 0) := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      (tendsto_add_atTop_iff_nat 1).2 (tendsto_const_div_atTop_nhds_zero_nat c)
  have hratio : Tendsto (fun n : ℕ => (K n : ℝ) / ((n : ℝ) + 1)) atTop (𝓝 1) := by
    have ht : Tendsto (fun n : ℕ => 1 - (m : ℝ) / ((n : ℝ) + 1)) atTop (𝓝 1) := by
      simpa only [sub_zero] using (tendsto_const_nhds (x := (1 : ℝ))).sub (hdiv (m : ℝ))
    apply ht.congr'
    filter_upwards [eventually_ge_atTop (m.natAbs + 1)] with n hn
    have hm : m ≤ (m.natAbs : ℤ) := Int.le_natAbs
    have hnonneg : 0 ≤ (n : ℤ) + 1 - m := by omega
    have hcastInt : ((K n : ℕ) : ℤ) = (n : ℤ) + 1 - m :=
      Int.toNat_of_nonneg hnonneg
    have hcast : (K n : ℝ) = (n : ℝ) + 1 - (m : ℝ) := by exact_mod_cast hcastInt
    rw [hcast]
    have hden : (n : ℝ) + 1 ≠ 0 := by positivity
    field_simp [hden]
  have hprod := (hf.comp hK).mul hratio
  simp only [zero_mul] at hprod
  apply hprod.congr'
  filter_upwards [hK.eventually (eventually_ge_atTop 1)] with n hn
  have hkn : (K n : ℝ) ≠ 0 := by exact_mod_cast (show K n ≠ 0 by omega)
  simp only [Function.comp_apply]
  change (f (K n) / (K n : ℝ)) * ((K n : ℝ) / ((n : ℝ) + 1)) =
    f (K n) / ((n : ℝ) + 1)
  field_simp [hkn]

private theorem first_moment_of_native (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hmoment : ∃ p : ℝ, 2 < p ∧ (∫⁻ x, ENNReal.ofReal (|x| ^ p) ∂μ) < ∞) :
    Integrable (fun t : ℝ => t) μ := by
  obtain ⟨p, hp, hpMoment⟩ := hmoment
  have hpos := (ProbabilityBasics.negative_moment_and_positive_tail_of_absolute_moment
    μ hp hpMoment).2
  have hneg := ProbabilityBasics.integrated_sqrt_lower_tail_lt_top_of_absolute_moment
    μ hp hpMoment
  exact integrable_id_of_martin_tails μ hneg hpos

/-- At a supporting tilt the actual shared-horizon finite edge has mean
converging to the negative tilt coordinate, as in JR arXiv:1810.03580v3,
proof of Theorem 4.8 and corrected equation (4.17). -/
theorem tendsto_integral_finiteBusemannEdge_sharedHorizon
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hmoment : ∃ p : ℝ, 2 < p ∧ (∫⁻ t, ENNReal.ofReal (|t| ^ p) ∂μ) < ∞)
    (g : Quadrant → ℝ) (hg : IsExpectedRateShape μ g) (h : SupportTilt g)
    (x : Lattice) (i : Fin 2) :
    Tendsto (fun n : ℕ => ∫ p : Environment × Fin (n + 1),
      finiteBusemannEdge p.1 h.val x ((p.2.val + 1 : ℕ) : ℤ) i
        ∂finiteBusemannSharedHorizonLaw μ n) atTop (𝓝 (-finiteTiltCoordinate h.val i)) := by
  let f : ℕ → ℝ := fun k => ∫ ω : Environment,
    (finiteTiltedPotential ω h.val 0 (k : ℤ)).toReal ∂environmentLaw μ
  let m : ℤ := x.1 + x.2
  let t : ℝ := finiteTiltCoordinate h.val i
  have hμ := first_moment_of_native μ hmoment
  have hf : Tendsto (fun k : ℕ => f k / (k : ℝ)) atTop (𝓝 0) :=
    integral_finiteTiltedPotential_div_tendsto_zero μ hmoment g hg h
  have htop := tendsto_signed_shifted_ratio f m hf
  have hdiv (c : ℝ) : Tendsto (fun n : ℕ => c / ((n : ℝ) + 1)) atTop (𝓝 0) := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      (tendsto_add_atTop_iff_nat 1).2 (tendsto_const_div_atTop_nhds_zero_nat c)
  have hcount : Tendsto (fun n : ℕ =>
      1 - (max m 0 : ℝ) / ((n : ℝ) + 1)) atTop (𝓝 1) := by
    simpa only [sub_zero] using
      (tendsto_const_nhds (x := (1 : ℝ))).sub (hdiv (max m 0 : ℝ))
  have hlimit : Tendsto (fun n : ℕ =>
      f (((n : ℤ) + 1 - m).toNat) / ((n : ℝ) + 1) -
        f ((max (-m) 0).toNat) / ((n : ℝ) + 1) -
        (1 - (max m 0 : ℝ) / ((n : ℝ) + 1)) * t) atTop (𝓝 (-t)) := by
    simpa only [sub_self, one_mul, zero_sub] using
      (htop.sub (hdiv (f ((max (-m) 0).toNat)))).sub (hcount.mul tendsto_const_nhds)
  apply hlimit.congr'
  filter_upwards [eventually_ge_atTop ((max m 0).natAbs + 1)] with n hn
  have hw : max (x.1 + x.2) 0 < (n : ℤ) + 1 := by
    have hm : max m 0 ≤ ((max m 0).natAbs : ℤ) := Int.le_natAbs
    dsimp [m] at hm
    omega
  have hfinite := integral_finiteBusemannEdge_sharedHorizon μ hμ h.val x i n hw
  dsimp only at hfinite
  rw [hfinite]
  dsimp only [f, m, t]
  simp only [Int.cast_max, Int.cast_zero]
  have hden : (n : ℝ) + 1 ≠ 0 := by positivity
  field_simp [hden]

/-- The actual finite shared-horizon edge has a uniform bound on its absolute
mean, including the initial windows, in the setting of JR arXiv:1810.03580v3,
proof of Theorem 4.8 after equation (4.17). -/
theorem exists_uniform_integral_abs_finiteBusemannEdge_sharedHorizon_bound
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hmoment : ∃ p : ℝ, 2 < p ∧ (∫⁻ t, ENNReal.ofReal (|t| ^ p) ∂μ) < ∞)
    (g : Quadrant → ℝ) (hg : IsExpectedRateShape μ g) (h : SupportTilt g)
    (x : Lattice) (i : Fin 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ,
      (∫ p : Environment × Fin (n + 1),
        |finiteBusemannEdge p.1 h.val x ((p.2.val + 1 : ℕ) : ℤ) i|
          ∂finiteBusemannSharedHorizonLaw μ n) ≤ C := by
  let E : (n : ℕ) → Environment × Fin (n + 1) → ℝ := fun n p =>
    finiteBusemannEdge p.1 h.val x ((p.2.val + 1 : ℕ) : ℤ) i
  let a : ℕ → ℝ := fun n => ∫ p, E n p ∂finiteBusemannSharedHorizonLaw μ n
  let b : ℝ := ∫ t : ℝ, max (-t) 0 ∂μ
  have hμ := first_moment_of_native μ hmoment
  have ha : Tendsto a atTop (𝓝 (-finiteTiltCoordinate h.val i)) :=
    tendsto_integral_finiteBusemannEdge_sharedHorizon μ hmoment g hg h x i
  obtain ⟨A, hA⟩ := ha.bddAbove_range
  refine ⟨max 0 (A + 2 * b), le_max_left _ _, ?_⟩
  intro n
  have hi : Integrable (E n) (finiteBusemannSharedHorizonLaw μ n) := by
    rw [finiteBusemannSharedHorizonLaw]
    exact integrable_uniformOrigin_family (environmentLaw μ) n
      (fun k ω => finiteBusemannEdge ω h.val x ((k.val + 1 : ℕ) : ℤ) i)
      (fun k => measurable_finiteBusemannEdge h.val x ((k.val + 1 : ℕ) : ℤ) i)
      (fun k => integrable_finiteBusemannEdge μ hμ h.val x ((k.val + 1 : ℕ) : ℤ) i)
  have hneg := integral_finite_busemann_edge_negative_excess_shared_horizon_le
    μ hμ h.val x i n 0 le_rfl
  have ht : (∫ p, max (-E n p) 0 ∂finiteBusemannSharedHorizonLaw μ n) ≤ b := by
    simpa only [E, b, sub_zero] using hneg
  have hid : (fun p => |E n p|) = fun p => E n p + 2 * max (-E n p) 0 := by
    funext p
    by_cases hp : 0 ≤ E n p
    · rw [abs_of_nonneg hp, max_eq_right (neg_nonpos.mpr hp)]
      ring
    · have hn : E n p ≤ 0 := le_of_not_ge hp
      rw [abs_of_nonpos hn, max_eq_left (neg_nonneg.mpr hn)]
      ring
  have hmean : a n ≤ A := hA ⟨n, rfl⟩
  have hiNeg : Integrable (fun p => max (-E n p) 0)
      (finiteBusemannSharedHorizonLaw μ n) := by
    simpa only [Pi.neg_apply] using hi.neg.pos_part
  have hsum : (∫ p, E n p + 2 * max (-E n p) 0
      ∂finiteBusemannSharedHorizonLaw μ n) =
      a n + ∫ p, 2 * max (-E n p) 0 ∂finiteBusemannSharedHorizonLaw μ n := by
    have hh := integral_add hi (hiNeg.const_mul 2)
    simpa only [Pi.add_apply, Pi.mul_apply] using hh
  calc
    (∫ p, |E n p| ∂finiteBusemannSharedHorizonLaw μ n) =
        a n + 2 * (∫ p, max (-E n p) 0 ∂finiteBusemannSharedHorizonLaw μ n) := by
      rw [hid, hsum, integral_const_mul]
    _ ≤ A + 2 * b := by linarith only [hmean, ht]
    _ ≤ max 0 (A + 2 * b) := le_max_right _ _

end LPP.Busemann
