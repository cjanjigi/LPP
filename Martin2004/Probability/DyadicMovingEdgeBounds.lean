/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Martin2004.Probability.NegativeMomentBounds
public import LPP_Foundations.Probability.CoordinateLaw
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Real

import ProbabilityBasics.Probability.IndependentCenteredMoment
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-!
# Moving dyadic mesh edges under an actual negative moment

The negative part of the original iid environment has simultaneous eventual
bounds along every terminal-excluded horizontal and vertical mesh edge.
The proof produces actual centered moments and deterministic-edge independence,
uses the independent centered-sum inequality, then applies Markov,
a finite union, dyadic summability and the first Borel-Cantelli lemma.
One original-environment almost-sure event precedes every real tolerance.
-/

public section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal BigOperators

namespace LPPDifferentiability

private theorem dyadic_edge_power_summable {r : ℝ} (hr : 1 < r) :
    Summable (fun k : ℕ => (((2 : ℕ) ^ k : ℕ) : ℝ) ^ (1 - r)) := by
  have hratio : ‖(2 : ℝ) ^ (1 - r)‖ < 1 := by
    rw [Real.norm_of_nonneg (Real.rpow_nonneg (by norm_num) _)]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (sub_neg.mpr hr)
  have hseries := summable_geometric_of_norm_lt_one hratio
  simpa only [Nat.cast_pow, Nat.cast_ofNat,
    Real.rpow_pow_comm (by norm_num : (0 : ℝ) ≤ 2)] using hseries

private theorem measureReal_gt_le_integral_abs_rpow_div
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (f : Ω → ℝ) {r t : ℝ} (hr : 0 ≤ r) (ht : 0 < t)
    (hf : Integrable (fun ω => |f ω| ^ r) P) :
    P.real {ω | t < f ω} ≤ (∫ ω, |f ω| ^ r ∂P) / t ^ r := by
  have ht_power : 0 < t ^ r := Real.rpow_pos_of_pos ht r
  have hmarkov := mul_meas_ge_le_integral_of_nonneg
    (Filter.Eventually.of_forall (fun ω => Real.rpow_nonneg (abs_nonneg (f ω)) r))
    hf (t ^ r)
  calc
    P.real {ω | t < f ω} ≤ P.real {ω | t ^ r ≤ |f ω| ^ r} := by
      refine measureReal_mono ?_ (measure_ne_top P _)
      intro ω hω
      exact Real.rpow_le_rpow ht.le
        (le_trans (le_of_lt hω) (le_abs_self (f ω))) hr
    _ ≤ (∫ ω, |f ω| ^ r ∂P) / t ^ r := by
      apply (le_div_iff₀ ht_power).2
      simpa only [mul_comm] using hmarkov

private theorem moving_edge_markov_coefficient
    {a q h r M : ℝ} (ha : 0 < a) (hq : 0 < q) (hh : 0 < h) :
    (2 : ℝ) ^ r * h * M / (a * q * h) ^ r =
      ((2 : ℝ) ^ r * M / (a * q) ^ r) * h ^ (1 - r) := by
  rw [Real.mul_rpow (mul_pos ha hq).le hh.le,
    Real.rpow_sub hh 1 r, Real.rpow_one]
  ring

private theorem moving_mesh_edge_index_card (q : ℕ) :
    Fintype.card (Bool × Fin (2 * q) × Fin (2 * q + 1)) =
      2 * (2 * q) * (2 * q + 1) := by
  simp only [Fintype.card_prod, Fintype.card_bool, Fintype.card_fin]
  ring

private theorem negativePart_centered_coordinate_mean
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (p : ℝ) (hp : 1 < p)
    (hmoment : (∫⁻ t, ENNReal.ofReal ((max (-t) 0) ^ p) ∂μ) < ∞)
    (z : Lattice) :
    (∫ ω : Environment, max (-ω z) 0 - (∫ t, max (-t) 0 ∂μ)
      ∂environmentLaw μ) = 0 := by
  have hY := integrable_negativePart_of_lintegral_lt_top μ p hp hmoment
  have hcenter : Measurable (fun t : ℝ => max (-t) 0 -
      (∫ s, max (-s) 0 ∂μ)) := by fun_prop
  calc
    _ = ∫ t, max (-t) 0 - (∫ s, max (-s) 0 ∂μ)
        ∂(environmentLaw μ).map (fun ω : Environment => ω z) :=
      (integral_map_of_stronglyMeasurable (measurable_environment_eval z)
        hcenter.stronglyMeasurable).symm
    _ = ∫ t, max (-t) 0 - (∫ s, max (-s) 0 ∂μ) ∂μ := by
      rw [environmentLaw_map_eval]
    _ = 0 := by rw [integral_sub hY (integrable_const _), integral_const]; simp

private theorem negativePart_centered_coordinate_power_integrable
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (p : ℝ) (hp : 1 < p)
    (hmoment : (∫⁻ t, ENNReal.ofReal ((max (-t) 0) ^ p) ∂μ) < ∞)
    (z : Lattice) :
    Integrable (fun ω : Environment =>
      |max (-ω z) 0 - (∫ t, max (-t) 0 ∂μ)| ^ min p 2)
      (environmentLaw μ) := by
  have hcoordinate : MeasurePreserving (fun ω : Environment => ω z)
      (environmentLaw μ) μ :=
    ⟨measurable_environment_eval z, environmentLaw_map_eval μ z⟩
  exact hcoordinate.integrable_comp_of_integrable
    (integrable_centered_negativePart_rpow_of_lintegral_lt_top μ p hp hmoment)

private theorem iIndepFun_negativePart_centered_samples
    {I : Type*} (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (f : I → Lattice) (hf : Function.Injective f) :
    ProbabilityTheory.iIndepFun (fun i (ω : Environment) =>
      max (-ω (f i)) 0 - (∫ t, max (-t) 0 ∂μ)) (environmentLaw μ) := by
  exact ((iIndepFun_environment_eval μ).precomp hf).comp
    (fun _ (t : ℝ) => max (-t) 0 - (∫ s, max (-s) 0 ∂μ)) (fun _ => by fun_prop)

private theorem horizontal_edge_sites_injective (x y h : ℕ) :
    Function.Injective (fun l : Fin h =>
      (((x + l : ℕ) : ℤ), ((y : ℕ) : ℤ))) := by
  intro l m hlm
  apply Fin.ext
  have hfirst := congrArg Prod.fst hlm
  exact Nat.add_left_cancel (Int.ofNat_inj.mp hfirst)

private theorem vertical_edge_sites_injective (x y h : ℕ) :
    Function.Injective (fun l : Fin h =>
      (((x : ℕ) : ℤ), ((y + l : ℕ) : ℤ))) := by
  intro l m hlm
  apply Fin.ext
  have hsecond := congrArg Prod.snd hlm
  exact Nat.add_left_cancel (Int.ofNat_inj.mp hsecond)


private theorem negativePart_centered_coordinate_power_integral
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (p : ℝ) (z : Lattice) :
    (∫ ω : Environment,
      |max (-ω z) 0 - (∫ t, max (-t) 0 ∂μ)| ^ min p 2 ∂environmentLaw μ) =
      ∫ t, |max (-t) 0 - (∫ s, max (-s) 0 ∂μ)| ^ min p 2 ∂μ := by
  have hpower : Measurable (fun t : ℝ =>
      |max (-t) 0 - (∫ s, max (-s) 0 ∂μ)| ^ min p 2) := by fun_prop
  calc
    _ = ∫ t, |max (-t) 0 - (∫ s, max (-s) 0 ∂μ)| ^ min p 2
        ∂(environmentLaw μ).map (fun ω : Environment => ω z) :=
      (integral_map_of_stronglyMeasurable (measurable_environment_eval z)
        hpower.stronglyMeasurable).symm
    _ = _ := by rw [environmentLaw_map_eval]

private theorem negativePart_centered_samples_moment_bound
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (p : ℝ) (hp : 1 < p)
    (hmoment : (∫⁻ t, ENNReal.ofReal ((max (-t) 0) ^ p) ∂μ) < ∞)
    (h : ℕ) (f : Fin h → Lattice) (hf : Function.Injective f) :
    Integrable (fun ω : Environment =>
      |∑ l : Fin h, (max (-ω (f l)) 0 - (∫ t, max (-t) 0 ∂μ))| ^ min p 2)
      (environmentLaw μ) ∧
    (∫ ω : Environment,
      |∑ l : Fin h, (max (-ω (f l)) 0 - (∫ t, max (-t) 0 ∂μ))| ^ min p 2
        ∂environmentLaw μ) ≤
      (2 : ℝ) ^ min p 2 * h *
        (∫ t, |max (-t) 0 - (∫ s, max (-s) 0 ∂μ)| ^ min p 2 ∂μ) := by
  let Z : Fin h → Environment → ℝ := fun l ω =>
    max (-ω (f l)) 0 - (∫ t, max (-t) 0 ∂μ)
  have hZ (l : Fin h) : Measurable (Z l) := by dsimp [Z]; fun_prop
  have hfull := integrable_and_integral_abs_rpow_sum_independent_centered_le
    (environmentLaw μ) Finset.univ Z hZ
    (iIndepFun_negativePart_centered_samples μ f hf)
    (one_lt_min_p_two_of_one_lt hp).le (min_p_two_le_two p)
    (fun l _ => negativePart_centered_coordinate_power_integrable μ p hp hmoment (f l))
    (fun l _ => negativePart_centered_coordinate_mean μ p hp hmoment (f l))
  refine ⟨hfull.2.1, ?_⟩
  calc
    _ ≤ (2 : ℝ) ^ min p 2 * ∑ l : Fin h,
        (∫ ω : Environment, |Z l ω| ^ min p 2 ∂environmentLaw μ) := hfull.2.2
    _ = _ := by
      simp only [Z, negativePart_centered_coordinate_power_integral μ p,
        Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring


private theorem negativePart_samples_tail
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (p : ℝ) (hp : 1 < p)
    (hmoment : (∫⁻ t, ENNReal.ofReal ((max (-t) 0) ^ p) ∂μ) < ∞)
    (h q : ℕ) (hh : 0 < h) (hq : 1 ≤ q) (a : ℝ) (ha : 0 < a)
    (f : Fin h → Lattice) (hf : Function.Injective f) :
    (environmentLaw μ).real {ω : Environment |
      (h : ℝ) * (∫ t, max (-t) 0 ∂μ) + a * q * h <
        ∑ l : Fin h, max (-ω (f l)) 0} ≤
      ((2 : ℝ) ^ min p 2 *
        (∫ t, |max (-t) 0 - (∫ s, max (-s) 0 ∂μ)| ^ min p 2 ∂μ) /
          (a * q) ^ min p 2) * (h : ℝ) ^ (1 - min p 2) := by
  have hsum := negativePart_centered_samples_moment_bound μ p hp hmoment h f hf
  have hhR : (0 : ℝ) < h := Nat.cast_pos.mpr hh
  have hqR : (0 : ℝ) < q := Nat.cast_pos.mpr (lt_of_lt_of_le Nat.zero_lt_one hq)
  have hthreshold : 0 < a * q * h := mul_pos (mul_pos ha hqR) hhR
  have hcenter (ω : Environment) :
      (∑ l : Fin h, (max (-ω (f l)) 0 - (∫ t, max (-t) 0 ∂μ))) =
        (∑ l : Fin h, max (-ω (f l)) 0) - (h : ℝ) * (∫ t, max (-t) 0 ∂μ) := by
    simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
  have hevent : {ω : Environment |
      (h : ℝ) * (∫ t, max (-t) 0 ∂μ) + a * q * h < ∑ l : Fin h, max (-ω (f l)) 0} =
      {ω : Environment | a * q * h <
        ∑ l : Fin h, (max (-ω (f l)) 0 - (∫ t, max (-t) 0 ∂μ))} := by
    ext ω
    simp only [Set.mem_ofPred_eq, hcenter]
    constructor <;> intro hlt <;> linarith only [hlt]
  rw [hevent]
  calc
    _ ≤ (∫ ω : Environment,
        |∑ l : Fin h, (max (-ω (f l)) 0 - (∫ t, max (-t) 0 ∂μ))| ^ min p 2
          ∂environmentLaw μ) / (a * q * h) ^ min p 2 :=
      measureReal_gt_le_integral_abs_rpow_div (environmentLaw μ) _
        (le_of_lt (lt_trans zero_lt_one (one_lt_min_p_two_of_one_lt hp)))
        hthreshold hsum.1
    _ ≤ ((2 : ℝ) ^ min p 2 * h *
        (∫ t, |max (-t) 0 - (∫ s, max (-s) 0 ∂μ)| ^ min p 2 ∂μ)) /
          (a * q * h) ^ min p 2 :=
      div_le_div_of_nonneg_right hsum.2 (Real.rpow_nonneg hthreshold.le _)
    _ = _ := moving_edge_markov_coefficient ha hqR hhR

private def movingMeshSite (q k : ℕ)
    (e : Bool × Fin (2 * q) × Fin (2 * q + 1)) (l : Fin (2 ^ k)) : Lattice :=
  if e.1 then
    ((((e.2.2.val * 2 ^ k : ℕ) : ℤ)), (((e.2.1.val * 2 ^ k + l.val : ℕ) : ℤ)))
  else
    ((((e.2.1.val * 2 ^ k + l.val : ℕ) : ℤ)), (((e.2.2.val * 2 ^ k : ℕ) : ℤ)))

private theorem movingMeshSite_injective (q k : ℕ)
    (e : Bool × Fin (2 * q) × Fin (2 * q + 1)) :
    Function.Injective (movingMeshSite q k e) := by
  rcases e with ⟨b, i, j⟩
  cases b
  · exact horizontal_edge_sites_injective (i.val * 2 ^ k) (j.val * 2 ^ k) (2 ^ k)
  · exact vertical_edge_sites_injective (j.val * 2 ^ k) (i.val * 2 ^ k) (2 ^ k)

private theorem ae_all_tolerances_of_finite_family_dyadic_power_tail
    {Ω I : Type*} [MeasurableSpace Ω] [Fintype I]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (N : ℕ) (hcard : Fintype.card I = N)
    (S : ℕ → I → Ω → ℝ) (q : ℕ) {r : ℝ} (hr : 1 < r)
    (hTail : ∀ a : ℝ, 0 < a → ∃ C : ℝ, 0 ≤ C ∧
      ∀ k : ℕ, ∀ e : I,
        P.real {ω | a * q * (((2 : ℕ) ^ k : ℕ) : ℝ) < S k e ω} ≤
          C * (((2 : ℕ) ^ k : ℕ) : ℝ) ^ (1 - r)) :
    ∀ᵐ ω ∂P, ∀ a : ℝ, 0 < a → ∃ K : ℕ, ∀ k : ℕ, K ≤ k →
      ∀ e : I, S k e ω ≤ a * q * (((2 : ℕ) ^ k : ℕ) : ℝ) := by
  classical
  have hfixed (a : ℝ) (ha : 0 < a) :
      ∀ᵐ ω ∂P, ∀ᶠ k : ℕ in Filter.atTop,
        ∀ e : I, S k e ω ≤ a * q * (((2 : ℕ) ^ k : ℕ) : ℝ) := by
    obtain ⟨C, _hC, hbound⟩ := hTail a ha
    let A : ℕ → I → Set Ω := fun k e =>
      {ω | a * q * (((2 : ℕ) ^ k : ℕ) : ℝ) < S k e ω}
    let B : ℕ → Set Ω := fun k => ⋃ e : I, A k e
    have hB (k : ℕ) : P.real (B k) ≤
        (N : ℝ) * C *
          (((2 : ℕ) ^ k : ℕ) : ℝ) ^ (1 - r) := by
      calc
        P.real (B k) ≤ ∑ e : I, P.real (A k e) :=
          measureReal_iUnion_fintype_le _
        _ ≤ ∑ _e : I, C * (((2 : ℕ) ^ k : ℕ) : ℝ) ^ (1 - r) :=
          Finset.sum_le_sum (fun e _ => hbound k e)
        _ = _ := by simp only [Finset.sum_const, Finset.card_univ, hcard, nsmul_eq_mul]; ring
    have hreal : Summable (fun k : ℕ => P.real (B k)) := by
      apply Summable.of_nonneg_of_le (fun _ => measureReal_nonneg) hB
      exact (dyadic_edge_power_summable hr).mul_left ((N : ℝ) * C)
    have hsum : (∑' k : ℕ, P (B k)) ≠ ∞ := by
      calc
        (∑' k : ℕ, P (B k)) = ∑' k : ℕ, ENNReal.ofReal (P.real (B k)) := by
          apply tsum_congr
          intro k
          exact (ofReal_measureReal (measure_ne_top P _)).symm
        _ = ENNReal.ofReal (∑' k : ℕ, P.real (B k)) :=
          (ENNReal.ofReal_tsum_of_nonneg (fun _ => measureReal_nonneg) hreal).symm
        _ ≠ ∞ := ENNReal.ofReal_ne_top
    filter_upwards [MeasureTheory.ae_eventually_notMem hsum] with ω hω
    filter_upwards [hω] with k hk
    intro e
    apply le_of_not_gt
    intro hbad
    exact hk (Set.mem_iUnion.mpr ⟨e, hbad⟩)
  have hall : ∀ᵐ ω ∂P, ∀ n : ℕ, ∀ᶠ k : ℕ in Filter.atTop,
      ∀ e : I, S k e ω ≤
        (1 / ((n : ℝ) + 1)) * q * (((2 : ℕ) ^ k : ℕ) : ℝ) :=
    ae_all_iff.mpr fun n => hfixed _ (by positivity)
  filter_upwards [hall] with ω hω
  intro a ha
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt ha
  obtain ⟨K, hK⟩ := Filter.eventually_atTop.mp (hω n)
  refine ⟨K, fun k hk e => (hK k hk e).trans ?_⟩
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hn.le (Nat.cast_nonneg q)) (Nat.cast_nonneg _)



/-- From only an actual negative moment above one, all moving dyadic mesh edges
are eventually bounded on one original-environment event before every real
positive tolerance. Every literal sum includes its start and excludes its end. -/
theorem ae_eventually_all_dyadic_negativePart_mesh_edges
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (p : ℝ) (hp : 1 < p)
    (hmoment : (∫⁻ t, ENNReal.ofReal ((max (-t) 0) ^ p) ∂μ) < ∞)
    (q : ℕ) (hq : 1 ≤ q) :
    ∀ᵐ ω ∂environmentLaw μ, ∀ a : ℝ, 0 < a →
      ∃ K : ℕ, ∀ k : ℕ, K ≤ k →
        ∀ i : ℕ, i < 2 * q → ∀ j : ℕ, j ≤ 2 * q →
          (∑ l ∈ Finset.range (2 ^ k),
            max (-ω (((i * 2 ^ k + l : ℕ) : ℤ), ((j * 2 ^ k : ℕ) : ℤ))) 0) ≤
              (2 ^ k : ℝ) * (∫ t, max (-t) 0 ∂μ) + a * q * (2 ^ k : ℝ) ∧
          (∑ l ∈ Finset.range (2 ^ k),
            max (-ω (((j * 2 ^ k : ℕ) : ℤ), ((i * 2 ^ k + l : ℕ) : ℤ))) 0) ≤
              (2 ^ k : ℝ) * (∫ t, max (-t) 0 ∂μ) + a * q * (2 ^ k : ℝ) := by
  let S : ℕ → (Bool × Fin (2 * q) × Fin (2 * q + 1)) → Environment → ℝ :=
    fun k e ω => (∑ l : Fin (2 ^ k), max (-ω (movingMeshSite q k e l)) 0) -
      (2 ^ k : ℝ) * (∫ t, max (-t) 0 ∂μ)
  have htail (a : ℝ) (ha : 0 < a) : ∃ C : ℝ, 0 ≤ C ∧
      ∀ k : ℕ, ∀ e : Bool × Fin (2 * q) × Fin (2 * q + 1),
        (environmentLaw μ).real {ω | a * q * (((2 : ℕ) ^ k : ℕ) : ℝ) < S k e ω} ≤
          C * (((2 : ℕ) ^ k : ℕ) : ℝ) ^ (1 - min p 2) := by
    let C := (2 : ℝ) ^ min p 2 *
      (∫ t, |max (-t) 0 - (∫ s, max (-s) 0 ∂μ)| ^ min p 2 ∂μ) / (a * q) ^ min p 2
    refine ⟨C, ?_, ?_⟩
    · exact div_nonneg (mul_nonneg (Real.rpow_nonneg (by norm_num) _)
        (integral_nonneg (fun t => Real.rpow_nonneg (abs_nonneg _) _)))
        (Real.rpow_nonneg (mul_nonneg ha.le (Nat.cast_nonneg q)) _)
    · intro k e
      have h := negativePart_samples_tail μ p hp hmoment (2 ^ k) q
        (pow_pos (by norm_num) k) hq a ha (movingMeshSite q k e) (movingMeshSite_injective q k e)
      have hevent : {ω | a * q * (((2 : ℕ) ^ k : ℕ) : ℝ) < S k e ω} =
          {ω : Environment | (((2 : ℕ) ^ k : ℕ) : ℝ) * (∫ t, max (-t) 0 ∂μ) +
            a * q * (((2 : ℕ) ^ k : ℕ) : ℝ) <
              ∑ l : Fin (2 ^ k), max (-ω (movingMeshSite q k e l)) 0} := by
        ext ω
        simp only [Set.mem_ofPred_eq, S, Nat.cast_pow, Nat.cast_ofNat]
        constructor <;> intro hlt <;> linarith only [hlt]
      rw [hevent]
      exact h
  have hAE := ae_all_tolerances_of_finite_family_dyadic_power_tail
    (environmentLaw μ) (2 * (2 * q) * (2 * q + 1))
      (moving_mesh_edge_index_card q) S q (one_lt_min_p_two_of_one_lt hp) htail
  filter_upwards [hAE] with ω hω
  intro a ha
  obtain ⟨K, hK⟩ := hω a ha
  refine ⟨K, ?_⟩
  intro k hk i hi j hj
  have hhor := hK k hk (false, ⟨i, hi⟩, ⟨j, Nat.lt_succ_of_le hj⟩)
  have hver := hK k hk (true, ⟨i, hi⟩, ⟨j, Nat.lt_succ_of_le hj⟩)
  simp only [S, movingMeshSite, Bool.false_eq_true, ite_false, ite_true,
    Nat.cast_pow, Nat.cast_ofNat] at hhor hver
  rw [Fin.sum_univ_eq_sum_range (fun l : ℕ =>
    max (-ω (((i * 2 ^ k + l : ℕ) : ℤ), ((j * 2 ^ k : ℕ) : ℤ))) 0) (2 ^ k)] at hhor
  rw [Fin.sum_univ_eq_sum_range (fun l : ℕ =>
    max (-ω (((j * 2 ^ k : ℕ) : ℤ), ((i * 2 ^ k + l : ℕ) : ℤ))) 0) (2 ^ k)] at hver
  constructor <;> linarith only [hhor, hver]

end LPPDifferentiability
