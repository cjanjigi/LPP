/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import ProbabilityBasics.Probability.CenteredRpowSum
import Mathlib.Probability.Independence.Integration
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Tactic

/-! The real-order independent sum estimate used in the upper-tail remark. -/

public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators

namespace LPPDifferentiability

private theorem rpow_add_le_two_rpow_mul {a b q : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hq : 0 ≤ q) :
    (a + b) ^ q ≤ (2 : ℝ) ^ q * (a ^ q + b ^ q) := by
  have hmax : 0 ≤ max a b := ha.trans (le_max_left _ _)
  have hadd : a + b ≤ 2 * max a b := by
    linarith only [le_max_left a b, le_max_right a b]
  calc
    (a + b) ^ q ≤ (2 * max a b) ^ q :=
      Real.rpow_le_rpow (add_nonneg ha hb) hadd hq
    _ = (2 : ℝ) ^ q * (max a b) ^ q := Real.mul_rpow (by norm_num) hmax
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      rcases le_total a b with hab | hba
      · rw [max_eq_right hab]
        exact le_add_of_nonneg_left (Real.rpow_nonneg ha _)
      · rw [max_eq_left hba]
        exact le_add_of_nonneg_right (Real.rpow_nonneg hb _)

private theorem absorb_moment_term {p x A B c : ℝ}
    (hp : 2 < p) (hx : 0 ≤ x) (hA : 0 ≤ A) (hB : 0 ≤ B) (hc : 0 < c)
    (h : x ^ p ≤ c * (A + B * x ^ (p - 1))) :
    x ≤ ((2 * c) ^ p⁻¹ + 2 * c) * (A ^ p⁻¹ + B) := by
  have hp0 : 0 < p := by linarith only [hp]
  have hcoef : 0 ≤ (2 * c) ^ p⁻¹ := by positivity
  have hroot : 0 ≤ A ^ p⁻¹ := Real.rpow_nonneg hA _
  have hc0 : 0 ≤ 2 * c := by positivity
  by_cases hsmall : x ≤ 2 * c * B
  · exact hsmall.trans (mul_le_mul (by linarith only [hcoef])
      (by linarith only [hroot]) hB (add_nonneg hcoef hc0))
  · have hx' : 2 * c * B < x := lt_of_not_ge hsmall
    have hxp : x ^ p = x * x ^ (p - 1) :=
      Real.rpow_of_add_eq hx hp0.ne' (by ring : 1 + (p - 1) = p) |>.trans (by rw [Real.rpow_one])
    have hprod := mul_le_mul_of_nonneg_right hx'.le (Real.rpow_nonneg hx (p - 1))
    have habsorb : x ^ p ≤ 2 * c * A := by
      rw [← hxp] at hprod
      nlinarith only [h, hprod]
    have hbound : x ≤ (2 * c * A) ^ p⁻¹ := by
      apply (Real.rpow_le_rpow_iff hx (by positivity) hp0).mp
      rw [← Real.rpow_mul (by positivity), inv_mul_cancel₀ hp0.ne', Real.rpow_one]
      exact habsorb
    rw [Real.mul_rpow hc0 hA] at hbound
    exact hbound.trans (mul_le_mul (by linarith only [hc0])
      (by linarith only [hB]) hroot (add_nonneg hcoef hc0))

/-- For independent nonnegative summands, the real-order norm of the sum is
bounded by the sum of the means and the root of the summed moments, with a
constant depending only on the order. This fills the moment calculation
used at subsection `sub:ub_mom-chat` and generalizes the fourth-order step at Lemma `lem:excess`. -/
theorem exists_nonnegative_independent_sum_rpow_bound {p : ℝ} (hp : 2 < p) :
    ∃ K : ℝ, 0 < K ∧
      ∀ {Ω ι : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (F : Finset ι) (Y : ι → Ω → ℝ),
        (∀ i, Measurable (Y i)) → (∀ i ω, 0 ≤ Y i ω) → iIndepFun Y P →
        (∀ i ∈ F, Integrable (fun ω => Y i ω ^ p) P) →
        Integrable (fun ω => (∑ i ∈ F, Y i ω) ^ p) P ∧
        (∫ ω, (∑ i ∈ F, Y i ω) ^ p ∂P) ^ p⁻¹ ≤
          K * ((∑ i ∈ F, ∫ ω, Y i ω ^ p ∂P) ^ p⁻¹ +
            ∑ i ∈ F, ∫ ω, Y i ω ∂P) := by
  classical
  let q : ℝ := p - 1
  let c : ℝ := (2 : ℝ) ^ q
  have hp0 : 0 < p := by linarith only [hp]
  have hq : 0 ≤ q := by dsimp [q]; linarith only [hp]
  have hc : 0 < c := by dsimp [c]; positivity
  refine ⟨(2 * c) ^ p⁻¹ + 2 * c, by positivity, ?_⟩
  intro Ω ι _ P _ F Y hY hY0 hInd hMoment
  let S : Ω → ℝ := fun ω => ∑ i ∈ F, Y i ω
  let R : ι → Ω → ℝ := fun i ω => ∑ j ∈ F.erase i, Y j ω
  have hS0 (ω : Ω) : 0 ≤ S ω := Finset.sum_nonneg fun i _ => hY0 i ω
  have hR0 (i : ι) (ω : Ω) : 0 ≤ R i ω := Finset.sum_nonneg fun j _ => hY0 j ω
  have hRle (i : ι) (ω : Ω) : R i ω ≤ S ω :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset i F) (fun j _ _ => hY0 j ω)
  have hSsplit (i : ι) (hi : i ∈ F) (ω : Ω) : S ω = Y i ω + R i ω :=
    (Finset.add_sum_erase F (fun j => Y j ω) hi).symm
  have hYle (i : ι) (hi : i ∈ F) (ω : Ω) : Y i ω ≤ S ω := by
    rw [hSsplit i hi ω]
    exact le_add_of_nonneg_right (hR0 i ω)
  have hSmeas : Measurable S := Finset.measurable_sum _ (fun i _ => hY i)
  have hRmeas (i : ι) : Measurable (R i) := Finset.measurable_sum _ (fun j _ => hY j)
  have hqMeas : Measurable (fun x : ℝ => x ^ q) :=
    (Real.continuous_rpow_const hq).measurable

  -- The coordinate moments give a finite moment of the sum.
  have hAbs (i : ι) (hi : i ∈ F) : Integrable (fun ω => |Y i ω| ^ p) P := by
    simpa only [abs_of_nonneg (hY0 i _)] using hMoment i hi
  have hAbsSum := (integrable_sum_and_abs_rpow_of_moments P F Y (fun i _ => hY i)
    (by linarith only [hp]) hAbs).2
  have hSInt : Integrable (fun ω => S ω ^ p) P := by
    change Integrable (fun ω => |S ω| ^ p) P at hAbsSum
    simpa only [abs_of_nonneg (hS0 _)] using hAbsSum
  refine ⟨hSInt, ?_⟩
  have hSqInt : Integrable (fun ω => S ω ^ q) P := by
    have hNorm : Integrable (fun ω => ‖S ω‖ ^ p) P := by
      simpa only [Real.norm_eq_abs, abs_of_nonneg (hS0 _)] using hSInt
    have hLower := integrable_norm_rpow_of_le hSmeas.aestronglyMeasurable hq hp0.le
      (show q ≤ p by dsimp [q]; linarith) hNorm
    simpa only [Real.norm_eq_abs, abs_of_nonneg (hS0 _)] using hLower

  let M : ℝ := ∫ ω, S ω ^ p ∂P
  let x : ℝ := M ^ p⁻¹
  let A : ℝ := ∑ i ∈ F, ∫ ω, Y i ω ^ p ∂P
  let B : ℝ := ∑ i ∈ F, ∫ ω, Y i ω ∂P
  have hM : 0 ≤ M := integral_nonneg fun ω => Real.rpow_nonneg (hS0 ω) _
  have hx : 0 ≤ x := Real.rpow_nonneg hM _
  have hA : 0 ≤ A := Finset.sum_nonneg fun i _ =>
    integral_nonneg fun ω => Real.rpow_nonneg (hY0 i ω) _
  have hB : 0 ≤ B := Finset.sum_nonneg fun i _ => integral_nonneg (hY0 i)
  have hxpow : x ^ p = M := by
    dsimp [x]
    rw [← Real.rpow_mul hM, inv_mul_cancel₀ hp0.ne', Real.rpow_one]
  have hprod (t : ℝ) (ht : 0 ≤ t) : t * t ^ q = t ^ p := by
    simpa only [Real.rpow_one] using (Real.rpow_of_add_eq ht hp0.ne'
      (by dsimp [q]; ring : (1 : ℝ) + q = p)).symm
  have hSqLe : (∫ ω, S ω ^ q ∂P) ≤ x ^ q := by
    have hratio : 0 ≤ q / p := div_nonneg hq hp0.le
    have hratio1 : q / p ≤ 1 := (div_le_iff₀ hp0).2 (by dsimp [q]; linarith)
    have hrexp (t : ℝ) (ht : 0 ≤ t) : (t ^ p) ^ (q / p) = t ^ q := by
      rw [← Real.rpow_mul ht, show p * (q / p) = q by field_simp]
    have hJ := (Real.concaveOn_rpow hratio hratio1).le_map_integral
      (Real.continuous_rpow_const hratio).continuousOn isClosed_Ici
      (μ := P) (f := fun ω => S ω ^ p)
      (Eventually.of_forall fun ω => Real.rpow_nonneg (hS0 ω) p) hSInt
      (show Integrable (fun ω => (S ω ^ p) ^ (q / p)) P by
        simpa only [hrexp _ (hS0 _)] using hSqInt)
    change (∫ ω, (S ω ^ p) ^ (q / p) ∂P) ≤ M ^ (q / p) at hJ
    simp_rw [hrexp _ (hS0 _)] at hJ
    simpa only [x, ← Real.rpow_mul hM, div_eq_inv_mul] using hJ

  -- Each summand is independent of the sum over the other indices.
  have hterm (i : ι) (hi : i ∈ F) :
      Integrable (fun ω => Y i ω * S ω ^ q) P := by
    apply hSInt.mono' ((hY i).mul (hqMeas.comp hSmeas)).aestronglyMeasurable
    exact Eventually.of_forall fun ω => by
      change ‖Y i ω * S ω ^ q‖ ≤ S ω ^ p
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hY0 i ω)
        (Real.rpow_nonneg (hS0 ω) _)), ← hprod _ (hS0 ω)]
      exact mul_le_mul_of_nonneg_right (hYle i hi ω) (Real.rpow_nonneg (hS0 ω) _)
  have hpair (i : ι) (hi : i ∈ F) :
      Integrable (fun ω => Y i ω * R i ω ^ q) P := by
    apply (hterm i hi).mono' ((hY i).mul (hqMeas.comp (hRmeas i))).aestronglyMeasurable
    exact Eventually.of_forall fun ω => by
      change ‖Y i ω * R i ω ^ q‖ ≤ Y i ω * S ω ^ q
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hY0 i ω)
        (Real.rpow_nonneg (hR0 i ω) _))]
      exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (hR0 i ω) (hRle i ω) hq) (hY0 i ω)
  have hbound (i : ι) (hi : i ∈ F) :
      (∫ ω, Y i ω * S ω ^ q ∂P) ≤
        c * ((∫ ω, Y i ω ^ p ∂P) + (∫ ω, Y i ω ∂P) * x ^ q) := by
    have hIndR : IndepFun (R i) (Y i) P := by
      simpa only [R, Finset.sum_fn] using
        hInd.indepFun_finsetSum_of_notMem hY (Finset.notMem_erase i F)
    have hIndPow : IndepFun (Y i) (fun ω => R i ω ^ q) P :=
      hIndR.symm.comp measurable_id hqMeas
    have hRpowInt : Integrable (fun ω => R i ω ^ q) P := by
      apply hSqInt.mono' (hqMeas.comp (hRmeas i)).aestronglyMeasurable
      exact Eventually.of_forall fun ω => by
        change ‖R i ω ^ q‖ ≤ S ω ^ q
        rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (hR0 i ω) _)]
        exact Real.rpow_le_rpow (hR0 i ω) (hRle i ω) hq
    have hmeanR : (∫ ω, R i ω ^ q ∂P) ≤ x ^ q :=
      (integral_mono hRpowInt hSqInt fun ω =>
        Real.rpow_le_rpow (hR0 i ω) (hRle i ω) hq).trans hSqLe
    calc
      _ ≤ ∫ ω, c * (Y i ω ^ p + Y i ω * R i ω ^ q) ∂P := by
        apply integral_mono (hterm i hi) (((hMoment i hi).add (hpair i hi)).const_mul c)
        intro ω
        have hsBound := rpow_add_le_two_rpow_mul (hY0 i ω) (hR0 i ω) hq
        change Y i ω * S ω ^ q ≤ c * (Y i ω ^ p + Y i ω * R i ω ^ q)
        rw [hSsplit i hi ω]
        calc
          _ ≤ Y i ω * (c * (Y i ω ^ q + R i ω ^ q)) :=
            mul_le_mul_of_nonneg_left hsBound (hY0 i ω)
          _ = _ := by rw [← hprod _ (hY0 i ω)]; ring
      _ = c * ((∫ ω, Y i ω ^ p ∂P) + (∫ ω, Y i ω ∂P) * (∫ ω, R i ω ^ q ∂P)) := by
        rw [integral_const_mul, integral_add (hMoment i hi) (hpair i hi),
          hIndPow.integral_fun_mul_eq_mul_integral (hY i).aestronglyMeasurable
            (hqMeas.comp (hRmeas i)).aestronglyMeasurable]
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (add_le_add_right (mul_le_mul_of_nonneg_left hmeanR (integral_nonneg (hY0 i))) _) hc.le

  -- Expand the moment by one factor of the sum, then absorb its lower-order term.
  have hsum : M ≤ c * (A + B * x ^ q) := by
    calc
      M = ∫ ω, ∑ i ∈ F, Y i ω * S ω ^ q ∂P := by
        apply integral_congr_ae
        exact Eventually.of_forall fun ω => by
          change S ω ^ p = ∑ i ∈ F, Y i ω * S ω ^ q
          rw [← Finset.sum_mul]
          exact (hprod _ (hS0 ω)).symm
      _ = ∑ i ∈ F, ∫ ω, Y i ω * S ω ^ q ∂P := integral_finsetSum _ hterm
      _ ≤ ∑ i ∈ F, c * ((∫ ω, Y i ω ^ p ∂P) + (∫ ω, Y i ω ∂P) * x ^ q) :=
        Finset.sum_le_sum hbound
      _ = _ := by rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.sum_mul]
  have hineq : x ^ p ≤ c * (A + B * x ^ (p - 1)) := hxpow ▸ hsum
  exact absorb_moment_term hp hx hA hB hc hineq

end LPPDifferentiability
