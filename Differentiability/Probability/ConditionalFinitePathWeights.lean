/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Differentiability.Probability.ConditionalLightMoments
public import ProbabilityBasics.Probability.BernsteinConcentration
public import ProbabilityBasics.Probability.IndependentBadCount
import Mathlib.MeasureTheory.Constructions.Pi

/-!
# Path weights under the good-site product law

The heavy and light decomposition in Lemma B.1 of the differentiability
preprint gives a two-term lower-tail bound for path weights. The conditional
moments and independence are derived from the original weight law.

## References

- C. Janjigian, F. Rassoul-Agha and T. Seppäläinen,
  *Differentiability of the shape function in the planar corner growth model*, preprint.
-/

public section

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

namespace LPPDifferentiability

/-- The source's deterministic heavy and light decomposition, including an empty sum. -/
theorem finite_weight_ge_of_heavy_count_light_sum
    {I : Type*} [Fintype I] [DecidableEq I] (x : I → ℝ)
    (T b c t : ℝ) (hT : 0 ≤ T) (K : ℕ) (hK : 1 ≤ K)
    (hx : ∀ i, -T ≤ x i)
    (hcount : (@Finset.filter I (fun i => b < max (-(x i)) 0)
      (Classical.decPred _) Finset.univ).card < K)
    (hlight : (∑ i, if max (-(x i)) 0 ≤ b then max (-(x i)) 0 else 0) ≤ c + t) :
    -c - (K - 1 : ℕ) * T - t ≤ ∑ i, x i := by
  classical
  let S := Finset.univ.filter fun i => b < max (-(x i)) 0
  have hcard : S.card ≤ K - 1 := by dsimp [S]; omega
  have hheavy : (∑ i, if b < max (-(x i)) 0 then max (-(x i)) 0 else 0) ≤
      (K - 1 : ℕ) * T := by
    rw [← Finset.sum_filter]
    calc
      (∑ i ∈ S, max (-(x i)) 0) ≤ ∑ _i ∈ S, T :=
        Finset.sum_le_sum fun i _ => max_le (by linarith [hx i]) hT
      _ = (S.card : ℝ) * T := by simp
      _ ≤ (K - 1 : ℕ) * T := mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hT
  have hneg : (∑ i, -(max (-(x i)) 0)) ≤ ∑ i, x i := by
    apply Finset.sum_le_sum
    intro i _
    linarith only [le_max_left (-(x i)) 0]
  have hsplit : (∑ i, max (-(x i)) 0) =
      (∑ i, if b < max (-(x i)) 0 then max (-(x i)) 0 else 0) +
      (∑ i, if max (-(x i)) 0 ≤ b then max (-(x i)) 0 else 0) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => (conditionalNegativeSplit_add b (x i)).symm
  rw [Finset.sum_neg_distrib, hsplit] at hneg
  linarith only [hneg, hheavy, hlight]

/-- Distinct collected weights under the literal good-site product law satisfy
exactly the two-term bound in the source. All moments are produced from mu. -/
theorem conditional_finite_weight_failure_le
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (T p b t : ℝ)
    (hp : 1 < p) (hT : 0 < T)
    (hthreshold : (2 : ℝ≥0∞)⁻¹ ≤ μ (Set.Ici (-T))) (hb : 0 < b) (ht : 0 < t)
    (hmoment : (∫⁻ x, ENNReal.ofReal ((max (-x) 0) ^ p) ∂μ) < ∞)
    (m n K : ℕ) (hmn : m ≤ n) (hK : 1 ≤ K) :
    (Measure.pi (fun _ : Fin m =>
      (μ (Set.Ici (-T)))⁻¹ • μ.restrict (Set.Ici (-T)))).real
      {x | (∑ i, x i) < -2 * (∫ y, max (-y) 0 ∂μ) * m - (K - 1 : ℕ) * T - t} ≤
      (2 * n * (∫ y, (max (-y) 0) ^ p ∂μ) * b ^ (-p)) ^ K +
        Real.exp (-t ^ 2 / (2 * b * (2 * (∫ y, max (-y) 0 ∂μ) * n + t / 3))) := by
  classical
  let ν : Measure ℝ := (μ (Set.Ici (-T)))⁻¹ • μ.restrict (Set.Ici (-T))
  let P : Measure (Fin m → ℝ) := Measure.pi (fun _ : Fin m => ν)
  let C : ℝ := ∫ y, max (-y) 0 ∂μ
  let D : ℝ := ∫ y, (max (-y) 0) ^ p ∂μ
  let Z : ℝ → ℝ := fun y => if max (-y) 0 ≤ b then max (-y) 0 else 0
  let E : Fin m → Set (Fin m → ℝ) := fun i => {x | b < max (-(x i)) 0}
  let A : Set (Fin m → ℝ) := {x | K ≤ (Finset.univ.filter fun i => x ∈ E i).card}
  let B : Set (Fin m → ℝ) := {x | (∑ i, Z (x i)) > 2 * C * m + t}
  let : IsProbabilityMeasure ν := conditionalNegativeRestriction_isProbabilityMeasure μ T hthreshold
  have hC : 0 ≤ C := integral_nonneg fun _ => le_max_right _ _
  have hD : 0 ≤ D := integral_nonneg fun y => Real.rpow_nonneg (le_max_right _ _) p
  have hq : 0 ≤ 2 * D * b ^ (-p) := by positivity
  have hZ : Measurable Z := measurable_conditionalLightPart b
  have heval (i : Fin m) : MeasurePreserving (fun x : Fin m → ℝ => x i) P ν :=
    measurePreserving_eval (fun _ : Fin m => ν) i
  have hE (i : Fin m) : MeasurableSet (E i) :=
    measurableSet_lt measurable_const (((measurable_pi_apply i).neg).max measurable_const)
  have hind : iIndepFun (fun i (x : Fin m → ℝ) => x i) P :=
    iIndepFun_pi (fun _ => measurable_id.aemeasurable)
  have hEi : iIndepSet E P := by
    apply (iIndepSet_iff_meas_biInter hE).2
    intro S
    exact hind.measure_inter_preimage_eq_mul S
      (fun _ _ => measurableSet_lt measurable_const (measurable_id.neg.max measurable_const))
  have htail (i : Fin m) : P.real (E i) ≤ 2 * D * b ^ (-p) := by
    have heq : P.real (E i) = ν.real {y : ℝ | max (-y) 0 > b} := by
      rw [← (heval i).map_eq]
      exact (map_measureReal_apply (μ := P) (measurable_pi_apply i)
        (s := {y : ℝ | max (-y) 0 > b})
        (measurableSet_lt measurable_const (measurable_id.neg.max measurable_const))).symm
    rw [heq]
    exact conditionalNegativePart_strict_tail_le μ T p b hp hthreshold hb hmoment
  have hA : P.real A ≤ (2 * n * D * b ^ (-p)) ^ K := by
    have h := measureReal_iIndepSet_badCount_ge_le_pow P E hE hEi
      (2 * D * b ^ (-p)) hq htail K
    change P.real A ≤ _ at h
    apply h.trans
    apply pow_le_pow_left₀ (mul_nonneg (Nat.cast_nonneg _) hq)
    calc
      (Fintype.card (Fin m) : ℝ) * (2 * D * b ^ (-p)) = (m : ℝ) * (2 * D * b ^ (-p)) := by simp
      _ ≤ (n : ℝ) * (2 * D * b ^ (-p)) :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hmn) hq
      _ = 2 * n * D * b ^ (-p) := by ring
  have hmean : (∑ i : Fin m, ∫ x, Z (x i) ∂P) ≤ 2 * C * m := by
    calc
      (∑ i : Fin m, ∫ x, Z (x i) ∂P) = ∑ _i : Fin m, ∫ y, Z y ∂ν := by
        apply Finset.sum_congr rfl
        intro i _
        rw [← (heval i).map_eq, integral_map (measurable_pi_apply i).aemeasurable hZ.aestronglyMeasurable]
      _ ≤ ∑ _i : Fin m, 2 * C :=
        Finset.sum_le_sum fun _ _ => integral_conditionalLightPart_le μ T p b hp hthreshold hb hmoment
      _ = 2 * C * m := by simp; ring
  have hsecond : (∑ i : Fin m, ∫ x, (Z (x i)) ^ 2 ∂P) ≤ 2 * C * n * b := by
    calc
      (∑ i : Fin m, ∫ x, (Z (x i)) ^ 2 ∂P) = ∑ _i : Fin m, ∫ y, (Z y) ^ 2 ∂ν := by
        apply Finset.sum_congr rfl
        intro i _
        rw [← (heval i).map_eq, integral_map (measurable_pi_apply i).aemeasurable
          (hZ.pow_const 2).aestronglyMeasurable]
      _ ≤ ∑ _i : Fin m, 2 * C * b :=
        Finset.sum_le_sum fun _ _ => integral_conditionalLightPart_sq_le μ T p b hp hthreshold hb hmoment
      _ = 2 * C * m * b := by simp; ring
      _ ≤ 2 * C * n * b := by gcongr
  have hB : P.real B ≤ Real.exp (-t ^ 2 / (2 * b * (2 * C * n + t / 3))) := by
    apply (measureReal_mono (show B ⊆ {x | (∑ i : Fin m, Z (x i)) >
      (∑ i : Fin m, ∫ y, Z (y i) ∂P) + t} from by
        intro x hx
        change (∑ i, Z (x i)) > 2 * C * m + t at hx
        change (∑ i, Z (x i)) > (∑ i, ∫ y, Z (y i) ∂P) + t
        linarith only [hmean, hx])).trans
    exact bernstein_upper_tail_of_second_moment_sum_le
      (fun i => hZ.comp (measurable_pi_apply i))
      (hind.comp (fun _ => Z) (fun _ => hZ)) hb
      (fun _ => Filter.Eventually.of_forall fun x => conditionalLightPart_bounds b hb.le _) C n hsecond t ht
  have hs : ∀ᵐ x ∂P, ∀ i, -T ≤ x i := by
    rw [ae_all_iff]
    intro i
    exact (heval i).quasiMeasurePreserving.ae (ae_conditionalNegativeRestriction_ge μ T)
  have hsub : ∀ᵐ x ∂P,
      x ∈ {x | (∑ i : Fin m, x i) < -2 * C * m - (K - 1 : ℕ) * T - t} → x ∈ A ∪ B := by
    filter_upwards [hs] with x hx hfail
    by_contra hnot
    have hnot' : x ∉ A ∧ x ∉ B := not_or.mp hnot
    have hcount : (Finset.univ.filter fun i => b < max (-(x i)) 0).card < K :=
      lt_of_not_ge hnot'.1
    have hl : (∑ i, if max (-(x i)) 0 ≤ b then max (-(x i)) 0 else 0) ≤ 2 * C * m + t :=
      le_of_not_gt hnot'.2
    have h := finite_weight_ge_of_heavy_count_light_sum x T b (2 * C * m) t hT.le K hK hx hcount hl
    linarith only [h, hfail]
  change P.real _ ≤ _
  calc
    P.real {x | (∑ i, x i) < -2 * C * m - (K - 1 : ℕ) * T - t} ≤ P.real (A ∪ B) :=
      ENNReal.toReal_mono (measure_ne_top P _) (measure_mono_ae hsub)
    _ ≤ P.real A + P.real B := measureReal_union_le _ _
    _ ≤ _ := add_le_add hA hB

end LPPDifferentiability
