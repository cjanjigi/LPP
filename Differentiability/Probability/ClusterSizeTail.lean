/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Differentiability.Model.NeighborClusterCount
public import LPP_Foundations.Probability.FiniteEnvironmentLaw
public import Mathlib.MeasureTheory.Measure.Real
import LPP_Foundations.Probability.EnvironmentLaw
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Order.Filter.AtTopBot.Archimedean
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! # Cluster-size tail for very bad sites

The probability that the actual environment has a chain of `K + 1` very bad
sites of `Q`, each after the first within `d0` of an earlier one, is at most
`|Q| K! (2 d0 + 1) ^ (2 K) pT ^ (K + 1)` with `pT = μ.real (Iio (-T))`. Under
the polynomial scaling of the source this bound tends to zero.
-/

public section

open MeasureTheory Set Filter Topology

namespace LPPDifferentiability

/-- Distinct actual coordinates are all very bad with probability `pT ^ n`. -/
private theorem environmentLaw_real_all_bad_injective
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (T : ℝ) {n : ℕ}
    (f : Fin n → Lattice) (hf : Function.Injective f) :
    (environmentLaw μ).real {ω : Environment | ∀ i, ω (f i) < -T} =
      (μ.real (Iio (-T))) ^ n := by
  classical
  let coordinates : Environment → Fin n → ℝ := fun ω i => ω (f i)
  let rectangle : Set (Fin n → ℝ) := Set.univ.pi (fun _ => Iio (-T))
  have hrectangle : MeasurableSet rectangle :=
    MeasurableSet.univ_pi fun _ => measurableSet_Iio
  have hcoordinates : Measurable coordinates :=
    measurable_finite_environment_coordinates f
  have hpre : coordinates ⁻¹' rectangle = {ω : Environment | ∀ i, ω (f i) < -T} := by
    ext ω
    simp [coordinates, rectangle]
  have hlaw : (environmentLaw μ).map coordinates = Measure.pi (fun _ : Fin n => μ) :=
    environmentLaw_map_finite_coordinates μ f hf
  have hprod : (Measure.pi (fun _ : Fin n => μ)) rectangle =
      ∏ _i : Fin n, μ (Iio (-T)) := by
    change (Measure.pi (fun _ : Fin n => μ)) (Set.univ.pi (fun _ : Fin n => Iio (-T))) = _
    exact Measure.pi_pi (fun _ : Fin n => μ) (fun _ => Iio (-T))
  calc
    (environmentLaw μ).real {ω : Environment | ∀ i, ω (f i) < -T} =
        (environmentLaw μ).real (coordinates ⁻¹' rectangle) := by rw [hpre]
    _ = ((environmentLaw μ).map coordinates).real rectangle :=
      (map_measureReal_apply hcoordinates hrectangle).symm
    _ = (Measure.pi (fun _ : Fin n => μ)).real rectangle := by rw [hlaw]
    _ = (μ.real (Iio (-T))) ^ n := by
      rw [measureReal_def, hprod, ENNReal.toReal_prod]
      simp [measureReal_def]

/-- Chain bound: the probability that the environment has a chain of `K + 1`
distinct very bad sites of `Q`, each after the first within `d0` of an earlier
one, is at most `|Q| K! (2 d0 + 1) ^ (2 K) pT ^ (K + 1)`. -/
theorem environmentLaw_real_close_chain_le
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (T : ℝ) (d0 K : ℕ) (Q : Finset Lattice) :
    (environmentLaw μ).real {ω : Environment | ∃ f : Fin (K + 1) → Lattice,
      Function.Injective f ∧ (∀ i, f i ∈ Q ∧ ω (f i) < -T) ∧
      ∀ i : Fin (K + 1), 0 < i.val → ∃ j : Fin (K + 1), j.val < i.val ∧
        |(f i).1 - (f j).1| + |(f i).2 - (f j).2| ≤ (d0 : ℤ)} ≤
      (Q.card : ℝ) * (K.factorial : ℝ) * (2 * (d0 : ℝ) + 1) ^ (2 * K) *
        (μ.real (Iio (-T))) ^ (K + 1) := by
  classical
  obtain ⟨F, hF, hcard⟩ := exists_close_chain_finset_card_le_mul_card d0 K Q
  have hsub : {ω : Environment | ∃ f : Fin (K + 1) → Lattice,
      Function.Injective f ∧ (∀ i, f i ∈ Q ∧ ω (f i) < -T) ∧
      ∀ i : Fin (K + 1), 0 < i.val → ∃ j : Fin (K + 1), j.val < i.val ∧
        |(f i).1 - (f j).1| + |(f i).2 - (f j).2| ≤ (d0 : ℤ)} ⊆
      ⋃ f ∈ F, {ω : Environment | ∀ i, ω (f i) < -T} := by
    rintro ω ⟨f, hinj, hbad, hchain⟩
    simp only [Set.mem_iUnion]
    exact ⟨f, (hF f).mpr ⟨hinj, fun i => (hbad i).1, hchain⟩, fun i => (hbad i).2⟩
  calc
    _ ≤ (environmentLaw μ).real (⋃ f ∈ F, {ω : Environment | ∀ i, ω (f i) < -T}) :=
      measureReal_mono hsub (measure_ne_top _ _)
    _ ≤ ∑ f ∈ F, (environmentLaw μ).real {ω : Environment | ∀ i, ω (f i) < -T} :=
      measureReal_biUnion_finset_le F _
    _ = ∑ _f ∈ F, (μ.real (Iio (-T))) ^ (K + 1) := by
      apply Finset.sum_congr rfl
      intro f hf
      exact environmentLaw_real_all_bad_injective μ T f ((hF f).mp hf).1
    _ = (F.card : ℝ) * (μ.real (Iio (-T))) ^ (K + 1) := by simp
    _ ≤ ((Q.card * (K.factorial * (2 * d0 + 1) ^ (2 * K)) : ℕ) : ℝ) *
        (μ.real (Iio (-T))) ^ (K + 1) :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (pow_nonneg measureReal_nonneg _)
    _ = _ := by push_cast; ring

private theorem cluster_rhs_eq (K d0 : ℕ) (C ε p' x L : ℝ) (hx : 0 ≤ x) (hε : 0 < ε) :
    C * Real.exp L ^ 4 * (K.factorial : ℝ) * (2 * (d0 : ℝ) + 1) ^ (2 * K) *
        (C * (x / ε) ^ p' * Real.exp L ^ (-p')) ^ (K + 1) =
      (C ^ (K + 2) * (K.factorial : ℝ) * (2 * (d0 : ℝ) + 1) ^ (2 * K) /
          ε ^ (p' * ((K : ℝ) + 1))) *
        (x ^ (p' * ((K : ℝ) + 1)) * Real.exp (-(((K : ℝ) + 1) * p' - 4) * L)) := by
  have hc : ((K + 1 : ℕ) : ℝ) = (K : ℝ) + 1 := by push_cast; ring
  have h1 : ((x / ε) ^ p') ^ (K + 1) = x ^ (p' * ((K : ℝ) + 1)) / ε ^ (p' * ((K : ℝ) + 1)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (div_nonneg hx hε.le), Real.div_rpow hx hε.le, hc]
  have h2 : (Real.exp L ^ (-p')) ^ (K + 1) = Real.exp (((K + 1 : ℕ) : ℝ) * (L * -p')) := by
    rw [← Real.exp_mul, Real.exp_nat_mul]
  have h3 : Real.exp L ^ 4 = Real.exp (((4 : ℕ) : ℝ) * L) := by
    rw [Real.exp_nat_mul]
  calc
    _ = C ^ (K + 2) * (K.factorial : ℝ) * (2 * (d0 : ℝ) + 1) ^ (2 * K) *
          ((x / ε) ^ p') ^ (K + 1) * (Real.exp L ^ 4 * (Real.exp L ^ (-p')) ^ (K + 1)) := by
      ring
    _ = _ := by
      rw [h1, h2, h3, ← Real.exp_add]
      have : ((4 : ℕ) : ℝ) * L + ((K + 1 : ℕ) : ℝ) * (L * -p') =
          -(((K : ℝ) + 1) * p' - 4) * L := by
        rw [hc]; push_cast; ring
      rw [this]
      ring

/-- Under the polynomial scaling of the source, the cluster-size tail bound
tends to zero: `pT ≤ C (k / ε) ^ p' s ^ (-p')` and `|Q| ≤ C s ^ 4` with
`s = 2 ^ k`, and `(K + 1) p' > 4`. -/
theorem tendsto_cluster_size_tail_bound
    (d0 K : ℕ) (C ε p' : ℝ) (hC : 0 ≤ C) (hε : 0 < ε) (hp : 4 < ((K : ℝ) + 1) * p')
    (Qcard : ℕ → ℕ) (pT : ℕ → ℝ) (hpT0 : ∀ k, 0 ≤ pT k)
    (hpT : ∀ᶠ k : ℕ in atTop, pT k ≤ C * ((k : ℝ) / ε) ^ p' * ((2 : ℝ) ^ k) ^ (-p'))
    (hQ : ∀ᶠ k : ℕ in atTop, (Qcard k : ℝ) ≤ C * ((2 : ℝ) ^ k) ^ 4) :
    Tendsto (fun k : ℕ => (Qcard k : ℝ) * (K.factorial : ℝ) *
      (2 * (d0 : ℝ) + 1) ^ (2 * K) * pT k ^ (K + 1)) atTop (𝓝 0) := by
  let c1 : ℝ := C ^ (K + 2) * (K.factorial : ℝ) * (2 * (d0 : ℝ) + 1) ^ (2 * K) /
    ε ^ (p' * ((K : ℝ) + 1))
  have hb : 0 < (((K : ℝ) + 1) * p' - 4) * Real.log 2 :=
    mul_pos (by linarith) (Real.log_pos (by norm_num))
  have hlim : Tendsto (fun k : ℕ => c1 * ((k : ℝ) ^ (p' * ((K : ℝ) + 1)) *
      Real.exp (-((((K : ℝ) + 1) * p' - 4) * Real.log 2) * (k : ℝ)))) atTop (𝓝 0) := by
    have h := ((tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (p' * ((K : ℝ) + 1)) _ hb).comp
      tendsto_natCast_atTop_atTop).const_mul c1
    rw [mul_zero] at h
    exact h
  have hrhs : ∀ k : ℕ, C * ((2 : ℝ) ^ k) ^ 4 * (K.factorial : ℝ) * (2 * (d0 : ℝ) + 1) ^ (2 * K) *
      (C * ((k : ℝ) / ε) ^ p' * ((2 : ℝ) ^ k) ^ (-p')) ^ (K + 1) =
      c1 * ((k : ℝ) ^ (p' * ((K : ℝ) + 1)) *
        Real.exp (-((((K : ℝ) + 1) * p' - 4) * Real.log 2) * (k : ℝ))) := by
    intro k
    have hu : (2 : ℝ) ^ k = Real.exp ((k : ℝ) * Real.log 2) := by
      rw [← Real.log_pow, Real.exp_log (by positivity)]
    rw [hu, cluster_rhs_eq K d0 C ε p' (k : ℝ) _ (Nat.cast_nonneg k) hε]
    have : -(((K : ℝ) + 1) * p' - 4) * ((k : ℝ) * Real.log 2) =
        -((((K : ℝ) + 1) * p' - 4) * Real.log 2) * (k : ℝ) := by ring
    rw [this]
  refine squeeze_zero' (Filter.Eventually.of_forall fun k => ?_) ?_ hlim
  · have := hpT0 k
    positivity
  · filter_upwards [hpT, hQ] with k hpk hQk
    rw [← hrhs k]
    have h1 : pT k ^ (K + 1) ≤
        (C * ((k : ℝ) / ε) ^ p' * ((2 : ℝ) ^ k) ^ (-p')) ^ (K + 1) :=
      pow_le_pow_left₀ (hpT0 k) hpk _
    have hA : (Qcard k : ℝ) * (K.factorial : ℝ) * (2 * (d0 : ℝ) + 1) ^ (2 * K) ≤
        C * ((2 : ℝ) ^ k) ^ 4 * (K.factorial : ℝ) * (2 * (d0 : ℝ) + 1) ^ (2 * K) := by
      gcongr
    exact mul_le_mul hA h1 (pow_nonneg (hpT0 k) _) (by positivity)

end LPPDifferentiability
