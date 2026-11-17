/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProbabilityBasics.Probability.RectangleMaximal
import Mathlib.MeasureTheory.Measure.Continuity
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

/-! Countable maximal control for actual prefix rectangle averages and almost sure boundedness. -/

@[expose] public section

open MeasureTheory Filter
open scoped BigOperators ENNReal Topology

namespace ProbabilityBasics

private theorem measurable_countable_rectangle_bound
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (T : (ℤ × ℤ) → Ω → Ω)
    (hzero : ∀ s, T 0 s = s)
    (hadd : ∀ z w s, T (z + w) s = T z (T w s))
    (hT : ∀ z, MeasurePreserving (T z) μ μ)
    (f : Ω → ℝ) (hfm : Measurable f) (hf : Integrable f μ)
    (b : Fin 2 → ℝ) (hb : ∀ i, 0 < b i) (t : ℝ) (ht : 0 < t) :
    let R : ℕ → Finset (ℤ × ℤ) := fun n =>
      (Finset.Ico (0 : ℤ) ((⌊(n : ℝ) * b 0⌋₊ : ℕ) : ℤ)).product
        (Finset.Ico (0 : ℤ) ((⌊(n : ℝ) * b 1⌋₊ : ℕ) : ℤ))
    let A : ℕ → Ω → ℝ := fun n s => (∑ z ∈ R n, f (T z s)) / (n : ℝ)^2
    MeasurableSet {s | ∃ n : ℕ, t < |A n s|} ∧
      μ.real {s | ∃ n : ℕ, t < |A n s|} ≤ (4 * b 0 * b 1 / t) * ∫ s, |f s| ∂μ := by
  classical
  let R : ℕ → Finset (ℤ × ℤ) := fun n =>
    (Finset.Ico (0 : ℤ) ((⌊(n : ℝ) * b 0⌋₊ : ℕ) : ℤ)).product
      (Finset.Ico (0 : ℤ) ((⌊(n : ℝ) * b 1⌋₊ : ℕ) : ℤ))
  let A : ℕ → Ω → ℝ := fun n s => (∑ z ∈ R n, f (T z s)) / (n : ℝ)^2
  let E : ℕ → Set Ω := fun N => {s | ∃ n ∈ Finset.Icc 0 N, t < |A n s|}
  let F : Set Ω := {s | ∃ n : ℕ, t < |A n s|}
  change MeasurableSet F ∧ μ.real F ≤ (4 * b 0 * b 1 / t) * ∫ s, |f s| ∂μ
  have hProduct : 0 < b 0 * b 1 := mul_pos (hb 0) (hb 1)
  -- Exact integer cards and the two floor bounds give the actual n-squared scaling.
  have hCard (n : ℕ) : ((R n).card : ℝ) ≤ (n : ℝ)^2 * (b 0 * b 1) := by
    have hCardNat : (R n).card = ⌊(n : ℝ) * b 0⌋₊ * ⌊(n : ℝ) * b 1⌋₊ :=
      (integer_rectangle_difference_regularities ⌊(n : ℝ) * b 0⌋₊ ⌊(n : ℝ) * b 1⌋₊).1
    have hFloor0 : (⌊(n : ℝ) * b 0⌋₊ : ℝ) ≤ (n : ℝ) * b 0 :=
      Nat.floor_le (mul_nonneg (Nat.cast_nonneg n) (hb 0).le)
    have hFloor1 : (⌊(n : ℝ) * b 1⌋₊ : ℝ) ≤ (n : ℝ) * b 1 :=
      Nat.floor_le (mul_nonneg (Nat.cast_nonneg n) (hb 1).le)
    rw [hCardNat, Nat.cast_mul]
    calc
      (⌊(n : ℝ) * b 0⌋₊ : ℝ) * (⌊(n : ℝ) * b 1⌋₊ : ℝ) ≤
          ((n : ℝ) * b 0) * ((n : ℝ) * b 1) :=
        mul_le_mul hFloor0 hFloor1 (Nat.cast_nonneg _) (mul_nonneg (Nat.cast_nonneg n) (hb 0).le)
      _ = (n : ℝ)^2 * (b 0 * b 1) := by ring
  have hNonzero (n : ℕ) (s : Ω) (hc : t < |A n s|) : n ≠ 0 := by
    intro hn
    subst n
    have hA0 : A 0 s = 0 := by simp [A]
    rw [hA0, abs_zero] at hc
    exact (not_lt_of_ge ht.le) hc
  have hCross (n : ℕ) (s : Ω) (hc : t < |A n s|) :
      (t / (b 0 * b 1)) * ((R n).card : ℝ) < ∑ z ∈ R n, |f (T z s)| := by
    have hn : 0 < (n : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (hNonzero n s hc))
    have hnSq : 0 < (n : ℝ)^2 := sq_pos_of_pos hn
    have hAbs : t < |∑ z ∈ R n, f (T z s)| / (n : ℝ)^2 := by
      simpa only [A, abs_div, abs_of_nonneg (sq_nonneg (n : ℝ))] using hc
    have hRaw : t * (n : ℝ)^2 < ∑ z ∈ R n, |f (T z s)| :=
      ((lt_div_iff₀ hnSq).mp hAbs).trans_le (Finset.abs_sum_le_sum_abs _ _)
    have hScale : (t / (b 0 * b 1)) * ((n : ℝ)^2 * (b 0 * b 1)) = t * (n : ℝ)^2 := by
      calc
        _ = ((t / (b 0 * b 1)) * (b 0 * b 1)) * (n : ℝ)^2 := by ring
        _ = t * (n : ℝ)^2 := by rw [div_mul_cancel₀ _ (ne_of_gt hProduct)]
    have hScaled := mul_le_mul_of_nonneg_left (hCard n) (div_pos ht hProduct).le
    rw [hScale] at hScaled
    exact hScaled.trans_lt hRaw
  -- These are actual measurable finite bad events, increasing with their horizon.
  have hAverageMeas (n : ℕ) : Measurable (A n) := by
    have hSum : Measurable (fun s => ∑ z ∈ R n, f (T z s)) := by
      apply Finset.measurable_sum
      intro z hz
      simpa only [Function.comp_def] using hfm.comp (hT z).measurable
    exact hSum.div_const ((n : ℝ)^2)
  have hEMeas (N : ℕ) : MeasurableSet (E N) := by
    have hEq : E N = ⋃ n ∈ Finset.Icc 0 N, {s | t < |A n s|} := by
      ext s
      simp only [E, Set.mem_ofPred_eq, Set.mem_iUnion, exists_prop]
    rw [hEq]
    apply Finset.measurableSet_biUnion
    intro n hn
    apply measurableSet_lt measurable_const
    simpa only [Real.norm_eq_abs] using (hAverageMeas n).norm
  have hMono : Monotone E := by
    intro N M hNM s hs
    rcases hs with ⟨n, hn, hc⟩
    exact ⟨n, Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hn).1,
      (Finset.mem_Icc.mp hn).2.trans hNM⟩, hc⟩
  have hFiniteBound (N : ℕ) : μ.real (E N) ≤
      (4 * b 0 * b 1 / t) * ∫ s, |f s| ∂μ := by
    have hSubset : E N ⊆ {s | ∃ n ∈ Finset.Icc 1 N,
        (t / (b 0 * b 1)) * ((R n).card : ℝ) < ∑ z ∈ R n, |f (T z s)|} := by
      intro s hs
      rcases hs with ⟨n, hn, hc⟩
      exact ⟨n, Finset.mem_Icc.mpr ⟨Nat.one_le_iff_ne_zero.mpr (hNonzero n s hc),
        (Finset.mem_Icc.mp hn).2⟩, hCross n s hc⟩
    have hRaw := finite_rectangle_maximal_weak_one_one μ T hzero hadd hT f hf b hb N
      (t / (b 0 * b 1)) (div_pos ht hProduct)
    calc
      μ.real (E N) ≤ μ.real {s | ∃ n ∈ Finset.Icc 1 N,
          (t / (b 0 * b 1)) * ((R n).card : ℝ) < ∑ z ∈ R n, |f (T z s)|} :=
        measureReal_mono hSubset
      _ ≤ (4 / (t / (b 0 * b 1))) * ∫ s, |f s| ∂μ := hRaw
      _ = (4 * b 0 * b 1 / t) * ∫ s, |f s| ∂μ := by
        rw [div_div_eq_mul_div]
        ring
  have hUnion : (⋃ N : ℕ, E N) = F := by
    ext s
    constructor
    · intro hs
      obtain ⟨N, hN⟩ := Set.mem_iUnion.mp hs
      rcases hN with ⟨n, _, hc⟩
      exact ⟨n, hc⟩
    · rintro ⟨n, hc⟩
      exact Set.mem_iUnion.mpr ⟨n, n, Finset.mem_Icc.mpr ⟨Nat.zero_le n, le_rfl⟩, hc⟩
  have hFMeas : MeasurableSet F := by
    rw [← hUnion]
    exact MeasurableSet.iUnion hEMeas
  -- Genuine measure continuity and finite-toReal continuity preserve the uniform constant.
  have hLimitENN : Tendsto (fun N : ℕ => μ (E N)) atTop (𝓝 (μ F)) := by
    have h := tendsto_measure_iUnion_atTop (μ := μ) hMono
    rw [hUnion] at h
    simpa only [Function.comp_def] using h
  have hLimitReal : Tendsto (fun N : ℕ => μ.real (E N)) atTop (𝓝 (μ.real F)) := by
    simpa only [Function.comp_def, measureReal_def] using
      (ENNReal.tendsto_toReal (measure_ne_top μ F)).comp hLimitENN
  refine ⟨hFMeas, ?_⟩
  exact le_of_tendsto_of_tendsto hLimitReal tendsto_const_nhds
    (Eventually.of_forall hFiniteBound)

/-- The actual n-squared normalized prefix rectangle averages satisfy the
countable weak maximal bound and have an almost surely bounded absolute range.
This is Krengel, Ergodic Theorems, §6.2 Corollary 2.7 and the maximal input to
Theorem 2.8. The original signed observable need only be integrable. -/
theorem prefix_rectangle_maximal_bound_and_ae_bounded
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (T : (ℤ × ℤ) → Ω → Ω)
    (hzero : ∀ s, T 0 s = s)
    (hadd : ∀ z w s, T (z + w) s = T z (T w s))
    (hT : ∀ z, MeasurePreserving (T z) μ μ)
    (f : Ω → ℝ) (hf : Integrable f μ)
    (b : Fin 2 → ℝ) (hb : ∀ i, 0 < b i) :
    let R : ℕ → Finset (ℤ × ℤ) := fun n =>
      (Finset.Ico (0 : ℤ) ((⌊(n : ℝ) * b 0⌋₊ : ℕ) : ℤ)).product
        (Finset.Ico (0 : ℤ) ((⌊(n : ℝ) * b 1⌋₊ : ℕ) : ℤ))
    let A : ℕ → Ω → ℝ := fun n s =>
      (∑ z ∈ R n, f (T z s)) / (n : ℝ)^2
    (∀ t : ℝ, 0 < t → μ.real {s | ∃ n : ℕ, t < |A n s|} ≤
      (4 * b 0 * b 1 / t) * ∫ s, |f s| ∂μ) ∧
      (∀ᵐ s ∂μ, BddAbove (Set.range (fun n : ℕ => |A n s|))) := by
  classical
  let R : ℕ → Finset (ℤ × ℤ) := fun n =>
    (Finset.Ico (0 : ℤ) ((⌊(n : ℝ) * b 0⌋₊ : ℕ) : ℤ)).product
      (Finset.Ico (0 : ℤ) ((⌊(n : ℝ) * b 1⌋₊ : ℕ) : ℤ))
  let A : ℕ → Ω → ℝ := fun n s => (∑ z ∈ R n, f (T z s)) / (n : ℝ)^2
  change (∀ t : ℝ, 0 < t → μ.real {s | ∃ n : ℕ, t < |A n s|} ≤
    (4 * b 0 * b 1 / t) * ∫ s, |f s| ∂μ) ∧
    (∀ᵐ s ∂μ, BddAbove (Set.range (fun n : ℕ => |A n s|)))
  -- One event of agreement under ALL signed shifts transfers ALL original averages.
  let q : Ω → ℝ := hf.aestronglyMeasurable.mk f
  have hqMeas : Measurable q := hf.aestronglyMeasurable.measurable_mk
  have hEq : f =ᵐ[μ] q := hf.aestronglyMeasurable.ae_eq_mk
  have hqInt : Integrable q μ := hf.congr hEq
  let Aq : ℕ → Ω → ℝ := fun n s => (∑ z ∈ R n, q (T z s)) / (n : ℝ)^2
  have hAll : ∀ᵐ s ∂μ, ∀ z : ℤ × ℤ, f (T z s) = q (T z s) := by
    rw [ae_all_iff]
    intro z
    have h := (hT z).quasiMeasurePreserving.ae_eq_comp hEq
    filter_upwards [h] with s hs
    simpa only [Function.comp_apply] using hs
  have hAverages : ∀ᵐ s ∂μ, ∀ n : ℕ, A n s = Aq n s := by
    filter_upwards [hAll] with s hs
    intro n
    have hSum : (∑ z ∈ R n, f (T z s)) = ∑ z ∈ R n, q (T z s) := by
      apply Finset.sum_congr rfl
      intro z hz
      exact hs z
    exact congrArg (fun x : ℝ => x / (n : ℝ)^2) hSum
  have hAbsIntegral : (∫ s, |q s| ∂μ) = ∫ s, |f s| ∂μ :=
    integral_congr_ae (hEq.fun_comp abs).symm
  have hWeak (t : ℝ) (ht : 0 < t) : μ.real {s | ∃ n : ℕ, t < |A n s|} ≤
      (4 * b 0 * b 1 / t) * ∫ s, |f s| ∂μ := by
    have hEvent : {s | ∃ n : ℕ, t < |A n s|} =ᵐ[μ] {s | ∃ n : ℕ, t < |Aq n s|} := by
      filter_upwards [hAverages] with s hs
      apply propext
      constructor
      · rintro ⟨n, hc⟩
        exact ⟨n, by rw [← hs n]; exact hc⟩
      · rintro ⟨n, hc⟩
        exact ⟨n, by rw [hs n]; exact hc⟩
    have hqBound := measurable_countable_rectangle_bound μ T hzero hadd hT q hqMeas hqInt b hb t ht
    change MeasurableSet {s | ∃ n : ℕ, t < |Aq n s|} ∧
      μ.real {s | ∃ n : ℕ, t < |Aq n s|} ≤ (4 * b 0 * b 1 / t) * ∫ s, |q s| ∂μ at hqBound
    calc
      μ.real {s | ∃ n : ℕ, t < |A n s|} = μ.real {s | ∃ n : ℕ, t < |Aq n s|} :=
        measureReal_congr hEvent
      _ ≤ (4 * b 0 * b 1 / t) * ∫ s, |q s| ∂μ := hqBound.2
      _ = (4 * b 0 * b 1 / t) * ∫ s, |f s| ∂μ := by rw [hAbsIntegral]
  refine ⟨hWeak, ?_⟩
  -- An unbounded real range crosses every positive threshold, whose measures tend to zero.
  let U : Set Ω := {s | ¬BddAbove (Set.range (fun n : ℕ => |A n s|))}
  let C : ℝ := 4 * b 0 * b 1 * ∫ s, |f s| ∂μ
  have hSubset (t : ℝ) : U ⊆ {s | ∃ n : ℕ, t < |A n s|} := by
    intro s hs
    change ¬BddAbove (Set.range (fun n : ℕ => |A n s|)) at hs
    obtain ⟨y, hy, hty⟩ := not_bddAbove_iff.mp hs t
    obtain ⟨n, rfl⟩ := hy
    exact ⟨n, hty⟩
  have hUBound (k : ℕ) (hk : 0 < k) : μ.real U ≤ C / (k : ℝ) := by
    have hkReal : 0 < (k : ℝ) := Nat.cast_pos.mpr hk
    calc
      μ.real U ≤ μ.real {s | ∃ n : ℕ, (k : ℝ) < |A n s|} := measureReal_mono (hSubset (k : ℝ))
      _ ≤ (4 * b 0 * b 1 / (k : ℝ)) * ∫ s, |f s| ∂μ := hWeak (k : ℝ) hkReal
      _ = C / (k : ℝ) := by dsimp only [C]; ring
  have hULe : μ.real U ≤ 0 := by
    apply le_of_tendsto_of_tendsto tendsto_const_nhds (tendsto_const_div_atTop_nhds_zero_nat C)
    filter_upwards [eventually_gt_atTop 0] with k hk
    exact hUBound k hk
  have hURealZero : μ.real U = 0 := le_antisymm hULe measureReal_nonneg
  have hUZero : μ U = 0 := (measureReal_eq_zero_iff (measure_ne_top μ U)).mp hURealZero
  exact ae_iff.mpr hUZero

end ProbabilityBasics
