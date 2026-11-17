/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module
public import ProbabilityBasics.Probability.JointBirkhoffL1
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
public import Mathlib.MeasureTheory.MeasurableSpace.Invariants
public import Mathlib.Data.Int.Interval
public import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

public section
open MeasureTheory Filter Set
open scoped BigOperators
open scoped Topology
namespace ProbabilityBasics

private theorem signed_invariant_version
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (T : (ℤ × ℤ) → Ω → Ω) (hzero : ∀ s, T 0 s = s)
    (hadd : ∀ z w s, T (z + w) s = T z (T w s))
    (hT : ∀ z, MeasurePreserving (T z) μ μ)
    (v : Ω → ℝ) (hvm : Measurable v)
    (h0 : ∀ᵐ s ∂μ, v (T (1, 0) s) = v s)
    (h1 : ∀ᵐ s ∂μ, v (T (0, 1) s) = v s) :
    ∃ g : Ω → ℝ, Measurable g ∧ g =ᵐ[μ] v ∧
      ∀ z s, g (T z s) = g s := by
  classical
  let H : AddSubgroup (ℤ × ℤ) :=
    { carrier := {z | ∀ᵐ s ∂μ, v (T z s) = v s}
      zero_mem' := by
        change ∀ᵐ s ∂μ, v (T 0 s) = v s
        filter_upwards [] with s
        rw [hzero]
      add_mem' := by
        intro z w hz hw
        change ∀ᵐ s ∂μ, v (T z s) = v s at hz
        change ∀ᵐ s ∂μ, v (T w s) = v s at hw
        change ∀ᵐ s ∂μ, v (T (z + w) s) = v s
        have hz' := (hT w).quasiMeasurePreserving.ae hz
        filter_upwards [hz', hw] with s hs hs'
        exact (congrArg v (hadd z w s)).trans (hs.trans hs')
      neg_mem' := by
        intro z hz
        change ∀ᵐ s ∂μ, v (T z s) = v s at hz
        change ∀ᵐ s ∂μ, v (T (-z) s) = v s
        have hz' := (hT (-z)).quasiMeasurePreserving.ae hz
        filter_upwards [hz'] with s hs
        have hh : T z (T (-z) s) = s := by
          rw [← hadd, add_neg_cancel, hzero]
        rw [hh] at hs
        exact hs.symm }
  have h0H : (1, 0) ∈ H := h0
  have h1H : (0, 1) ∈ H := h1
  have hall (z : ℤ × ℤ) : ∀ᵐ s ∂μ, v (T z s) = v s := by
    have h := H.add_mem (H.zsmul_mem h0H z.1) (H.zsmul_mem h1H z.2)
    have hz : z.1 • ((1, 0) : ℤ × ℤ) + z.2 • ((0, 1) : ℤ × ℤ) = z := by
      ext <;> simp
    rw [hz] at h
    exact h
  let C : Set Ω := {s | ∀ z w, v (T z s) = v (T w s)}
  have hCm : MeasurableSet C := by
    simp only [C, Set.ofPred_forall]
    exact MeasurableSet.iInter fun z => MeasurableSet.iInter fun w =>
      measurableSet_eq_fun (hvm.comp (hT z).measurable) (hvm.comp (hT w).measurable)
  have hCae : ∀ᵐ s ∂μ, s ∈ C := by
    filter_upwards [ae_all_iff.mpr hall] with s hs
    exact fun z w => (hs z).trans (hs w).symm
  have hCforward (z : ℤ × ℤ) (s : Ω) (hs : s ∈ C) : T z s ∈ C := by
    intro x y
    rw [← hadd, ← hadd]
    exact hs (x + z) (y + z)
  have hCiff (z : ℤ × ℤ) (s : Ω) : T z s ∈ C ↔ s ∈ C := by
    constructor
    · intro hs
      have hback := hCforward (-z) (T z s) hs
      rw [← hadd, neg_add_cancel, hzero] at hback
      exact hback
    · exact hCforward z s
  let g : Ω → ℝ := C.indicator v
  have hgeq : g =ᵐ[μ] v := by
    filter_upwards [hCae] with s hs
    exact Set.indicator_of_mem hs v
  refine ⟨g, hvm.indicator hCm, hgeq, ?_⟩
  intro z s
  change C.indicator v (T z s) = C.indicator v s
  by_cases hs : s ∈ C
  · rw [Set.indicator_of_mem ((hCiff z s).mpr hs), Set.indicator_of_mem hs]
    simpa only [hzero] using hs z 0
  · have hnot : T z s ∉ C := fun h => hs ((hCiff z s).mp h)
    rw [Set.indicator_of_notMem hnot, Set.indicator_of_notMem hs]

/-- The fixed-aspect rectangle L1 limit and its full invariant conditional mean, following Krengel, Ergodic Theorems, section 6.2. -/
theorem exists_prefix_rectangle_l1_condExp
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (T : (ℤ × ℤ) → Ω → Ω)
    (hzero : ∀ s, T 0 s = s)
    (hadd : ∀ z w s, T (z + w) s = T z (T w s))
    (hT : ∀ z, MeasurePreserving (T z) μ μ)
    (f : Ω → ℝ) (hf : Integrable f μ)
    (b : Fin 2 → ℝ) (hb : ∀ i, 0 < b i) :
    let mΩ : MeasurableSpace Ω := inferInstance
    let I : MeasurableSpace Ω :=
      ⨅ z : ℤ × ℤ, @MeasurableSpace.invariants Ω mΩ (T z)
    letI : MeasurableSpace Ω := mΩ
    let R : ℕ → Finset (ℤ × ℤ) := fun n =>
      (Finset.Ico (0 : ℤ) ((⌊(n : ℝ) * b 0⌋₊ : ℕ) : ℤ)).product
        (Finset.Ico (0 : ℤ) ((⌊(n : ℝ) * b 1⌋₊ : ℕ) : ℤ))
    ∃ g : Ω → ℝ, Measurable[I] g ∧ Integrable g μ ∧
      (∀ (z : ℤ × ℤ) s, g (T z s) = g s) ∧
      (∀ A : Set Ω, MeasurableSet[I] A →
        (∫ s in A, g s ∂μ) = ∫ s in A, f s ∂μ) ∧
      g =ᵐ[μ] μ[f | I] ∧
      Tendsto (fun n : ℕ => ∫ s,
        |(∑ z ∈ R n, f (T z s)) / (n : ℝ)^2 - b 0 * b 1 * g s| ∂μ)
        atTop (𝓝 0)
 := by
  classical
  let mΩ : MeasurableSpace Ω := inferInstance
  let I : MeasurableSpace Ω := ⨅ z : ℤ × ℤ, @MeasurableSpace.invariants Ω mΩ (T z)
  let : MeasurableSpace Ω := mΩ
  let S : Ω → Ω := T (1, 0)
  let U : Ω → Ω := T (0, 1)
  have hcomm : Function.Commute S U := by
    intro s
    change T (1, 0) (T (0, 1) s) = T (0, 1) (T (1, 0) s)
    rw [← hadd, ← hadd]
    congr 1
  obtain ⟨v, hvm, hvi, hvS, hvU, hvMean, hvL1⟩ :=
    exists_joint_birkhoffL1_limit μ S U (hT (1, 0)) (hT (0, 1)) hcomm f hf
  obtain ⟨g, hgm, hgv, hgInv⟩ := signed_invariant_version μ T hzero hadd hT v hvm hvS hvU
  have hgi : Integrable g μ := hvi.congr hgv.symm
  have hgmI : Measurable[I] g := by
    intro A hA
    apply MeasurableSpace.measurableSet_iInf.mpr
    intro z
    apply MeasurableSpace.measurableSet_invariants.mpr
    refine ⟨hgm hA, ?_⟩
    ext s
    simp only [Set.mem_preimage]
    rw [hgInv]
  have hIle : I ≤ mΩ := by
    exact (iInf_le (fun z : ℤ × ℤ => @MeasurableSpace.invariants Ω mΩ (T z)) 0).trans
      (MeasurableSpace.invariants_le (T 0))
  have hgMean (A : Set Ω) (hA : MeasurableSet[I] A) :
      (∫ s in A, g s ∂μ) = ∫ s in A, f s ∂μ := by
    have hh (z : ℤ × ℤ) := MeasurableSpace.measurableSet_invariants.mp
      (MeasurableSpace.measurableSet_iInf.mp hA z)
    calc
      _ = ∫ s in A, v s ∂μ := integral_congr_ae (ae_restrict_of_ae hgv)
      _ = ∫ s in A, f s ∂μ := hvMean A (hh 0).1 (hh (1,0)).2 (hh (0,1)).2
  have hgCE : g =ᵐ[μ] μ[f | I] := by
    exact ae_eq_condExp_of_forall_setIntegral_eq hIle hf
      (fun _ _ _ => hgi.integrableOn) (fun A hA _ => hgMean A hA)
      hgmI.stronglyMeasurable.aestronglyMeasurable
  let A : ℕ → ℕ := fun n => ⌊(n : ℝ) * b 0⌋₊
  let B : ℕ → ℕ := fun n => ⌊(n : ℝ) * b 1⌋₊
  let R : ℕ → Finset (ℤ × ℤ) := fun n =>
    (Finset.Ico (0 : ℤ) (A n : ℤ)).product (Finset.Ico (0 : ℤ) (B n : ℤ))
  let K : ℕ → ℝ := fun n => ((A n : ℝ) / (n : ℝ)) * ((B n : ℝ) / (n : ℝ))
  let G : ℕ → Ω → ℝ := fun n =>
    birkhoffAverage ℝ S (birkhoffAverage ℝ U f (B n)) (A n)
  have hA : Tendsto A atTop atTop := by
    simpa only [A, mul_comm] using tendsto_nat_floor_mul_atTop (b 0) (hb 0)
  have hB : Tendsto B atTop atTop := by
    simpa only [B, mul_comm] using tendsto_nat_floor_mul_atTop (b 1) (hb 1)
  have hfloor (i : Fin 2) : Tendsto
      (fun n : ℕ => (⌊(n : ℝ) * b i⌋₊ : ℝ) / (n : ℝ)) atTop (𝓝 (b i)) := by
    have hh := (tendsto_nat_floor_mul_div_atTop (hb i).le).comp
      (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop)
    simpa only [Function.comp_def, mul_comm] using hh
  have hK : Tendsto K atTop (𝓝 (b 0 * b 1)) := (hfloor 0).mul (hfloor 1)
  have hL1v : Tendsto (fun n => ∫ s, |G n s - v s| ∂μ) atTop (𝓝 0) :=
    hvL1 A B hA hB
  have hL1g : Tendsto (fun n => ∫ s, |G n s - g s| ∂μ) atTop (𝓝 0) := by
    apply hL1v.congr'
    filter_upwards [] with n
    apply integral_congr_ae
    filter_upwards [hgv] with s hs
    rw [hs]
  have hiter (z : ℤ × ℤ) (n : ℕ) (s : Ω) :
      (T z)^[n] s = T (n • z) s := by
    induction n with
    | zero => simp only [Function.iterate_zero_apply, zero_nsmul, hzero]
    | succ n ih =>
      rw [Function.iterate_succ_apply', ih, ← hadd]
      congr 1
      simp only [succ_nsmul, add_comm]
  have hsumIco (N : ℕ) (q : ℤ → ℝ) :
      (∑ x ∈ Finset.Ico (0 : ℤ) (N : ℤ), q x) =
        ∑ k ∈ Finset.range N, q (k : ℤ) := by
    rw [Int.Ico_eq_finset_map]
    simp
  have hrect (a c : ℕ) (q : ℤ × ℤ → ℝ) :
      (∑ z ∈ (Finset.Ico (0 : ℤ) (a : ℤ)).product
          (Finset.Ico (0 : ℤ) (c : ℤ)), q z) =
        ∑ j ∈ Finset.range a, ∑ k ∈ Finset.range c, q ((j : ℤ), (k : ℤ)) := by
    calc
      _ = ∑ j ∈ Finset.Ico (0 : ℤ) (a : ℤ),
          ∑ k ∈ Finset.Ico (0 : ℤ) (c : ℤ), q (j, k) := Finset.sum_product _ _ _
      _ = ∑ j ∈ Finset.range a,
          ∑ k ∈ Finset.Ico (0 : ℤ) (c : ℤ), q ((j : ℤ), k) := by rw [hsumIco]
      _ = ∑ j ∈ Finset.range a, ∑ k ∈ Finset.range c, q ((j : ℤ), (k : ℤ)) := by
        apply Finset.sum_congr rfl
        intro j hj
        exact hsumIco c (fun k => q ((j : ℤ), k))
  have hshift (j k : ℕ) (s : Ω) :
      (U^[k]) ((S^[j]) s) = T ((j : ℤ), (k : ℤ)) s := by
    rw [hiter, hiter, ← hadd]
    congr 1
    ext <;> simp
  have hsum (n : ℕ) (s : Ω) :
      (∑ z ∈ R n, f (T z s)) =
        ∑ j ∈ Finset.range (A n), ∑ k ∈ Finset.range (B n),
          f ((U^[k]) ((S^[j]) s)) := by
    rw [hrect]
    apply Finset.sum_congr rfl
    intro j hj
    apply Finset.sum_congr rfl
    intro k hk
    rw [hshift]
  have hApos : ∀ᶠ n in atTop, 0 < A n := hA.eventually (eventually_gt_atTop 0)
  have hBpos : ∀ᶠ n in atTop, 0 < B n := hB.eventually (eventually_gt_atTop 0)
  have hraw : ∀ᶠ n in atTop, ∀ s,
      (∑ z ∈ R n, f (T z s)) / (n : ℝ)^2 = K n * G n s := by
    filter_upwards [hApos, hBpos, eventually_gt_atTop 0] with n han hbn hn s
    have ha : (A n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt han)
    have hb' : (B n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hbn)
    have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
    rw [hsum]
    simp only [G, birkhoffAverage, birkhoffSum, smul_eq_mul, Finset.mul_sum]
    dsimp [K]
    field_simp [ha, hb', hn']
    simpa only [Finset.sum_div, Finset.mul_sum, mul_div_assoc] using
      (mul_div_cancel_left₀
        (∑ j ∈ Finset.range (A n), ∑ k ∈ Finset.range (B n),
          f ((U^[k]) ((S^[j]) s))) (pow_ne_zero 2 hn')).symm
  have hGint (n : ℕ) : Integrable (G n) μ :=
    LPPDifferentiability.integrable_birkhoffAverage (hT (1,0))
      (LPPDifferentiability.integrable_birkhoffAverage (hT (0,1)) hf (B n)) (A n)
  let E : ℕ → ℝ := fun n => ∫ s, |K n * G n s - (b 0 * b 1) * g s| ∂μ
  let H : ℕ → ℝ := fun n =>
    |K n| * (∫ s, |G n s - g s| ∂μ) +
      |K n - b 0 * b 1| * (∫ s, |g s| ∂μ)
  have hH : Tendsto H atTop (𝓝 0) := by
    have h1 := hK.abs.mul hL1g
    have h2 := (hK.sub (tendsto_const_nhds :
      Tendsto (fun _ : ℕ => b 0 * b 1) atTop (𝓝 (b 0 * b 1)))).abs.mul
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => ∫ s, |g s| ∂μ) atTop
        (𝓝 (∫ s, |g s| ∂μ)))
    simpa [H] using h1.add h2
  have hbound (n : ℕ) : E n ≤ H n := by
    have hleft : Integrable (fun s => |K n * G n s - (b 0 * b 1) * g s|) μ := by
      simpa only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] using
        (((hGint n).const_mul (K n)).sub (hgi.const_mul (b 0 * b 1))).abs
    have hfirst : Integrable (fun s => |K n| * |G n s - g s|) μ := by
      simpa only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] using
        (((hGint n).sub hgi).abs.const_mul |K n|)
    have hsecond : Integrable (fun s => |K n - b 0 * b 1| * |g s|) μ := by
      exact hgi.abs.const_mul _
    have hpt (s : Ω) : |K n * G n s - (b 0 * b 1) * g s| ≤
        |K n| * |G n s - g s| + |K n - b 0 * b 1| * |g s| := by
      calc
        _ = |K n * (G n s - g s) + (K n - b 0 * b 1) * g s| := by congr 1; ring
        _ ≤ |K n * (G n s - g s)| + |(K n - b 0 * b 1) * g s| := abs_add_le _ _
        _ = _ := by simp only [abs_mul]
    have hh := integral_mono hleft (hfirst.add hsecond) hpt
    simp only [Pi.add_apply, integral_add hfirst hsecond, integral_const_mul] at hh
    exact hh
  have hE : Tendsto E atTop (𝓝 0) :=
    squeeze_zero (fun n => integral_nonneg fun s => abs_nonneg _) hbound hH
  refine ⟨g, hgmI, hgi, hgInv, hgMean, hgCE, ?_⟩
  apply hE.congr'
  filter_upwards [hraw] with n hn
  apply integral_congr_ae
  filter_upwards [] with s
  rw [hn s]

end ProbabilityBasics
