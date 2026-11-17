/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProbabilityBasics.Probability.BirkhoffInvariantSetIntegrals

/-! The same Birkhoff L¹ limit retains invariance under a commuting preserving map. -/

@[expose] public section

open MeasureTheory Filter
open scoped Topology BigOperators

namespace ProbabilityBasics

/-- The Birkhoff L¹ limit of an observable fixed almost everywhere by a commuting
measure-preserving map remains fixed by that map. The same witness retains both
invariances and every invariant-set integral. This is the norm-limit inheritance
step in Krengel, Ergodic Theorems, §6.2 Theorem 2.8, finite-measure identification remark. -/
theorem exists_birkhoffL1_invariant_of_commute
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (S T : Ω → Ω) (hS : MeasurePreserving S μ μ) (hT : MeasurePreserving T μ μ)
    (hcomm : Function.Commute S T)
    (f : Ω → ℝ) (hf : Integrable f μ)
    (hInv : ∀ᵐ s ∂μ, f (S s) = f s) :
    ∃ g : Ω → ℝ, Measurable g ∧ Integrable g μ ∧
      (∀ᵐ s ∂μ, g (T s) = g s) ∧
      (∀ᵐ s ∂μ, g (S s) = g s) ∧
      Tendsto (fun n : ℕ => ∫ s, |birkhoffAverage ℝ T f n s - g s| ∂μ)
        atTop (𝓝 0) ∧
      (∀ A : Set Ω, MeasurableSet A → T ⁻¹' A = A →
        (∫ s in A, g s ∂μ) = ∫ s in A, f s ∂μ) := by
  -- Retain exactly the witness and all fields from the original-L¹ producer.
  obtain ⟨g, hgm, hgi, hgT, hL1, hMeans⟩ :=
    exists_birkhoffL1_invariant_set_integrals μ T hT f hf
  let u : ℕ → Ω → ℝ := fun n => birkhoffAverage ℝ T f n
  -- Every actual finite average is S-fixed on an event obtained by genuine iterate pullbacks.
  have hAll : ∀ᵐ s ∂μ, ∀ k : ℕ, f (S ((T^[k]) s)) = f ((T^[k]) s) :=
    ae_all_iff.mpr fun k => (hT.iterate k).quasiMeasurePreserving.ae hInv
  have hAverageInv (n : ℕ) : ∀ᵐ s ∂μ, u n (S s) = u n s := by
    filter_upwards [hAll] with s hs
    dsimp only [u]
    unfold birkhoffAverage birkhoffSum
    apply congrArg (fun x : ℝ => (n : ℝ)⁻¹ • x)
    apply Finset.sum_congr rfl
    intro k hk
    rw [← (hcomm.iterate_right k) s]
    exact hs k
  let e : ℕ → Ω → ℝ := fun n s => |u n s - g s|
  let d : Ω → ℝ := fun s => |g (S s) - g s|
  have hErrorInt (n : ℕ) : Integrable (e n) μ := by
    simpa only [Pi.sub_apply] using
      ((LPPDifferentiability.integrable_birkhoffAverage hT hf n).sub hgi).abs
  have hgCompInt : Integrable (fun s => g (S s)) μ :=
    hS.integrable_comp_of_integrable hgi
  have hDefectInt : Integrable d μ := by
    simpa only [Pi.sub_apply] using (hgCompInt.sub hgi).abs
  -- Actual map transport makes the shifted error integral equal to the whole error integral.
  have hTransport (n : ℕ) : (∫ s, e n (S s) ∂μ) = ∫ s, e n s ∂μ := by
    have hMapped : AEStronglyMeasurable (e n) (μ.map S) := by
      rw [hS.map_eq]
      exact (hErrorInt n).aestronglyMeasurable
    have hMap := integral_map hS.aemeasurable hMapped
    rw [hS.map_eq] at hMap
    exact hMap.symm
  have hPoint (n : ℕ) : ∀ᵐ s ∂μ, d s ≤ e n (S s) + e n s := by
    filter_upwards [hAverageInv n] with s hs
    have hTerm : |g (S s) - u n s| = |u n (S s) - g (S s)| := by
      rw [hs]
      exact abs_sub_comm _ _
    calc
      d s = |g (S s) - g s| := rfl
      _ ≤ |g (S s) - u n s| + |u n s - g s| := abs_sub_le _ _ _
      _ = e n (S s) + e n s := by
        change |g (S s) - u n s| + |u n s - g s| =
          |u n (S s) - g (S s)| + |u n s - g s|
        rw [hTerm]
  have hBound (n : ℕ) : (∫ s, d s ∂μ) ≤ 2 * ∫ s, e n s ∂μ := by
    have hCompInt : Integrable (fun s => e n (S s)) μ :=
      hS.integrable_comp_of_integrable (hErrorInt n)
    have hIntegral := integral_mono_ae hDefectInt (hCompInt.add (hErrorInt n)) (hPoint n)
    simp only [Pi.add_apply] at hIntegral
    rw [integral_add hCompInt (hErrorInt n), hTransport n] at hIntegral
    simpa only [two_mul] using hIntegral
  -- Closure of this fixedness law follows from the actual L¹ error tending to zero.
  have hTwice : Tendsto (fun n : ℕ => 2 * ∫ s, e n s ∂μ) atTop (𝓝 0) := by
    simpa only [mul_zero] using hL1.const_mul (2 : ℝ)
  have hDefectLimit : Tendsto (fun _ : ℕ => ∫ s, d s ∂μ) atTop (𝓝 0) :=
    squeeze_zero (fun _ => integral_nonneg fun s => abs_nonneg (g (S s) - g s)) hBound hTwice
  have hDefectZero : (∫ s, d s ∂μ) = 0 :=
    tendsto_nhds_unique tendsto_const_nhds hDefectLimit
  have hDefectAE : d =ᵐ[μ] 0 :=
    (integral_eq_zero_iff_of_nonneg_ae
      (Eventually.of_forall fun s => abs_nonneg (g (S s) - g s)) hDefectInt).mp hDefectZero
  have hgS : ∀ᵐ s ∂μ, g (S s) = g s := by
    filter_upwards [hDefectAE] with s hs
    change |g (S s) - g s| = 0 at hs
    exact sub_eq_zero.mp (abs_eq_zero.mp hs)
  exact ⟨g, hgm, hgi, hgT, hgS, hL1, hMeans⟩

end ProbabilityBasics
