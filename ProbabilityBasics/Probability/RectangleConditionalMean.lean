/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProbabilityBasics.Probability.RectanglePointwise
public import ProbabilityBasics.Probability.RectangleL1Convergence
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Tactic

/-! Almost-sure convergence of rectangle averages to the full invariant mean. -/

@[expose] public section

open MeasureTheory Filter
open scoped BigOperators Topology

namespace ProbabilityBasics

/-- Actual fixed-aspect prefix rectangle averages converge almost surely to
the conditional mean on the sigma-algebra invariant under every signed shift.
This is the finite-measure invariant-mean identification in Krengel,
*Ergodic Theorems*, Section 6.2. -/
theorem ae_tendsto_prefix_rectangle_condExp
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
    ∀ᵐ s ∂μ, Tendsto (fun n : ℕ =>
      (∑ z ∈ R n, f (T z s)) / (n : ℝ)^2)
      atTop (𝓝 (b 0 * b 1 * (μ[f | I]) s)) := by
  let mΩ : MeasurableSpace Ω := inferInstance
  let I : MeasurableSpace Ω :=
    ⨅ z : ℤ × ℤ, @MeasurableSpace.invariants Ω mΩ (T z)
  let : MeasurableSpace Ω := mΩ
  let R : ℕ → Finset (ℤ × ℤ) := fun n =>
    (Finset.Ico (0 : ℤ) ((⌊(n : ℝ) * b 0⌋₊ : ℕ) : ℤ)).product
      (Finset.Ico (0 : ℤ) ((⌊(n : ℝ) * b 1⌋₊ : ℕ) : ℤ))
  let A : ℕ → Ω → ℝ := fun n s =>
    (∑ z ∈ R n, f (T z s)) / (n : ℝ)^2
  change ∀ᵐ s ∂μ, Tendsto (fun n : ℕ => A n s) atTop
    (𝓝 (b 0 * b 1 * (μ[f | I]) s))

  -- The two producers give the same finite averages and inputs.
  rcases exists_prefix_rectangle_l1_condExp μ T hzero hadd hT f hf b hb with
    ⟨g, -, hgInt, -, -, hgCE, hL1⟩
  let v : Ω → ℝ := fun s => b 0 * b 1 * g s
  have hAE : ∀ᵐ s ∂μ, ∃ l : ℝ, Tendsto (fun n : ℕ => A n s) atTop (𝓝 l) := by
    simpa only [A] using
      (ae_tendsto_prefix_rectangle_averages μ T hzero hadd hT f hf b hb)
  have hL1' : Tendsto (fun n : ℕ => ∫ s, |A n s - v s| ∂μ) atTop (𝓝 0) := by
    simpa only [A, v] using hL1

  -- Integrability of each actual average follows from the signed MP action.
  have hA (n : ℕ) : Integrable (A n) μ := by
    have hsum : Integrable (fun s => ∑ z ∈ R n, f (T z s)) μ := by
      apply integrable_finsetSum (R n)
      intro z hz
      exact (hT z).integrable_comp_of_integrable hf
    simpa only [A] using hsum.div_const ((n : ℝ)^2)
  have hv : Integrable v μ := by
    dsimp only [v]
    exact hgInt.const_mul (b 0 * b 1)
  have hDiff (n : ℕ) : Integrable (fun s => A n s - v s) μ := (hA n).sub hv

  -- The real L1 error is exactly the L1 seminorm at exponent one.
  have hNormEq (n : ℕ) :
      eLpNorm (fun s => A n s - v s) 1 μ =
        ENNReal.ofReal (∫ s, |A n s - v s| ∂μ) := by
    rw [eLpNorm_one_eq_lintegral_enorm (hDiff n).aestronglyMeasurable,
      ← ofReal_integral_norm_eq_lintegral_enorm (hDiff n)]
    simp only [Real.norm_eq_abs]
  have hNorm : Tendsto
      (fun n : ℕ => eLpNorm (fun s => A n s - v s) 1 μ) atTop (𝓝 0) := by
    simpa only [ENNReal.ofReal_zero, ← hNormEq] using ENNReal.tendsto_ofReal hL1'
  have hInMeasure : TendstoInMeasure μ A atTop v :=
    tendstoInMeasure_of_tendsto_eLpNorm (p := 1) one_ne_zero hNorm

  -- Identify the local pointwise limit through one AE-convergent subsequence.
  obtain ⟨ns, hns, hSub⟩ := hInMeasure.exists_seq_tendsto_ae
  filter_upwards [hAE, hSub, hgCE] with s hsAE hsSub hsCE
  obtain ⟨l, hl⟩ := hsAE
  have hlSub : Tendsto (fun k : ℕ => A (ns k) s) atTop (𝓝 l) :=
    hl.comp hns.tendsto_atTop
  have hlEq : l = b 0 * b 1 * (μ[f | I]) s := by
    calc
      l = v s := tendsto_nhds_unique hlSub hsSub
      _ = b 0 * b 1 * (μ[f | I]) s := by
        dsimp only [v]
        rw [hsCE]
  exact hlEq ▸ hl

end ProbabilityBasics
