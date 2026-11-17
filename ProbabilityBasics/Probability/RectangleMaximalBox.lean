/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProbabilityBasics.Combinatorics.RectangleWeightedCount
public import Mathlib.Dynamics.Ergodic.MeasurePreserving
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Tactic

/-! Finite-box integration for the rectangle maximal inequality. -/

public section

open MeasureTheory Filter Set
open scoped BigOperators ENNReal

namespace ProbabilityBasics

/-- Integrating the finite rectangle count over an invariant probability law
produces the finite-box bound in Krengel's Section 6.2 transference argument. -/
theorem finite_rectangle_box_integral_of_measurable
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (T : (ℤ × ℤ) → Ω → Ω)
    (hzero : ∀ s, T 0 s = s)
    (hadd : ∀ z w s, T (z + w) s = T z (T w s))
    (hT : ∀ z, MeasurePreserving (T z) μ μ)
    (f : Ω → ℝ) (hfm : Measurable f) (hfi : Integrable f μ)
    (b : Fin 2 → ℝ) (hb : ∀ i, 0 < b i)
    (N m : ℕ) (t : ℝ) (ht : 0 < t) :
    let R : ℕ → Finset (ℤ × ℤ) := fun n =>
      (Finset.Ico (0 : ℤ) ((⌊(n : ℝ) * b 0⌋₊ : ℕ) : ℤ)).product
        (Finset.Ico (0 : ℤ) ((⌊(n : ℝ) * b 1⌋₊ : ℕ) : ℤ))
    let E : Set Ω := {s | ∃ n ∈ Finset.Icc 1 N,
      t * ((R n).card : ℝ) < ∑ v ∈ R n, |f (T v s)|}
    let M : ℕ := max ⌊(N : ℝ) * b 0⌋₊ ⌊(N : ℝ) * b 1⌋₊
    t * (m : ℝ)^2 * μ.real E ≤
      4 * (((m + M : ℕ) : ℝ)^2) * ∫ s, |f s| ∂μ := by
  classical
  let a : ℕ → ℕ := fun n => ⌊(n : ℝ) * b 0⌋₊
  let c : ℕ → ℕ := fun n => ⌊(n : ℝ) * b 1⌋₊
  let R : ℕ → Finset (ℤ × ℤ) := fun n =>
    (Finset.Ico (0 : ℤ) (a n : ℤ)).product (Finset.Ico (0 : ℤ) (c n : ℤ))
  let E : Set Ω := {s | ∃ n ∈ Finset.Icc 1 N,
    t * ((R n).card : ℝ) < ∑ v ∈ R n, |f (T v s)|}
  let M : ℕ := max (a N) (c N)
  let A : Finset (ℤ × ℤ) := (Finset.Ico (0 : ℤ) (m : ℤ)).product
    (Finset.Ico (0 : ℤ) (m : ℤ))
  let B : Finset (ℤ × ℤ) := (Finset.Ico (0 : ℤ) ((m + M : ℕ) : ℤ)).product
    (Finset.Ico (0 : ℤ) ((m + M : ℕ) : ℤ))
  change t * (m : ℝ)^2 * μ.real E ≤
    4 * (((m + M : ℕ) : ℝ)^2) * ∫ s, |f s| ∂μ
  have ha : Monotone a := by
    intro j k hjk
    apply Nat.floor_mono
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hjk) (hb 0).le
  have hc : Monotone c := by
    intro j k hjk
    apply Nat.floor_mono
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hjk) (hb 1).le
  have hcontain : ∀ u ∈ A, ∀ n ∈ Finset.Icc 1 N, ∀ v ∈ R n, u + v ∈ B := by
    intro u hu n hn v hv
    have hnN := (Finset.mem_Icc.mp hn).2
    have h1 : a n ≤ M := (ha hnN).trans (le_max_left _ _)
    have h2 : c n ≤ M := (hc hnN).trans (le_max_right _ _)
    have h1' : (a n : ℤ) ≤ (M : ℤ) := by exact_mod_cast h1
    have h2' : (c n : ℤ) ≤ (M : ℤ) := by exact_mod_cast h2
    rcases Finset.mem_product.mp hu with ⟨hu1, hu2⟩
    rcases Finset.mem_product.mp hv with ⟨hv1, hv2⟩
    rcases Finset.mem_Ico.mp hu1 with ⟨hu10, hu1m⟩
    rcases Finset.mem_Ico.mp hu2 with ⟨hu20, hu2m⟩
    rcases Finset.mem_Ico.mp hv1 with ⟨hv10, hv1a⟩
    rcases Finset.mem_Ico.mp hv2 with ⟨hv20, hv2c⟩
    apply Finset.mem_product.mpr
    constructor <;> apply Finset.mem_Ico.mpr <;> constructor <;>
      simp only [Prod.fst_add, Prod.snd_add, Nat.cast_add] <;> omega
  have hEmeas : MeasurableSet E := by
    have heq : E = ⋃ n ∈ Finset.Icc 1 N,
        {s : Ω | t * ((R n).card : ℝ) < ∑ v ∈ R n, |f (T v s)|} := by
      ext s
      simp [E]
    rw [heq]
    apply Finset.measurableSet_biUnion
    intro n hn
    apply measurableSet_lt measurable_const
    apply Finset.measurable_sum
    intro v hv
    simpa only [Function.comp_apply, Real.norm_eq_abs] using
      (hfm.comp (hT v).measurable).norm
  let Cnt : Ω → ℝ := fun s => ∑ u ∈ A, (T u ⁻¹' E).indicator (fun _ => (1 : ℝ)) s
  let W : Ω → ℝ := fun s => ∑ v ∈ B, |f (T v s)|
  have hCntInt : Integrable Cnt μ := by
    apply integrable_finsetSum
    intro u hu
    exact (integrable_const (1 : ℝ)).indicator ((hT u).measurable hEmeas)
  have hWInt : Integrable W μ := by
    apply integrable_finsetSum
    intro v hv
    exact (hT v).integrable_comp_of_integrable hfi.abs
  have hpoint (s : Ω) : t * Cnt s ≤ 4 * W s := by
    let Bad : (ℤ × ℤ) → Prop := fun u => ∃ n ∈ Finset.Icc 1 N,
      (R n).Nonempty ∧ t * ((R n).card : ℝ) < ∑ v ∈ R n, |f (T (u + v) s)|
    let : DecidablePred Bad := Classical.decPred Bad
    have hbad (u : ℤ × ℤ) : Bad u ↔ T u s ∈ E := by
      change (∃ n ∈ Finset.Icc 1 N, (R n).Nonempty ∧
        t * ((R n).card : ℝ) < ∑ v ∈ R n, |f (T (u + v) s)|) ↔ _
      have hshift (v : ℤ × ℤ) : T (u + v) s = T v (T u s) := by
        rw [add_comm u v, hadd]
      simp only [E, Set.mem_ofPred_eq]
      constructor
      · rintro ⟨n, hn, _, hsum⟩
        exact ⟨n, hn, by simpa only [hshift] using hsum⟩
      · rintro ⟨n, hn, hsum⟩
        have hne : (R n).Nonempty := by
          by_contra hn'
          have hempty : R n = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn'
          simp [hempty] at hsum
        exact ⟨n, hn, hne, by simpa only [hshift] using hsum⟩
    have hcount := weighted_rectangle_weak_count a c ha hc A B N
      (fun v => |f (T v s)|) (fun v => abs_nonneg _) t ht hcontain
    dsimp only at hcount
    have hcount' : t * (((A.filter Bad).card : ℕ) : ℝ) ≤ 4 * W s := by
      simpa only [Bad, R, W] using hcount
    have hcnt : (((A.filter Bad).card : ℕ) : ℝ) = Cnt s := by
      rw [Finset.natCast_card_filter]
      apply Finset.sum_congr rfl
      intro u hu
      simp only [Set.indicator_apply, Set.mem_preimage]
      change (if Bad u then (1 : ℝ) else 0) = if T u s ∈ E then 1 else 0
      by_cases huBad : Bad u
      · have huE : T u s ∈ E := (hbad u).mp huBad
        simp only [ite_eq_left huBad, ite_eq_left huE]
      · have huE : T u s ∉ E := fun huE => huBad ((hbad u).mpr huE)
        simp only [ite_eq_right huBad, ite_eq_right huE]
    rw [hcnt] at hcount'
    have hid := hzero s
    simpa only [hid] using hcount'
  have hCntIntegral : (∫ s, Cnt s ∂μ) = (m : ℝ)^2 * μ.real E := by
    rw [show Cnt = fun s => ∑ u ∈ A,
      (T u ⁻¹' E).indicator (fun _ => (1 : ℝ)) s by rfl]
    rw [integral_finsetSum]
    · have hterm (u : ℤ × ℤ) :
          (∫ s, (T u ⁻¹' E).indicator (fun _ => (1 : ℝ)) s ∂μ) = μ.real E := by
        calc
          _ = μ.real (T u ⁻¹' E) := by
            simpa only [smul_eq_mul, mul_one] using
              (integral_indicator_const (μ := μ) (1 : ℝ) ((hT u).measurable hEmeas))
          _ = μ.real E := (hT u).measureReal_preimage hEmeas.nullMeasurableSet
      simp only [hterm, Finset.sum_const, nsmul_eq_mul]
      have hcard : A.card = m * m := (integer_rectangle_difference_regularities m m).1
      rw [hcard]
      push_cast
      ring
    · intro u hu
      exact (integrable_const (1 : ℝ)).indicator ((hT u).measurable hEmeas)
  have hWIntegral : (∫ s, W s ∂μ) = (((m + M : ℕ) : ℝ)^2) * ∫ s, |f s| ∂μ := by
    rw [show W = fun s => ∑ v ∈ B, |f (T v s)| by rfl]
    rw [integral_finsetSum]
    · have hterm (v : ℤ × ℤ) : (∫ s, |f (T v s)| ∂μ) = ∫ s, |f s| ∂μ := by
        have hm : AEStronglyMeasurable (fun s => |f s|) (μ.map (T v)) := by
          rw [(hT v).map_eq]
          exact hfi.abs.aestronglyMeasurable
        have hmap := integral_map (hT v).aemeasurable hm
        rw [(hT v).map_eq] at hmap
        exact hmap.symm
      simp only [hterm, Finset.sum_const, nsmul_eq_mul]
      have hcard : B.card = (m + M) * (m + M) :=
        (integer_rectangle_difference_regularities (m + M) (m + M)).1
      rw [hcard]
      push_cast
      ring
    · intro v hv
      exact (hT v).integrable_comp_of_integrable hfi.abs
  have hintegral := integral_mono (hCntInt.const_mul t) (hWInt.const_mul 4) hpoint
  rw [integral_const_mul, integral_const_mul, hCntIntegral, hWIntegral] at hintegral
  linarith only [hintegral]

end ProbabilityBasics
