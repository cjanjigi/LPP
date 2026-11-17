/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import ProbabilityBasics.Probability.RectangleConditionalMean
public import ProbabilityBasics.Probability.RectangleCountableMaximal
public import Mathlib.Data.Finset.Prod
import ProbabilityBasics.Analysis.GridWeightedAverages
import Mathlib.Tactic

/-! Affine weights on actual prefix rectangles with zero invariant conditional mean. -/

@[expose] public section

open MeasureTheory Filter
open scoped BigOperators Topology

namespace ProbabilityBasics

private theorem sum_integer_interval (N : ℕ) (g : ℤ → ℝ) :
    (∑ x ∈ Finset.Ico (0 : ℤ) (N : ℤ), g x) =
      ∑ k ∈ Finset.range N, g (k : ℤ) := by
  rw [Int.Ico_eq_finset_map]
  simp

private theorem sum_integer_rectangle (N M : ℕ) (g : ℤ × ℤ → ℝ) :
    (∑ z ∈ (Finset.Ico (0 : ℤ) (N : ℤ)).product
      (Finset.Ico (0 : ℤ) (M : ℤ)), g z) =
        ∑ k ∈ Finset.range N, ∑ l ∈ Finset.range M, g ((k : ℤ), (l : ℤ)) := by
  calc
    _ = ∑ k ∈ Finset.Ico (0 : ℤ) (N : ℤ),
        ∑ l ∈ Finset.Ico (0 : ℤ) (M : ℤ), g (k, l) := Finset.sum_product _ _ _
    _ = ∑ k ∈ Finset.range N,
        ∑ l ∈ Finset.Ico (0 : ℤ) (M : ℤ), g ((k : ℤ), l) := by rw [sum_integer_interval]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro k _
      exact sum_integer_interval M (fun l => g ((k : ℤ), l))

private theorem sum_integer_rectangle_rows (N M : ℕ) (g : ℤ × ℤ → ℝ) :
    (∑ z ∈ (Finset.Ico (0 : ℤ) (N : ℤ)).product
      (Finset.Ico (0 : ℤ) (M : ℤ)), g z) =
        ∑ l ∈ Finset.range M, ∑ k ∈ Finset.range N, g ((k : ℤ), (l : ℤ)) := by
  rw [sum_integer_rectangle]
  exact Finset.sum_comm

/-- Every affine coordinate weight has almost surely vanishing prefix rectangle averages
when the actual full-action invariant conditional mean is zero. This is the fixed-grid
step in JR1810.03580v3, Appendix B, Lemma B.5, for an original integrable observable. -/
theorem ae_tendsto_affine_weighted_prefix_rectangles_of_condExp_zero
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
    let coord : Fin 2 → (ℤ × ℤ) → ℤ := fun j z => if j = 0 then z.1 else z.2
    μ[f | I] =ᵐ[μ] (fun _ => (0 : ℝ)) →
      ∀ᵐ s ∂μ, ∀ (j : Fin 2) (c d : ℝ),
        Tendsto (fun n : ℕ =>
          (∑ z ∈ R n, (c + d * ((((coord j z : ℤ) : ℝ) + 1) / (n : ℝ))) *
            f (T z s)) / (n : ℝ)^2) atTop (𝓝 0) := by
  classical
  let mΩ : MeasurableSpace Ω := inferInstance
  let I : MeasurableSpace Ω :=
    ⨅ z : ℤ × ℤ, @MeasurableSpace.invariants Ω mΩ (T z)
  let : MeasurableSpace Ω := mΩ
  let R : ℕ → Finset (ℤ × ℤ) := fun n =>
    (Finset.Ico (0 : ℤ) ((⌊(n : ℝ) * b 0⌋₊ : ℕ) : ℤ)).product
      (Finset.Ico (0 : ℤ) ((⌊(n : ℝ) * b 1⌋₊ : ℕ) : ℤ))
  let coord : Fin 2 → (ℤ × ℤ) → ℤ := fun j z => if j = 0 then z.1 else z.2
  change μ[f | I] =ᵐ[μ] (fun _ => (0 : ℝ)) → _
  intro hzeroCE
  let L : Fin 2 → ℕ → ℕ := fun j n => ⌊(n : ℝ) * b j⌋₊
  let row : Fin 2 → Ω → ℕ → ℕ → ℝ := fun j s n k =>
    if j = 0 then ∑ l ∈ Finset.range (L 1 n), f (T ((k : ℤ), (l : ℤ)) s)
    else ∑ l ∈ Finset.range (L 0 n), f (T ((l : ℤ), (k : ℤ)) s)
  -- Produce actual prefix limits for the countable mesh aspects using the original f.
  have hmesh (j : Fin 2) (m q : ℕ) : ∀ᵐ s ∂μ, 0 < m →
      Tendsto (fun n : ℕ =>
        (∑ k ∈ Finset.range ⌊(n : ℝ) * b j * (q : ℝ) / (m : ℝ)⌋₊,
          row j s n k) / (n : ℝ)^2) atTop (𝓝 0) := by
    by_cases hm : 0 < m
    · by_cases hq : q = 0
      · subst q
        filter_upwards [] with s
        intro _
        simpa only [Nat.cast_zero, mul_zero, zero_div, Nat.floor_zero,
          Finset.range_zero, Finset.sum_empty] using
          (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
      · let β : Fin 2 → ℝ := fun i => if i = j then b i * (q : ℝ) / (m : ℝ) else b i
        have hβ : ∀ i, 0 < β i := by
          intro i
          dsimp only [β]
          split_ifs
          · exact div_pos (mul_pos (hb i) (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hq)))
              (Nat.cast_pos.mpr hm)
          · exact hb i
        have hPET := ae_tendsto_prefix_rectangle_condExp μ T hzero hadd hT f hf β hβ
        filter_upwards [hPET, hzeroCE] with s hs hsCE
        intro _
        have hlim : Tendsto (fun n : ℕ =>
            (∑ z ∈ (Finset.Ico (0 : ℤ) ((⌊(n : ℝ) * β 0⌋₊ : ℕ) : ℤ)).product
              (Finset.Ico (0 : ℤ) ((⌊(n : ℝ) * β 1⌋₊ : ℕ) : ℤ)), f (T z s)) /
                (n : ℝ)^2) atTop (𝓝 0) := by
          change Tendsto _ atTop (𝓝 (β 0 * β 1 * (μ[f | I]) s)) at hs
          simpa only [hsCE, mul_zero] using hs
        have hfloor (i : Fin 2) (n : ℕ) :
            ⌊(n : ℝ) * (b i * (q : ℝ) / (m : ℝ))⌋₊ =
              ⌊(n : ℝ) * b i * (q : ℝ) / (m : ℝ)⌋₊ := by
          congr 1
          ring
        convert hlim using 1
        funext n
        congr 1
        fin_cases j
        · change (∑ k ∈ Finset.range ⌊(n : ℝ) * b 0 * (q : ℝ) / (m : ℝ)⌋₊,
              ∑ l ∈ Finset.range ⌊(n : ℝ) * b 1⌋₊, f (T ((k : ℤ), (l : ℤ)) s)) =
            ∑ z ∈ (Finset.Ico (0 : ℤ) ((⌊(n : ℝ) * (b 0 * (q : ℝ) / (m : ℝ))⌋₊ : ℕ) : ℤ)).product
              (Finset.Ico (0 : ℤ) ((⌊(n : ℝ) * b 1⌋₊ : ℕ) : ℤ)), f (T z s)
          rw [sum_integer_rectangle, hfloor 0 n]
        · change (∑ k ∈ Finset.range ⌊(n : ℝ) * b 1 * (q : ℝ) / (m : ℝ)⌋₊,
              ∑ l ∈ Finset.range ⌊(n : ℝ) * b 0⌋₊, f (T ((l : ℤ), (k : ℤ)) s)) =
            ∑ z ∈ (Finset.Ico (0 : ℤ) ((⌊(n : ℝ) * b 0⌋₊ : ℕ) : ℤ)).product
              (Finset.Ico (0 : ℤ) ((⌊(n : ℝ) * (b 1 * (q : ℝ) / (m : ℝ))⌋₊ : ℕ) : ℤ)), f (T z s)
          rw [sum_integer_rectangle_rows, hfloor 1 n]
    · exact Eventually.of_forall (fun _ hm' => False.elim (hm hm'))
  have hmeshAll : ∀ᵐ s ∂μ, ∀ (j : Fin 2) (m q : ℕ), 0 < m →
      Tendsto (fun n : ℕ =>
        (∑ k ∈ Finset.range ⌊(n : ℝ) * b j * (q : ℝ) / (m : ℝ)⌋₊,
          row j s n k) / (n : ℝ)^2) atTop (𝓝 0) :=
    ae_all_iff.mpr (fun j => ae_all_iff.mpr (fun m => ae_all_iff.mpr (fun q => hmesh j m q)))
  -- The original absolute observable supplies a genuine all-n rectangle bound.
  have hmax := (prefix_rectangle_maximal_bound_and_ae_bounded μ T hzero hadd hT
    (fun s => |f s|) hf.abs b hb).2
  filter_upwards [hmeshAll, hmax] with s hs hAbs
  obtain ⟨M, hM⟩ := hAbs
  have hAbsBound (n : ℕ) : (∑ z ∈ R n, |f (T z s)|) / (n : ℝ)^2 ≤ M := by
    exact (le_abs_self _).trans (hM ⟨n, rfl⟩)
  have hrowBound (j : Fin 2) : BddAbove (Set.range (fun n : ℕ =>
      (∑ k ∈ Finset.range (L j n), |row j s n k|) / (n : ℝ)^2)) := by
    refine ⟨M, ?_⟩
    rintro _ ⟨n, rfl⟩
    have htriangle : (∑ k ∈ Finset.range (L j n), |row j s n k|) ≤
        ∑ z ∈ R n, |f (T z s)| := by
      fin_cases j
      · change (∑ k ∈ Finset.range (L 0 n),
            |∑ l ∈ Finset.range (L 1 n), f (T ((k : ℤ), (l : ℤ)) s)|) ≤ _
        change _ ≤ ∑ z ∈ (Finset.Ico (0 : ℤ) (L 0 n : ℤ)).product
          (Finset.Ico (0 : ℤ) (L 1 n : ℤ)), |f (T z s)|
        rw [sum_integer_rectangle]
        exact Finset.sum_le_sum (fun k _ => Finset.abs_sum_le_sum_abs _ _)
      · change (∑ k ∈ Finset.range (L 1 n),
            |∑ l ∈ Finset.range (L 0 n), f (T ((l : ℤ), (k : ℤ)) s)|) ≤ _
        change _ ≤ ∑ z ∈ (Finset.Ico (0 : ℤ) (L 0 n : ℤ)).product
          (Finset.Ico (0 : ℤ) (L 1 n : ℤ)), |f (T z s)|
        rw [sum_integer_rectangle_rows]
        exact Finset.sum_le_sum (fun k _ => Finset.abs_sum_le_sum_abs _ _)
    exact (div_le_div_of_nonneg_right htriangle (sq_nonneg (n : ℝ))).trans (hAbsBound n)
  -- Genuinely consume the deterministic grid theorem once per coordinate.
  have hweighted (j : Fin 2) :=
    tendsto_affine_weighted_prefix_sums_of_grid_limits (row j s) (b j) (hb j) 2
      (fun m hm q _ => hs j m q hm) (hrowBound j)
  intro j c d
  have heq (n : ℕ) :
      (∑ z ∈ R n, (c + d * ((((coord j z : ℤ) : ℝ) + 1) / (n : ℝ))) *
        f (T z s)) / (n : ℝ)^2 =
      (∑ k ∈ Finset.range (L j n),
        (c + d * (((k : ℝ) + 1) / (n : ℝ))) * row j s n k) / (n : ℝ)^2 := by
    congr 1
    fin_cases j
    · change (∑ z ∈ (Finset.Ico (0 : ℤ) (L 0 n : ℤ)).product
          (Finset.Ico (0 : ℤ) (L 1 n : ℤ)),
            (c + d * (((z.1 : ℝ) + 1) / (n : ℝ))) * f (T z s)) =
          ∑ k ∈ Finset.range (L 0 n), (c + d * (((k : ℝ) + 1) / (n : ℝ))) *
            (∑ l ∈ Finset.range (L 1 n), f (T ((k : ℤ), (l : ℤ)) s))
      rw [sum_integer_rectangle]
      simp only [Int.cast_natCast, Finset.mul_sum]
    · change (∑ z ∈ (Finset.Ico (0 : ℤ) (L 0 n : ℤ)).product
          (Finset.Ico (0 : ℤ) (L 1 n : ℤ)),
            (c + d * (((z.2 : ℝ) + 1) / (n : ℝ))) * f (T z s)) =
          ∑ k ∈ Finset.range (L 1 n), (c + d * (((k : ℝ) + 1) / (n : ℝ))) *
            (∑ l ∈ Finset.range (L 0 n), f (T ((l : ℤ), (k : ℤ)) s))
      rw [sum_integer_rectangle_rows]
      simp only [Int.cast_natCast, Finset.mul_sum]
  exact (hweighted j c d).congr' (Eventually.of_forall (fun n => (heq n).symm))

end ProbabilityBasics
