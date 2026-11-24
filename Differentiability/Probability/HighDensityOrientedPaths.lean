/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Differentiability.Probability.OrientedPathEvent
public import Differentiability.Probability.FiniteContourFamilyBadEvent
import Differentiability.FinalDraft.OrientedPaths.ContourCover
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Tactic

/-!
# Peierls estimate for high-density oriented site paths

A Peierls-type estimate bounds the probability of a high-density set of oriented
site paths by a sum over square contours of finite endpoint clusters.
-/

public section

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace LPPDifferentiability

private theorem contour_power_identity (k n : ℕ) (ζ : ℝ) (hζ : 0 < ζ) :
    (((n + 4) * 3 ^ (n + 3) : ℕ) : ℝ) *
        ζ ^ (((n + 4 : ℕ) : ℝ) / (4 * (((2 * k + 1) ^ 2 : ℕ) : ℝ))) =
      ((n + 4 : ℕ) : ℝ) *
        (3 * ζ ^ (1 / (4 * (((2 * k + 1) ^ 2 : ℕ) : ℝ)))) ^ (n + 3) *
          ζ ^ (1 / (4 * (((2 * k + 1) ^ 2 : ℕ) : ℝ))) := by
  let d : ℝ := 4 * (((2 * k + 1) ^ 2 : ℕ) : ℝ)
  have he : ((n + 4 : ℕ) : ℝ) / d =
      (1 / d) * ((n + 3 : ℕ) : ℝ) + 1 / d := by
    push_cast
    ring
  have hc : (((n + 4) * 3 ^ (n + 3) : ℕ) : ℝ) =
      ((n + 4 : ℕ) : ℝ) * (3 : ℝ) ^ (n + 3) := by
    push_cast
    rfl
  change _ * ζ ^ (((n + 4 : ℕ) : ℝ) / d) =
    ((n + 4 : ℕ) : ℝ) * (3 * ζ ^ (1 / d)) ^ (n + 3) * ζ ^ (1 / d)
  rw [hc, he, Real.rpow_add hζ, Real.rpow_mul_natCast hζ.le, mul_pow]
  ring

private theorem exists_square_contour_series_bound (k : ℕ) :
    ∃ ζ : ℝ, 0 < ζ ∧ ζ < 1 ∧
      Summable (fun n : ℕ =>
        ((n + 4 : ℕ) : ℝ) *
          (3 * ζ ^ (1 / (4 * (((2 * k + 1) ^ 2 : ℕ) : ℝ))) : ℝ) ^ (n + 3) *
            ζ ^ (1 / (4 * (((2 * k + 1) ^ 2 : ℕ) : ℝ)))) ∧
      (∑' n : ℕ,
        ((n + 4 : ℕ) : ℝ) *
          (3 * ζ ^ (1 / (4 * (((2 * k + 1) ^ 2 : ℕ) : ℝ))) : ℝ) ^ (n + 3) *
            ζ ^ (1 / (4 * (((2 * k + 1) ^ 2 : ℕ) : ℝ)))) < 1 := by
  let D : ℕ := 4 * (2 * k + 1) ^ 2
  let ζ : ℝ := (1 / 12 : ℝ) ^ D
  have hD : D ≠ 0 := by dsimp [D]; positivity
  have hDcast : (D : ℝ) = 4 * (((2 * k + 1) ^ 2 : ℕ) : ℝ) := by
    simp only [D, Nat.cast_mul, Nat.cast_ofNat]
  have hroot : ζ ^ (1 / (4 * (((2 * k + 1) ^ 2 : ℕ) : ℝ))) = 1 / 12 := by
    rw [← hDcast, one_div]
    exact Real.pow_rpow_inv_natCast (by norm_num) hD
  have hζpos : 0 < ζ := by dsimp [ζ]; positivity
  have hζlt : ζ < 1 := pow_lt_one₀ (by norm_num) (by norm_num) hD
  refine ⟨ζ, hζpos, hζlt, ?_⟩
  rw [hroot, show (3 : ℝ) * (1 / 12) = 1 / 4 by norm_num]
  let t (n : ℕ) : ℝ := ((n + 4 : ℕ) : ℝ) * (1 / 4 : ℝ) ^ (n + 3) * (1 / 12)
  let b (n : ℕ) : ℝ := (1 / 192 : ℝ) * (1 / 2 : ℝ) ^ n
  have hlinear (n : ℕ) : n + 4 ≤ 4 * 2 ^ n := by
    induction n with
    | zero => norm_num
    | succ n ih =>
      rw [pow_succ, ← Nat.mul_assoc]
      omega
  have hbound (n : ℕ) : t n ≤ b n := by
    have hlin : ((n + 4 : ℕ) : ℝ) ≤ 4 * (2 : ℝ) ^ n := by
      exact_mod_cast hlinear n
    calc
      _ ≤ (4 * (2 : ℝ) ^ n) * (1 / 4 : ℝ) ^ (n + 3) * (1 / 12) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hlin (by positivity))
          (by norm_num)
      _ = b n := by
        rw [pow_add]
        dsimp [b]
        calc
          _ = (4 * (1 / 4 : ℝ) ^ 3 * (1 / 12)) *
              ((2 : ℝ) ^ n * (1 / 4 : ℝ) ^ n) := by ring
          _ = _ := by rw [← mul_pow]; norm_num
  have hbSum : HasSum b (1 / 96 : ℝ) := by
    have h := (hasSum_geometric_of_lt_one (by norm_num : 0 ≤ (1 / 2 : ℝ))
      (by norm_num : (1 / 2 : ℝ) < 1)).mul_left (1 / 192 : ℝ)
    convert h using 1
    norm_num [b]
  have htSum : Summable t :=
    Summable.of_nonneg_of_le (fun n => by dsimp [t]; positivity) hbound hbSum.summable
  exact ⟨htSum, (htSum.tsum_le_tsum hbound hbSum.summable).trans_lt
    (hbSum.tsum_eq.trans_lt (by norm_num))⟩

private theorem measure_all_bad_forward_sites_le
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (G : ℕ × ℕ → Set Ω) (k m : ℕ) (ζ : ℝ) (hζpos : 0 < ζ) (hζlt : ζ < 1)
    (hMarginal : ∀ v, P.real ((G v)ᶜ) ≤ ζ)
    (hIndep : ∀ T : Finset (ℕ × ℕ),
      (∀ u ∈ T, ∀ v ∈ T, u ≠ v →
        k < Nat.dist u.1 v.1 ∨ k < Nat.dist u.2 v.2) →
      iIndepSet (fun v : {u : ℕ × ℕ // u ∈ T} => G v.1) P)
    (S : Finset (ℕ × ℕ)) (hm : m ≤ 4 * S.card) :
    P.real {ω : Ω | ∀ v ∈ S, ω ∉ G v} ≤
      ζ ^ ((m : ℝ) / (4 * (((2 * k + 1) ^ 2 : ℕ) : ℝ))) := by
  -- Select separated sites before taking probabilities.
  obtain ⟨T, hTS, hSep, _, hCard⟩ := exists_separated_natural_lattice_subset S k
  have hSubset : {ω : Ω | ∀ v ∈ S, ω ∉ G v} ⊆ {ω : Ω | ∀ v ∈ T, ω ∉ G v} :=
    fun _ hω v hv => hω v (hTS hv)
  have hDenom : 0 < 4 * (((2 * k + 1) ^ 2 : ℕ) : ℝ) := by positivity
  have hExp : (m : ℝ) / (4 * (((2 * k + 1) ^ 2 : ℕ) : ℝ)) ≤ (T.card : ℝ) := by
    rw [div_le_iff₀ hDenom]
    calc
      _ ≤ 4 * (S.card : ℝ) := by exact_mod_cast hm
      _ ≤ 4 * ((((2 * k + 1) ^ 2 : ℕ) : ℝ) * (T.card : ℝ)) :=
        mul_le_mul_of_nonneg_left (by exact_mod_cast hCard) (by norm_num)
      _ = _ := by ring
  calc
    _ ≤ P.real {ω : Ω | ∀ v ∈ T, ω ∉ G v} := measureReal_mono hSubset
    _ ≤ ζ ^ T.card := measure_all_bad_sites_le_pow P G k ζ hMarginal hIndep T hSep
    _ = ζ ^ (T.card : ℝ) := (Real.rpow_natCast ζ T.card).symm
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_ge hζpos hζlt.le hExp

private theorem measureReal_iUnion_le_of_summable
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (E : ℕ → Set Ω) (t : ℕ → ℝ) (ht : ∀ n, 0 ≤ t n)
    (hs : Summable t) (hE : ∀ n, P.real (E n) ≤ t n) :
    P.real (⋃ n, E n) ≤ ∑' n, t n := by
  have hEach (n : ℕ) : P (E n) ≤ ENNReal.ofReal (t n) := by
    rw [← ENNReal.ofReal_toReal (measure_ne_top P (E n))]
    exact ENNReal.ofReal_le_ofReal (hE n)
  have hUnion : P (⋃ n, E n) ≤ ENNReal.ofReal (∑' n, t n) := by
    calc
      _ ≤ ∑' n, P (E n) := measure_iUnion_le E
      _ ≤ ∑' n, ENNReal.ofReal (t n) := ENNReal.tsum_le_tsum hEach
      _ = ENNReal.ofReal (∑' n, t n) := (ENNReal.ofReal_tsum_of_nonneg ht hs).symm
  have hReal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hUnion
  simpa only [Measure.real, ENNReal.toReal_ofReal (tsum_nonneg ht)] using hReal

/-- For each dependence range one cutoff works for every probability space and
all measurable site events satisfying the marginal and independence conditions.
The path event includes the initial site at zero. Final draft, Lemma `lem:oriented`. -/
theorem exists_high_density_oriented_path_cutoff (k : ℕ) :
    ∃ ζ : ℝ, 0 < ζ ∧ ζ < 1 ∧
      ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (G : ℕ × ℕ → Set Ω),
        (∀ v, MeasurableSet (G v)) →
        (∀ v, P.real ((G v)ᶜ) ≤ ζ) →
        (∀ T : Finset (ℕ × ℕ),
          (∀ u ∈ T, ∀ v ∈ T, u ≠ v →
            k < Nat.dist u.1 v.1 ∨ k < Nat.dist u.2 v.2) →
          iIndepSet (fun v : {u : ℕ × ℕ // u ∈ T} => G v.1) P) →
        MeasurableSet
          {ω : Ω | ∃ q : ℕ → ℕ × ℕ, q 0 = (0, 0) ∧
            (∀ i, q (i + 1) = q i + (1, 0) ∨ q (i + 1) = q i + (0, 1)) ∧
            ∀ i, ω ∈ G (q i)} ∧
        0 < P.real
          {ω : Ω | ∃ q : ℕ → ℕ × ℕ, q 0 = (0, 0) ∧
            (∀ i, q (i + 1) = q i + (1, 0) ∨ q (i + 1) = q i + (0, 1)) ∧
            ∀ i, ω ∈ G (q i)} := by
  classical
  obtain ⟨ζ, hζpos, hζlt, hsum, hsumlt⟩ := exists_square_contour_series_bound k
  refine ⟨ζ, hζpos, hζlt, ?_⟩
  intro Ω _ P _ G hG hMarginal hIndep
  -- Use the counted square contours and their deterministic forward labels.
  obtain ⟨W, hCount, hLabels, hCover⟩ := exists_square_contour_bad_site_cover
  let B (c : Cycle (Lattice × Lattice)) := {ω : Ω | ∀ x ∈ squareContourForwardSites c, ω ∉ G x}
  let E (n : ℕ) : Set Ω := ⋃ c ∈ W n, B c
  let t (n : ℕ) : ℝ := ((n + 4 : ℕ) : ℝ) *
    (3 * ζ ^ (1 / (4 * (((2 * k + 1) ^ 2 : ℕ) : ℝ)))) ^ (n + 3) *
      ζ ^ (1 / (4 * (((2 * k + 1) ^ 2 : ℕ) : ℝ)))
  have hBound (n : ℕ) : P.real (E n) ≤ t n := by
    let r : ℝ := ζ ^ (((n + 4 : ℕ) : ℝ) / (4 * (((2 * k + 1) ^ 2 : ℕ) : ℝ)))
    calc
      _ ≤ ∑ c ∈ W n, P.real (B c) := measureReal_biUnion_finset_le _ _
      _ ≤ ∑ _c ∈ W n, r :=
        Finset.sum_le_sum fun c hc => measure_all_bad_forward_sites_le P G k (n + 4) ζ hζpos hζlt
          hMarginal hIndep (squareContourForwardSites c) (hLabels n c hc)
      _ = ((W n).card : ℝ) * r := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (((n + 4) * 3 ^ (n + 3) : ℕ) : ℝ) * r :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hCount n) (Real.rpow_nonneg hζpos.le _)
      _ = t n := contour_power_identity k n ζ hζpos
  let A : Set Ω := {ω | ∃ q : ℕ → ℕ × ℕ, q 0 = (0, 0) ∧
    (∀ i, q (i + 1) = q i + (1, 0) ∨ q (i + 1) = q i + (0, 1)) ∧
    ∀ i, ω ∈ G (q i)}
  have hA : MeasurableSet A := measurableSet_exists_infinite_good_oriented_path G hG
  -- Failure is covered by the countable union over lengths, starting at four.
  have hSubset : Aᶜ ⊆ ⋃ n, E n := by
    intro ω hω
    obtain ⟨n, c, hc, hb⟩ := hCover {x | ω ∈ G x} hω
    exact Set.mem_iUnion.mpr ⟨n, Set.mem_iUnion.mpr ⟨c, Set.mem_iUnion.mpr ⟨hc, hb⟩⟩⟩
  have hUnion : P.real (⋃ n, E n) ≤ ∑' n, t n :=
    measureReal_iUnion_le_of_summable P E t (fun n => by dsimp [t]; positivity)
      hsum hBound
  have hComplement : P.real Aᶜ < 1 :=
    lt_of_le_of_lt ((measureReal_mono hSubset).trans hUnion) hsumlt
  refine ⟨hA, ?_⟩
  have hIdentity := probReal_compl_eq_one_sub (μ := P) hA
  change 0 < P.real A
  linarith only [hIdentity, hComplement]

end LPPDifferentiability
