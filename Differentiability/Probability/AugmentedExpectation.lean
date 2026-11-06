/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Differentiability.Model.OrientedPercolation
public import LPP_Foundations.Frozen.Model.EnvironmentLaw
import Differentiability.Model.AugmentedPassage
import Differentiability.Model.AugmentedProcessLaws
import Differentiability.Model.OrientedPercolationLaws
import Differentiability.Probability.AugmentedBlockLaws
import Differentiability.Probability.AugmentedMeasurability
import LPP_Foundations.Probability.EnvironmentLaw
import Differentiability.Probability.HalfLineEdge
import Differentiability.Probability.LevelSigma
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.Tactic.Linarith

/-!
# The augmented process in expectation

Two statements about the process that starts from the antidiagonal half-line. The process
tests for a triangle at the lowest point at the start of each block of `T` levels, and it has
at most `n` augmentations in `n` blocks.

* `integral_augmented_count`: the expected number of augmentations is `n ρ_T`, where `ρ_T` is the
  probability of a triangle at the origin.
* `integral_augmented_edge_gain`: the edge after `n` blocks exceeds the edge of the plain
  growth from the half-line, in expectation, by at least `n T ρ_T`.

Both are proved by summing over the fixed block index `j < n`. For `j < n` the cap is not
reached, so, almost surely, an augmentation happens at block `j` exactly when there is a triangle
at the lowest point. The count is the sum of these indicators. The edge gain of block `j` is at
least the indicator times the exact gain of the half-line seen from the site just above the lowest
point (the pathwise freezing lemma of `AugmentedProcessLaws`); its mean is `T ρ_T` by the
probabilistic freezing lemma of `AugmentedBlockLaws`.
-/

@[expose] public section

namespace LPPDifferentiability

open MeasureTheory Set

/-! ## Private helpers -/

/-- The lowest point of the occupied set after `j` blocks: the site on level `j T` with the
largest first coordinate. -/
private noncomputable abbrev lowPt (ω : Environment) (T : ℕ) (c₀ : ℝ) (S : Set Lattice) (k j : ℕ) : Lattice :=
  (maxFirst (augmentedProcess ω T c₀ S k j).1,
    (j : ℤ) * T - maxFirst (augmentedProcess ω T c₀ S k j).1)

/-- If the guard of the augmentation holds at block `j`, the next set contains the targets and
the counter goes up by one. -/
private theorem step_pos (ω : Environment) (T : ℕ) (c₀ : ℝ) (S : Set Lattice) (k j : ℕ)
    (h : (augmentedProcess ω T c₀ S k j).2 < k ∧
      lowPt ω T c₀ S k j ∈ (augmentedProcess ω T c₀ S k j).1 ∧
      IsTriangle ω T c₀ (lowPt ω T c₀ S k j)) :
    (augmentedProcess ω T c₀ S k (j + 1)).1 =
        openReachSet (topSites ω) (augmentedProcess ω T c₀ S k j).1 T ∪
          triangleTargets T (lowPt ω T c₀ S k j) ∧
      (augmentedProcess ω T c₀ S k (j + 1)).2 = (augmentedProcess ω T c₀ S k j).2 + 1 := by
  simp only [augmentedProcess]
  split_ifs with h'
  · exact ⟨rfl, rfl⟩
  · exact absurd h h'

/-- If the guard of the augmentation fails at block `j`, the next set is the plain open growth
and the counter does not change. -/
private theorem step_neg (ω : Environment) (T : ℕ) (c₀ : ℝ) (S : Set Lattice) (k j : ℕ)
    (h : ¬ ((augmentedProcess ω T c₀ S k j).2 < k ∧
      lowPt ω T c₀ S k j ∈ (augmentedProcess ω T c₀ S k j).1 ∧
      IsTriangle ω T c₀ (lowPt ω T c₀ S k j))) :
    (augmentedProcess ω T c₀ S k (j + 1)).1 =
        openReachSet (topSites ω) (augmentedProcess ω T c₀ S k j).1 T ∧
      (augmentedProcess ω T c₀ S k (j + 1)).2 = (augmentedProcess ω T c₀ S k j).2 := by
  simp only [augmentedProcess]
  split_ifs with h'
  · exact absurd h' h
  · exact ⟨rfl, rfl⟩

/-- The counter after zero blocks is zero. -/
private theorem count_zero (ω : Environment) (T : ℕ) (c₀ : ℝ) (S : Set Lattice) (k : ℕ) :
    (augmentedProcess ω T c₀ S k 0).2 = 0 := by
  rw [augmentedProcess]

/-- The occupied set after zero blocks is the start set. -/
private theorem set_zero (ω : Environment) (T : ℕ) (c₀ : ℝ) (S : Set Lattice) (k : ℕ) :
    (augmentedProcess ω T c₀ S k 0).1 = S := by
  rw [augmentedProcess]

/-- Below the cap, if the lowest point is in the set, the counter rises at block `j` by exactly
the indicator of a triangle at the lowest point. -/
private theorem count_step (ω : Environment) (T : ℕ) (c₀ : ℝ) (S : Set Lattice) (k j : ℕ)
    (hj : j < k) (hmem : lowPt ω T c₀ S k j ∈ (augmentedProcess ω T c₀ S k j).1) :
    ((augmentedProcess ω T c₀ S k (j + 1)).2 : ℝ) - ((augmentedProcess ω T c₀ S k j).2 : ℝ) =
      {ω' : Environment | IsTriangle ω' T c₀ (lowPt ω' T c₀ S k j)}.indicator
        (fun _ => (1 : ℝ)) ω := by
  have hK : (augmentedProcess ω T c₀ S k j).2 < k :=
    lt_of_le_of_lt (augmentedProcess_count_le ω T c₀ S k j).1 hj
  by_cases hE : IsTriangle ω T c₀ (lowPt ω T c₀ S k j)
  · obtain ⟨-, h2⟩ := step_pos ω T c₀ S k j ⟨hK, hmem, hE⟩
    rw [Set.indicator_of_mem (show ω ∈ {ω' : Environment |
      IsTriangle ω' T c₀ (lowPt ω' T c₀ S k j)} from hE), h2]
    push_cast
    ring
  · obtain ⟨-, h2⟩ := step_neg ω T c₀ S k j (fun h => hE h.2.2)
    rw [Set.indicator_of_notMem (show ω ∉ {ω' : Environment |
      IsTriangle ω' T c₀ (lowPt ω' T c₀ S k j)} from hE), h2]
    ring

/-- The pathwise edge gain of one block. For `j < k`, if the lowest point is in the set and the
open growth from the set after `T + m` further levels is non-empty, then the indicator of a
triangle at the lowest point times the gain of the half-line seen from the site above the lowest
point is at most the increase of the edge, when the set at block `j` (reaching `M = T + m`
levels) is replaced by the set at block `j + 1` (reaching `m` levels). -/
private theorem edge_step (ω : Environment) (T : ℕ) (hT : 1 ≤ T) (c₀ : ℝ) (k j m M : ℕ)
    (hM : M = T + m) (hj : j < k)
    (hmem : lowPt ω T c₀ antidiagHalfLine k j ∈
      (augmentedProcess ω T c₀ antidiagHalfLine k j).1)
    (hne : (openReachSet (topSites ω)
      (augmentedProcess ω T c₀ antidiagHalfLine k j).1 (T + m)).Nonempty) :
    {ω' : Environment | IsTriangle ω' T c₀ (lowPt ω' T c₀ antidiagHalfLine k j)}.indicator
        (fun _ => (1 : ℝ)) ω *
      ((openEdge (topSites (fun z => ω (((lowPt ω T c₀ antidiagHalfLine k j).1,
          (lowPt ω T c₀ antidiagHalfLine k j).2 + (T : ℤ)) + z)))
          (antidiagHalfLine ∪ antidiagRightBlock T) m : ℝ) -
        (halfLineEdge (fun z => ω (((lowPt ω T c₀ antidiagHalfLine k j).1,
          (lowPt ω T c₀ antidiagHalfLine k j).2 + (T : ℤ)) + z)) m : ℝ)) ≤
      (openEdge (topSites ω) (augmentedProcess ω T c₀ antidiagHalfLine k (j + 1)).1 m : ℝ) -
        (openEdge (topSites ω) (augmentedProcess ω T c₀ antidiagHalfLine k j).1 M : ℝ) := by
  subst hM
  have hK : (augmentedProcess ω T c₀ antidiagHalfLine k j).2 < k :=
    lt_of_le_of_lt (augmentedProcess_count_le ω T c₀ antidiagHalfLine k j).1 hj
  have hopen : openEdge (topSites ω) (openReachSet (topSites ω)
      (augmentedProcess ω T c₀ antidiagHalfLine k j).1 T) m =
      openEdge (topSites ω) (augmentedProcess ω T c₀ antidiagHalfLine k j).1 (T + m) := by
    unfold openEdge
    rw [openReachSet_add]
  by_cases hE : IsTriangle ω T c₀ (lowPt ω T c₀ antidiagHalfLine k j)
  · obtain ⟨h1, -⟩ := step_pos ω T c₀ antidiagHalfLine k j ⟨hK, hmem, hE⟩
    rw [Set.indicator_of_mem (show ω ∈ {ω' : Environment |
      IsTriangle ω' T c₀ (lowPt ω' T c₀ antidiagHalfLine k j)} from hE), one_mul, h1]
    have hA' : ∀ u ∈ antidiagHalfLine, u.1 ≤ 0 := fun u hu =>
      (show u.1 + u.2 = 0 ∧ u.1 ≤ 0 from hu).2
    have hb : BddAbove (Prod.fst '' (augmentedProcess ω T c₀ antidiagHalfLine k j).1) := by
      refine ⟨0 + (j : ℤ) * T, ?_⟩
      rintro _ ⟨v, hv, rfl⟩
      exact augmentedProcess_fst_le ω T c₀ antidiagHalfLine 0 hA' k j v hv
    have hX : ∀ x ∈ (augmentedProcess ω T c₀ antidiagHalfLine k j).1,
        x.1 + x.2 = (lowPt ω T c₀ antidiagHalfLine k j).1 +
          (lowPt ω T c₀ antidiagHalfLine k j).2 ∧
        x.1 ≤ (lowPt ω T c₀ antidiagHalfLine k j).1 := by
      intro x hx
      have hl : x.1 + x.2 = (j : ℤ) * T :=
        augmentedProcess_subset_levelSet ω T c₀ antidiagHalfLine
          antidiagHalfLine_subset_levelSet k j hx
      refine ⟨?_, le_maxFirst _ hb hx⟩
      rw [hl]
      show _ = maxFirst (augmentedProcess ω T c₀ antidiagHalfLine k j).1 +
        ((j : ℤ) * T - maxFirst (augmentedProcess ω T c₀ antidiagHalfLine k j).1)
      ring
    have hg := openEdge_triangle_gain_ge ω T hT c₀ _ hE _ hX m hne
    rw [← hopen]
    exact_mod_cast hg
  · obtain ⟨h1, -⟩ := step_neg ω T c₀ antidiagHalfLine k j (fun h => hE h.2.2)
    rw [Set.indicator_of_notMem (show ω ∉ {ω' : Environment |
      IsTriangle ω' T c₀ (lowPt ω' T c₀ antidiagHalfLine k j)} from hE), zero_mul, h1, hopen]
    simp

/-- The edge difference of the statement is integrable: it is measurable, non-negative and at
most `n T` minus the edge of the plain growth, almost surely. -/
private theorem integrable_edge_difference (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hp₀ : 0 < ν {1}) (T : ℕ) (hT : 1 ≤ T) (c₀ : ℝ) (n : ℕ) :
    Integrable (fun ω => ((maxFirst (augmentedProcess ω T c₀ antidiagHalfLine n n).1 : ℝ) -
        halfLineEdge ω (n * T))) (environmentLaw ν) := by
  have hm : Measurable (fun ω : Environment =>
      maxFirst (augmentedProcess ω T c₀ antidiagHalfLine n n).1) :=
    (measurable_maxFirst_augmentedProcess T hT c₀ antidiagHalfLine
      antidiagHalfLine_subset_levelSet n n).mono
      (levelsAtMost_le _) le_rfl
  have hmR : Measurable (fun ω : Environment =>
      ((maxFirst (augmentedProcess ω T c₀ antidiagHalfLine n n).1 : ℤ) : ℝ)) :=
    (measurable_of_countable (fun z : ℤ => (z : ℝ))).comp hm
  have hint := integrable_halfLineEdge ν hp₀ (n * T)
  refine Integrable.mono' ((integrable_const ((n : ℝ) * T)).sub hint)
    (hmR.aestronglyMeasurable.sub hint.aestronglyMeasurable) ?_
  filter_upwards [ae_openEdge_le_openEdge_augmentedProcess ν hp₀ T c₀ antidiagHalfLine
    subset_rfl antidiagHalfLine_infinite n] with ω hω
  have h1 : halfLineEdge ω (n * T) ≤
      maxFirst (augmentedProcess ω T c₀ antidiagHalfLine n n).1 := by
    have h := hω n 0
    unfold openEdge at h
    rw [openReachSet_zero] at h
    exact h
  have h2 : maxFirst (augmentedProcess ω T c₀ antidiagHalfLine n n).1 ≤ (n : ℤ) * T := by
    have h := openEdge_augmentedProcess_le ω T c₀ antidiagHalfLine subset_rfl n n 0
    unfold openEdge at h
    rw [openReachSet_zero] at h
    simpa using h
  have h1' : (halfLineEdge ω (n * T) : ℝ) ≤
      (maxFirst (augmentedProcess ω T c₀ antidiagHalfLine n n).1 : ℝ) := by exact_mod_cast h1
  have h2' : (maxFirst (augmentedProcess ω T c₀ antidiagHalfLine n n).1 : ℝ) ≤
      (n : ℝ) * T := by exact_mod_cast h2
  rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.2 h1')]
  simp only [Pi.sub_apply]
  linarith

/-! ## The two statements -/

/-- The expected number of augmentations of the augmented process with cap `n` after `n` blocks,
started from the half-line, is `n ρ_T`, where `ρ_T` is the probability of a triangle at the
origin. The count is integrable. The count is the sum over the blocks `j < n` of the indicator of
a triangle at the lowest point, because, almost surely, the lowest point lies in the occupied set
and the cap has not been reached before block `n`. Each indicator has mean `ρ_T` by the block law
of the lowest point. -/
theorem integral_augmented_count (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hp₀ : 0 < ν {1}) (T : ℕ) (hT : 1 ≤ T) (c₀ : ℝ) (n : ℕ) :
    Integrable (fun ω => ((augmentedProcess ω T c₀ antidiagHalfLine n n).2 : ℝ))
        (environmentLaw ν) ∧
      ∫ ω, ((augmentedProcess ω T c₀ antidiagHalfLine n n).2 : ℝ) ∂environmentLaw ν =
        n * (environmentLaw ν).real {ω | IsTriangle ω T c₀ 0} := by
  have hEmeas : ∀ j : ℕ, MeasurableSet {ω : Environment |
      IsTriangle ω T c₀ (lowPt ω T c₀ antidiagHalfLine n j)} := fun j =>
    levelsAtMost_le _ _ (measurableSet_isTriangle_lowestPoint T hT c₀ antidiagHalfLine
      antidiagHalfLine_subset_levelSet n j)
  have hint : ∀ j : ℕ, Integrable ({ω : Environment |
      IsTriangle ω T c₀ (lowPt ω T c₀ antidiagHalfLine n j)}.indicator (fun _ => (1 : ℝ)))
        (environmentLaw ν) := fun j => (integrable_const (1 : ℝ)).indicator (hEmeas j)
  have hsum : ∀ᵐ ω ∂environmentLaw ν,
      ((augmentedProcess ω T c₀ antidiagHalfLine n n).2 : ℝ) =
        ∑ j ∈ Finset.range n, {ω' : Environment |
          IsTriangle ω' T c₀ (lowPt ω' T c₀ antidiagHalfLine n j)}.indicator
            (fun _ => (1 : ℝ)) ω := by
    filter_upwards [ae_lowestPoint_mem_augmentedProcess ν hp₀ T c₀ antidiagHalfLine
      subset_rfl antidiagHalfLine_infinite n] with ω hω
    have hs := Finset.sum_range_sub
      (fun j => ((augmentedProcess ω T c₀ antidiagHalfLine n j).2 : ℝ)) n
    beta_reduce at hs
    rw [count_zero] at hs
    have hs2 := Finset.sum_congr (rfl : Finset.range n = Finset.range n) fun j hj =>
      count_step ω T c₀ antidiagHalfLine n j (Finset.mem_range.1 hj) (hω j)
    rw [← hs2, hs]
    simp
  have hρ : ∀ j : ℕ, (environmentLaw ν).real {ω : Environment |
      IsTriangle ω T c₀ (lowPt ω T c₀ antidiagHalfLine n j)} =
        (environmentLaw ν).real {ω | IsTriangle ω T c₀ 0} := fun j =>
    measure_isTriangle_lowestPoint ν T hT c₀ antidiagHalfLine antidiagHalfLine_subset_levelSet n j
  refine ⟨(integrable_finsetSum _ fun j _ => hint j).congr
    (hsum.mono fun ω h => h.symm), ?_⟩
  rw [integral_congr_ae hsum, integral_finsetSum _ fun j _ => hint j]
  have hj : ∀ j ∈ Finset.range n, ∫ ω, {ω' : Environment |
      IsTriangle ω' T c₀ (lowPt ω' T c₀ antidiagHalfLine n j)}.indicator
        (fun _ => (1 : ℝ)) ω ∂environmentLaw ν =
      (environmentLaw ν).real {ω | IsTriangle ω T c₀ 0} := fun j _ => by
    rw [integral_indicator_const _ (hEmeas j), hρ j]
    simp
  rw [Finset.sum_congr rfl hj]
  simp

/-- The expected edge after `n` blocks of the augmented process with cap `n`, started from the
half-line, exceeds the expected edge of the plain open growth by at least `n T ρ_T`; the
difference is integrable. Block by block: for `j < n`, almost surely, the edge computed from the
set at block `j + 1` minus the edge computed from the set at block `j` is at least the indicator
of a triangle at the lowest point times the half-line gain seen from the site above it
(pathwise freezing lemma). The mean of that product is `T ρ_T` (probabilistic freezing lemma).
The block differences telescope to the quantity in the statement. -/
theorem integral_augmented_edge_gain (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hp₀ : 0 < ν {1}) (T : ℕ) (hT : 1 ≤ T) (c₀ : ℝ) (n : ℕ) :
    Integrable (fun ω => ((maxFirst (augmentedProcess ω T c₀ antidiagHalfLine n n).1 : ℝ) -
        halfLineEdge ω (n * T))) (environmentLaw ν) ∧
      (n : ℝ) * T * (environmentLaw ν).real {ω | IsTriangle ω T c₀ 0} ≤
        ∫ ω, ((maxFirst (augmentedProcess ω T c₀ antidiagHalfLine n n).1 : ℝ) -
          halfLineEdge ω (n * T)) ∂environmentLaw ν := by
  have hgint := integrable_edge_difference ν hp₀ T hT c₀ n
  refine ⟨hgint, ?_⟩
  let hfun : ℕ → Environment → ℝ := fun j ω =>
    {ω' : Environment | IsTriangle ω' T c₀ (lowPt ω' T c₀ antidiagHalfLine n j)}.indicator
        (fun _ => (1 : ℝ)) ω *
      ((openEdge (topSites (fun z => ω (((lowPt ω T c₀ antidiagHalfLine n j).1,
          (lowPt ω T c₀ antidiagHalfLine n j).2 + (T : ℤ)) + z)))
          (antidiagHalfLine ∪ antidiagRightBlock T) ((n - (j + 1)) * T) : ℝ) -
        (halfLineEdge (fun z => ω (((lowPt ω T c₀ antidiagHalfLine n j).1,
          (lowPt ω T c₀ antidiagHalfLine n j).2 + (T : ℤ)) + z)) ((n - (j + 1)) * T) : ℝ))
  have hF : ∀ j : ℕ, Integrable (hfun j) (environmentLaw ν) ∧
      ∫ ω, hfun j ω ∂environmentLaw ν = (T : ℝ) * (environmentLaw ν).real
        {ω : Environment | IsTriangle ω T c₀ (lowPt ω T c₀ antidiagHalfLine n j)} := fun j => by
    have h := integral_isTriangle_lowestPoint_mul_shifted_gain ν hp₀ T hT c₀ antidiagHalfLine
      antidiagHalfLine_subset_levelSet n j ((n - (j + 1)) * T)
    exact h
  have hρ : ∀ j : ℕ, (environmentLaw ν).real {ω : Environment |
      IsTriangle ω T c₀ (lowPt ω T c₀ antidiagHalfLine n j)} =
        (environmentLaw ν).real {ω | IsTriangle ω T c₀ 0} := fun j =>
    measure_isTriangle_lowestPoint ν T hT c₀ antidiagHalfLine antidiagHalfLine_subset_levelSet n j
  have hineq : ∀ᵐ ω ∂environmentLaw ν, ∑ j ∈ Finset.range n, hfun j ω ≤
      (maxFirst (augmentedProcess ω T c₀ antidiagHalfLine n n).1 : ℝ) -
        halfLineEdge ω (n * T) := by
    filter_upwards [ae_openReachSet_augmentedProcess_nonempty ν hp₀ T c₀ antidiagHalfLine
      subset_rfl antidiagHalfLine_infinite n,
      ae_lowestPoint_mem_augmentedProcess ν hp₀ T c₀ antidiagHalfLine subset_rfl
        antidiagHalfLine_infinite n] with ω hn hm
    have hs := Finset.sum_range_sub
      (fun j => (openEdge (topSites ω) (augmentedProcess ω T c₀ antidiagHalfLine n j).1
        ((n - j) * T) : ℝ)) n
    have hD0 : openEdge (topSites ω) (augmentedProcess ω T c₀ antidiagHalfLine n 0).1
        ((n - 0) * T) = halfLineEdge ω (n * T) := by
      rw [set_zero]
      rfl
    have hDn : openEdge (topSites ω) (augmentedProcess ω T c₀ antidiagHalfLine n n).1
        ((n - n) * T) = maxFirst (augmentedProcess ω T c₀ antidiagHalfLine n n).1 := by
      rw [Nat.sub_self, Nat.zero_mul]
      unfold openEdge
      rw [openReachSet_zero]
    simp only [hD0, hDn] at hs
    rw [← hs]
    refine Finset.sum_le_sum fun j hj => ?_
    have hjn : j < n := Finset.mem_range.1 hj
    have hM : (n - j) * T = T + (n - (j + 1)) * T := by
      have : n - j = (n - (j + 1)) + 1 := by omega
      rw [this]
      ring
    exact edge_step ω T hT c₀ n j ((n - (j + 1)) * T) ((n - j) * T) hM hjn (hm j)
      (hn j (T + (n - (j + 1)) * T))
  have hle := integral_mono_ae (integrable_finsetSum _ fun j _ => (hF j).1) hgint hineq
  rw [integral_finsetSum _ fun j _ => (hF j).1] at hle
  have hj : ∀ j ∈ Finset.range n, ∫ ω, hfun j ω ∂environmentLaw ν =
      (T : ℝ) * (environmentLaw ν).real {ω | IsTriangle ω T c₀ 0} := fun j _ => by
    rw [(hF j).2, hρ j]
  rw [Finset.sum_congr rfl hj] at hle
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hle
  linarith

end LPPDifferentiability
