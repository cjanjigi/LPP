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
import Differentiability.Model.PercolationTriangles
import Differentiability.Probability.AugmentedMeasurability
import Differentiability.Probability.HalfLineEdge
import Differentiability.Probability.LevelIndependence
import Differentiability.Probability.LevelSigma
import Differentiability.Probability.RightBlockGain
import Differentiability.Probability.TriangleProbability
import Mathlib.Probability.IdentDistrib
import Mathlib.Probability.Independence.Integration

/-!
# Almost-sure facts and block laws of the augmented process

The probabilistic half of the freezing step of the flat-edge argument.

The first three theorems say that, almost surely and for every block `j`, the occupied set of
the augmented process always reaches non-empty sets, its lowest point belongs to it, and its
edge is at least the edge of the plain open-path growth from the start set. They follow from
the pathwise facts of `AugmentedProcessLaws` and the almost-sure non-emptiness of the plain
growth from an infinite start set.

The last two theorems are the block laws. The triangle test at the lowest point of block `j`
has the same probability as the triangle test at the origin, and the product of that test with
the gain of the environment seen from the site just above the lowest point has expected value
`T` times the test probability. Both come from the independence of levels
(`indepFun_identDistrib_shift_of_levelsAtMost`), applied to a random site that is determined
by the lower levels.

The corresponding steps in Georgiou, Rassoul-Agha and Seppäläinen (manuscript in preparation)
use the strong Markov property at a random block; here every statement is for a fixed block
`j`.

## References

- Georgiou, Rassoul-Agha and Seppäläinen (manuscript in preparation), the oriented-percolation
  gain lemma and the endpoint differentiability argument.
-/

@[expose] public section

namespace LPPDifferentiability

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal

/-! ## Pathwise helpers -/

/-- If the plain growth from `A` is never empty, then neither is the growth from the occupied
set at any block, because the occupied set contains the plain growth from `A`. -/
private theorem nonempty_reach_of_plain (ω : Environment) (T : ℕ) (c₀ : ℝ) (A : Set Lattice)
    (k : ℕ) (h : ∀ n : ℕ, (openReachSet (topSites ω) A n).Nonempty) (j m : ℕ) :
    (openReachSet (topSites ω) (augmentedProcess ω T c₀ A k j).1 m).Nonempty := by
  have hsub : openReachSet (topSites ω) A (j * T + m) ⊆
      openReachSet (topSites ω) (augmentedProcess ω T c₀ A k j).1 m := by
    rw [← openReachSet_add]
    exact openReachSet_mono subset_rfl (openReachSet_subset_augmentedProcess ω T c₀ A k j) m
  exact (h (j * T + m)).mono hsub

/-- The occupied set at block `j` has first coordinates at most `j T` when the start set lies
in the half-line. -/
private theorem fst_le_of_halfLine (ω : Environment) (T : ℕ) (c₀ : ℝ) (A : Set Lattice)
    (hA : A ⊆ antidiagHalfLine) (k j : ℕ) :
    ∀ v ∈ (augmentedProcess ω T c₀ A k j).1, v.1 ≤ 0 + (j : ℤ) * T :=
  augmentedProcess_fst_le ω T c₀ A 0
    (fun u hu => (show u.1 + u.2 = 0 ∧ u.1 ≤ 0 from hA hu).2) k j

/-- The site on level `L` with the largest first coordinate belongs to a non-empty set that
lies on level `L` and is bounded in the first coordinate. -/
private theorem lowest_mem_of (X : Set Lattice) (L : ℤ) (hX : X ⊆ levelSet L) (hne : X.Nonempty)
    (hb : BddAbove (Prod.fst '' X)) : (maxFirst X, L - maxFirst X) ∈ X := by
  obtain ⟨v, hv, hvv⟩ := maxFirst_mem X hne hb
  have hl : v.1 + v.2 = L := hX hv
  have e : (maxFirst X, L - maxFirst X) = v :=
    Prod.ext hvv.symm (by show L - maxFirst X = v.2; omega)
  rw [e]
  exact hv

/-! ## Almost-sure facts -/

/-- Almost surely, from every block `j` the occupied set of the augmented process reaches a
non-empty set after any number `m` of open steps. The occupied set itself need not be
infinite for this. -/
theorem ae_openReachSet_augmentedProcess_nonempty (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hp₀ : 0 < ν {1}) (T : ℕ) (c₀ : ℝ) (A : Set Lattice) (hA : A ⊆ antidiagHalfLine)
    (hinf : A.Infinite) (k : ℕ) :
    ∀ᵐ ω ∂environmentLaw ν, ∀ j m : ℕ,
      (openReachSet (topSites ω) (augmentedProcess ω T c₀ A k j).1 m).Nonempty := by
  filter_upwards [ae_openReachSet_nonempty_of_infinite ν hp₀ A hA hinf] with ω hω j m
  exact nonempty_reach_of_plain ω T c₀ A k hω j m

/-- Almost surely, for every block `j`, the lowest point of the occupied set of the augmented
process (the site on level `j T` with the largest first coordinate) belongs to the set. -/
theorem ae_lowestPoint_mem_augmentedProcess (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hp₀ : 0 < ν {1}) (T : ℕ) (c₀ : ℝ) (A : Set Lattice) (hA : A ⊆ antidiagHalfLine)
    (hinf : A.Infinite) (k : ℕ) :
    ∀ᵐ ω ∂environmentLaw ν, ∀ j : ℕ,
      (maxFirst (augmentedProcess ω T c₀ A k j).1,
        (j : ℤ) * T - maxFirst (augmentedProcess ω T c₀ A k j).1) ∈
          (augmentedProcess ω T c₀ A k j).1 := by
  filter_upwards [ae_openReachSet_nonempty_of_infinite ν hp₀ A hA hinf] with ω hω j
  have hlev : A ⊆ levelSet 0 := fun u hu => (show u.1 + u.2 = 0 ∧ u.1 ≤ 0 from hA hu).1
  have hne : (augmentedProcess ω T c₀ A k j).1.Nonempty := by
    have h := nonempty_reach_of_plain ω T c₀ A k hω j 0
    rwa [openReachSet_zero] at h
  have hb : BddAbove (Prod.fst '' (augmentedProcess ω T c₀ A k j).1) := by
    refine ⟨0 + (j : ℤ) * T, ?_⟩
    rintro _ ⟨v, hv, rfl⟩
    exact fst_le_of_halfLine ω T c₀ A hA k j v hv
  exact lowest_mem_of _ ((j : ℤ) * T) (augmentedProcess_subset_levelSet ω T c₀ A hlev k j)
    hne hb

/-- Almost surely, for every block `j` and every number `m` of further steps, the edge of the
plain open-path growth from `A` after `j T + m` steps is at most the edge of the growth from
the occupied set at block `j` after `m` steps. -/
theorem ae_openEdge_le_openEdge_augmentedProcess (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hp₀ : 0 < ν {1}) (T : ℕ) (c₀ : ℝ) (A : Set Lattice) (hA : A ⊆ antidiagHalfLine)
    (hinf : A.Infinite) (k : ℕ) :
    ∀ᵐ ω ∂environmentLaw ν, ∀ j m : ℕ,
      openEdge (topSites ω) A (j * T + m) ≤
        openEdge (topSites ω) (augmentedProcess ω T c₀ A k j).1 m := by
  filter_upwards [ae_openReachSet_nonempty_of_infinite ν hp₀ A hA hinf] with ω hω j m
  have hsub : openReachSet (topSites ω) A (j * T + m) ⊆
      openReachSet (topSites ω) (augmentedProcess ω T c₀ A k j).1 m := by
    rw [← openReachSet_add]
    exact openReachSet_mono subset_rfl (openReachSet_subset_augmentedProcess ω T c₀ A k j) m
  have hb' : BddAbove (Prod.fst '' openReachSet (topSites ω)
      (augmentedProcess ω T c₀ A k j).1 m) := by
    refine ⟨0 + (j : ℤ) * T + (m : ℤ), ?_⟩
    rintro _ ⟨v, hv, rfl⟩
    exact bddAbove_fst_openReachSet (topSites ω) _ m _ (fst_le_of_halfLine ω T c₀ A hA k j) v hv
  have hb : BddAbove (Prod.fst '' openReachSet (topSites ω) A (j * T + m)) :=
    hb'.mono (Set.image_mono hsub)
  obtain ⟨v, hv, hvv⟩ := maxFirst_mem _ (hω (j * T + m)) hb
  unfold openEdge
  rw [← hvv]
  exact le_maxFirst _ hb' (hsub hv)

/-! ## Block laws -/

/-- The triangle test at a random site on level `m` that is determined by the weights at
levels at most `m` has the same probability as the triangle test at the origin. -/
private theorem real_isTriangle_random_site (ν : Measure ℝ) [IsProbabilityMeasure ν] (m : ℤ)
    (r : Environment → Lattice) (hr : Measurable[levelsAtMost m] r)
    (hlev : ∀ ω, (r ω).1 + (r ω).2 = m) (T : ℕ) (hT : 1 ≤ T) (c₀ : ℝ) :
    (environmentLaw ν).real {ω | IsTriangle ω T c₀ (r ω)} =
      (environmentLaw ν).real {ω | IsTriangle ω T c₀ 0} := by
  obtain ⟨F, hFdef⟩ : ∃ F : Environment → ℝ,
      F = fun ω => ({ω | IsTriangle ω T c₀ 0} : Set Environment).indicator (fun _ => (1 : ℝ)) ω :=
    ⟨_, rfl⟩
  have hF : Measurable F := by
    rw [hFdef]
    exact measurable_const.indicator (measurableSet_isTriangle T c₀ 0)
  have hloc : ∀ ω ω' : Environment, (∀ z : Lattice, 0 < z.1 + z.2 → ω z = ω' z) →
      F ω = F ω' := by
    intro ω ω' h
    have hiff : IsTriangle ω T c₀ 0 ↔ IsTriangle ω' T c₀ 0 :=
      isTriangle_local T hT c₀ 0 ω ω' (fun z h1 _ => h z (by simpa using h1))
    by_cases h1 : IsTriangle ω T c₀ 0
    · simp [hFdef, h1, hiff.1 h1]
    · have h2 : ¬ IsTriangle ω' T c₀ 0 := fun x => h1 (hiff.2 x)
      simp [hFdef, h1, h2]
  obtain ⟨-, hid⟩ := indepFun_identDistrib_shift_of_levelsAtMost ν m r hr hlev F hF hloc
    (fun _ => (0 : ℝ)) measurable_const
  have hm := hid.measure_mem_eq (measurableSet_singleton (1 : ℝ))
  have h1 : (fun ω : Environment => F (fun z => ω (r ω + z))) ⁻¹' {1} =
      {ω | IsTriangle ω T c₀ (r ω)} := by
    ext ω
    have h := isTriangle_translate ω T c₀ (r ω) 0
    rw [add_zero] at h
    by_cases hω : IsTriangle ω T c₀ (r ω)
    · have h' : IsTriangle (fun z => ω (r ω + z)) T c₀ 0 := h.2 hω
      simp [hFdef, hω, h']
    · have h' : ¬ IsTriangle (fun z => ω (r ω + z)) T c₀ 0 := fun x => hω (h.1 x)
      simp [hFdef, hω, h']
  have h2 : F ⁻¹' {1} = {ω | IsTriangle ω T c₀ 0} := by
    ext ω
    by_cases hω : IsTriangle ω T c₀ 0
    · simp [hFdef, hω]
    · simp [hFdef, hω]
  rw [measureReal_def, measureReal_def, ← h1, ← h2, hm]

/-- The triangle test at the lowest point of the occupied set at block `j` has the same
probability as the triangle test at the origin. The lowest point is a random site on level
`j T` that is determined by the weights at levels at most `j T`, and the triangle test at the
origin reads only levels `1` to `T`. -/
theorem measure_isTriangle_lowestPoint (ν : Measure ℝ) [IsProbabilityMeasure ν] (T : ℕ)
    (hT : 1 ≤ T) (c₀ : ℝ) (S : Set Lattice) (hS : S ⊆ levelSet 0) (k j : ℕ) :
    (environmentLaw ν).real {ω | IsTriangle ω T c₀
      (maxFirst (augmentedProcess ω T c₀ S k j).1,
        (j : ℤ) * T - maxFirst (augmentedProcess ω T c₀ S k j).1)} =
      (environmentLaw ν).real {ω | IsTriangle ω T c₀ 0} :=
  real_isTriangle_random_site ν ((j : ℤ) * T)
    (fun ω => (maxFirst (augmentedProcess ω T c₀ S k j).1,
      (j : ℤ) * T - maxFirst (augmentedProcess ω T c₀ S k j).1))
    ((measurable_of_countable (fun a : ℤ => (a, (j : ℤ) * T - a))).comp
      (measurable_maxFirst_augmentedProcess T hT c₀ S hS k j))
    (fun ω => by
      show maxFirst (augmentedProcess ω T c₀ S k j).1 +
        ((j : ℤ) * T - maxFirst (augmentedProcess ω T c₀ S k j).1) = (j : ℤ) * T
      ring) T hT c₀

/-- The freezing step for a random site `t` on level `L` that is determined by the lower
levels, an event `E` that is determined by the levels up to `L`, and a measurable functional
`gain` of mean `c ≠ 0` that ignores levels at most `0`. The product of the indicator of `E`
with `gain` read from `t` is integrable, and its integral is `c` times the probability of
`E`. -/
private theorem integral_indicator_mul_shifted (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (L : ℤ) (t : Environment → Lattice) (ht : Measurable[levelsAtMost L] t)
    (htl : ∀ ω, (t ω).1 + (t ω).2 = L) (E : Set Environment)
    (hE : MeasurableSet[levelsAtMost L] E) (gain : Environment → ℝ) (hgm : Measurable gain)
    (hloc : ∀ ω ω' : Environment, (∀ z : Lattice, 0 < z.1 + z.2 → ω z = ω' z) →
      gain ω = gain ω')
    (c : ℝ) (hc : c ≠ 0) (hint : ∫ ω, gain ω ∂environmentLaw ν = c) :
    Integrable (fun ω => E.indicator (fun _ => (1 : ℝ)) ω * gain (fun z => ω (t ω + z)))
        (environmentLaw ν) ∧
      ∫ ω, E.indicator (fun _ => (1 : ℝ)) ω * gain (fun z => ω (t ω + z))
          ∂environmentLaw ν = c * (environmentLaw ν).real E := by
  obtain ⟨hind, hid⟩ := indepFun_identDistrib_shift_of_levelsAtMost ν L t ht htl gain hgm hloc
    (E.indicator (fun _ => (1 : ℝ))) (measurable_const.indicator hE)
  have hEm : MeasurableSet E := levelsAtMost_le L _ hE
  have hgint : Integrable gain (environmentLaw ν) :=
    Integrable.of_integral_ne_zero (by rw [hint]; exact hc)
  have hshint : Integrable (fun ω => gain (fun z => ω (t ω + z))) (environmentLaw ν) :=
    hid.integrable_iff.2 hgint
  refine ⟨?_, ?_⟩
  · have heq : (fun ω => E.indicator (fun _ => (1 : ℝ)) ω * gain (fun z => ω (t ω + z))) =
        E.indicator (fun ω => gain (fun z => ω (t ω + z))) := by
      funext ω
      by_cases h : ω ∈ E <;> simp [h]
    rw [heq]
    exact hshint.indicator hEm
  · rw [hind.integral_fun_mul_eq_mul_integral
      (measurable_const.indicator hEm).aestronglyMeasurable
      hid.aemeasurable_fst.aestronglyMeasurable]
    have h1 : ∫ ω, E.indicator (fun _ => (1 : ℝ)) ω ∂environmentLaw ν =
        (environmentLaw ν).real E := by
      rw [integral_indicator_const (1 : ℝ) hEm, smul_eq_mul, mul_one]
    rw [h1, hid.integral_eq, hint, mul_comm]

/-- The freezing lemma, probabilistic part. The product of the triangle test at the lowest
point of block `j` with the gain of the environment seen from the site just above that point
is integrable, and its expected value is `T` times the probability of the test. The test is
determined by the levels up to `j T + T`, the site by the levels up to `j T`, and the gain
ignores levels at most `0`, so the independence of levels applies at level `j T + T`. -/
theorem integral_isTriangle_lowestPoint_mul_shifted_gain (ν : Measure ℝ)
    [IsProbabilityMeasure ν] (hp₀ : 0 < ν {1}) (T : ℕ) (hT : 1 ≤ T) (c₀ : ℝ)
    (S : Set Lattice) (hS : S ⊆ levelSet 0) (k j m : ℕ) :
    let r : Environment → Lattice := fun ω =>
      (maxFirst (augmentedProcess ω T c₀ S k j).1,
        (j : ℤ) * T - maxFirst (augmentedProcess ω T c₀ S k j).1)
    let E : Set Environment := {ω | IsTriangle ω T c₀ (r ω)}
    let gain : Environment → ℝ := fun ω' =>
      (openEdge (topSites ω') (antidiagHalfLine ∪ antidiagRightBlock T) m : ℝ) -
        halfLineEdge ω' m
    Integrable (fun ω => E.indicator (fun _ => (1 : ℝ)) ω *
        gain (fun z => ω (((r ω).1, (r ω).2 + (T : ℤ)) + z))) (environmentLaw ν) ∧
      ∫ ω, E.indicator (fun _ => (1 : ℝ)) ω *
          gain (fun z => ω (((r ω).1, (r ω).2 + (T : ℤ)) + z)) ∂environmentLaw ν =
        (T : ℝ) * (environmentLaw ν).real E := by
  intro r E gain
  have hS0 : antidiagHalfLine ∪ antidiagRightBlock T ⊆ levelSet 0 := by
    intro z hz
    rcases hz with hz | hz
    · exact (show z.1 + z.2 = 0 ∧ z.1 ≤ 0 from hz).1
    · exact (show z.1 + z.2 = 0 ∧ 1 ≤ z.1 ∧ z.1 ≤ T from hz).1
  have hZ : antidiagHalfLine ⊆ levelSet 0 :=
    fun z hz => (show z.1 + z.2 = 0 ∧ z.1 ≤ 0 from hz).1
  have hgm : Measurable gain := by
    have h1 : Measurable (fun ω' : Environment =>
        openEdge (topSites ω') (antidiagHalfLine ∪ antidiagRightBlock T) m) :=
      (measurable_openEdge_levelsAtMost _ 0 hS0 m).mono (levelsAtMost_le _) le_rfl
    have h2 : Measurable (fun ω' : Environment => halfLineEdge ω' m) :=
      (measurable_openEdge_levelsAtMost antidiagHalfLine 0 hZ m).mono (levelsAtMost_le _) le_rfl
    exact ((measurable_of_countable (Int.cast : ℤ → ℝ)).comp h1).sub
      ((measurable_of_countable (Int.cast : ℤ → ℝ)).comp h2)
  have hloc : ∀ ω ω' : Environment, (∀ z : Lattice, 0 < z.1 + z.2 → ω z = ω' z) →
      gain ω = gain ω' := by
    intro ω ω' h
    have key : ∀ S' : Set Lattice, S' ⊆ levelSet 0 →
        openEdge (topSites ω) S' m = openEdge (topSites ω') S' m := by
      intro S' hS'
      unfold openEdge
      rw [openReachSet_congr (topSites ω) (topSites ω') S' 0 m hS' (fun z h1 _ => ?_)]
      show ω z = 1 ↔ ω' z = 1
      rw [h z h1]
    show ((openEdge (topSites ω) (antidiagHalfLine ∪ antidiagRightBlock T) m : ℤ) : ℝ) -
        ((halfLineEdge ω m : ℤ) : ℝ) =
      ((openEdge (topSites ω') (antidiagHalfLine ∪ antidiagRightBlock T) m : ℤ) : ℝ) -
        ((halfLineEdge ω' m : ℤ) : ℝ)
    rw [key _ hS0]
    unfold halfLineEdge
    rw [key _ hZ]
  have hmeas : Measurable[levelsAtMost ((j : ℤ) * T)]
      (fun ω : Environment => maxFirst (augmentedProcess ω T c₀ S k j).1) :=
    measurable_maxFirst_augmentedProcess T hT c₀ S hS k j
  have ht : Measurable[levelsAtMost ((j : ℤ) * T + T)]
      (fun ω : Environment => (maxFirst (augmentedProcess ω T c₀ S k j).1,
        (j : ℤ) * T - maxFirst (augmentedProcess ω T c₀ S k j).1 + (T : ℤ))) :=
    ((measurable_of_countable (fun a : ℤ => (a, (j : ℤ) * T - a + (T : ℤ)))).comp hmeas).mono
      (levelsAtMost_mono (by omega)) le_rfl
  exact integral_indicator_mul_shifted ν ((j : ℤ) * T + T)
    (fun ω => (maxFirst (augmentedProcess ω T c₀ S k j).1,
      (j : ℤ) * T - maxFirst (augmentedProcess ω T c₀ S k j).1 + (T : ℤ))) ht
    (fun ω => by
      show maxFirst (augmentedProcess ω T c₀ S k j).1 +
        ((j : ℤ) * T - maxFirst (augmentedProcess ω T c₀ S k j).1 + (T : ℤ)) =
          (j : ℤ) * T + T
      ring) E (measurableSet_isTriangle_lowestPoint T hT c₀ S hS k j) gain hgm hloc (T : ℝ)
    (Nat.cast_ne_zero.2 (by omega)) (integral_halfLine_rightBlock_gain ν hp₀ T m)

end LPPDifferentiability
