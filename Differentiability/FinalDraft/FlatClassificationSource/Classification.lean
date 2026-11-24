/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, and Timo Seppäläinen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Differentiability.FinalDraft.FlatClassificationSource.ZeroAtom
import all Differentiability.Probability.TopFlatSegment
import Differentiability.Probability.FlatShapeAdapters
import Differentiability.Probability.FlatTopThinning
import Differentiability.Probability.FlatEdgeDifferentiability
import Differentiability.Probability.TopIndicatorShape
import Mathlib.Tactic

/-! # Classifying the level-one set for normalized bounded-above weights -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology

namespace LPPDifferentiability.FinalDraft

/-- Expected rates of the rightmost reached point from the antidiagonal half-line. -/
noncomputable def expectedHalfLineRates (ν : Measure ℝ) [IsProbabilityMeasure ν] : Set ℝ :=
  range fun n : ℕ =>
    (∫ ω, (halfLineEdge ω (n + 1) : ℝ) ∂environmentLaw ν) / ((n : ℝ) + 1)

/-- Passing to Bernoulli weights with the same top mass preserves all the expected rates. -/
theorem expectedHalfLineRates_eq_bernoulli_topMass (ν : Measure ℝ) [IsProbabilityMeasure ν] :
    expectedHalfLineRates ν = expectedHalfLineRates
      (bernoulliMeasure (1 : ℝ) 0 ⟨ν.real {1}, measureReal_nonneg, measureReal_le_one⟩) := by
  unfold expectedHalfLineRates
  congr 1
  funext n
  rw [integral_halfLineEdge_eq_bernoulli_topMass ν (n + 1)]

private theorem exists_shape_of_normalized_top_field (ν : Measure ℝ) [IsProbabilityMeasure ν] :
    ∃ gtop : Quadrant → ℝ, Continuous gtop ∧
      (∀ (c : ℝ≥0) (x : Quadrant), gtop (c * x.1, c * x.2) = (c : ℝ) * gtop x) ∧
      (∀ (x y : Quadrant) (r t : ℝ≥0), r + t = 1 →
        (r : ℝ) * gtop x + (t : ℝ) * gtop y ≤ gtop (r * x.1 + t * y.1, r * x.2 + t * y.2)) ∧
      (∀ᵐ ω ∂environmentLaw ν, ∀ ε : ℝ, 0 < ε →
        ∃ N : ℕ, 1 ≤ N ∧ ∀ d : ℕ × ℕ, N ≤ d.1 + d.2 →
          |lastPassage (topField ω) 0 d - gtop ((d.1 : ℝ≥0), (d.2 : ℝ≥0))| ≤
            ε * ((d.1 + d.2 : ℕ) : ℝ)) := by
  let f (w : ℝ) : ℝ := if w = 1 then 1 else 0
  have hf : Measurable f :=
    Measurable.ite (measurableSet_singleton _) measurable_const measurable_const
  let κ := ν.map f
  let : IsProbabilityMeasure κ := (Measure.isProbabilityMeasure_map_iff hf.aemeasurable).mpr inferInstance
  have hκ : ∀ᵐ t ∂κ, 0 ≤ t ∧ t ≤ 1 := by
    apply (ae_map_iff hf.aemeasurable measurableSet_Icc).mpr
    exact Eventually.of_forall fun t => by by_cases h : t = 1 <;> simp [f, h]
  obtain ⟨g, hcont, hhom, hconc, hsample, -, -, -, -⟩ :=
    exists_shape_with_expected_bounds_of_ae_mem_unit_interval κ hκ
  refine ⟨g, hcont, hhom, hconc, ?_⟩
  have hmap : (environmentLaw ν).map topField = environmentLaw κ :=
    environmentLaw_map_coordinatewise ν f hf
  have hmeas : Measurable topField := measurable_coordinatewise_environment_map f hf
  exact ae_of_ae_map hmeas.aemeasurable (by rwa [hmap])

/-- A rate below the horizontal coordinate rules out equality at one for the original shape. -/
private theorem weighted_shape_lt_one_of_rate_below (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hle : ∀ᵐ w ∂ν, w ≤ 1) (hp : 0 < ν {1}) (g : Quadrant → ℝ)
    (hcont : Continuous g)
    (hhom : ∀ (c : ℝ≥0) (x : Quadrant), g (c * x.1, c * x.2) = (c : ℝ) * g x)
    (hshape : ∀ᵐ ω ∂environmentLaw ν, ∀ ε : ℝ, 0 < ε →
      ∃ N : ℕ, 1 ≤ N ∧ ∀ d : ℕ × ℕ, N ≤ d.1 + d.2 →
        |lastPassage ω 0 d - g ((d.1 : ℝ≥0), (d.2 : ℝ≥0))| ≤
          ε * ((d.1 + d.2 : ℕ) : ℝ))
    (s : ℝ) (hs₀ : 0 ≤ s) (hs₁ : s ≤ 1) (r : ℝ) (hr : r ∈ expectedHalfLineRates ν)
    (hstrict : r < s) :
    g (toQuadrant (s, 1 - s)) < 1 := by
  let c := (r + s) / 2
  have hrc : r < c := by dsimp [c]; linarith
  have hcs : c < s := by dsimp [c]; linarith
  obtain ⟨n, hn⟩ := hr
  have hnMean : ∫ ω, (halfLineEdge ω (n + 1) : ℝ) ∂environmentLaw ν < c * (↑(n + 1) : ℝ) := by
    have hpos : 0 < (n : ℝ) + 1 := by positivity
    have h := (div_lt_iff₀ hpos).mp (hn.trans_lt hrc)
    simpa only [Nat.cast_succ] using h
  obtain ⟨δ, hδ, hq, hMean⟩ :=
    exists_nearTopDensity_halfLineEdge_lt ν hle hp (n + 1) (c * (↑(n + 1) : ℝ)) hnMean
  exact weighted_shape_lt_one_of_threshold_mean ν hle δ hδ hq g hcont hhom hshape
    c (n + 1) (Nat.succ_pos n) hMean s hcs hs₀ hs₁

/-- The normalized classification for the actual weight law. A zero atom or unbounded
rates give strictness everywhere. A real rate infimum gives the level-one interval and
differentiability at its two edges. -/
theorem normalized_weighted_shape_classification
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (hle : ∀ᵐ w ∂ν, w ≤ 1)
    (hp₁ : ν {1} < 1)
    (hneg : ∃ p : ℝ, 1 < p ∧ (∫⁻ w, ENNReal.ofReal ((max (-w) 0) ^ p) ∂ν) < ∞)
    (g : Quadrant → ℝ) (hcont : Continuous g)
    (hhom : ∀ (c : ℝ≥0) (x : Quadrant), g (c * x.1, c * x.2) = (c : ℝ) * g x)
    (hconc : ∀ (x y : Quadrant) (r t : ℝ≥0), r + t = 1 →
      (r : ℝ) * g x + (t : ℝ) * g y ≤ g (r * x.1 + t * y.1, r * x.2 + t * y.2))
    (hshape : ∀ᵐ ω ∂environmentLaw ν, ∀ ε : ℝ, 0 < ε →
      ∃ N : ℕ, 1 ≤ N ∧ ∀ d : ℕ × ℕ, N ≤ d.1 + d.2 →
        |lastPassage ω 0 d - g ((d.1 : ℝ≥0), (d.2 : ℝ≥0))| ≤
          ε * ((d.1 + d.2 : ℕ) : ℝ)) :
    (∀ t ∈ Icc (0 : ℝ) 1, g (toQuadrant (t, 1 - t)) ≤ 1) ∧
    (ν {1} = 0 → ∀ t ∈ Icc (0 : ℝ) 1, g (toQuadrant (t, 1 - t)) < 1) ∧
    (0 < ν {1} →
      (¬ BddBelow (expectedHalfLineRates ν) →
        ∀ t ∈ Icc (0 : ℝ) 1, g (toQuadrant (t, 1 - t)) < 1) ∧
      ∀ β : ℝ, IsGLB (expectedHalfLineRates ν) β → 1 / 2 ≤ β ∧ β < 1 ∧
        (∀ t ∈ Icc (0 : ℝ) 1,
          g (toQuadrant (t, 1 - t)) = 1 ↔ t ∈ Icc (1 - β) β) ∧
        DifferentiableAt ℝ (quadrantExtension g) (β, 1 - β) ∧
        DifferentiableAt ℝ (quadrantExtension g) (1 - β, β)) := by
  have hupper : ∀ t ∈ Icc (0 : ℝ) 1, g (toQuadrant (t, 1 - t)) ≤ 1 := by
    intro t ht
    have h := (expected_floor_limit_of_shape_block ν hle hneg g hcont hhom hconc hshape).2.2
      (toQuadrant (t, 1 - t))
    rw [toQuadrant_fst_coe t ht.1, toQuadrant_snd_coe t ht.2] at h
    linarith
  refine ⟨hupper, fun hp t ht =>
    weighted_shape_lt_one_of_atom_one_zero ν hle hp g hcont hhom hshape t ht.1 ht.2, ?_⟩
  intro hp
  have hStrict (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) (r : ℝ)
      (hr : r ∈ expectedHalfLineRates ν) (hrt : r < t) :
      g (toQuadrant (t, 1 - t)) < 1 :=
    weighted_shape_lt_one_of_rate_below ν hle hp g hcont hhom hshape t ht.1 ht.2 r hr hrt
  constructor
  · intro hUnbounded t ht
    by_contra! hn
    apply hUnbounded
    refine ⟨t, fun r hr => ?_⟩
    by_contra! hrt
    exact (not_le.mpr (hStrict t ht r hr hrt)) hn
  · intro β hβ
    obtain ⟨gtop, htcont, hthom, htconc, htshape⟩ := exists_shape_of_normalized_top_field ν
    obtain ⟨hβhalf, hβone, hTopInterval⟩ :=
      (top_shape_flat_segment_of_expected_edge_rates ν hp hp₁ gtop htcont hthom htconc
        htshape).2 β hβ
    have hinside (t : ℝ) (ht : t ∈ Icc (1 - β) β) : g (toQuadrant (t, 1 - t)) = 1 := by
      have htUnit : t ∈ Icc (0 : ℝ) 1 := ⟨by linarith [ht.1], ht.2.trans hβone.le⟩
      apply gbar_eq_one_of_gtop_eq_one ν hle hp hp₁ hneg g hcont hhom hconc hshape gtop
        htcont hthom htconc htshape t htUnit
      exact (hTopInterval t htUnit).mpr ht
    have hright (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) (hbt : β < t) :
        g (toQuadrant (t, 1 - t)) < 1 := by
      obtain ⟨r, hr, hrt⟩ := hβ.exists_between hbt
      exact hStrict t ht r hr hrt.2
    have hsym (t : ℝ) : g (toQuadrant (1 - t, 1 - (1 - t))) = g (toQuadrant (t, 1 - t)) := by
      have h := shape_swap_of_coordinatewise_field ν id measurable_id g hcont hhom hshape
        (toQuadrant (t, 1 - t))
      simpa only [toQuadrant, sub_sub_cancel] using h
    have hInterval (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
        g (toQuadrant (t, 1 - t)) = 1 ↔ t ∈ Icc (1 - β) β := by
      refine ⟨fun he => ⟨?_, ?_⟩, hinside t⟩
      · by_contra! hout
        have h := hright (1 - t) ⟨by linarith [ht.2], by linarith [ht.1]⟩ (by linarith)
        rw [hsym t, he] at h
        exact lt_irrefl _ h
      · by_contra! hout
        have h := hright t ht hout
        rw [he] at h
        exact lt_irrefl _ h
    exact ⟨hβhalf, hβone, hInterval,
      differentiableAt_flat_segment_endpoints_of_expected_edge_rate ν hle hp hp₁ hneg
        g hcont hhom hconc hshape β hβhalf hβone hβ hinside⟩

end LPPDifferentiability.FinalDraft
