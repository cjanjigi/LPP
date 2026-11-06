/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Mathlib.Probability.Distributions.Bernoulli
public import Mathlib.Probability.Distributions.Geometric
public import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Geometric and Bernoulli laws for the stationary column model

These are the two one-variable laws of the stationary column model. They are used to bound the
one-site-per-column passage time `T̃(m, n)` of Martin (2004), Lemma 4.1.

* `geometricCountLaw θ`: the law on the real line of a count `k` with probability
  `(1 - θ) θ ^ k`. Mathlib's `geometricMeasure q` counts failures before the first success when
  the success probability is `q`, so the count law is `geometricMeasure (1 - θ)` carried to the
  real line by the cast `ℕ → ℝ`.
* Its probability-measure instance and its mean `θ / (1 - θ)` when `θ < 1`.
* The Bernoulli bridge: a probability measure on the real line that is almost surely `0` or `1`
  and gives mass `p` to `{1}` is Mathlib's `bernoulliMeasure 1 0 p`, which puts mass `p` on `1`
  and mass `1 - p` on `0`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set unitInterval

namespace LPPDifferentiability

/-! ## The geometric count law -/

/-- The cast from the natural numbers to the real line is measurable (the domain is discrete). -/
private lemma measurable_natCast_real : Measurable (fun k : ℕ => (k : ℝ)) :=
  Measurable.of_discrete

/-- The law on the real line of a count `k` with `P(k) = (1 - θ) θ ^ k`. Mathlib's
`geometricMeasure q` has `P(k) = (1 - q) ^ k q`, so we use success probability `q = 1 - θ`
(that is, `σ θ`) and carry the result to the real line with the cast. -/
noncomputable def geometricCountLaw (θ : unitInterval) : Measure ℝ :=
  (geometricMeasure (σ θ)).map (fun k : ℕ => (k : ℝ))

/-- Unfolding lemma for `geometricCountLaw`. -/
theorem geometricCountLaw_def (θ : unitInterval) :
    geometricCountLaw θ = (geometricMeasure (σ θ)).map (fun k : ℕ => (k : ℝ)) := rfl

/-- The count law is a probability measure, because the image of a probability measure under a
measurable map is one. -/
instance isProbabilityMeasure_geometricCountLaw (θ : unitInterval) :
    IsProbabilityMeasure (geometricCountLaw θ) :=
  (Measure.isProbabilityMeasure_map_iff measurable_natCast_real.aemeasurable).2 inferInstance

/-- The series `∑ k, (1 - θ) θ ^ k * k` (written with the success probability `σ θ` as Mathlib's
weights are) has sum `θ / (1 - θ)` when `θ < 1`. This is the arithmetic behind the mean. -/
private lemma hasSum_geometricCountLaw_mean {θ : unitInterval} (hθ : (θ : ℝ) < 1) :
    HasSum (fun k : ℕ =>
      (1 - ((σ θ : unitInterval) : ℝ)) ^ k * ((σ θ : unitInterval) : ℝ) * (k : ℝ))
      ((θ : ℝ) / (1 - θ)) := by
  have hne : (1 - (θ : ℝ)) ≠ 0 := (sub_pos.mpr hθ).ne'
  -- the series for `∑ k, k * θ ^ k`, with `‖θ‖ < 1`
  have hnorm : ‖(θ : ℝ)‖ < 1 := by
    rw [Real.norm_of_nonneg θ.2.1]
    exact hθ
  have hbase := (hasSum_coe_mul_geometric_of_norm_lt_one hnorm).mul_left (1 - (θ : ℝ))
  -- the terms agree: `(1 - (1 - θ)) ^ k * (1 - θ) * k = (1 - θ) * (k * θ ^ k)`
  have hterm : ∀ k : ℕ,
      (1 - ((σ θ : unitInterval) : ℝ)) ^ k * ((σ θ : unitInterval) : ℝ) * (k : ℝ) =
        (1 - (θ : ℝ)) * ((k : ℝ) * (θ : ℝ) ^ k) := by
    intro k
    rw [unitInterval.coe_symm_eq, sub_sub_cancel]
    ring
  -- the sums agree: `θ / (1 - θ) = (1 - θ) * (θ / (1 - θ) ^ 2)`
  have hvalue : (θ : ℝ) / (1 - θ) = (1 - (θ : ℝ)) * ((θ : ℝ) / (1 - θ) ^ 2) := by
    rw [← mul_div_assoc, pow_two, mul_div_mul_left _ _ hne]
  simp only [hterm]
  rw [hvalue]
  exact hbase

/-- The count law has a finite mean `θ / (1 - θ)` when `θ < 1`: the identity function is
integrable and its integral is `θ / (1 - θ)`. This is the mean of the stationary column weights
used for the passage-time bound (Martin (2004), Lemma 4.1). -/
theorem integrable_and_integral_id_geometricCountLaw {θ : unitInterval} (hθ : (θ : ℝ) < 1) :
    Integrable (fun t : ℝ => t) (geometricCountLaw θ) ∧
      ∫ t : ℝ, t ∂geometricCountLaw θ = (θ : ℝ) / (1 - θ) := by
  -- the success probability `σ θ = 1 - θ` is not zero
  have hsucc : σ θ ≠ 0 := by
    intro h
    have h' : ((σ θ : unitInterval) : ℝ) = ((0 : unitInterval) : ℝ) := congrArg Subtype.val h
    have h0 : ((0 : unitInterval) : ℝ) = 0 := rfl
    rw [unitInterval.coe_symm_eq, h0] at h'
    linarith
  have hsum := hasSum_geometricCountLaw_mean hθ
  have hmeas := measurable_natCast_real
  -- integrability: the weighted series converges
  have hint : Integrable (fun t : ℝ => t) (geometricCountLaw θ) := by
    rw [geometricCountLaw_def,
      integrable_map_measure measurable_id'.aestronglyMeasurable hmeas.aemeasurable,
      integrable_geometricMeasure_iff hsucc]
    exact hsum.summable.congr fun k => by simp
  refine ⟨hint, ?_⟩
  -- the mean: change variables to `ℕ`, then use the series
  rw [geometricCountLaw_def, integral_map hmeas.aemeasurable measurable_id'.aestronglyMeasurable,
    integral_geometricMeasure hsucc]
  simpa only [smul_eq_mul] using hsum.tsum_eq

/-! ## The Bernoulli bridge -/

/-- The real number `q ∈ [0, 1]` as an extended nonnegative real is the coercion of its
nonnegative real. -/
lemma ofReal_unitInterval (q : unitInterval) :
    ENNReal.ofReal (q : ℝ) = (unitInterval.toNNReal q : ENNReal) := by
  exact (ENNReal.ofReal_eq_coe_nnreal q.2.1).trans rfl

/-- A probability measure on the real line that is almost surely `0` or `1` and gives mass `p` to
`{1}` is the Bernoulli law with mass `p` on `1` and mass `1 - p` on `0`. This is the bridge from
"a zero-one valued weight with `P(1) = p`" (Martin (2004), Lemma 4.1) to Mathlib's
`bernoulliMeasure`; `p` is automatically in `[0, 1]`, as the mass of a set. -/
theorem exists_eq_bernoulliMeasure_of_ae_zero_or_one (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (h01 : ∀ᵐ t ∂μ, t = 0 ∨ t = 1) (p : ℝ) (hp : μ.real {1} = p) :
    ∃ hp01 : p ∈ unitInterval, μ = bernoulliMeasure (1 : ℝ) 0 ⟨p, hp01⟩ := by
  have hp01 : p ∈ unitInterval := by
    rw [← hp]
    exact ⟨measureReal_nonneg, measureReal_le_one⟩
  refine ⟨hp01, ?_⟩
  -- the two-point set `{0, 1}` carries all the mass
  have hpair : MeasurableSet ({0, 1} : Set ℝ) := (Set.toFinite _).measurableSet
  have hconull : μ ({0, 1} : Set ℝ)ᶜ = 0 := by
    rw [← mem_ae_iff]
    filter_upwards [h01] with t ht
    exact ht
  have hpair_one : μ ({0, 1} : Set ℝ) = 1 := (prob_compl_eq_zero_iff hpair).mp hconull
  -- any set has the same mass as its trace on `{0, 1}`
  have htrace : ∀ s : Set ℝ, μ s = μ (s ∩ {0, 1}) := fun s => (measure_inter_conull hconull).symm
  -- the mass of `{1}` and of `{0}`, as real numbers and as extended reals
  have hmass_sum : μ.real {0} + μ.real {1} = 1 := by
    have hunion : μ.real ({0} ∪ {1} : Set ℝ) = μ.real {0} + μ.real {1} :=
      measureReal_union (Set.disjoint_singleton.mpr (by norm_num)) (measurableSet_singleton 1)
    rw [Set.singleton_union, measureReal_def, hpair_one, ENNReal.toReal_one] at hunion
    exact hunion.symm
  have hmass_zero : μ.real {0} = 1 - p := by linarith
  have hone : μ {1} = (unitInterval.toNNReal ⟨p, hp01⟩ : ENNReal) := by
    have h : μ {1} = ENNReal.ofReal p := by
      rw [← hp]
      exact (ofReal_measureReal (measure_ne_top μ {1})).symm
    exact h.trans (ofReal_unitInterval ⟨p, hp01⟩)
  have hzero : μ {0} = (unitInterval.toNNReal (σ ⟨p, hp01⟩) : ENNReal) := by
    have h : μ {0} = ENNReal.ofReal (1 - p) := by
      rw [← hmass_zero]
      exact (ofReal_measureReal (measure_ne_top μ {0})).symm
    have hsymm : ENNReal.ofReal (1 - p) = ENNReal.ofReal ((σ ⟨p, hp01⟩ : unitInterval) : ℝ) :=
      congrArg ENNReal.ofReal (unitInterval.coe_symm_eq ⟨p, hp01⟩).symm
    exact (h.trans hsymm).trans (ofReal_unitInterval (σ ⟨p, hp01⟩))
  -- the four cases of Mathlib's characterization of the Bernoulli law
  refine eq_bernoulliMeasure ?_ ?_ ?_ ?_
  · intro s _ h1 h0
    have hs : s ∩ {0, 1} = {0, 1} :=
      Set.inter_eq_right.mpr (by
        intro t ht
        rcases ht with rfl | rfl
        · exact h0
        · exact h1)
    rw [htrace s, hs, hpair_one]
  · intro s _ h1 h0
    have hs : s ∩ {0, 1} = {1} := by
      ext t
      simp only [mem_inter_iff, mem_insert_iff, mem_singleton_iff]
      constructor
      · rintro ⟨hts, rfl | rfl⟩
        · exact absurd hts h0
        · rfl
      · rintro rfl
        exact ⟨h1, Or.inr rfl⟩
    rw [htrace s, hs, hone]
  · intro s _ h1 h0
    have hs : s ∩ {0, 1} = {0} := by
      ext t
      simp only [mem_inter_iff, mem_insert_iff, mem_singleton_iff]
      constructor
      · rintro ⟨hts, rfl | rfl⟩
        · rfl
        · exact absurd hts h1
      · rintro rfl
        exact ⟨h0, Or.inl rfl⟩
    rw [htrace s, hs, hzero]
  · intro s _ h1 h0
    have hs : s ∩ {0, 1} = ∅ := by
      ext t
      simp only [mem_inter_iff, mem_insert_iff, mem_singleton_iff, mem_empty_iff_false,
        iff_false]
      rintro ⟨hts, rfl | rfl⟩
      · exact h0 hts
      · exact h1 hts
    rw [htrace s, hs, measure_empty]

end LPPDifferentiability
