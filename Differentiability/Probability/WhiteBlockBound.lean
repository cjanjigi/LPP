/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Differentiability.Model.OrientedPercolation
public import Differentiability.Model.OrientedPercolationLaws
public import Differentiability.Probability.HalfLineEdge
public import LPP_Foundations.Probability.Stationarity
public import Mathlib.Tactic
import Differentiability.Probability.AugmentedMeasurability

/-!
# White-block probability bound

A block of scale `N` that is not black contains an open path of `N` steps that
starts on its middle level and moves right by at least `c₁ N`. There are `N + 1`
possible starting sites. Shift invariance and a union bound therefore bound
the probability of a white block by `N + 1` times the corresponding half-line
edge probability.
-/

@[expose] public section

namespace LPPDifferentiability

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal

/-- The shift of the weights by a lattice point is measurable. -/
private theorem measurable_shift (u : Lattice) :
    Measurable (fun ω : Environment => fun z : Lattice => ω (u + z)) :=
  Measurable.of_eval fun z => measurable_pi_apply (u + z)

/-- The event that the half-line edge at scale `N` is at least `c N` is measurable. -/
private theorem measurableSet_halfLine_ge (c : ℝ) (N : ℕ) :
    MeasurableSet {ω : Environment | c * N ≤ ((halfLineEdge ω N : ℤ) : ℝ)} := by
  have hE : Measurable[levelsAtMost (0 + (N : ℤ))]
      (fun ω : Environment => halfLineEdge ω N) :=
    measurable_openEdge_levelsAtMost antidiagHalfLine 0 (fun z hz => hz.1) N
  have hR : Measurable[levelsAtMost (0 + (N : ℤ))]
      (fun ω : Environment => ((halfLineEdge ω N : ℤ) : ℝ)) :=
    (measurable_of_countable (fun k : ℤ => (k : ℝ))).comp hE
  have hS : MeasurableSet[levelsAtMost (0 + (N : ℤ))]
      {ω : Environment | c * N ≤ ((halfLineEdge ω N : ℤ) : ℝ)} :=
    measurableSet_le measurable_const hR
  exact (levelsAtMost_le _) _ hS

/-- Translating the weights by `u` preserves the probability of a measurable event. -/
private theorem measureReal_shift_preimage (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (u : Lattice) {G : Set Environment} (hG : MeasurableSet G) :
    (environmentLaw ν).real ((fun ω : Environment => fun z : Lattice => ω (u + z)) ⁻¹' G) =
      (environmentLaw ν).real G := by
  rw [measureReal_def, measureReal_def, ← Measure.map_apply (measurable_shift u) hG,
    environmentLaw_map_translation ν u]

/-- The starting site on the middle level of block `z`: the `i`-th of the `N + 1` sites
`(N z₁ + i, N z₂ + (N - i))`. -/
private def whiteStart (N : ℕ) (z : Lattice) (i : ℕ) : Lattice :=
  ((N : ℤ) * z.1 + (i : ℤ), (N : ℤ) * z.2 + ((N : ℤ) - (i : ℤ)))

/-- An open path of `N` steps from `u` that moves right by at least `c N` shows that the
half-line edge of the shifted weights is at least `c N`. -/
private theorem le_halfLineEdge_shift (ω : Environment) (N : ℕ) (c : ℝ) (u v : Lattice)
    (hv : (v.1 - u.1) + (v.2 - u.2) = (N : ℤ)) (hc : c * N ≤ ((v.1 - u.1 : ℤ) : ℝ))
    (hopen : OpenReach (topSites ω) u v) :
    c * N ≤ ((halfLineEdge (fun y : Lattice => ω (u + y)) N : ℤ) : ℝ) := by
  set w : Lattice := (v.1 - u.1, v.2 - u.2) with hw_def
  have hu_w : u + w = v := by
    rw [hw_def]
    ext <;> simp
  have hlev : v.1 + v.2 = u.1 + u.2 + (N : ℤ) := by omega
  have hmem0 : v ∈ openReachSet (topSites ω) {u} N := ⟨u, rfl, hopen, hlev⟩
  have hw0 : w ∈ openReachSet ((fun z : Lattice => u + z) ⁻¹' topSites ω)
      {0} N := by
    rw [mem_openReachSet_translate]
    have himg : (fun z : Lattice => u + z) '' ({0} : Set Lattice) = {u} := by
      ext x
      simp
    rw [himg, hu_w]
    exact hmem0
  have hsub : ({0} : Set Lattice) ⊆ antidiagHalfLine := by
    intro x hx
    rw [mem_singleton_iff] at hx
    subst hx
    exact ⟨by norm_num, by norm_num⟩
  have hw1 : w ∈ openReachSet (topSites (fun y : Lattice => ω (u + y))) antidiagHalfLine N :=
    openReachSet_mono subset_rfl hsub N hw0
  have hbdd : BddAbove (Prod.fst '' openReachSet (topSites (fun y : Lattice => ω (u + y)))
      antidiagHalfLine N) := by
    refine ⟨(N : ℤ), ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    have := bddAbove_fst_openReachSet (topSites (fun y : Lattice => ω (u + y)))
      antidiagHalfLine N 0 (fun x hx => hx.2) x hx
    simpa using this
  have hle : w.1 ≤ maxFirst (openReachSet (topSites (fun y : Lattice => ω (u + y)))
      antidiagHalfLine N) := le_maxFirst _ hbdd hw1
  have hw_fst : w.1 = v.1 - u.1 := rfl
  show c * N ≤ ((maxFirst (openReachSet (topSites (fun y : Lattice => ω (u + y)))
      antidiagHalfLine N) : ℤ) : ℝ)
  have hcast : ((w.1 : ℤ) : ℝ) ≤ ((maxFirst (openReachSet (topSites (fun y : Lattice => ω (u + y)))
      antidiagHalfLine N) : ℤ) : ℝ) := by exact_mod_cast hle
  rw [hw_fst] at hcast
  exact le_trans hc hcast

/-- If block `z` is not black, then for one of the `N + 1` starting sites, the shifted
half-line edge is at least `c₁ N`. -/
private theorem exists_start_of_not_black (N : ℕ) (c₁ : ℝ) (z : Lattice) (ω : Environment)
    (h : ¬ IsBlackBlock (topSites ω) N c₁ z) :
    ∃ i ∈ Finset.range (N + 1),
      ω ∈ (fun ω' : Environment => fun y : Lattice => ω' (whiteStart N z i + y)) ⁻¹'
        {ω' : Environment | c₁ * N ≤ ((halfLineEdge ω' N : ℤ) : ℝ)} := by
  unfold IsBlackBlock at h
  push Not at h
  obtain ⟨u, v, hcorner, huv, hu, hv, hc, hopen⟩ := h
  obtain ⟨h1, h2⟩ := Prod.le_def.mp hcorner
  have ha0 : (0 : ℤ) ≤ u.1 - (N : ℤ) * z.1 := by simp at h1; omega
  have hb0 : (0 : ℤ) ≤ u.2 - (N : ℤ) * z.2 := by simp at h2; omega
  obtain ⟨i, hi⟩ : ∃ i : ℕ, (i : ℤ) = u.1 - (N : ℤ) * z.1 :=
    ⟨(u.1 - (N : ℤ) * z.1).toNat, Int.toNat_of_nonneg ha0⟩
  have hiN : i ≤ N := by omega
  have hstart : whiteStart N z i = u := by
    unfold whiteStart
    ext
    · simp only
      omega
    · simp only
      omega
  refine ⟨i, Finset.mem_range.mpr (Nat.lt_succ_of_le hiN), ?_⟩
  show c₁ * N ≤ ((halfLineEdge (fun y : Lattice => ω (whiteStart N z i + y)) N : ℤ) : ℝ)
  rw [hstart]
  exact le_halfLineEdge_shift ω N c₁ u v (by omega) hc hopen

/-- The probability that block `z` of scale `N` is not black is at most `N + 1` times the
probability that the half-line edge at scale `N` is at least `c₁ N`. -/
theorem white_block_probability_le (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (N : ℕ) (c₁ : ℝ) (z : Lattice) :
    (environmentLaw ν).real {ω | ¬ IsBlackBlock (topSites ω) N c₁ z} ≤
      ((N : ℝ) + 1) * (environmentLaw ν).real {ω | c₁ * N ≤ halfLineEdge ω N} := by
  have hsub : {ω : Environment | ¬ IsBlackBlock (topSites ω) N c₁ z} ⊆
      ⋃ i ∈ Finset.range (N + 1),
        (fun ω' : Environment => fun y : Lattice => ω' (whiteStart N z i + y)) ⁻¹'
          {ω' : Environment | c₁ * N ≤ ((halfLineEdge ω' N : ℤ) : ℝ)} := by
    intro ω hω
    obtain ⟨i, hi, hmem⟩ := exists_start_of_not_black N c₁ z ω hω
    exact mem_iUnion₂.mpr ⟨i, hi, hmem⟩
  calc (environmentLaw ν).real {ω | ¬ IsBlackBlock (topSites ω) N c₁ z}
      ≤ (environmentLaw ν).real (⋃ i ∈ Finset.range (N + 1),
          (fun ω' : Environment => fun y : Lattice => ω' (whiteStart N z i + y)) ⁻¹'
            {ω' : Environment | c₁ * N ≤ ((halfLineEdge ω' N : ℤ) : ℝ)}) :=
        measureReal_mono hsub (measure_ne_top _ _)
    _ ≤ ∑ i ∈ Finset.range (N + 1),
          (environmentLaw ν).real ((fun ω' : Environment => fun y : Lattice =>
            ω' (whiteStart N z i + y)) ⁻¹'
              {ω' : Environment | c₁ * N ≤ ((halfLineEdge ω' N : ℤ) : ℝ)}) :=
        measureReal_biUnion_finset_le _ _
    _ = ∑ _i ∈ Finset.range (N + 1),
          (environmentLaw ν).real {ω : Environment | c₁ * N ≤ ((halfLineEdge ω N : ℤ) : ℝ)} :=
        Finset.sum_congr rfl fun i _ =>
          measureReal_shift_preimage ν _ (measurableSet_halfLine_ge c₁ N)
    _ = ((N : ℝ) + 1) * (environmentLaw ν).real {ω | c₁ * N ≤ halfLineEdge ω N} := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        push_cast
        ring

end LPPDifferentiability
