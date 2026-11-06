/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import LPP_Foundations.Analysis.ExponentialShapeFormula
public import Martin2004.Model.LastPassage.ExitGrid
public import Martin2004.Probability.ExponentialLaw
public import Martin2004.Probability.PassageUpperDeviation
public import Martin2004.Probability.StationaryBoundaryLaw
public import Martin2004.Probability.StationaryMean
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# The stationary rate is at most the exit-grid bound

This file proves the probabilistic half of the lower bound in the proof of Martin (2004),
Theorem 2.4. Martin gets this step from the exact formula for the exponential distribution, which
is applied in that proof. Here the lower bound goes through the stationary model instead.

Let `g` be the expected-rate shape of `Exp(1)`, let `0 < ρ < 1`, and put
`m = ⌊x N⌋` and `n = ⌊y N⌋`. The proof has four steps.

* (a) The weights are almost surely nonnegative, so the exit-grid reduction bounds the stationary
  passage time `G(m, n)` by one of `2 K` grid terms (a boundary sum plus a bulk passage time).
* (b) Each of the four kinds of pieces, divided by `N`, exceeds its limit plus `δ / 2` with
  probability tending to zero. A finite union over the `K` grid indices gives that
  `G(m, n) / N` exceeds the exit-grid bound plus `δ` with probability tending to zero.
* (c) The mean of `G(m, n) / N` tends to `x / (1 - ρ) + y / ρ`, and its second moment is bounded.
* (d) If the means converge, the second moments are bounded, and upper deviations above a
  constant vanish in probability, then the limit of the means is at most that constant.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace LPPDifferentiability

/-! ## Grid lengths and the limits of their ratios -/

/-- The number of sites `⌊x N⌋` of the grid in the direction of a coordinate `x`. -/
private noncomputable abbrev gridLength (x : ℝ≥0) (N : ℕ) : ℕ := ⌊(x : ℝ) * N⌋₊

/-- `⌊x N⌋ / N` tends to `x`. -/
private theorem tendsto_gridLength_div (x : ℝ≥0) :
    Tendsto (fun N : ℕ => (gridLength x N : ℝ) / N) atTop (𝓝 (x : ℝ)) :=
  (tendsto_nat_floor_mul_div_atTop (R := ℝ) (NNReal.coe_nonneg x)).comp
    tendsto_natCast_atTop_atTop

/-- If `a N / N` tends to `α`, then `(a N * s / K) / N` (natural division) tends to
`α * s / K`: the natural division loses less than `1`. -/
private theorem tendsto_natDiv_div {a : ℕ → ℕ} {α : ℝ}
    (ha : Tendsto (fun N : ℕ => (a N : ℝ) / N) atTop (𝓝 α)) (s : ℕ) {K : ℕ} (hK : 0 < K) :
    Tendsto (fun N : ℕ => ((a N * s / K : ℕ) : ℝ) / N) atTop (𝓝 (α * s / K)) := by
  have hKr : (0 : ℝ) < K := by exact_mod_cast hK
  have hup : Tendsto (fun N : ℕ => (a N : ℝ) / N * s / K) atTop (𝓝 (α * s / K)) :=
    (ha.mul_const (s : ℝ)).div_const (K : ℝ)
  have hlow : Tendsto (fun N : ℕ => (a N : ℝ) / N * s / K - 1 / (N : ℝ)) atTop
      (𝓝 (α * s / K - 0)) := hup.sub tendsto_one_div_atTop_nhds_zero_nat
  rw [sub_zero] at hlow
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow hup ?_ ?_
  · filter_upwards [eventually_gt_atTop 0] with N hN
    have hNr : (0 : ℝ) < N := by exact_mod_cast hN
    have h := Nat.div_add_mod (a N * s) K
    have hmod := Nat.mod_lt (a N * s) hK
    have e : (K : ℝ) * ((a N * s / K : ℕ) : ℝ) + ((a N * s % K : ℕ) : ℝ) = (a N : ℝ) * s := by
      exact_mod_cast h
    have hm : ((a N * s % K : ℕ) : ℝ) < K := by exact_mod_cast hmod
    have hq : (a N : ℝ) * s / K - 1 ≤ ((a N * s / K : ℕ) : ℝ) := by
      rw [sub_le_iff_le_add, div_le_iff₀ hKr]
      nlinarith
    have hrew : (a N : ℝ) / N * s / K - 1 / (N : ℝ) = ((a N : ℝ) * s / K - 1) / N := by
      ring
    rw [hrew]
    exact div_le_div_of_nonneg_right hq hNr.le
  · filter_upwards [eventually_gt_atTop 0] with N hN
    have hNr : (0 : ℝ) < N := by exact_mod_cast hN
    have hq : ((a N * s / K : ℕ) : ℝ) ≤ (a N : ℝ) * s / K := by
      have h := Nat.cast_div_le (α := ℝ) (m := a N * s) (n := K)
      rwa [Nat.cast_mul] at h
    have hrew : (a N : ℝ) / N * s / K = ((a N : ℝ) * s / K) / N := by ring
    rw [hrew]
    exact div_le_div_of_nonneg_right hq hNr.le

/-- If `a N / N` tends to a positive limit, then `a N` is eventually positive. -/
private theorem eventually_pos_of_tendsto {a : ℕ → ℕ} {α : ℝ} (hα : 0 < α)
    (ha : Tendsto (fun N : ℕ => (a N : ℝ) / N) atTop (𝓝 α)) : ∀ᶠ N : ℕ in atTop, 0 < a N := by
  filter_upwards [ha.eventually (lt_mem_nhds hα)] with N hN
  by_contra h
  have h0 : a N = 0 := by omega
  rw [h0] at hN
  simp at hN

/-- The long side of a bulk piece: `(a N - a N r / K - 1) / N` tends to `α (K - r) / K`. -/
private theorem tendsto_bulk_long {a : ℕ → ℕ} {α : ℝ} (hα : 0 < α)
    (ha : Tendsto (fun N : ℕ => (a N : ℝ) / N) atTop (𝓝 α)) {r K : ℕ} (hr : r < K) :
    Tendsto (fun N : ℕ => ((a N - a N * r / K - 1 : ℕ) : ℝ) / N) atTop
      (𝓝 (α * ((K - r : ℕ) : ℝ) / K)) := by
  have hK : 0 < K := by omega
  have hKr : (K : ℝ) ≠ 0 := by exact_mod_cast hK.ne'
  have hlim : Tendsto (fun N : ℕ =>
      (a N : ℝ) / N - ((a N * r / K : ℕ) : ℝ) / N - 1 / (N : ℝ)) atTop
      (𝓝 (α - α * r / K - 0)) :=
    (ha.sub (tendsto_natDiv_div ha r hK)).sub tendsto_one_div_atTop_nhds_zero_nat
  have hval : α - α * r / K - 0 = α * ((K - r : ℕ) : ℝ) / K := by
    rw [Nat.cast_sub hr.le, sub_zero]
    field_simp
  rw [hval] at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_pos_of_tendsto hα ha] with N hN
  have hlt : a N * r / K < a N := Nat.div_lt_of_lt_mul (by nlinarith)
  have h1 : a N - a N * r / K - 1 + a N * r / K + 1 = a N := by omega
  have h2 : ((a N - a N * r / K - 1 : ℕ) : ℝ) + ((a N * r / K : ℕ) : ℝ) + 1 = (a N : ℝ) := by
    exact_mod_cast h1
  have e : ((a N - a N * r / K - 1 : ℕ) : ℝ) = (a N : ℝ) - ((a N * r / K : ℕ) : ℝ) - 1 := by
    linarith
  have key : (a N : ℝ) / N - ((a N * r / K : ℕ) : ℝ) / N - 1 / (N : ℝ) =
      ((a N - a N * r / K - 1 : ℕ) : ℝ) / N := by
    rw [e]
    ring
  exact key

/-- The short side of a bulk piece: `(b N - 1) / N` has the same limit as `b N / N`. -/
private theorem tendsto_pred_div {b : ℕ → ℕ} {β : ℝ} (hβ : 0 < β)
    (hb : Tendsto (fun N : ℕ => (b N : ℝ) / N) atTop (𝓝 β)) :
    Tendsto (fun N : ℕ => ((b N - 1 : ℕ) : ℝ) / N) atTop (𝓝 β) := by
  have hlim : Tendsto (fun N : ℕ => (b N : ℝ) / N - 1 / (N : ℝ)) atTop (𝓝 (β - 0)) :=
    hb.sub tendsto_one_div_atTop_nhds_zero_nat
  rw [sub_zero] at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_pos_of_tendsto hβ hb] with N hN
  have e : ((b N - 1 : ℕ) : ℝ) = (b N : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ b N)]
    simp
  have key : (b N : ℝ) / N - 1 / (N : ℝ) = ((b N - 1 : ℕ) : ℝ) / N := by
    rw [e]
    ring
  exact key

/-! ## Measures of finite unions -/

/-- If two families of events have probabilities tending to zero, so does their union. -/
private theorem tendsto_measure_union_zero {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {A B : ℕ → Set Ω} (hA : Tendsto (fun N => μ (A N)) atTop (𝓝 0))
    (hB : Tendsto (fun N => μ (B N)) atTop (𝓝 0)) :
    Tendsto (fun N => μ (A N ∪ B N)) atTop (𝓝 0) := by
  have hsum : Tendsto (fun N => μ (A N) + μ (B N)) atTop (𝓝 (0 + 0)) := hA.add hB
  rw [add_zero] at hsum
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsum
    (Eventually.of_forall fun N => zero_le)
    (Eventually.of_forall fun N => measure_union_le _ _)

/-- The same for a finite union of families of events. -/
private theorem tendsto_measure_iUnion_zero {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {ι : Type*} [Fintype ι] {A : ι → ℕ → Set Ω}
    (h : ∀ i, Tendsto (fun N => μ (A i N)) atTop (𝓝 0)) :
    Tendsto (fun N => μ (⋃ i, A i N)) atTop (𝓝 0) := by
  have hsum : Tendsto (fun N => ∑ i, μ (A i N)) atTop (𝓝 (∑ _i : ι, (0 : ℝ≥0∞))) :=
    tendsto_finsetSum Finset.univ fun i _ => h i
  rw [Finset.sum_const_zero] at hsum
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsum
    (Eventually.of_forall fun N => zero_le)
    (Eventually.of_forall fun N => measure_iUnion_fintype_le _ _)

/-! ## The four kinds of pieces of a grid term -/

/-- The boundary sum along the bottom row up to the grid point `m (r + 1) / K`. -/
private noncomputable abbrev boundaryRow (ρ : ℝ) (x : ℝ≥0) (K r N : ℕ) (ω : Environment) : ℝ :=
  inclusivePassage (stationaryEnvironment ρ ω) 0 (gridLength x N * (r + 1) / K, 0)

/-- The bulk piece started just after the grid point `m r / K`, on the row side. -/
private noncomputable abbrev bulkRow (x y : ℝ≥0) (K r N : ℕ) (ω : Environment) : ℝ :=
  inclusivePassage ω ((((gridLength x N * r / K : ℕ) : ℤ) + 1, 1) : Lattice)
    (gridLength x N - gridLength x N * r / K - 1, gridLength y N - 1)

/-- The boundary sum along the left column up to the grid point `n (r + 1) / K`. -/
private noncomputable abbrev boundaryColumn (ρ : ℝ) (y : ℝ≥0) (K r N : ℕ) (ω : Environment) : ℝ :=
  inclusivePassage (stationaryEnvironment ρ ω) 0 (0, gridLength y N * (r + 1) / K)

/-- The bulk piece started just after the grid point `n r / K`, on the column side. -/
private noncomputable abbrev bulkColumn (x y : ℝ≥0) (K r N : ℕ) (ω : Environment) : ℝ :=
  inclusivePassage ω ((1, ((gridLength y N * r / K : ℕ) : ℤ) + 1) : Lattice)
    (gridLength x N - 1, gridLength y N - gridLength y N * r / K - 1)

/-- The event that a function of the environment, divided by `N`, exceeds a bound `b`. -/
private abbrev exceedSet (f : Environment → ℝ) (b : ℝ) (N : ℕ) : Set Environment :=
  {ω | b < f ω / N}

/-- The union over the grid indices of the events that one of the four pieces of the grid term
exceeds its bound. -/
private abbrev gridEvents (ρ : ℝ) (x y : ℝ≥0) (K N : ℕ) (δ : ℝ)
    (βH γH βV γV : Fin K → ℝ) : Set Environment :=
  ⋃ r : Fin K,
    ((exceedSet (boundaryRow ρ x K r N) (βH r + δ / 2) N ∪
        exceedSet (bulkRow x y K r N) (γH r + δ / 2) N) ∪
      (exceedSet (boundaryColumn ρ y K r N) (βV r + δ / 2) N ∪
        exceedSet (bulkColumn x y K r N) (γV r + δ / 2) N))

/-- Step (a), for one environment. Suppose all weights are nonnegative and `G(m, n) / N` exceeds
`c + δ`, where `c` is at least every sum `β + γ` of limits. Then for some grid index, one of the
four pieces of the corresponding grid term exceeds its limit plus `δ / 2`. -/
private theorem exists_piece_exceeds {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) {x y : ℝ≥0} {K : ℕ}
    (hK : 0 < K) {N : ℕ} (hN : 0 < N) (hm : 0 < gridLength x N) (hn : 0 < gridLength y N)
    {ω : Environment} (hω : ∀ z, 0 ≤ ω z) {c δ : ℝ} (βH γH βV γV : Fin K → ℝ)
    (hH : ∀ r, βH r + γH r ≤ c) (hV : ∀ r, βV r + γV r ≤ c)
    (hgt : c + δ < stationaryPassage ρ ω (gridLength x N) (gridLength y N) / N) :
    ω ∈ gridEvents ρ x y K N δ βH γH βV γV := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  obtain ⟨r, h | h⟩ := stationaryPassage_le_exitGridTerm hρ0 hρ1 hω hm hn hK
  · have hdiv : stationaryPassage ρ ω (gridLength x N) (gridLength y N) / N ≤
        (boundaryRow ρ x K r N ω + bulkRow x y K r N ω) / N :=
      div_le_div_of_nonneg_right h hNr.le
    rw [add_div] at hdiv
    refine Set.mem_iUnion.2 ⟨r, ?_⟩
    by_contra hcon
    simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_lt] at hcon
    obtain ⟨⟨h1, h2⟩, -, -⟩ := hcon
    linarith [hH r]
  · have hdiv : stationaryPassage ρ ω (gridLength x N) (gridLength y N) / N ≤
        (boundaryColumn ρ y K r N ω + bulkColumn x y K r N ω) / N :=
      div_le_div_of_nonneg_right h hNr.le
    rw [add_div] at hdiv
    refine Set.mem_iUnion.2 ⟨r, ?_⟩
    by_contra hcon
    simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_lt] at hcon
    obtain ⟨-, h1, h2⟩ := hcon
    linarith [hV r]

/-! ## Step (b): upper deviations of the stationary passage time -/

/-- Step (b). The probability that `G(m, n) / N` exceeds the exit-grid bound plus `δ` tends to
zero. The four kinds of pieces have limits by the boundary law and the bulk deviation theorem;
a union bound over the `K` grid indices combines them. -/
private theorem tendsto_measure_exitGrid_gt {g : Quadrant → ℝ}
    (hg : IsExpectedRateShape (expMeasure 1) g) {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    {x y : ℝ≥0} (hx : 0 < x) (hy : 0 < y) {K : ℕ} (hK : 0 < K) {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun N : ℕ => environmentLaw (expMeasure 1)
      {ω | exitGridBound g ρ x y K + δ <
        stationaryPassage ρ ω (gridLength x N) (gridLength y N) / N}) atTop (𝓝 0) := by
  obtain ⟨-, hneg, hpos⟩ := expMeasure_one_martin_hypotheses
  have hδ2 : 0 < δ / 2 := half_pos hδ
  have hxr : (0 : ℝ) < x := NNReal.coe_pos.mpr hx
  have hyr : (0 : ℝ) < y := NNReal.coe_pos.mpr hy
  have hxl := tendsto_gridLength_div x
  have hyl := tendsto_gridLength_div y
  -- the limits of the four kinds of pieces
  obtain ⟨βH, hβH⟩ : ∃ f : Fin K → ℝ, ∀ r : Fin K,
      f r = (x : ℝ) * (((r : ℕ) + 1 : ℕ) : ℝ) / K / (1 - ρ) := ⟨_, fun r => rfl⟩
  obtain ⟨βV, hβV⟩ : ∃ f : Fin K → ℝ, ∀ r : Fin K,
      f r = (y : ℝ) * (((r : ℕ) + 1 : ℕ) : ℝ) / K / ρ := ⟨_, fun r => rfl⟩
  obtain ⟨γH, hγH⟩ : ∃ f : Fin K → ℝ, ∀ r : Fin K,
      f r = g (x * ((K - (r : ℕ) : ℕ) : ℝ≥0) / K, y) := ⟨_, fun r => rfl⟩
  obtain ⟨γV, hγV⟩ : ∃ f : Fin K → ℝ, ∀ r : Fin K,
      f r = g (x, y * ((K - (r : ℕ) : ℕ) : ℝ≥0) / K) := ⟨_, fun r => rfl⟩
  -- boundary pieces tend to zero in probability
  have hbH : ∀ r : Fin K, Tendsto (fun N : ℕ => environmentLaw (expMeasure 1)
      (exceedSet (boundaryRow ρ x K r N) (βH r + δ / 2) N)) atTop (𝓝 0) := by
    intro r
    rw [hβH r]
    exact (tendsto_measure_stationaryBoundary_gt hρ0 hρ1
      (fun N => gridLength x N * ((r : ℕ) + 1) / K)
      (tendsto_natDiv_div hxl ((r : ℕ) + 1) hK) hδ2).1
  have hbV : ∀ r : Fin K, Tendsto (fun N : ℕ => environmentLaw (expMeasure 1)
      (exceedSet (boundaryColumn ρ y K r N) (βV r + δ / 2) N)) atTop (𝓝 0) := by
    intro r
    rw [hβV r]
    exact (tendsto_measure_stationaryBoundary_gt hρ0 hρ1
      (fun N => gridLength y N * ((r : ℕ) + 1) / K)
      (tendsto_natDiv_div hyl ((r : ℕ) + 1) hK) hδ2).2
  -- bulk pieces tend to zero in probability
  have hgH : ∀ r : Fin K, Tendsto (fun N : ℕ => environmentLaw (expMeasure 1)
      (exceedSet (bulkRow x y K r N) (γH r + δ / 2) N)) atTop (𝓝 0) := by
    intro r
    rw [hγH r]
    have hrK : (r : ℕ) < K := r.isLt
    have hv1 : ((x * ((K - (r : ℕ) : ℕ) : ℝ≥0) / K : ℝ≥0) : ℝ) =
        (x : ℝ) * ((K - (r : ℕ) : ℕ) : ℝ) / K := by
      rw [NNReal.coe_div, NNReal.coe_mul, NNReal.coe_natCast, NNReal.coe_natCast]
    have hd : Tendsto (fun N : ℕ =>
        (((gridLength x N - gridLength x N * (r : ℕ) / K - 1 : ℕ) : ℝ) / N,
          ((gridLength y N - 1 : ℕ) : ℝ) / N)) atTop
        (𝓝 (((x * ((K - (r : ℕ) : ℕ) : ℝ≥0) / K : ℝ≥0) : ℝ), (y : ℝ))) := by
      rw [hv1]
      exact (tendsto_bulk_long hxr hxl hrK).prodMk_nhds (tendsto_pred_div hyr hyl)
    exact tendsto_measure_inclusivePassage_gt (expMeasure 1) hneg hpos hg
      (fun N => ((((gridLength x N * (r : ℕ) / K : ℕ) : ℤ) + 1, 1) : Lattice))
      (fun N => (gridLength x N - gridLength x N * (r : ℕ) / K - 1, gridLength y N - 1))
      (x * ((K - (r : ℕ) : ℕ) : ℝ≥0) / K, y)
      (add_pos_of_nonneg_of_pos (NNReal.coe_nonneg _) hyr) hd hδ2
  have hgV : ∀ r : Fin K, Tendsto (fun N : ℕ => environmentLaw (expMeasure 1)
      (exceedSet (bulkColumn x y K r N) (γV r + δ / 2) N)) atTop (𝓝 0) := by
    intro r
    rw [hγV r]
    have hrK : (r : ℕ) < K := r.isLt
    have hv2 : ((y * ((K - (r : ℕ) : ℕ) : ℝ≥0) / K : ℝ≥0) : ℝ) =
        (y : ℝ) * ((K - (r : ℕ) : ℕ) : ℝ) / K := by
      rw [NNReal.coe_div, NNReal.coe_mul, NNReal.coe_natCast, NNReal.coe_natCast]
    have hd : Tendsto (fun N : ℕ =>
        (((gridLength x N - 1 : ℕ) : ℝ) / N,
          ((gridLength y N - gridLength y N * (r : ℕ) / K - 1 : ℕ) : ℝ) / N)) atTop
        (𝓝 ((x : ℝ), ((y * ((K - (r : ℕ) : ℕ) : ℝ≥0) / K : ℝ≥0) : ℝ))) := by
      rw [hv2]
      exact (tendsto_pred_div hxr hxl).prodMk_nhds (tendsto_bulk_long hyr hyl hrK)
    exact tendsto_measure_inclusivePassage_gt (expMeasure 1) hneg hpos hg
      (fun N => ((1, ((gridLength y N * (r : ℕ) / K : ℕ) : ℤ) + 1) : Lattice))
      (fun N => (gridLength x N - 1, gridLength y N - gridLength y N * (r : ℕ) / K - 1))
      (x, y * ((K - (r : ℕ) : ℕ) : ℝ≥0) / K)
      (add_pos_of_pos_of_nonneg hxr (NNReal.coe_nonneg _)) hd hδ2
  -- the finite union over the grid indices
  have hUnion : Tendsto (fun N : ℕ => environmentLaw (expMeasure 1)
      (gridEvents ρ x y K N δ βH γH βV γV)) atTop (𝓝 0) :=
    tendsto_measure_iUnion_zero fun r =>
      tendsto_measure_union_zero (tendsto_measure_union_zero (hbH r) (hgH r))
        (tendsto_measure_union_zero (hbV r) (hgV r))
  -- the exit-grid bound is at least every pair of limits
  have hbound : ∀ r : Fin K, max
      ((((r : ℕ) : ℝ) + 1) / K * x / (1 - ρ) + g (x * ((K - (r : ℕ) : ℕ) : ℝ≥0) / K, y))
      ((((r : ℕ) : ℝ) + 1) / K * y / ρ + g (x, y * ((K - (r : ℕ) : ℕ) : ℝ≥0) / K)) ≤
      exitGridBound g ρ x y K := by
    intro r
    unfold exitGridBound
    have hbdd : BddAbove (Set.range fun r : Fin K => max
        ((((r : ℕ) : ℝ) + 1) / K * x / (1 - ρ) + g (x * ((K - (r : ℕ) : ℕ) : ℝ≥0) / K, y))
        ((((r : ℕ) : ℝ) + 1) / K * y / ρ + g (x, y * ((K - (r : ℕ) : ℕ) : ℝ≥0) / K))) :=
      (Set.finite_range _).bddAbove
    exact le_ciSup hbdd r
  have hH : ∀ r : Fin K, βH r + γH r ≤ exitGridBound g ρ x y K := by
    intro r
    have e : βH r = (((r : ℕ) : ℝ) + 1) / K * x / (1 - ρ) := by
      rw [hβH r]
      push_cast
      ring
    rw [e, hγH r]
    exact (le_max_left _ _).trans (hbound r)
  have hV : ∀ r : Fin K, βV r + γV r ≤ exitGridBound g ρ x y K := by
    intro r
    have e : βV r = (((r : ℕ) : ℝ) + 1) / K * y / ρ := by
      rw [hβV r]
      push_cast
      ring
    rw [e, hγV r]
    exact (le_max_right _ _).trans (hbound r)
  -- the event is almost surely contained in the union, for large `N`
  have hevent : ∀ᶠ N : ℕ in atTop, environmentLaw (expMeasure 1)
      {ω | exitGridBound g ρ x y K + δ <
        stationaryPassage ρ ω (gridLength x N) (gridLength y N) / N} ≤
      environmentLaw (expMeasure 1) (gridEvents ρ x y K N δ βH γH βV γV) := by
    filter_upwards [eventually_gt_atTop 0, eventually_pos_of_tendsto hxr hxl,
      eventually_pos_of_tendsto hyr hyl] with N hN hm hn
    refine measure_mono_ae ?_
    filter_upwards [ae_nonneg_environmentLaw_expMeasure_one] with ω hω hmem
    exact exists_piece_exceeds hρ0 hρ1 hK hN hm hn hω βH γH βV γV hH hV hmem
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hUnion
    (Eventually.of_forall fun N => zero_le) hevent

/-! ## Steps (c) and (d): the stationary rate -/

/-- The stationary rate is at most the exit-grid bound. For the expected-rate shape `g` of `Exp(1)`,
`0 < ρ < 1`, positive `x` and `y`, and a positive number `K` of grid pieces,
`x / (1 - ρ) + y / ρ ≤ exitGridBound g ρ x y K`. This is the probabilistic half of the lower bound
in the proof of Martin (2004), Theorem 2.4. The mean of the stationary passage time to
`(⌊x N⌋, ⌊y N⌋)`, divided by `N`, tends to the left side. It is controlled from above by the
exit-grid terms, whose limits involve only `g`. -/
theorem stationaryRate_le_exitGridBound {g : Quadrant → ℝ}
    (hg : IsExpectedRateShape (expMeasure 1) g) {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    {x y : ℝ≥0} (hx : 0 < x) (hy : 0 < y) {K : ℕ} (hK : 0 < K) :
    (x : ℝ) / (1 - ρ) + (y : ℝ) / ρ ≤ exitGridBound g ρ x y K := by
  have hxl := tendsto_gridLength_div x
  have hyl := tendsto_gridLength_div y
  obtain ⟨C, hCdef⟩ : ∃ C : ℝ, C = (1 + (x : ℝ) + y) *
      (2 + 2 * (y : ℝ) / ρ ^ 2 + 2 * (x : ℝ) / (1 - ρ) ^ 2) := ⟨_, rfl⟩
  refine le_of_tendsto_integral_of_tendsto_measure_gt (environmentLaw (expMeasure 1))
    (fun N ω => stationaryPassage ρ ω (gridLength x N) (gridLength y N) / N) (C := C)
    ?_ ?_ ?_ ?_
  · -- each variable is square integrable
    intro N
    obtain ⟨hint, -⟩ :=
      integrable_and_integral_stationaryPassage hρ0 hρ1 (gridLength x N) (gridLength y N)
    obtain ⟨hint2, -⟩ :=
      integrable_and_integral_sq_stationaryPassage_le hρ0 hρ1 (gridLength x N) (gridLength y N)
    have hG : MemLp (fun ω => stationaryPassage ρ ω (gridLength x N) (gridLength y N)) 2
        (environmentLaw (expMeasure 1)) :=
      (memLp_two_iff_integrable_sq hint.aestronglyMeasurable).2 hint2
    have e : (fun ω : Environment =>
        stationaryPassage ρ ω (gridLength x N) (gridLength y N) / (N : ℝ)) =
        fun ω => (N : ℝ)⁻¹ * stationaryPassage ρ ω (gridLength x N) (gridLength y N) := by
      funext ω
      rw [div_eq_inv_mul]
    show MemLp (fun ω : Environment =>
      stationaryPassage ρ ω (gridLength x N) (gridLength y N) / (N : ℝ)) 2
        (environmentLaw (expMeasure 1))
    rw [e]
    exact hG.const_mul _
  · -- Step (c): the second moments are bounded
    intro N
    have hCnn : 0 ≤ C := by
      rw [hCdef]
      positivity
    rcases Nat.eq_zero_or_pos N with rfl | hN
    · simpa using hCnn
    · obtain ⟨-, hsq⟩ := integrable_and_integral_sq_stationaryPassage_le hρ0 hρ1
        (gridLength x N) (gridLength y N)
      have hNr : (0 : ℝ) < N := by exact_mod_cast hN
      have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
      have hm : (gridLength x N : ℝ) ≤ N * x := by
        have h := Nat.floor_le (a := (x : ℝ) * N) (by positivity)
        linarith
      have hn : (gridLength y N : ℝ) ≤ N * y := by
        have h := Nat.floor_le (a := (y : ℝ) * N) (by positivity)
        linarith
      have h1 : (1 + gridLength x N + gridLength y N : ℝ) ≤ N * (1 + x + y) := by
        linarith
      have a1 : 2 * (gridLength y N : ℝ) / ρ ^ 2 ≤ 2 * (N * y) / ρ ^ 2 := by gcongr
      have a2 : 2 * (gridLength x N : ℝ) / (1 - ρ) ^ 2 ≤ 2 * (N * x) / (1 - ρ) ^ 2 := by
        gcongr
      have h2 : (2 + 2 * (gridLength y N : ℝ) / ρ ^ 2 + 2 * (gridLength x N : ℝ) / (1 - ρ) ^ 2) ≤
          N * (2 + 2 * (y : ℝ) / ρ ^ 2 + 2 * (x : ℝ) / (1 - ρ) ^ 2) := by
        have e : (N : ℝ) * (2 + 2 * (y : ℝ) / ρ ^ 2 + 2 * (x : ℝ) / (1 - ρ) ^ 2) =
            2 * N + 2 * (N * y) / ρ ^ 2 + 2 * (N * x) / (1 - ρ) ^ 2 := by ring
        rw [e]
        linarith
      have hprod := mul_le_mul h1 h2 (by positivity) (by positivity)
      have hint : ∫ ω, (stationaryPassage ρ ω (gridLength x N) (gridLength y N) / (N : ℝ)) ^ 2
          ∂environmentLaw (expMeasure 1) =
          (∫ ω, stationaryPassage ρ ω (gridLength x N) (gridLength y N) ^ 2
            ∂environmentLaw (expMeasure 1)) / (N : ℝ) ^ 2 := by
        simp_rw [div_pow]
        rw [integral_div]
      show ∫ ω, (stationaryPassage ρ ω (gridLength x N) (gridLength y N) / (N : ℝ)) ^ 2
          ∂environmentLaw (expMeasure 1) ≤ C
      rw [hint, div_le_iff₀ (pow_pos hNr 2)]
      calc _ ≤ (1 + (gridLength x N : ℝ) + gridLength y N) *
            (2 + 2 * (gridLength y N : ℝ) / ρ ^ 2 + 2 * (gridLength x N : ℝ) / (1 - ρ) ^ 2) :=
            hsq
        _ ≤ (N * (1 + (x : ℝ) + y)) *
            (N * (2 + 2 * (y : ℝ) / ρ ^ 2 + 2 * (x : ℝ) / (1 - ρ) ^ 2)) := hprod
        _ = C * (N : ℝ) ^ 2 := by rw [hCdef]; ring
  · -- Step (c): the means converge
    have e : ∀ N : ℕ, ∫ ω, stationaryPassage ρ ω (gridLength x N) (gridLength y N) / (N : ℝ)
        ∂environmentLaw (expMeasure 1) =
        (1 + (gridLength x N : ℝ) / (1 - ρ) + (gridLength y N : ℝ) / ρ) / N := by
      intro N
      rw [integral_div, (integrable_and_integral_stationaryPassage hρ0 hρ1
        (gridLength x N) (gridLength y N)).2]
    have hlim : Tendsto (fun N : ℕ =>
        (1 + (gridLength x N : ℝ) / (1 - ρ) + (gridLength y N : ℝ) / ρ) / N) atTop
        (𝓝 ((x : ℝ) / (1 - ρ) + (y : ℝ) / ρ)) := by
      have hfun : (fun N : ℕ =>
          (1 + (gridLength x N : ℝ) / (1 - ρ) + (gridLength y N : ℝ) / ρ) / N) =
          fun N : ℕ => 1 / (N : ℝ) + ((gridLength x N : ℝ) / N) / (1 - ρ) +
            ((gridLength y N : ℝ) / N) / ρ := by
        funext N
        ring
      rw [hfun]
      have h := ((tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).add (hxl.div_const (1 - ρ))).add
        (hyl.div_const ρ)
      rwa [zero_add] at h
    have hfun : (fun N : ℕ => ∫ ω, stationaryPassage ρ ω (gridLength x N) (gridLength y N) /
        (N : ℝ) ∂environmentLaw (expMeasure 1)) =
        fun N : ℕ => (1 + (gridLength x N : ℝ) / (1 - ρ) + (gridLength y N : ℝ) / ρ) / N :=
      funext e
    show Tendsto (fun N : ℕ => ∫ ω, stationaryPassage ρ ω (gridLength x N) (gridLength y N) /
        (N : ℝ) ∂environmentLaw (expMeasure 1)) atTop _
    rw [hfun]
    exact hlim
  · -- Step (b): upper deviations above the exit-grid bound vanish in probability
    intro δ hδ
    exact tendsto_measure_exitGrid_gt hg hρ0 hρ1 hx hy hK hδ

end LPPDifferentiability
