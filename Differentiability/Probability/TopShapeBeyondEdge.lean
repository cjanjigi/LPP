/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Differentiability.Probability.TopPassageDecay
public import LPP_Foundations.Frozen.Analysis.ToQuadrant
public import LPP_Foundations.Frozen.Model.Quadrant
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

/-!
# The top shape is below one beyond the edge

Assume the weights are at most one and equal to one with positive probability, and that the
mean half-line edge at some length `L` is below `c L`. Let `gtop` be a continuous,
homogeneous function on the quadrant that is the almost sure uniform shape of the top
passage time. For `c < s ≤ 1` the value of `gtop` at `(s, 1 - s)` is strictly below one.

The proof has three steps:

* Apply the decay estimate for the top passage time (total form) at the intermediate
  speed `s' = (c + s) / 2`, not at `s`. The lattice point `(⌊s n⌋, n - ⌊s n⌋)` on level `n`
  need not satisfy `s (k + ℓ) ≤ k`, but it satisfies `s' (k + ℓ) ≤ k` once `n (s - s') ≥ 1`.
* The bounds `A e^{-B n}` are summable. By the first Borel-Cantelli lemma, almost surely the
  top passage time to the floor point of level `n` is below `(1 - δ) n` for all large `n`.
* Combine this with the almost sure shape hypothesis, and with homogeneity and continuity of
  `gtop` along `⌊s n⌋ / n → s`, to get `gtop (s, 1 - s) ≤ 1 - δ`.

The total form of the decay estimate also covers `s = 0`, where a bound in `k` alone would
give nothing.

## Main results

- `gtop_lt_one_beyond_edge`: `gtop (s, 1 - s) < 1` for `c < s ≤ 1`.

## References

- Georgiou, Rassoul-Agha and Seppäläinen (manuscript in preparation), the flat-edge theorem.
-/

@[expose] public section

namespace LPPDifferentiability

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal

/-- The scaled floor points `(⌊s n⌋ / n, (n - ⌊s n⌋) / n)` of level one tend to
`(s, 1 - s)` when `0 ≤ s ≤ 1`. -/
private theorem floorPoint_tendsto (s : ℝ) (hs₀ : 0 ≤ s) (hs₁ : s ≤ 1) :
    Tendsto (fun n : ℕ => (((⌊s * (n : ℝ)⌋₊ : ℕ) : ℝ≥0) * (n : ℝ≥0)⁻¹,
      (((n - ⌊s * (n : ℝ)⌋₊ : ℕ) : ℝ≥0) * (n : ℝ≥0)⁻¹))) atTop
      (𝓝 (toQuadrant (s, 1 - s))) := by
  have h1 : Tendsto (fun n : ℕ => (⌊s * (n : ℝ)⌋₊ : ℝ) * (n : ℝ)⁻¹) atTop (𝓝 s) := by
    have h := (tendsto_nat_floor_mul_div_atTop hs₀).comp tendsto_natCast_atTop_atTop
    exact Tendsto.congr (fun n => div_eq_mul_inv _ _) h
  have h2 : Tendsto (fun n : ℕ => ((n - ⌊s * (n : ℝ)⌋₊ : ℕ) : ℝ) * (n : ℝ)⁻¹) atTop
      (𝓝 (1 - s)) := by
    have h := (tendsto_const_nhds (x := (1 : ℝ))).sub h1
    refine Tendsto.congr' ?_ h
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
    have hle : ⌊s * (n : ℝ)⌋₊ ≤ n :=
      Nat.floor_le_of_le (mul_le_of_le_one_left (Nat.cast_nonneg n) hs₁)
    rw [Nat.cast_sub hle, sub_mul, mul_inv_cancel₀ hn0]
  refine Tendsto.prodMk_nhds ?_ ?_
  · refine NNReal.tendsto_coe.1 ?_
    rw [Real.coe_toNNReal s hs₀]
    refine Tendsto.congr (fun n => ?_) h1
    simp only [NNReal.coe_mul, NNReal.coe_inv, NNReal.coe_natCast]
  · refine NNReal.tendsto_coe.1 ?_
    rw [Real.coe_toNNReal (1 - s) (sub_nonneg.2 hs₁)]
    refine Tendsto.congr (fun n => ?_) h2
    simp only [NNReal.coe_mul, NNReal.coe_inv, NNReal.coe_natCast]

/-- The two coordinates of the floor point of level `n` add up to `n`. -/
private theorem floor_level_cast (s : ℝ) (hs₁ : s ≤ 1) (n : ℕ) :
    ((⌊s * (n : ℝ)⌋₊ : ℕ) : ℝ) + ((n - ⌊s * (n : ℝ)⌋₊ : ℕ) : ℝ) = (n : ℝ) := by
  have hle : ⌊s * (n : ℝ)⌋₊ ≤ n :=
    Nat.floor_le_of_le (mul_le_of_le_one_left (Nat.cast_nonneg n) hs₁)
  have hlev : ⌊s * (n : ℝ)⌋₊ + (n - ⌊s * (n : ℝ)⌋₊) = n := by omega
  exact_mod_cast hlev

/-- One floor point: if the passage time to `(k, n - k)` is below `(1 - δ) n` and within
`ε n` of the shape, then homogeneity bounds the shape at the scaled point by `1 - δ + ε`. -/
private theorem gtop_scaled_point_bound (gtop : Quadrant → ℝ)
    (hthom : ∀ (c : ℝ≥0) (x : Quadrant), gtop (c * x.1, c * x.2) = (c : ℝ) * gtop x)
    (ε δ : ℝ) (ω : Environment) (n k : ℕ) (hnpos : 0 < n)
    (hlp : lastPassage (topField ω) 0 (k, n - k) < (1 - δ) * n)
    (hdev : |lastPassage (topField ω) 0 (k, n - k) -
        gtop ((k : ℝ≥0), ((n - k : ℕ) : ℝ≥0))| ≤ ε * (n : ℝ)) :
    gtop ((k : ℝ≥0) * (n : ℝ≥0)⁻¹, ((n - k : ℕ) : ℝ≥0) * (n : ℝ≥0)⁻¹) ≤ 1 - δ + ε := by
  have hn0 : (n : ℝ≥0) ≠ 0 := by exact_mod_cast hnpos.ne'
  have hscale : ∀ a : ℝ≥0, (n : ℝ≥0) * (a * (n : ℝ≥0)⁻¹) = a := fun a => by
    rw [mul_comm a, ← mul_assoc, mul_inv_cancel₀ hn0, one_mul]
  have hhom : gtop ((n : ℝ≥0) * ((k : ℝ≥0) * (n : ℝ≥0)⁻¹),
      (n : ℝ≥0) * (((n - k : ℕ) : ℝ≥0) * (n : ℝ≥0)⁻¹)) =
      ((n : ℝ≥0) : ℝ) * gtop ((k : ℝ≥0) * (n : ℝ≥0)⁻¹,
        ((n - k : ℕ) : ℝ≥0) * (n : ℝ≥0)⁻¹) :=
    hthom (n : ℝ≥0) ((k : ℝ≥0) * (n : ℝ≥0)⁻¹, ((n - k : ℕ) : ℝ≥0) * (n : ℝ≥0)⁻¹)
  rw [hscale, hscale, NNReal.coe_natCast] at hhom
  have hnR : (0 : ℝ) < n := by exact_mod_cast hnpos
  have hup := (abs_le.1 hdev).1
  have hmul : (n : ℝ) * gtop ((k : ℝ≥0) * (n : ℝ≥0)⁻¹, ((n - k : ℕ) : ℝ≥0) * (n : ℝ≥0)⁻¹) ≤
      (n : ℝ) * (1 - δ + ε) := by linarith
  exact le_of_mul_le_mul_left hmul hnR

/-- The deterministic half of the argument for one environment: if the shape estimate holds
and the passage time to the level-`n` floor point of the direction `(s, 1 - s)` is eventually
below `(1 - δ) n`, then the shape at `(s, 1 - s)` is at most `1 - δ`. -/
private theorem gtop_le_of_eventually_low (gtop : Quadrant → ℝ) (htcont : Continuous gtop)
    (hthom : ∀ (c : ℝ≥0) (x : Quadrant), gtop (c * x.1, c * x.2) = (c : ℝ) * gtop x)
    (s δ : ℝ) (hs₀ : 0 ≤ s) (hs₁ : s ≤ 1) (ω : Environment)
    (hshape : ∀ ε : ℝ, 0 < ε →
      ∃ N : ℕ, 1 ≤ N ∧ ∀ d : ℕ × ℕ, N ≤ d.1 + d.2 →
        |lastPassage (topField ω) 0 d - gtop ((d.1 : ℝ≥0), (d.2 : ℝ≥0))| ≤
          ε * ((d.1 + d.2 : ℕ) : ℝ))
    (hlow : ∀ᶠ n : ℕ in atTop,
      lastPassage (topField ω) 0 (⌊s * (n : ℝ)⌋₊, n - ⌊s * (n : ℝ)⌋₊) < (1 - δ) * n) :
    gtop (toQuadrant (s, 1 - s)) ≤ 1 - δ := by
  refine _root_.le_of_forall_pos_le_add fun ε hε => ?_
  obtain ⟨N, hN1, hN⟩ := hshape ε hε
  have hlim := (htcont.tendsto (toQuadrant (s, 1 - s))).comp (floorPoint_tendsto s hs₀ hs₁)
  refine le_of_tendsto hlim ?_
  filter_upwards [hlow, eventually_ge_atTop N] with n hn hnN
  have hnpos : 0 < n := by omega
  have hle : ⌊s * (n : ℝ)⌋₊ ≤ n :=
    Nat.floor_le_of_le (mul_le_of_le_one_left (Nat.cast_nonneg n) hs₁)
  have hlev : ⌊s * (n : ℝ)⌋₊ + (n - ⌊s * (n : ℝ)⌋₊) = n := by omega
  have h := hN (⌊s * (n : ℝ)⌋₊, n - ⌊s * (n : ℝ)⌋₊) (by
    show N ≤ ⌊s * (n : ℝ)⌋₊ + (n - ⌊s * (n : ℝ)⌋₊)
    omega)
  change |lastPassage (topField ω) 0 (⌊s * (n : ℝ)⌋₊, n - ⌊s * (n : ℝ)⌋₊) -
      gtop ((⌊s * (n : ℝ)⌋₊ : ℝ≥0), ((n - ⌊s * (n : ℝ)⌋₊ : ℕ) : ℝ≥0))| ≤
      ε * ((⌊s * (n : ℝ)⌋₊ + (n - ⌊s * (n : ℝ)⌋₊) : ℕ) : ℝ) at h
  rw [hlev] at h
  exact gtop_scaled_point_bound gtop hthom ε δ ω n _ hnpos hn h

/-- **Top shape below one beyond the edge.** Let the weight law `ν` be at most `1` almost
surely, with `ν {1}` positive and below one. Let `gtop` be a continuous, homogeneous, concave
function on the quadrant that is the almost sure uniform shape of the top passage time.
If the mean half-line edge at some length `L` is below `c L`, then `gtop` is strictly below
`1` at `(s, 1 - s)` for every `s` with `c < s ≤ 1` and `0 ≤ s`.

This is a step in the proof of the flat-edge theorem of Georgiou, Rassoul-Agha and Seppäläinen
(manuscript in preparation). The proof combines the decay estimate at `s' = (c + s) / 2`,
Borel-Cantelli, and the shape hypothesis. Concavity of `gtop` and `ν {1} < 1` are not needed
by the proof. -/
theorem gtop_lt_one_beyond_edge (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hp₀ : 0 < ν {1}) (hp₁ : ν {1} < 1)
    (gtop : Quadrant → ℝ) (htcont : Continuous gtop)
    (hthom : ∀ (c : ℝ≥0) (x : Quadrant), gtop (c * x.1, c * x.2) = (c : ℝ) * gtop x)
    (htconc : ∀ (x y : Quadrant) (r t : ℝ≥0), r + t = 1 →
      (r : ℝ) * gtop x + (t : ℝ) * gtop y ≤ gtop (r * x.1 + t * y.1, r * x.2 + t * y.2))
    (htshape : ∀ᵐ ω ∂environmentLaw ν, ∀ ε : ℝ, 0 < ε →
      ∃ N : ℕ, 1 ≤ N ∧ ∀ d : ℕ × ℕ, N ≤ d.1 + d.2 →
        |lastPassage (topField ω) 0 d - gtop ((d.1 : ℝ≥0), (d.2 : ℝ≥0))| ≤
          ε * ((d.1 + d.2 : ℕ) : ℝ))
    (c : ℝ) (L : ℕ) (hL : 0 < L)
    (hc : ∫ ω, (halfLineEdge ω L : ℝ) ∂environmentLaw ν < c * L)
    (s : ℝ) (hcs : c < s) (hs₀ : 0 ≤ s) (hs₁ : s ≤ 1) :
    gtop (toQuadrant (s, 1 - s)) < 1 := by
  classical
  have _hp₁ := hp₁
  have _htconc := htconc
  -- the intermediate speed
  obtain ⟨s', hcs', hs's⟩ : ∃ s' : ℝ, c < s' ∧ s' < s :=
    ⟨(c + s) / 2, by linarith, by linarith⟩
  obtain ⟨δ, A, B, hδ, hA, hB, hdecay⟩ :=
    top_passage_beyond_edge_decay_total ν hp₀ c L hL hc s' hcs' (by linarith)
  obtain ⟨n₀, hn₀⟩ : ∃ n₀ : ℕ, 1 / (s - s') ≤ n₀ := exists_nat_ge _
  -- the bad events along the direction `(s, 1 - s)`
  obtain ⟨E, hE⟩ : ∃ E : ℕ → Set Environment, ∀ n ω, ω ∈ E n ↔
      (1 - δ) * (((⌊s * (n : ℝ)⌋₊ : ℕ) : ℝ) + ((n - ⌊s * (n : ℝ)⌋₊ : ℕ) : ℝ)) ≤
        lastPassage (topField ω) 0 (⌊s * (n : ℝ)⌋₊, n - ⌊s * (n : ℝ)⌋₊) :=
    ⟨fun n => {ω | (1 - δ) * (((⌊s * (n : ℝ)⌋₊ : ℕ) : ℝ) +
        ((n - ⌊s * (n : ℝ)⌋₊ : ℕ) : ℝ)) ≤
      lastPassage (topField ω) 0 (⌊s * (n : ℝ)⌋₊, n - ⌊s * (n : ℝ)⌋₊)}, fun _ _ => Iff.rfl⟩
  have hbound : ∀ n : ℕ, n₀ ≤ n →
      (environmentLaw ν).real (E n) ≤ A * Real.exp (-(B * (n : ℝ))) := by
    intro n hn
    have hcast := floor_level_cast s hs₁ n
    have hgap : 1 ≤ (n : ℝ) * (s - s') := by
      have h1 : 1 / (s - s') ≤ (n : ℝ) := le_trans hn₀ (by exact_mod_cast hn)
      exact (div_le_iff₀ (sub_pos.2 hs's)).1 h1
    have hfl := Nat.lt_floor_add_one (s * (n : ℝ))
    have hcond : s' * (((⌊s * (n : ℝ)⌋₊ : ℕ) : ℝ) + ((n - ⌊s * (n : ℝ)⌋₊ : ℕ) : ℝ)) ≤
        ((⌊s * (n : ℝ)⌋₊ : ℕ) : ℝ) := by
      rw [hcast]
      nlinarith
    have hmain := hdecay ⌊s * (n : ℝ)⌋₊ (n - ⌊s * (n : ℝ)⌋₊) hcond
    have hEeq : E n = {ω | (1 - δ) * (((⌊s * (n : ℝ)⌋₊ : ℕ) : ℝ) +
        ((n - ⌊s * (n : ℝ)⌋₊ : ℕ) : ℝ)) ≤
        lastPassage (topField ω) 0 (⌊s * (n : ℝ)⌋₊, n - ⌊s * (n : ℝ)⌋₊)} := by
      ext ω
      exact hE n ω
    have hmain' : (environmentLaw ν).real (E n) ≤
        A * Real.exp (-(B * (((⌊s * (n : ℝ)⌋₊ : ℕ) : ℝ) +
          ((n - ⌊s * (n : ℝ)⌋₊ : ℕ) : ℝ)))) := by
      rw [hEeq]
      exact hmain
    rwa [hcast] at hmain'
  -- summability of the bounds
  have hsum_real : Summable (fun n : ℕ => A * Real.exp (-(B * ((n + n₀ : ℕ) : ℝ)))) := by
    have hgeom : Summable (fun n : ℕ => A * Real.exp (-(B * (n : ℝ)))) := by
      have hr : Real.exp (-B) < 1 := by
        have h := Real.exp_lt_exp.2 (show -B < 0 by linarith)
        rwa [Real.exp_zero] at h
      have hs := (summable_geometric_of_lt_one (Real.exp_pos (-B)).le hr).mul_left A
      refine hs.congr fun n => ?_
      have hexp : -(B * (n : ℝ)) = (n : ℝ) * -B := by ring
      rw [hexp, Real.exp_nat_mul]
    exact (summable_nat_add_iff n₀).2 hgeom
  have hsum : ∑' n : ℕ, (environmentLaw ν) (E (n + n₀)) ≠ ∞ := by
    have hle : ∀ n : ℕ, (environmentLaw ν) (E (n + n₀)) ≤
        ENNReal.ofReal (A * Real.exp (-(B * ((n + n₀ : ℕ) : ℝ)))) := by
      intro n
      calc (environmentLaw ν) (E (n + n₀))
          = ENNReal.ofReal ((environmentLaw ν).real (E (n + n₀))) :=
            (ofReal_measureReal (measure_ne_top _ _)).symm
        _ ≤ _ := ENNReal.ofReal_le_ofReal (hbound _ (Nat.le_add_left _ _))
    refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hle)
    rw [← ENNReal.ofReal_tsum_of_nonneg
      (fun n => mul_nonneg hA.le (Real.exp_pos _).le) hsum_real]
    exact ENNReal.ofReal_ne_top
  -- Borel-Cantelli
  have hae1 := ae_eventually_notMem hsum
  have hae2 : ∀ᵐ ω ∂environmentLaw ν, ∀ᶠ n : ℕ in atTop,
      lastPassage (topField ω) 0 (⌊s * (n : ℝ)⌋₊, n - ⌊s * (n : ℝ)⌋₊) < (1 - δ) * n := by
    filter_upwards [hae1] with ω hω
    obtain ⟨m, hm⟩ := eventually_atTop.1 hω
    refine eventually_atTop.2 ⟨m + n₀, fun n hn => ?_⟩
    have h := hm (n - n₀) (by omega)
    have hn' : n - n₀ + n₀ = n := by omega
    rw [hn'] at h
    refine not_le.1 (fun h' => h ((hE n ω).2 ?_))
    rw [floor_level_cast s hs₁ n]
    exact h'
  obtain ⟨ω, hω1, hω2⟩ := (hae2.and htshape).exists
  have hfinal := gtop_le_of_eventually_low gtop htcont hthom s δ hs₀ hs₁ ω hω2 hω1
  linarith

end LPPDifferentiability
