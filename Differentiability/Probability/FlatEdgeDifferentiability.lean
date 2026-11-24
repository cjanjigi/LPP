/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Differentiability.Model.OrientedPercolation
public import LPP_Foundations.Frozen.Model.LastPassage
public import LPP_Foundations.Frozen.Model.EnvironmentLaw
public import LPP_Foundations.Frozen.Analysis.QuadrantExtension
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Differentiability.Analysis.FlatEdgeProfile
import Differentiability.Probability.FlatEdgeStartPoint
import Differentiability.Probability.AugmentedExpectation
import Differentiability.Probability.HalfLineEdge
import Differentiability.Probability.TriangleProbability
import Differentiability.Probability.StartSetDeviation
import Differentiability.Probability.FlatShapeAdapters
import LPP_Foundations.Probability.EnvironmentLaw
import Differentiability.Model.OrientedPercolationLaws
import Mathlib.Tactic

/-!
# Differentiability of the shape at the edges of the flat segment

The weights are at most `1`, the top weight `1` has mass in `(0, 1)`, `β` is the infimum of
the expected half-line edge rates, `1/2 ≤ β < 1`, and `ḡ = 1` on `[1 - β, β]`. Then the
quadrant extension of the shape is differentiable at `(β, 1 - β)` and `(1 - β, β)`.

For each `T`, with the triangle floor `c₀` and `ρ_T` the triangle probability, the augmented
process gives `ḡ(β + ρ_T) ≥ 1 - (1 - c₀) ρ_T / T` (`flatEdge_goal_bound` below). Its proof
combines the start point of `Probability/FlatEdgeStartPoint.lean`, Markov's inequality for the
plain edge, the expected count and edge gain of the augmented process, the bound on the maximal
positive deviation over start points, and the supporting line of
`Analysis/FlatEdgeProfile.lean`. Since `ρ_T > 0` and `ρ_T → 0`, this is the chord bound that
`differentiableAt_flat_edges_of_chord_bound` turns into differentiability.

## Main results

- `differentiableAt_flat_segment_endpoints_of_expected_edge_rate`: differentiability of the
  quadrant extension at the two endpoints of the flat segment.

## References

- Georgiou, Rassoul-Agha and Seppäläinen (manuscript in preparation), the edge-differentiability
  theorem.
- C. Janjigian, F. Rassoul-Agha and T. Seppäläinen, *Differentiability of the shape function in
  the planar corner growth model*, parts `flat:b` and `flat:c` of Theorem `thm:flat-top`.
-/

public section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal

namespace LPPDifferentiability

/-- The maximal positive deviation over the start points `(-k, k)`, `k ≤ C N`, and the
displacements `(i, N - i)` (the same expression as the `let` of
`expected_max_positive_deviation_startSet`). -/
private noncomputable def startDeviation (g : Quadrant → ℝ) (C N : ℕ) (ω : Environment) : ℝ :=
  ⨆ (k : Fin (C * N + 1)) (i : Fin (N + 1)),
    max (lastPassage ω (-(k : ℤ), (k : ℤ)) ((i : ℕ), N - i) - ω (-(k : ℤ), (k : ℤ)) +
      ω ((-(k : ℤ), (k : ℤ)) + (((i : ℕ) : ℤ), ((N - i : ℕ) : ℤ))) -
      g (((i : ℕ) : ℝ≥0), ((N - i : ℕ) : ℝ≥0))) 0

/-- The deviation is a supremum of positive parts, hence nonnegative. -/
private theorem startDeviation_nonneg (g : Quadrant → ℝ) (C N : ℕ) (ω : Environment) :
    0 ≤ startDeviation g C N ω :=
  le_ciSup_of_le (Set.finite_range _).bddAbove ⟨0, Nat.succ_pos _⟩
    (le_ciSup_of_le (Set.finite_range _).bddAbove ⟨0, Nat.succ_pos _⟩ (le_max_right _ _))

/-- The deviation variable is integrable, and `o(N)` in mean. -/
private theorem startDeviation_laws (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hle : ∀ᵐ t ∂ν, t ≤ 1)
    (hneg : ∃ pneg : ℝ, 1 < pneg ∧
      (∫⁻ t, ENNReal.ofReal ((max (-t) 0) ^ pneg) ∂ν) < ∞)
    (g : Quadrant → ℝ) (hgcont : Continuous g)
    (hghom : ∀ (c : ℝ≥0) (x : Quadrant), g (c * x.1, c * x.2) = (c : ℝ) * g x)
    (hgconc : ∀ (x y : Quadrant) (r t : ℝ≥0), r + t = 1 →
      (r : ℝ) * g x + (t : ℝ) * g y ≤ g (r * x.1 + t * y.1, r * x.2 + t * y.2))
    (hgshape : ∀ᵐ ω ∂environmentLaw ν, ∀ ε : ℝ, 0 < ε →
      ∃ N : ℕ, 1 ≤ N ∧ ∀ d : ℕ × ℕ, N ≤ d.1 + d.2 →
        |lastPassage ω 0 d - g ((d.1 : ℝ≥0), (d.2 : ℝ≥0))| ≤
          ε * ((d.1 + d.2 : ℕ) : ℝ))
    (C : ℕ) :
    (∀ N : ℕ, Integrable (startDeviation g C N) (environmentLaw ν)) ∧
      Tendsto (fun N : ℕ => (∫ ω, startDeviation g C N ω ∂environmentLaw ν) / N) atTop
        (𝓝 0) :=
  expected_max_positive_deviation_startSet ν hle hneg g hgcont hghom hgconc hgshape C

/-- The chord bound at `β + ρ_T`: for `T ≥ 1`, `c₀ ≤ 1`, `ρ_T > 0` and `β + ρ_T < 1`,
`ḡ(β + ρ_T) ≥ 1 - (1 - c₀) ρ_T / T`. -/
private theorem flatEdge_goal_bound (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hle : ∀ᵐ t ∂ν, t ≤ 1) (hp₀ : 0 < ν {1})
    (hneg : ∃ pneg : ℝ, 1 < pneg ∧
      (∫⁻ t, ENNReal.ofReal ((max (-t) 0) ^ pneg) ∂ν) < ∞)
    (g : Quadrant → ℝ) (hgcont : Continuous g)
    (hghom : ∀ (c : ℝ≥0) (x : Quadrant), g (c * x.1, c * x.2) = (c : ℝ) * g x)
    (hgconc : ∀ (x y : Quadrant) (r t : ℝ≥0), r + t = 1 →
      (r : ℝ) * g x + (t : ℝ) * g y ≤ g (r * x.1 + t * y.1, r * x.2 + t * y.2))
    (hgshape : ∀ᵐ ω ∂environmentLaw ν, ∀ ε : ℝ, 0 < ε →
      ∃ N : ℕ, 1 ≤ N ∧ ∀ d : ℕ × ℕ, N ≤ d.1 + d.2 →
        |lastPassage ω 0 d - g ((d.1 : ℝ≥0), (d.2 : ℝ≥0))| ≤
          ε * ((d.1 + d.2 : ℕ) : ℝ))
    (β : ℝ) (hβ₀ : 0 ≤ β)
    (hβ : IsGLB (Set.range fun n : ℕ =>
      (∫ ω, (halfLineEdge ω (n + 1) : ℝ) ∂environmentLaw ν) / ((n : ℝ) + 1)) β)
    (hβval : quadrantExtension g (β, 1 - β) = 1)
    (hgle : ∀ y ∈ Icc (0 : ℝ) 1, quadrantExtension g (y, 1 - y) ≤ 1)
    (T : ℕ) (hT : 1 ≤ T) (c₀ : ℝ) (hc₀ : c₀ ≤ 1)
    (hρ : 0 < (environmentLaw ν).real {ω | IsTriangle ω T c₀ 0})
    (hβρ : β + (environmentLaw ν).real {ω | IsTriangle ω T c₀ 0} < 1) :
    1 - (1 - c₀) * (environmentLaw ν).real {ω | IsTriangle ω T c₀ 0} / T ≤
      quadrantExtension g (β + (environmentLaw ν).real {ω | IsTriangle ω T c₀ 0},
        1 - (β + (environmentLaw ν).real {ω | IsTriangle ω T c₀ 0})) := by
  obtain ⟨ρ, hρdef⟩ : ∃ ρ, (environmentLaw ν).real {ω | IsTriangle ω T c₀ 0} = ρ := ⟨_, rfl⟩
  rw [hρdef] at hρ hβρ ⊢
  have hT0 : (T : ℝ) ≠ 0 := by
    have : (0 : ℝ) < T := by exact_mod_cast hT
    exact this.ne'
  -- The supporting line at `p = β + ρ`, with slope `σ ≤ 0`.
  obtain ⟨σ, hσ, hsupp⟩ := exists_nonpos_supporting_line_of_flat_edge g hgconc β (β + ρ) hβ₀
    (by linarith) hβρ hβval hgle
  obtain ⟨gp, hgpdef⟩ : ∃ gp, quadrantExtension g (β + ρ, 1 - (β + ρ)) = gp := ⟨_, rfl⟩
  obtain ⟨q1, hq1def⟩ : ∃ q, quadrantExtension g (1, 1 - 1) = q := ⟨_, rfl⟩
  rw [hgpdef] at hsupp ⊢
  have hq1 : q1 ≤ 1 := by
    rw [← hq1def]
    exact hgle 1 ⟨zero_le_one, le_rfl⟩
  have hs1 : q1 ≤ gp + σ * (1 - (β + ρ)) := by
    rw [← hq1def]
    exact hsupp 1 ⟨zero_le_one, le_rfl⟩
  -- The integrated inequality, for every `n, C ≥ 1` (with `N = n T`).
  have hstar : ∀ n C : ℕ, 1 ≤ n → 1 ≤ C →
      ((n * T : ℕ) : ℝ) * (1 - (1 - c₀) * ρ / T) -
          (∫ ω, startDeviation g C (n * T) ω ∂environmentLaw ν) -
          (1 - q1) * ((1 - β) * ((n * T : ℕ) : ℝ) / C) ≤ ((n * T : ℕ) : ℝ) * gp := by
    intro n C hn hC
    obtain ⟨N, hN⟩ : ∃ N, N = n * T := ⟨_, rfl⟩
    rw [← hN]
    have hN1 : 1 ≤ N := by
      rw [hN]
      exact Nat.mul_le_mul hn hT
    have hNpos : (0 : ℝ) < N := by exact_mod_cast hN1
    have hNr : (N : ℝ) = n * T := by rw [hN, Nat.cast_mul]
    have hnT : (n : ℝ) = N / T := by rw [eq_div_iff hT0, hNr]
    have hCpos : (0 : ℝ) < C := by exact_mod_cast hC
    -- Expectations: the count and the edge gain, the plain edge, and the deviation.
    obtain ⟨hKint, hKval⟩ := integral_augmented_count ν hp₀ T hT c₀ n
    obtain ⟨hGint, hGval⟩ := integral_augmented_edge_gain ν hp₀ T hT c₀ n
    rw [← hN] at hGint hGval
    rw [hρdef] at hKval hGval
    have haint := integrable_halfLineEdge ν hp₀ N
    have hDint := (startDeviation_laws ν hle hneg g hgcont hghom hgconc hgshape C).1 N
    have hMint : Integrable
        (fun ω => (maxFirst (augmentedProcess ω T c₀ antidiagHalfLine n n).1 : ℝ))
        (environmentLaw ν) :=
      (hGint.add haint).congr (ae_of_all _ fun ω => by simp)
    -- `E a⁰_N ≥ β N`, from the infimum.
    have hβa : β * N ≤ ∫ ω, (halfLineEdge ω N : ℝ) ∂environmentLaw ν := by
      have hb : β ≤ (∫ ω, (halfLineEdge ω (N - 1 + 1) : ℝ) ∂environmentLaw ν) /
          (((N - 1 : ℕ) : ℝ) + 1) := hβ.1 (Set.mem_range_self (N - 1))
      rw [Nat.sub_add_cancel hN1] at hb
      have hc : ((N - 1 : ℕ) : ℝ) + 1 = N := by
        rw [Nat.cast_sub hN1, Nat.cast_one, sub_add_cancel]
      rw [hc, le_div_iff₀ hNpos] at hb
      exact hb
    -- The almost sure bound, with the supporting line and the Markov form of the bad event,
    -- as one linear inequality between integrable functions.
    have hpt : ∀ᵐ ω ∂environmentLaw ν,
        (N : ℝ) - (1 - q1) * (N / C) +
            ((c₀ - 1) * ((augmentedProcess ω T c₀ antidiagHalfLine n n).2 : ℝ) +
              ((1 - q1) / C * (halfLineEdge ω N : ℝ) - startDeviation g C N ω)) ≤
          ((N : ℝ) * gp - σ * ((β + ρ) * N)) +
            σ * (maxFirst (augmentedProcess ω T c₀ antidiagHalfLine n n).1 : ℝ) := by
      filter_upwards [ae_exists_flatEdge_startPoint_bound ν hp₀ g hghom T hT c₀ hc₀ n hn C N
        hN] with ω hω
      obtain ⟨y, hy, hMy, hgood⟩ := hω
      have hgood' : (N : ℝ) - halfLineEdge ω N ≤ C * N →
          (N : ℝ) + ((augmentedProcess ω T c₀ antidiagHalfLine n n).2 : ℝ) * (c₀ - 1) -
            startDeviation g C N ω ≤ N * quadrantExtension g (y, 1 - y) := hgood
      have hD0 := startDeviation_nonneg g C N ω
      have hK0 : (0 : ℝ) ≤ ((augmentedProcess ω T c₀ antidiagHalfLine n n).2 : ℝ) :=
        Nat.cast_nonneg _
      have ha_le : (halfLineEdge ω N : ℝ) ≤ N := by exact_mod_cast halfLineEdge_le ω N
      have hNy : (N : ℝ) * quadrantExtension g (y, 1 - y) ≤ N * (gp + σ * (y - (β + ρ))) :=
        mul_le_mul_of_nonneg_left (hsupp y hy) hNpos.le
      have hN1' : (N : ℝ) * q1 ≤ N * (gp + σ * (1 - (β + ρ))) :=
        mul_le_mul_of_nonneg_left hs1 hNpos.le
      have hyN : y * N ≤ N := by nlinarith [hy.2]
      have hσy : σ * (y * N - (β + ρ) * N) ≤
          σ * ((maxFirst (augmentedProcess ω T c₀ antidiagHalfLine n n).1 : ℝ) -
            (β + ρ) * N) :=
        mul_le_mul_of_nonpos_left (by linarith) hσ
      have hσ1 : σ * (N - (β + ρ) * N) ≤
          σ * ((maxFirst (augmentedProcess ω T c₀ antidiagHalfLine n n).1 : ℝ) -
            (β + ρ) * N) :=
        mul_le_mul_of_nonpos_left (by linarith) hσ
      have hid : (1 - q1) * ((N : ℝ) / C) - (1 - q1) / C * (halfLineEdge ω N : ℝ) =
          (1 - q1) * (((N : ℝ) - halfLineEdge ω N) / C) := by ring
      by_cases hG : (N : ℝ) - halfLineEdge ω N ≤ C * N
      -- Good event: the start point and the supporting line at `y`.
      · have h := hgood' hG
        have hw : 0 ≤ (1 - q1) * (((N : ℝ) - halfLineEdge ω N) / C) :=
          mul_nonneg (by linarith) (div_nonneg (by linarith) hCpos.le)
        linarith
      -- Bad event: the Markov term is at least `(1 - ḡ(1)) N`; the supporting line at `1`.
      · rw [not_le] at hG
        have hw : (1 - q1) * (N : ℝ) ≤ (1 - q1) * (((N : ℝ) - halfLineEdge ω N) / C) :=
          mul_le_mul_of_nonneg_left (le_of_lt ((lt_div_iff₀ hCpos).mpr (by linarith)))
            (by linarith)
        have hKc : (c₀ - 1) * ((augmentedProcess ω T c₀ antidiagHalfLine n n).2 : ℝ) ≤ 0 := by
          nlinarith
        linarith
    -- Integrate.
    have hKc : Integrable
        (fun ω => (c₀ - 1) * ((augmentedProcess ω T c₀ antidiagHalfLine n n).2 : ℝ))
        (environmentLaw ν) := hKint.const_mul _
    have hac : Integrable (fun ω => (1 - q1) / C * (halfLineEdge ω N : ℝ))
        (environmentLaw ν) := haint.const_mul _
    have haD : Integrable
        (fun ω => (1 - q1) / C * (halfLineEdge ω N : ℝ) - startDeviation g C N ω)
        (environmentLaw ν) := hac.sub hDint
    have hKaD : Integrable
        (fun ω => (c₀ - 1) * ((augmentedProcess ω T c₀ antidiagHalfLine n n).2 : ℝ) +
          ((1 - q1) / C * (halfLineEdge ω N : ℝ) - startDeviation g C N ω))
        (environmentLaw ν) := hKc.add haD
    have hσM : Integrable
        (fun ω => σ * (maxFirst (augmentedProcess ω T c₀ antidiagHalfLine n n).1 : ℝ))
        (environmentLaw ν) := hMint.const_mul σ
    have hLint : Integrable
        (fun ω => (N : ℝ) - (1 - q1) * (N / C) +
          ((c₀ - 1) * ((augmentedProcess ω T c₀ antidiagHalfLine n n).2 : ℝ) +
            ((1 - q1) / C * (halfLineEdge ω N : ℝ) - startDeviation g C N ω)))
        (environmentLaw ν) := (integrable_const ((N : ℝ) - (1 - q1) * (N / C))).add hKaD
    have hRint : Integrable
        (fun ω => ((N : ℝ) * gp - σ * ((β + ρ) * N)) +
          σ * (maxFirst (augmentedProcess ω T c₀ antidiagHalfLine n n).1 : ℝ))
        (environmentLaw ν) := (integrable_const ((N : ℝ) * gp - σ * ((β + ρ) * N))).add hσM
    have hmono := integral_mono_ae hLint hRint hpt
    rw [integral_add (integrable_const _) hKaD, integral_add hKc haD, integral_sub hac hDint,
      integral_const_mul, integral_const_mul, integral_add (integrable_const _) hσM,
      integral_const_mul, integral_const, integral_const, probReal_univ, one_smul,
      one_smul] at hmono
    rw [integral_sub hMint haint] at hGval
    -- Use `E M_n ≥ (β + ρ) N` and `σ ≤ 0`.
    have hρN : ρ * N = n * T * ρ := by rw [hNr]; ring
    have hσint : σ * (∫ ω, (maxFirst (augmentedProcess ω T c₀ antidiagHalfLine n n).1 : ℝ)
        ∂environmentLaw ν) ≤ σ * ((β + ρ) * N) :=
      mul_le_mul_of_nonpos_left (by linarith) hσ
    have hac' : (1 - q1) / C * (β * N) ≤
        (1 - q1) / C * ∫ ω, (halfLineEdge ω N : ℝ) ∂environmentLaw ν :=
      mul_le_mul_of_nonneg_left hβa (div_nonneg (by linarith) hCpos.le)
    have hK2 : (c₀ - 1) * ∫ ω, ((augmentedProcess ω T c₀ antidiagHalfLine n n).2 : ℝ)
        ∂environmentLaw ν = (c₀ - 1) * ρ * (N / T) := by
      rw [hKval, hnT]
      ring
    have hA : (N : ℝ) * (1 - (1 - c₀) * ρ / T) = N + (c₀ - 1) * ρ * (N / T) := by ring
    have hq : (1 - q1) * ((N : ℝ) / C) - (1 - q1) / C * (β * N) =
        (1 - q1) * ((1 - β) * N / C) := by ring
    linarith
  -- Let `C` and then `n` grow (explicit `δ`-argument).
  refine le_of_forall_pos_lt_add fun δ hδ => ?_
  obtain ⟨C₀, hC₀⟩ := exists_nat_gt ((1 - q1) * (1 - β) * 2 / δ)
  have hC1 : 1 ≤ C₀ + 1 := Nat.le_add_left 1 C₀
  have hCpos : (0 : ℝ) < ((C₀ + 1 : ℕ) : ℝ) := by positivity
  have hB : (1 - q1) * (1 - β) / ((C₀ + 1 : ℕ) : ℝ) < δ / 2 := by
    rw [div_lt_iff₀ hCpos]
    rw [div_lt_iff₀ hδ] at hC₀
    push_cast
    nlinarith
  obtain ⟨_, hDlim⟩ := startDeviation_laws ν hle hneg g hgcont hghom hgconc hgshape (C₀ + 1)
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp (hDlim.eventually (Iio_mem_nhds (half_pos hδ)))
  have hn1 : 1 ≤ N₀ + 1 := Nat.le_add_left 1 N₀
  have hle' : N₀ ≤ (N₀ + 1) * T := le_trans (Nat.le_succ N₀) (Nat.le_mul_of_pos_right _ hT)
  have hlt : (∫ ω, startDeviation g (C₀ + 1) ((N₀ + 1) * T) ω ∂environmentLaw ν) /
      (((N₀ + 1) * T : ℕ) : ℝ) < δ / 2 := hN₀ _ hle'
  have hS := hstar (N₀ + 1) (C₀ + 1) hn1 hC1
  obtain ⟨N, hN⟩ : ∃ N, N = (N₀ + 1) * T := ⟨_, rfl⟩
  rw [← hN] at hlt hS
  have hNpos : (0 : ℝ) < N := by
    rw [hN]
    exact_mod_cast (Nat.mul_pos (Nat.succ_pos N₀) hT : 0 < (N₀ + 1) * T)
  rw [div_lt_iff₀ hNpos] at hlt
  have hB' : (1 - q1) * ((1 - β) * N / ((C₀ + 1 : ℕ) : ℝ)) < N * (δ / 2) := by
    calc (1 - q1) * ((1 - β) * N / ((C₀ + 1 : ℕ) : ℝ)) =
        N * ((1 - q1) * (1 - β) / ((C₀ + 1 : ℕ) : ℝ)) := by ring
      _ < N * (δ / 2) := mul_lt_mul_of_pos_left hB hNpos
  refine lt_of_mul_lt_mul_left ?_ hNpos.le
  linarith

/-- **Differentiability at the edges of the flat segment** (the edge-differentiability theorem of
Georgiou, Rassoul-Agha and Seppäläinen, corresponding to the endpoint conclusions of
parts `flat:b` and `flat:c` of Theorem `thm:flat-top` of the differentiability paper).
Let the weights be at most `1` with `0 < ν {1} < 1` and a finite negative moment of order
above one. Let `g` be the shape of `ν` (continuous, homogeneous, concave, uniform shape law)
and let `β` be the infimum of the expected half-line edge rates `E a_{n+1} / (n + 1)`.
If `1/2 ≤ β < 1` and
`g (t, 1 - t) = 1` on `[1 - β, β]`, the quadrant extension of `g` is differentiable at
`(β, 1 - β)` and `(1 - β, β)`. -/
theorem differentiableAt_flat_segment_endpoints_of_expected_edge_rate
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hle : ∀ᵐ t ∂ν, t ≤ 1) (hp₀ : 0 < ν {1}) (hp₁ : ν {1} < 1)
    (hneg : ∃ pneg : ℝ, 1 < pneg ∧
      (∫⁻ t, ENNReal.ofReal ((max (-t) 0) ^ pneg) ∂ν) < ∞)
    (g : Quadrant → ℝ) (hgcont : Continuous g)
    (hghom : ∀ (c : ℝ≥0) (x : Quadrant), g (c * x.1, c * x.2) = (c : ℝ) * g x)
    (hgconc : ∀ (x y : Quadrant) (r t : ℝ≥0), r + t = 1 →
      (r : ℝ) * g x + (t : ℝ) * g y ≤ g (r * x.1 + t * y.1, r * x.2 + t * y.2))
    (hgshape : ∀ᵐ ω ∂environmentLaw ν, ∀ ε : ℝ, 0 < ε →
      ∃ N : ℕ, 1 ≤ N ∧ ∀ d : ℕ × ℕ, N ≤ d.1 + d.2 →
        |lastPassage ω 0 d - g ((d.1 : ℝ≥0), (d.2 : ℝ≥0))| ≤
          ε * ((d.1 + d.2 : ℕ) : ℝ))
    (β : ℝ) (hβhalf : 1 / 2 ≤ β) (hβone : β < 1)
    (hβ : IsGLB (Set.range fun n : ℕ =>
      (∫ ω, (halfLineEdge ω (n + 1) : ℝ) ∂environmentLaw ν) / ((n : ℝ) + 1)) β)
    (hflat : ∀ t ∈ Icc (1 - β) β, g (toQuadrant (t, 1 - t)) = 1) :
    DifferentiableAt ℝ (quadrantExtension g) (β, 1 - β) ∧
      DifferentiableAt ℝ (quadrantExtension g) (1 - β, β) := by
  -- The symmetry `g (s, t) = g (t, s)` and the bound `ḡ ≤ 1`.
  have hswap : ∀ x : Quadrant, g (x.2, x.1) = g x :=
    shape_swap_of_coordinatewise_field ν id measurable_id g hgcont hghom hgshape
  have hgle : ∀ y ∈ Icc (0 : ℝ) 1, quadrantExtension g (y, 1 - y) ≤ 1 := by
    intro y hy
    have h := (expected_floor_limit_of_shape_block ν hle hneg g hgcont hghom hgconc
      hgshape).2.2 (toQuadrant (y, 1 - y))
    have e1 : ((toQuadrant (y, 1 - y)).1 : ℝ) = y := Real.coe_toNNReal y hy.1
    have e2 : ((toQuadrant (y, 1 - y)).2 : ℝ) = 1 - y :=
      Real.coe_toNNReal (1 - y) (by linarith [hy.2])
    show g (toQuadrant (y, 1 - y)) ≤ 1
    linarith
  have hβ₀ : 0 ≤ β := by linarith
  have hβval : quadrantExtension g (β, 1 - β) = 1 := hflat β ⟨by linarith, le_rfl⟩
  -- The triangle floor `c₀` and the triangle probabilities `ρ_T`.
  obtain ⟨c₀, hc₀, hc₀pos⟩ := exists_triangle_floor ν hp₁ hle
  have hb : 0 < ν.real (Ico c₀ 1) := by
    rw [measureReal_def]
    exact ENNReal.toReal_pos hc₀pos.ne' (measure_ne_top _ _)
  have hc : 0 < ν.real {1} := by
    rw [measureReal_def]
    exact ENNReal.toReal_pos hp₀.ne' (measure_ne_top _ _)
  have ha : 0 < ν.real (Iio 1) := lt_of_lt_of_le hb (measureReal_mono fun x hx => hx.2)
  have hb1 : ν.real (Ico c₀ 1) ≤ 1 := (measureReal_mono (subset_univ _)).trans_eq probReal_univ
  have hc1 : ν.real {1} ≤ 1 := (measureReal_mono (subset_univ _)).trans_eq probReal_univ
  have ha1 : ν.real (Iio 1) < 1 := by
    have hu : ν.real (Iio 1 ∪ {1}) = ν.real (Iio 1) + ν.real {1} :=
      measureReal_union (Set.disjoint_singleton_right.mpr (lt_irrefl (1 : ℝ)))
        (measurableSet_singleton 1)
    have hle1 : ν.real (Iio 1 ∪ {1}) ≤ 1 :=
      (measureReal_mono (subset_univ _)).trans_eq probReal_univ
    linarith
  have hρpos : ∀ T : ℕ, 1 ≤ T → 0 < (environmentLaw ν).real {ω | IsTriangle ω T c₀ 0} := by
    intro T hT
    rw [triangle_probability ν T hT c₀ 0]
    exact mul_pos (mul_pos (pow_pos ha T) hb) (pow_pos hc _)
  have hρle : ∀ T : ℕ, 1 ≤ T →
      (environmentLaw ν).real {ω | IsTriangle ω T c₀ 0} ≤ ν.real (Iio 1) ^ T := by
    intro T hT
    rw [triangle_probability ν T hT c₀ 0]
    calc ν.real (Iio 1) ^ T * ν.real (Ico c₀ 1) * ν.real {1} ^ (T * (T + 1) / 2 - 1)
        ≤ ν.real (Iio 1) ^ T * ν.real (Ico c₀ 1) * 1 :=
          mul_le_mul_of_nonneg_left (pow_le_one₀ hc.le hc1)
            (mul_nonneg (pow_nonneg ha.le _) hb.le)
      _ ≤ ν.real (Iio 1) ^ T := by
          rw [mul_one]
          exact mul_le_of_le_one_right (pow_nonneg ha.le _) hb1
  -- `ρ_T → 0`.
  have hlim : Tendsto (fun T : ℕ => ν.real (Iio 1) ^ T) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one ha.le ha1
  -- The chord bound: for `ε > 0` take `T` large and `h = ρ_T`.
  have hchord : ∀ ε : ℝ, 0 < ε → ∃ h : ℝ, 0 < h ∧ h ≤ 1 - β ∧
      1 - ε * h ≤ quadrantExtension g (β + h, 1 - β - h) := by
    intro ε hε
    obtain ⟨T₀, hT₀⟩ := eventually_atTop.mp
      (hlim.eventually (Iio_mem_nhds (show (0 : ℝ) < 1 - β by linarith)))
    obtain ⟨T₁, hT₁⟩ := exists_nat_gt ((1 - c₀) / ε)
    obtain ⟨T, hTdef⟩ : ∃ T, T = max (max T₀ T₁) 1 := ⟨_, rfl⟩
    have hT : 1 ≤ T := by
      rw [hTdef]
      exact le_max_right _ _
    have hTT₀ : T₀ ≤ T := by
      rw [hTdef]
      exact le_trans (le_max_left T₀ T₁) (le_max_left _ 1)
    have hTT₁ : T₁ ≤ T := by
      rw [hTdef]
      exact le_trans (le_max_right T₀ T₁) (le_max_left _ 1)
    have hTpos : (0 : ℝ) < T := by exact_mod_cast hT
    have hsmall : ν.real (Iio 1) ^ T < 1 - β := hT₀ T hTT₀
    have hρ := hρpos T hT
    have hρ' := hρle T hT
    have hkey := flatEdge_goal_bound ν hle hp₀ hneg g hgcont hghom hgconc hgshape β hβ₀ hβ
      hβval hgle T hT c₀ hc₀.le hρ (by linarith)
    obtain ⟨ρ, hρdef⟩ : ∃ ρ, (environmentLaw ν).real {ω | IsTriangle ω T c₀ 0} = ρ :=
      ⟨_, rfl⟩
    rw [hρdef] at hρ hρ' hkey
    refine ⟨ρ, hρ, by linarith, ?_⟩
    have e : 1 - β - ρ = 1 - (β + ρ) := by ring
    rw [e]
    have hεT : (1 - c₀) / T < ε := by
      rw [div_lt_iff₀ hTpos]
      rw [div_lt_iff₀ hε] at hT₁
      have h1 : (T₁ : ℝ) ≤ T := by exact_mod_cast hTT₁
      have h2 : (T₁ : ℝ) * ε ≤ T * ε := mul_le_mul_of_nonneg_right h1 hε.le
      linarith
    have hmul : (1 - c₀) * ρ / T ≤ ε * ρ := by
      calc (1 - c₀) * ρ / T = (1 - c₀) / T * ρ := by ring
        _ ≤ ε * ρ := mul_le_mul_of_nonneg_right hεT.le hρ.le
    linarith
  exact differentiableAt_flat_edges_of_chord_bound g hghom hgconc hswap β hβhalf hβone hflat
    hchord

/-- Compatibility name for `differentiableAt_flat_segment_endpoints_of_expected_edge_rate`. -/
alias gbar_differentiableAt_edge_route_h :=
  differentiableAt_flat_segment_endpoints_of_expected_edge_rate

end LPPDifferentiability
