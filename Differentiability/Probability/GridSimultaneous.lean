/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Differentiability.Probability.GridGoodEvent
public import Differentiability.Analysis.GridFineCount
public import Martin2004.Probability.ShapeAboveMean
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# The simultaneous grid event (Lemma 5.7 (i) and (ii))

Lemma 5.7 (i) and (ii) of the differentiability preprint, with the helper estimates for the union
bound (5.31) and the sum over scales (5.32).

## References

* C. Janjigian, F. Rassoul-Agha and T. Seppäläinen, *Differentiability of the shape function in the
  planar corner growth model*, preprint, Lemma 5.7 and (5.31)-(5.33).
-/

public section

open MeasureTheory Filter Topology Set
open scoped NNReal ENNReal

namespace LPPDifferentiability

/-- The measure of a union over scales, grid levels and bins is at most the sum of the
per-triple bounds ((5.31) of the differentiability preprint). No measurability is needed. -/
private theorem union_measure_le (ν : Measure Environment) [IsFiniteMeasure ν] (J jstar : ℕ)
    (S H : ℕ → Finset ℤ) (Bad : ℕ → ℤ → ℤ → Set Environment) (q : ℕ → ℝ)
    (hq : ∀ j ∈ Finset.Icc J jstar, ∀ I ∈ S j, ∀ h ∈ H j, ν.real (Bad j I h) ≤ q j) :
    ν.real (⋃ j ∈ Finset.Icc J jstar, ⋃ I ∈ S j, ⋃ h ∈ H j, Bad j I h) ≤
      ∑ j ∈ Finset.Icc J jstar, ((S j).card : ℝ) * ((H j).card : ℝ) * q j := by
  refine (measureReal_biUnion_finset_le _ _).trans (Finset.sum_le_sum fun j hj => ?_)
  refine (measureReal_biUnion_finset_le _ _).trans ?_
  calc ∑ I ∈ S j, ν.real (⋃ h ∈ H j, Bad j I h) ≤ ∑ _I ∈ S j, ((H j).card : ℝ) * q j := by
        refine Finset.sum_le_sum fun I hI => ?_
        refine (measureReal_biUnion_finset_le _ _).trans ?_
        calc ∑ h ∈ H j, ν.real (Bad j I h) ≤ ∑ _h ∈ H j, q j :=
              Finset.sum_le_sum fun h hh => hq j hj I hI h hh
          _ = ((H j).card : ℝ) * q j := by rw [Finset.sum_const, nsmul_eq_mul]
    _ = ((S j).card : ℝ) * ((H j).card : ℝ) * q j := by
        rw [Finset.sum_const, nsmul_eq_mul, mul_assoc]

open scoped Classical in
/-- Equation (5.32) of the differentiability preprint: the sum over scales splits into the crossing
failures at coarse scales and the bad staircases at coarse and fine scales. -/
private theorem scale_sum_le {J jstar k m : ℕ} {c C q0 p : ℝ} (hC : 0 ≤ C)
    (S H : ℕ → Finset ℤ) (q : ℕ → ℝ)
    (hcard : ∀ j ∈ Finset.Icc J jstar, ((S j).card : ℝ) * ((H j).card : ℝ) ≤ C * 2 ^ (5 * j))
    (hq : ∀ j ∈ Finset.Icc J jstar, 0 ≤ q j)
    (hqc : ∀ j ∈ (Finset.Icc J jstar).filter
        (fun j : ℕ => 8 * (c * (j : ℝ) ^ 2 * 2 ^ (k - j)) ≤ (2 : ℝ) ^ (m - 4 * j - 1)),
      q j ≤ Real.exp (-(q0 * (j : ℝ) ^ 2)) + p * (60 * (j : ℝ) ^ 2 * ((2 : ℝ) ^ (k - j)) ^ 2))
    (hqf : ∀ j ∈ (Finset.Icc J jstar).filter
        (fun j : ℕ => ¬ 8 * (c * (j : ℝ) ^ 2 * 2 ^ (k - j)) ≤ (2 : ℝ) ^ (m - 4 * j - 1)),
      q j ≤ p * (9 * c * (j : ℝ) ^ 2 * ((2 : ℝ) ^ (k - j)) ^ 2)) :
    ∑ j ∈ Finset.Icc J jstar, ((S j).card : ℝ) * ((H j).card : ℝ) * q j ≤
      C * (∑ j ∈ (Finset.Icc J jstar).filter
        (fun j : ℕ => 8 * (c * (j : ℝ) ^ 2 * 2 ^ (k - j)) ≤ (2 : ℝ) ^ (m - 4 * j - 1)),
          (2 : ℝ) ^ (5 * j) * Real.exp (-(q0 * (j : ℝ) ^ 2))) +
      C * p * ((∑ j ∈ (Finset.Icc J jstar).filter
        (fun j : ℕ => 8 * (c * (j : ℝ) ^ 2 * 2 ^ (k - j)) ≤ (2 : ℝ) ^ (m - 4 * j - 1)),
          60 * (j : ℝ) ^ 2 * 2 ^ (5 * j) * ((2 : ℝ) ^ (k - j)) ^ 2) +
        (∑ j ∈ (Finset.Icc J jstar).filter
        (fun j : ℕ => ¬ 8 * (c * (j : ℝ) ^ 2 * 2 ^ (k - j)) ≤ (2 : ℝ) ^ (m - 4 * j - 1)),
          9 * c * (j : ℝ) ^ 2 * 2 ^ (5 * j) * ((2 : ℝ) ^ (k - j)) ^ 2)) := by
  have hC' : ∀ j : ℕ, 0 ≤ C * 2 ^ (5 * j) := fun j => by positivity
  rw [← Finset.sum_filter_add_sum_filter_not (Finset.Icc J jstar)
    (fun j : ℕ => 8 * (c * (j : ℝ) ^ 2 * 2 ^ (k - j)) ≤ (2 : ℝ) ^ (m - 4 * j - 1))]
  have h1 : ∑ j ∈ (Finset.Icc J jstar).filter
        (fun j : ℕ => 8 * (c * (j : ℝ) ^ 2 * 2 ^ (k - j)) ≤ (2 : ℝ) ^ (m - 4 * j - 1)),
        ((S j).card : ℝ) * ((H j).card : ℝ) * q j ≤
      C * (∑ j ∈ (Finset.Icc J jstar).filter
        (fun j : ℕ => 8 * (c * (j : ℝ) ^ 2 * 2 ^ (k - j)) ≤ (2 : ℝ) ^ (m - 4 * j - 1)),
          (2 : ℝ) ^ (5 * j) * Real.exp (-(q0 * (j : ℝ) ^ 2))) +
      C * p * (∑ j ∈ (Finset.Icc J jstar).filter
        (fun j : ℕ => 8 * (c * (j : ℝ) ^ 2 * 2 ^ (k - j)) ≤ (2 : ℝ) ^ (m - 4 * j - 1)),
          60 * (j : ℝ) ^ 2 * 2 ^ (5 * j) * ((2 : ℝ) ^ (k - j)) ^ 2) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun j hj => ?_
    have hjI := (Finset.mem_filter.1 hj).1
    calc ((S j).card : ℝ) * ((H j).card : ℝ) * q j ≤ C * 2 ^ (5 * j) * q j :=
          mul_le_mul_of_nonneg_right (hcard j hjI) (hq j hjI)
      _ ≤ C * 2 ^ (5 * j) * (Real.exp (-(q0 * (j : ℝ) ^ 2)) +
            p * (60 * (j : ℝ) ^ 2 * ((2 : ℝ) ^ (k - j)) ^ 2)) :=
          mul_le_mul_of_nonneg_left (hqc j hj) (hC' j)
      _ = _ := by ring
  have h2 : ∑ j ∈ (Finset.Icc J jstar).filter
        (fun j : ℕ => ¬ 8 * (c * (j : ℝ) ^ 2 * 2 ^ (k - j)) ≤ (2 : ℝ) ^ (m - 4 * j - 1)),
        ((S j).card : ℝ) * ((H j).card : ℝ) * q j ≤
      C * p * (∑ j ∈ (Finset.Icc J jstar).filter
        (fun j : ℕ => ¬ 8 * (c * (j : ℝ) ^ 2 * 2 ^ (k - j)) ≤ (2 : ℝ) ^ (m - 4 * j - 1)),
          9 * c * (j : ℝ) ^ 2 * 2 ^ (5 * j) * ((2 : ℝ) ^ (k - j)) ^ 2) := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun j hj => ?_
    have hjI := (Finset.mem_filter.1 hj).1
    calc ((S j).card : ℝ) * ((H j).card : ℝ) * q j ≤ C * 2 ^ (5 * j) * q j :=
          mul_le_mul_of_nonneg_right (hcard j hjI) (hq j hjI)
      _ ≤ C * 2 ^ (5 * j) * (p * (9 * c * (j : ℝ) ^ 2 * ((2 : ℝ) ^ (k - j)) ^ 2)) :=
          mul_le_mul_of_nonneg_left (hqf j hj) (hC' j)
      _ = _ := by ring
  rw [mul_add (C * p)]
  linarith

/-- Equation (5.33) of the differentiability preprint: the coarse crossing term is at most the tail
sum `β_J / c_{A,R}`. -/
private theorem coarse_beta_le {q0 : ℝ} (hq : 0 < q0) (J jstar : ℕ) (P : ℕ → Prop)
    [DecidablePred P] :
    ∑ j ∈ (Finset.Icc J jstar).filter P, (2 : ℝ) ^ (5 * j) * Real.exp (-(q0 * (j : ℝ) ^ 2)) ≤
      ∑' i : ℕ, (2 : ℝ) ^ (5 * (i + J)) * Real.exp (-(q0 * ((i + J : ℕ) : ℝ) ^ 2)) := by
  have hnn : ∀ j : ℕ, 0 ≤ (2 : ℝ) ^ (5 * j) * Real.exp (-(q0 * (j : ℝ) ^ 2)) :=
    fun j => by positivity
  calc ∑ j ∈ (Finset.Icc J jstar).filter P, (2 : ℝ) ^ (5 * j) * Real.exp (-(q0 * (j : ℝ) ^ 2))
      ≤ ∑ j ∈ Finset.Icc J jstar, (2 : ℝ) ^ (5 * j) * Real.exp (-(q0 * (j : ℝ) ^ 2)) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun j _ _ => hnn j
    _ = ∑ i ∈ Finset.range (jstar + 1 - J),
          (2 : ℝ) ^ (5 * (i + J)) * Real.exp (-(q0 * ((i + J : ℕ) : ℝ) ^ 2)) := by
        have hI : Finset.Icc J jstar = Finset.Ico J (jstar + 1) := by
          ext x; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega
        rw [hI, Finset.sum_Ico_eq_sum_range]
        exact Finset.sum_congr rfl fun i _ => by rw [add_comm J i]
    _ ≤ _ := ((summable_nat_add_iff J).2 (grid_beta_summable hq)).sum_le_tsum _
        fun i _ => hnn (i + J)

/-- **Lemma 5.7 (i) and (ii) of the differentiability preprint, for bounded weights**, in the form
of the hypothesis `hgrid` of `arbitrary_endpoints_defect_le`: the event `Gconn`, which is implied by
`G_{k,J}` of part (i), has probability at least `1 - 2 β_J` for record indices `k ≥ k₁`, with
`β_J → 0` depending on `A`, `R` (and `q0`), not on `ε₀`. -/
theorem grid_connections_simultaneous
    (μ : Measure ℝ) [IsProbabilityMeasure μ] {M : ℝ} (hM : 0 < M) (hb : ∀ᵐ x ∂μ, |x| ≤ M)
    (hneg : ∃ p : ℝ, 1 < p ∧
      (∫⁻ x, ENNReal.ofReal ((max (-x) 0) ^ p) ∂μ) < ∞)
    (hpos : (∫⁻ t in Ioi (0:ℝ), (μ (Ioi t)) ^ (1/2:ℝ)) < ∞)
    (g : Quadrant → ℝ) (hgcont : Continuous g)
    (hghom : ∀ (c : ℝ≥0) (x : Quadrant), g (c * x.1, c * x.2) = (c : ℝ) * g x)
    (hgconc : ∀ (x y : Quadrant) (r t : ℝ≥0), r + t = 1 →
      (r : ℝ) * g x + (t : ℝ) * g y ≤ g (r * x.1 + t * y.1, r * x.2 + t * y.2))
    (hgshape : ∀ᵐ ω ∂environmentLaw μ, ∀ ε : ℝ, 0 < ε →
      ∃ N : ℕ, 1 ≤ N ∧ ∀ d : ℕ × ℕ, N ≤ d.1 + d.2 →
        |lastPassage ω 0 d - g ((d.1 : ℝ≥0), (d.2 : ℝ≥0))| ≤
          ε * ((d.1 + d.2 : ℕ) : ℝ))
    (a : ℝ) (ha₀ : 0 < a) (ha₁ : a < 1) (q0 : ℝ) (hq0 : 0 < q0)
    (k0 : ℕ) (hk0 : 0 < k0) (m : ℕ → ℕ) (Kset : Set ℕ)
    (hm3 : ∀ k : ℕ, k0 ≤ k → m k ≤ 3 * k)
    (hKset : ∀ k ∈ Kset, k0 ≤ k)
    (htrial :
      let H : ℝ → ℝ := fun h => quadrantExtension g (a + h, 1 - a - h)
      let dl : ℝ := derivWithin H (Iio 0) 0
      let dr : ℝ := derivWithin H (Ioi 0) 0
      let K : ℝ := 100 * (1 + |dl| + |dr|)
      let P : ℕ → ℕ → ℝ := fun k n => (environmentLaw μ).real {ω : Environment |
        ∃ u : Lattice, u.1 + u.2 = 0 ∧ ∃ e : ℕ × ℕ, e.1 + e.2 = n ∧ ∃ q : Path u e,
          (∀ i, |(1 - a) * ((q.vertex i).1 : ℝ) - a * ((q.vertex i).2 : ℝ)| ≤
            8 * (2 : ℝ) ^ k) ∧
            g (toQuadrant (a, 1 - a)) * (n : ℝ) - K * (2 : ℝ) ^ k < pathWeight ω q}
      ∀ k ∈ Kset, 4 * k0 + 3 ≤ k → ∀ j : ℕ, j ≤ ⌈((m k : ℝ) - 1) / 4⌉₊ →
        (∀ l : ℕ, 1 ≤ l → (l : ℝ) < 2 ^ (m k - 4 * j - 1) → q0 < P (k - j) l) ∧
        (1 < (2 : ℝ) ^ (m k - 4 * j - 1) →
          (2 : ℝ) ^ (m k - 4 * j - 1) ≤ ((2 : ℝ) ^ (k - j)) ^ 3 / 2)) :
    let H : ℝ → ℝ := fun h => quadrantExtension g (a + h, 1 - a - h)
    let dl : ℝ := derivWithin H (Iio 0) 0
    let dr : ℝ := derivWithin H (Ioi 0) 0
    let K : ℝ := 100 * (1 + |dl| + |dr|)
    let G0 : ℝ := H 0
    let E : ℝ := ∫ x : ℝ, x ∂μ
    let cstar : ℝ := 50 / min a (1 - a)
    let C₁ : ℝ := 8 * cstar * (G0 - E) + 2 * K + 3 * cstar
    let Gconn : ℝ → ℝ → ℝ → ℕ → ℕ → Set Environment := fun A R ε₀ k J =>
      {ω : Environment | ∀ j : ℕ, J ≤ j → j ≤ ⌈((m k : ℝ) - 1) / 4⌉₊ →
        ∀ I : ℤ, ((2 ^ (m k - 4 * j - 1) : ℕ) : ℤ) ∣ I → |(I : ℝ)| ≤ (A + 4) * 2 ^ m k →
        ∀ ρ : ℝ, |ρ| ≤ R * 2 ^ k → ∀ z₀ z₁ : Lattice,
        (z₀.1 + z₀.2 = I ∧ ρ - 1 < (1 - a) * (z₀.1 : ℝ) - a * (z₀.2 : ℝ) ∧
          (1 - a) * (z₀.1 : ℝ) - a * (z₀.2 : ℝ) ≤ ρ) →
        (z₁.1 + z₁.2 = I + ((2 ^ (m k - 4 * j - 1) : ℕ) : ℤ) ∧
          ρ - 1 < (1 - a) * (z₁.1 : ℝ) - a * (z₁.2 : ℝ) ∧
          (1 - a) * (z₁.1 : ℝ) - a * (z₁.2 : ℝ) ≤ ρ) →
        ∃ (D : ℕ × ℕ) (y : Path z₀ D),
          z₀ + ((D.1 : ℤ), (D.2 : ℤ)) = z₁ ∧
          G0 * ((D.1 : ℝ) + (D.2 : ℝ)) + dl * ((1 - a) * (D.1 : ℝ) - a * (D.2 : ℝ)) -
              pathWeight ω y ≤
            C₁ * ((j : ℝ) ^ 2 * ((2 ^ (k - j) : ℕ) : ℝ)) + 2 * (ε₀ * 2 ^ k / (k : ℝ)) ∧
          G0 * ((D.1 : ℝ) + (D.2 : ℝ)) + dr * ((1 - a) * (D.1 : ℝ) - a * (D.2 : ℝ)) -
              pathWeight ω y ≤
            C₁ * ((j : ℝ) ^ 2 * ((2 ^ (k - j) : ℕ) : ℝ)) + 2 * (ε₀ * 2 ^ k / (k : ℝ)) ∧
          ∀ i, |(1 - a) * ((y.vertex i).1 : ℝ) - a * ((y.vertex i).2 : ℝ) - ρ| ≤
            C₁ * ((j : ℝ) ^ 2 * ((2 ^ (k - j) : ℕ) : ℝ))}
    ∀ A R : ℝ, 0 < A → 0 < R → ∃ β : ℕ → ℝ, Tendsto β atTop (𝓝 0) ∧
      ∀ ε₀ : ℝ, 0 < ε₀ → ∀ J : ℕ, 1 ≤ J → ∃ k1 : ℕ, ∀ k ∈ Kset, k1 ≤ k →
        (environmentLaw μ).real (Gconn A R ε₀ k J)ᶜ ≤ 2 * β J := by
  classical
  intro H dl dr K G0 E cstar C₁ Gconn A R hA hR
  have hθ : 0 < min a (1 - a) := lt_min ha₀ (by linarith)
  have hθ2 : min a (1 - a) ≤ 1 / 2 := by
    have h1 := min_le_left a (1 - a)
    have h2 := min_le_right a (1 - a)
    linarith
  have hcpos : 0 < cstar := by show 0 < 50 / min a (1 - a); positivity
  have hc1 : 1 ≤ cstar := by
    show 1 ≤ 50 / min a (1 - a)
    rw [le_div_iff₀ hθ]
    linarith
  have hG0 : G0 = g (toQuadrant (a, 1 - a)) := by simp [G0, H, quadrantExtension]
  have hEG : E ≤ G0 := by
    have h1 := integral_le_shape_of_negative_moment_and_positive_tail μ hneg hpos g hgcont hghom
      hgconc hgshape a.toNNReal (1 - a).toNNReal (by
        apply NNReal.coe_injective
        simp only [NNReal.coe_add, NNReal.coe_one, Real.coe_toNNReal _ ha₀.le,
          Real.coe_toNNReal _ (by linarith : (0 : ℝ) ≤ 1 - a)]
        ring)
    rw [hG0]
    exact h1
  have hdl : |dl| ≤ K := by show |dl| ≤ 100 * (1 + |dl| + |dr|); linarith [abs_nonneg dl, abs_nonneg dr]
  have hdr : |dr| ≤ K := by show |dr| ≤ 100 * (1 + |dl| + |dr|); linarith [abs_nonneg dl, abs_nonneg dr]
  have hCpos : 0 < (4 * (A + 4) + 1) * (2 * R + 2) := by positivity
  set C : ℝ := (4 * (A + 4) + 1) * (2 * R + 2) with hC
  refine ⟨fun J => C * ∑' i : ℕ, (2 : ℝ) ^ (5 * (i + J)) *
    Real.exp (-(q0 * ((i + J : ℕ) : ℝ) ^ 2)), grid_beta_tendsto q0 C, ?_⟩
  intro ε₀ hε₀ J hJ
  obtain ⟨k1', hk1'⟩ := grid_stair_term_eventually_le_five (D := 60 + 9 * cstar) (C := C)
    (q0 := q0) (ε0 := ε₀) (cs := cstar) (M := M) (by positivity) hCpos hq0 hε₀ hcpos hM J
  refine ⟨max k1' (4 * k0 + 3), fun k hkK hk => ?_⟩
  have hk' : k1' ≤ k := (le_max_left _ _).trans hk
  have hk4 : 4 * k0 + 3 ≤ k := (le_max_right _ _).trans hk
  have hmk : m k ≤ 3 * k := hm3 k (hKset k hkK)
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hs : (0 : ℝ) < 2 ^ k := by positivity
  have ht : 0 < ε₀ * 2 ^ k / (k : ℝ) := by positivity
  set jstar : ℕ := ⌈((m k : ℝ) - 1) / 4⌉₊ with hjstar
  -- grid levels and bins
  obtain ⟨S, hS⟩ : ∃ S : ℕ → Finset ℤ, ∀ j I, I ∈ S j ↔
      (((2 ^ (m k - 4 * j - 1) : ℕ) : ℤ) ∣ I ∧ |(I : ℝ)| ≤ (A + 4) * 2 ^ m k) := by
    choose S hS using fun j : ℕ => exists_finset_int_of_bounded
      (fun I => ((2 ^ (m k - 4 * j - 1) : ℕ) : ℤ) ∣ I ∧ |(I : ℝ)| ≤ (A + 4) * 2 ^ m k)
      ((A + 4) * 2 ^ m k) (fun I hI => hI.2)
    exact ⟨S, hS⟩
  obtain ⟨Hn, hHn⟩ : ∃ Hn : ℕ → Finset ℤ, ∀ j h, h ∈ Hn j ↔
      ∃ x : ℝ, (h : ℝ) * 2 ^ (k - j) ≤ x ∧ x < ((h : ℝ) + 1) * 2 ^ (k - j) ∧
        |x| ≤ R * 2 ^ k := by
    choose Hn hHn using fun j : ℕ => exists_finset_int_of_bounded
      (fun h : ℤ => ∃ x : ℝ, (h : ℝ) * 2 ^ (k - j) ≤ x ∧ x < ((h : ℝ) + 1) * 2 ^ (k - j) ∧
        |x| ≤ R * 2 ^ k) (R * 2 ^ k + 1) (fun h ⟨x, h1, h2, h3⟩ =>
        abs_bin_le (by positivity) (one_le_pow₀ (by norm_num)) h1 h2 h3)
    exact ⟨Hn, hHn⟩
  -- the good events at all triples
  have hgood : ∀ j : ℕ, ∀ I h : ℤ, ∃ Bad : Set Environment, J ≤ j → j ≤ jstar →
      ((8 * (cstar * (j : ℝ) ^ 2 * 2 ^ (k - j)) ≤ (2 : ℝ) ^ (m k - 4 * j - 1) →
        (environmentLaw μ).real Bad ≤ Real.exp (-(q0 * (j : ℝ) ^ 2)) +
          Real.exp (-(ε₀ * 2 ^ k / (k : ℝ)) ^ 2 / (16 * cstar * (k : ℝ) ^ 2 * 2 ^ k * M ^ 2)) *
            (60 * (j : ℝ) ^ 2 * ((2 : ℝ) ^ (k - j)) ^ 2)) ∧
      (¬ 8 * (cstar * (j : ℝ) ^ 2 * 2 ^ (k - j)) ≤ (2 : ℝ) ^ (m k - 4 * j - 1) →
        (environmentLaw μ).real Bad ≤
          Real.exp (-(ε₀ * 2 ^ k / (k : ℝ)) ^ 2 / (16 * cstar * (k : ℝ) ^ 2 * 2 ^ k * M ^ 2)) *
            (9 * cstar * (j : ℝ) ^ 2 * ((2 : ℝ) ^ (k - j)) ^ 2))) ∧
      ∀ ω : Environment, ω ∉ Bad → ∀ ρ : ℝ, (h : ℝ) * 2 ^ (k - j) ≤ ρ → ρ < ((h : ℝ) + 1) * 2 ^ (k - j) →
        ∀ z₀ z₁ : Lattice,
        (z₀.1 + z₀.2 = I ∧ ρ - 1 < (1 - a) * (z₀.1 : ℝ) - a * (z₀.2 : ℝ) ∧
          (1 - a) * (z₀.1 : ℝ) - a * (z₀.2 : ℝ) ≤ ρ) →
        (z₁.1 + z₁.2 = I + ((2 ^ (m k - 4 * j - 1) : ℕ) : ℤ) ∧
          ρ - 1 < (1 - a) * (z₁.1 : ℝ) - a * (z₁.2 : ℝ) ∧
          (1 - a) * (z₁.1 : ℝ) - a * (z₁.2 : ℝ) ≤ ρ) →
        ∃ (D : ℕ × ℕ) (y : Path z₀ D),
          z₀ + ((D.1 : ℤ), (D.2 : ℤ)) = z₁ ∧
          G0 * ((D.1 : ℝ) + (D.2 : ℝ)) + dl * ((1 - a) * (D.1 : ℝ) - a * (D.2 : ℝ)) -
              pathWeight ω y ≤
            C₁ * ((j : ℝ) ^ 2 * ((2 ^ (k - j) : ℕ) : ℝ)) + 2 * (ε₀ * 2 ^ k / (k : ℝ)) ∧
          G0 * ((D.1 : ℝ) + (D.2 : ℝ)) + dr * ((1 - a) * (D.1 : ℝ) - a * (D.2 : ℝ)) -
              pathWeight ω y ≤
            C₁ * ((j : ℝ) ^ 2 * ((2 ^ (k - j) : ℕ) : ℝ)) + 2 * (ε₀ * 2 ^ k / (k : ℝ)) ∧
          ∀ i, |(1 - a) * ((y.vertex i).1 : ℝ) - a * ((y.vertex i).2 : ℝ) - ρ| ≤
            C₁ * ((j : ℝ) ^ 2 * ((2 ^ (k - j) : ℕ) : ℝ)) := by
    intro j I h
    by_cases hj : J ≤ j ∧ j ≤ jstar
    · obtain ⟨hJj, hjj⟩ := hj
      obtain ⟨-, hjk, -, hw2⟩ := grid_scale_index_bounds hjstar hmk hk4 hk0 hjj
      have hj1 : 1 ≤ j := hJ.trans hJj
      have hwc : (((2 ^ (k - j) : ℕ) : ℝ)) = (2 : ℝ) ^ (k - j) := by push_cast; ring
      have hlc : (((2 ^ (m k - 4 * j - 1) : ℕ) : ℝ)) = (2 : ℝ) ^ (m k - 4 * j - 1) := by
        push_cast; ring
      have hlen : (j : ℝ) ^ 2 * (((2 ^ (k - j) : ℕ) : ℝ)) ≤ (k : ℝ) ^ 2 * 2 ^ k := by
        rw [hwc]
        exact mul_le_mul (pow_le_pow_left₀ (Nat.cast_nonneg j) (by exact_mod_cast hjk) 2)
          (pow_le_pow_right₀ (by norm_num) (by omega)) (by positivity) (by positivity)
      by_cases hc : 8 * (cstar * (j : ℝ) ^ 2 * 2 ^ (k - j)) ≤ (2 : ℝ) ^ (m k - 4 * j - 1)
      · have hl8 : 8 * cstar * ((j : ℝ) ^ 2 * (((2 ^ (k - j) : ℕ) : ℝ))) ≤
            (((2 ^ (m k - 4 * j - 1) : ℕ) : ℝ)) := by rw [hwc, hlc]; linarith
        have hj1' : (1 : ℝ) ≤ j := by exact_mod_cast hj1
        have hw2' : (2 : ℝ) ≤ 2 ^ (k - j) := by exact_mod_cast hw2
        have hP2 : (1 : ℝ) < (2 : ℝ) ^ (m k - 4 * j - 1) := by
          have hj2 : (1 : ℝ) ≤ (j : ℝ) ^ 2 := one_le_pow₀ hj1'
          have hcj : 1 ≤ cstar * (j : ℝ) ^ 2 := by nlinarith
          have hprod : 2 ≤ cstar * (j : ℝ) ^ 2 * 2 ^ (k - j) := by nlinarith
          linarith
        have hrec := (htrial k hkK hk4 j hjj)
        obtain ⟨Bad, hB1, hB2⟩ := grid_good_event_coarse μ hM hb a G0 E dl dr K
          (ε₀ * 2 ^ k / (k : ℝ)) cstar (2 ^ k) q0 ha₀ ha₁ rfl rfl hEG hdl hdr ht k
          (2 ^ (k - j)) j (2 ^ (m k - 4 * j - 1)) (by omega) hs hw2 hj1 hl8
          (by rw [hlc, hwc]; exact hrec.2 hP2)
          hlen (by
            intro n hn1 hn2
            have hn2' : (n : ℝ) < 2 ^ (m k - 4 * j - 1) := by rw [← hlc]; exact_mod_cast hn2
            have := hrec.1 n hn1 hn2'
            rw [hwc, hG0]
            exact this) I h
        refine ⟨Bad, fun _ _ => ⟨⟨fun _ => ?_, fun hn => absurd hc hn⟩, ?_⟩⟩
        · rw [hwc] at hB1; exact hB1
        · intro ω hω ρ h1 h2
          exact hB2 ω hω ρ (by rw [hwc]; exact h1) (by rw [hwc]; exact h2)
      · have hl8 : (((2 ^ (m k - 4 * j - 1) : ℕ) : ℝ)) <
            8 * cstar * ((j : ℝ) ^ 2 * (((2 ^ (k - j) : ℕ) : ℝ))) := by
          rw [hwc, hlc]; linarith [not_le.1 hc]
        obtain ⟨Bad, hB1, hB2⟩ := grid_good_event_fine μ hM hb a G0 E dl dr K
          (ε₀ * 2 ^ k / (k : ℝ)) cstar (2 ^ k) ha₀ ha₁ rfl rfl hEG hdl hdr ht k
          (2 ^ (k - j)) j (2 ^ (m k - 4 * j - 1)) (by omega) hs hw2 hj1 hl8 hlen I h
        refine ⟨Bad, fun _ _ => ⟨⟨fun hh => absurd hh hc, fun _ => ?_⟩, ?_⟩⟩
        · rw [hwc] at hB1; exact hB1
        · intro ω hω ρ h1 h2
          exact hB2 ω hω ρ (by rw [hwc]; exact h1) (by rw [hwc]; exact h2)
    · exact ⟨∅, fun h1 h2 => absurd ⟨h1, h2⟩ hj⟩
  choose Bad hBad using hgood
  set p : ℝ := Real.exp (-(ε₀ * 2 ^ k / (k : ℝ)) ^ 2 / (16 * cstar * (k : ℝ) ^ 2 * 2 ^ k * M ^ 2)) with hp
  have hsub : (Gconn A R ε₀ k J)ᶜ ⊆
      ⋃ j ∈ Finset.Icc J jstar, ⋃ I ∈ S j, ⋃ h ∈ Hn j, Bad j I h := by
    intro ω hω
    by_contra hcon
    apply hω
    simp only [Gconn, Set.mem_ofPred_eq]
    intro j hJj hjj I hdiv hI ρ hρ z₀ z₁ hz₀ hz₁
    have hw1 : (0 : ℝ) < 2 ^ (k - j) := by positivity
    obtain ⟨h, hh⟩ : ∃ h : ℤ, h = ⌊ρ / 2 ^ (k - j)⌋ := ⟨_, rfl⟩
    have hh1 : (h : ℝ) * 2 ^ (k - j) ≤ ρ := by
      have := Int.floor_le (ρ / 2 ^ (k - j))
      rw [← hh, le_div_iff₀ hw1] at this
      exact this
    have hh2 : ρ < ((h : ℝ) + 1) * 2 ^ (k - j) := by
      have := Int.lt_floor_add_one (ρ / 2 ^ (k - j))
      rw [← hh, div_lt_iff₀ hw1] at this
      exact this
    have hIm : I ∈ S j := (hS j I).2 ⟨hdiv, hI⟩
    have hhm : h ∈ Hn j := (hHn j h).2 ⟨ρ, hh1, hh2, hρ⟩
    have hnb : ω ∉ Bad j I h := fun hm => hcon (Set.mem_biUnion (Finset.mem_Icc.2 ⟨hJj, hjj⟩)
      (Set.mem_biUnion hIm (Set.mem_biUnion hhm hm)))
    exact (hBad j I h hJj hjj).2 ω hnb ρ hh1 hh2 z₀ z₁ hz₀ hz₁
  have hppos : 0 < p := Real.exp_pos _
  let q : ℕ → ℝ := fun j =>
    if 8 * (cstar * (j : ℝ) ^ 2 * 2 ^ (k - j)) ≤ (2 : ℝ) ^ (m k - 4 * j - 1) then
      Real.exp (-(q0 * (j : ℝ) ^ 2)) + p * (60 * (j : ℝ) ^ 2 * ((2 : ℝ) ^ (k - j)) ^ 2)
    else p * (9 * cstar * (j : ℝ) ^ 2 * ((2 : ℝ) ^ (k - j)) ^ 2)
  have hq : ∀ j ∈ Finset.Icc J jstar, ∀ I ∈ S j, ∀ h ∈ Hn j,
      (environmentLaw μ).real (Bad j I h) ≤ q j := by
    intro j hj I _ h _
    obtain ⟨hJj, hjj⟩ := Finset.mem_Icc.1 hj
    obtain ⟨⟨h1, h2⟩, -⟩ := hBad j I h hJj hjj
    by_cases hc : 8 * (cstar * (j : ℝ) ^ 2 * 2 ^ (k - j)) ≤ (2 : ℝ) ^ (m k - 4 * j - 1)
    · exact (h1 hc).trans (by simp only [q, hc, ↓reduceIte, le_refl])
    · exact (h2 hc).trans (by simp only [q, hc, ↓reduceIte, le_refl])
  have hqnn : ∀ j ∈ Finset.Icc J jstar, 0 ≤ q j := by
    intro j _
    simp only [q]
    split_ifs <;> positivity
  have hcard : ∀ j ∈ Finset.Icc J jstar,
      ((S j).card : ℝ) * ((Hn j).card : ℝ) ≤ C * 2 ^ (5 * j) := by
    intro j hj
    obtain ⟨-, hjjs⟩ := Finset.mem_Icc.1 hj
    obtain ⟨-, hjk, -, -⟩ := grid_scale_index_bounds hjstar hmk hk4 hk0 hjjs
    have h1 := (grid_count_le hA (m k) j (S j) (hS j)).2
    have h2 := (grid_bin_count_le hR hjk (Hn j) (hHn j)).2
    calc ((S j).card : ℝ) * ((Hn j).card : ℝ) ≤
          ((4 * (A + 4) + 1) * 2 ^ (4 * j)) * ((2 * R + 2) * 2 ^ j) :=
          mul_le_mul h1 h2 (Nat.cast_nonneg _) (by positivity)
      _ = C * 2 ^ (5 * j) := by
          rw [hC, show 5 * j = 4 * j + j by ring, pow_add]
          ring
  have hsum := scale_sum_le (J := J) (jstar := jstar) (k := k) (m := m k) (c := cstar) (C := C)
    (q0 := q0) (p := p) hCpos.le S Hn q hcard hqnn
    (fun j hj => by simp only [q, (Finset.mem_filter.1 hj).2, ↓reduceIte, le_refl])
    (fun j hj => by simp only [q, (Finset.mem_filter.1 hj).2, ↓reduceIte, le_refl])
  have hnine := grid_staircase_sum_le_nine (m := m k) (k := k) (k0 := k0) (J := J)
    (jstar := jstar) (c := cstar) hjstar hmk hk4 hk0 hJ hc1
  have hbeta := coarse_beta_le (q0 := q0) hq0 J jstar
    (fun j : ℕ => 8 * (cstar * (j : ℝ) ^ 2 * 2 ^ (k - j)) ≤ (2 : ℝ) ^ (m k - 4 * j - 1))
  have hp' : p = Real.exp (-(ε₀ ^ 2 / (16 * cstar * M ^ 2)) * ((2 : ℝ) ^ k / (k : ℝ) ^ 4)) := by
    rw [hp]
    congr 1
    rw [neg_div, grid_badstair_exponent (ε0 := ε₀) (cs := cstar) (M := M) (s := 2 ^ k) (k := k)
      (by omega) hs hcpos hM]
    ring
  have e1 := mul_le_mul_of_nonneg_left hbeta hCpos.le
  have e2 := mul_le_mul_of_nonneg_left hnine (mul_nonneg hCpos.le hppos.le)
  have e3 : C * p * ((60 + 9 * cstar) * (k : ℝ) ^ 3 * ((2 : ℝ) ^ k) ^ 5) ≤
      C * ∑' i : ℕ, (2 : ℝ) ^ (5 * (i + J)) * Real.exp (-(q0 * ((i + J : ℕ) : ℝ) ^ 2)) := by
    calc _ = (60 + 9 * cstar) * C * (k : ℝ) ^ 3 * ((2 : ℝ) ^ k) ^ 5 *
          Real.exp (-(ε₀ ^ 2 / (16 * cstar * M ^ 2)) * ((2 : ℝ) ^ k / (k : ℝ) ^ 4)) := by
          rw [hp']; ring
      _ ≤ _ := hk1' k hk'
  have e4 := (measureReal_mono hsub (measure_ne_top _ _)).trans (union_measure_le _ J jstar S Hn Bad q hq)
  beta_reduce
  linarith [hsum, e1, e2, e3, e4]

end LPPDifferentiability
