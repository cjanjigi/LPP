/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Martin2004.Probability.SparseAnimalBound
public import Martin2004.Probability.WeakGridRayConvergence
public import Martin2004.Probability.NegativeRemainderMean
public import Martin2004.Model.Paths.WeakShapeConnector
public import Martin2004.Analysis.DyadicQuadrantGrid
public import Martin2004.Analysis.DyadicQuadrantGridLarge
public import Martin2004.Probability.DyadicMovingEdgeBounds

import Mathlib.Tactic

/-!
# Weak-negative uniform lower estimate

The greedy connector, four sparse animal bounds, moving dyadic edges and
finite-ray limits give the uniform lower estimate for the same expected rate.
Nonnegative straight prefixes are dominated by full deterministic edges.
-/

public section

open MeasureTheory Filter Set
open scoped Topology ENNReal NNReal BigOperators

namespace LPPDifferentiability

private theorem horizontal_pathWeight_le_full_edge
    (Y : Environment) (hY : ∀ v, 0 ≤ Y v) (u : Lattice) (d : ℕ × ℕ)
    (p : Path u d) (h : ℕ) (hd : d.1 ≤ h) (hzero : d.2 = 0) :
    pathWeight Y p ≤ ∑ l : Fin h, Y (u.1 + (l.val : ℤ), u.2) := by
  classical
  let e : Fin (d.1 + d.2) → Fin h := fun i => ⟨i.val, by
    have hi := i.isLt
    omega⟩
  unfold pathWeight
  apply Finset.sum_le_sum_of_injOn e
  · intro i _ j _ hij
    apply Fin.ext
    exact congrArg (fun a : Fin h => a.val) hij
  · exact Finset.subset_univ _
  · intro i _
    have hrect := p.vertex_mem_Icc i.castSucc
    have hlevel := p.level i.castSucc
    simp only [Fin.val_castSucc] at hlevel
    have hlow := hrect.1.2
    have hupp := hrect.2.2
    simp only [Prod.snd_add, hzero, Nat.cast_zero, add_zero] at hupp
    have hv : p.vertex i.castSucc = (u.1 + (i.val : ℤ), u.2) := by
      apply Prod.ext <;> dsimp only <;> omega
    exact le_of_eq (congrArg Y hv)
  · intro a _ _
    exact hY _

private theorem vertical_pathWeight_le_full_edge
    (Y : Environment) (hY : ∀ v, 0 ≤ Y v) (u : Lattice) (d : ℕ × ℕ)
    (p : Path u d) (h : ℕ) (hd : d.2 ≤ h) (hzero : d.1 = 0) :
    pathWeight Y p ≤ ∑ l : Fin h, Y (u.1, u.2 + (l.val : ℤ)) := by
  classical
  let e : Fin (d.1 + d.2) → Fin h := fun i => ⟨i.val, by
    have hi := i.isLt
    omega⟩
  unfold pathWeight
  apply Finset.sum_le_sum_of_injOn e
  · intro i _ j _ hij
    apply Fin.ext
    exact congrArg (fun a : Fin h => a.val) hij
  · exact Finset.subset_univ _
  · intro i _
    have hrect := p.vertex_mem_Icc i.castSucc
    have hlevel := p.level i.castSucc
    simp only [Fin.val_castSucc] at hlevel
    have hlow := hrect.1.1
    have hupp := hrect.2.1
    simp only [Prod.fst_add, hzero, Nat.cast_zero, add_zero] at hupp
    have hv : p.vertex i.castSucc = (u.1, u.2 + (i.val : ℤ)) := by
      apply Prod.ext <;> dsimp only <;> omega
    exact le_of_eq (congrArg Y hv)
  · intro a _ _
    exact hY _

private theorem boundary_prefix_pathWeight_le_full_edges
    (Y : Environment) (hY : ∀ v, 0 ≤ Y v) (u : Lattice) (d : ℕ × ℕ)
    (p : Path u d) (k : Fin (d.1 + d.2 + 1)) (h : ℕ)
    (hd₁ : d.1 < h) (hd₂ : d.2 < h)
    (haxis : (p.splitDisplacement k).1 = 0 ∨ (p.splitDisplacement k).2 = 0)
    (B : ℝ)
    (hhor : (∑ l : Fin h, Y (u.1 + (l.val : ℤ), u.2)) ≤ B)
    (hver : (∑ l : Fin h, Y (u.1, u.2 + (l.val : ℤ))) ≤ B) :
    pathWeight Y (p.prefixPath k) ≤ B := by
  have hle := p.splitDisplacement_le k
  rcases haxis with haxis | haxis
  · exact (vertical_pathWeight_le_full_edge Y hY u _ (p.prefixPath k) h
      (hle.2.trans hd₂.le) haxis).trans hver
  · exact (horizontal_pathWeight_le_full_edge Y hY u _ (p.prefixPath k) h
      (hle.1.trans hd₁.le) haxis).trans hhor

private theorem ae_eventually_lastPassage_lower_fixed_tolerance
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : Integrable (fun t : ℝ => t) μ)
    (hpos : (∫⁻ t in Ioi (0 : ℝ), (μ (Ioi t)) ^ (1 / 2 : ℝ)) < ∞)
    (p : ℝ) (hp : 1 < p)
    (hmoment : (∫⁻ t, ENNReal.ofReal ((max (-t) 0) ^ p) ∂μ) < ∞)
    (g : Quadrant → ℝ) (hgc : Continuous g)
    (hhom : ∀ (c : ℝ≥0) (x : Quadrant), g (c • x) = (c : ℝ) * g x)
    (hg : ∀ x : Quadrant, Tendsto (fun n : ℕ =>
      (∫ ω : Environment, lastPassage ω 0
        (⌊(n : ℝ) * (x.1 : ℝ)⌋₊, ⌊(n : ℝ) * (x.2 : ℝ)⌋₊)
        ∂environmentLaw μ) / (n : ℝ)) atTop (𝓝 (g x)))
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᵐ ω ∂environmentLaw μ, ∃ N : ℕ, 1 ≤ N ∧
      ∀ z : ℕ × ℕ, N ≤ z.1 + z.2 →
        g ((z.1 : ℝ≥0), (z.2 : ℝ≥0)) - lastPassage ω 0 z ≤
          ε * ((z.1 + z.2 : ℕ) : ℝ) := by
  let δ : ℝ := ε / 64
  have hδ : 0 < δ := by dsimp only [δ]; positivity
  obtain ⟨C, _hC, hanimal⟩ := exists_sparseMinimumField_animalMaximum_eventually_bound
  have htail : Tendsto (fun L : ℝ => C * (∫ x, max (-L - x) 0 ∂μ))
      atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (tendsto_integral_negative_remainder_zero hμ).const_mul C
  obtain ⟨L₀, hL₀⟩ := eventually_atTop.mp (htail.eventually_lt_const hδ)
  let L : ℝ := max L₀ 0
  have hL : 0 ≤ L := le_max_right _ _
  have hsmall : C * (∫ x, max (-L - x) 0 ∂μ) < δ :=
    hL₀ L (le_max_left _ _)
  let m : ℝ := ∫ t, max (-t) 0 ∂μ
  obtain ⟨Q, hQ⟩ := exists_nat_gt ((2 * L + m) / δ)
  have hQcost : 2 * L + m ≤ δ * (Q : ℝ) := by
    have ht := (div_lt_iff₀ hδ).mp hQ
    linarith only [ht]
  obtain ⟨q, hq, hQq, hshape⟩ :=
    exists_uniform_dyadic_quadrant_grid_shape_error_of_lower_bound g hgc hhom δ hδ Q
  have hqpos : 0 < q := by omega
  have hqcost : 2 * L + m ≤ δ * (q : ℝ) :=
    hQcost.trans (mul_le_mul_of_nonneg_left (by exact_mod_cast hQq) hδ.le)
  have ha := hanimal μ hμ L hL
  have he := ae_eventually_all_dyadic_negativePart_mesh_edges μ p hp hmoment q (by omega)
  have hr := ae_exists_common_weak_grid_ray_threshold μ hμ hpos g hg
  filter_upwards [ha, he, hr] with ω hωa hωe hωr
  obtain ⟨A, hA, hanimals⟩ := hωa δ hδ
  obtain ⟨E, hedges⟩ := hωe δ hδ
  obtain ⟨R, _hR, hrays⟩ := hωr q δ hδ
  let K : ℕ := max E R
  let N : ℕ := max A (q * 2 ^ K)
  refine ⟨N, (by dsimp only [N]; omega), ?_⟩
  intro z hz
  have hzA : A ≤ z.1 + z.2 := (le_max_left _ _).trans hz
  have hzK : q * 2 ^ K ≤ z.1 + z.2 := (le_max_right _ _).trans hz
  obtain ⟨k, hk, hzlo, hzhi⟩ :=
    dyadic_quadrant_shell_index_eventually_large q K (z.1 + z.2) hqpos hzK
  let h : ℕ := 2 ^ k
  have hh : 0 < h := Nat.pow_pos (by decide)
  have hEk : E ≤ k := (le_max_left _ _).trans hk
  have hRh : R ≤ h := by
    have hRk : R ≤ k := (le_max_right _ _).trans hk
    exact hRk.trans (Nat.lt_two_pow_self (n := k)).le
  have hzhi' : z.1 + z.2 < 2 * (q * h) := by
    simpa only [pow_succ, h, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hzhi
  let w : ℕ × ℕ := (h * (z.1 / h), h * (z.2 / h))
  have hgeom := dyadic_quadrant_grid_rounding_properties q h hq hh z hzlo hzhi'
  change w.1 ≤ z.1 ∧ w.2 ≤ z.2 ∧ z.1 - w.1 < h ∧ z.2 - w.2 < h ∧
    (z.1 - w.1) + (z.2 - w.2) < 2 * h ∧ _ at hgeom
  rcases hgeom with ⟨hw₁, hw₂, hgap₁, hgap₂, _hgap, _hexists⟩
  have hi : z.1 / h < 2 * q := by
    apply (Nat.div_lt_iff_lt_mul hh).mpr
    have hc : z.1 < 2 * (q * h) := by omega
    simpa only [Nat.mul_assoc] using hc
  have hj : z.2 / h < 2 * q := by
    apply (Nat.div_lt_iff_lt_mul hh).mpr
    have hc : z.2 < 2 * (q * h) := by omega
    simpa only [Nat.mul_assoc] using hc
  have hedgehor := (hedges k hEk (z.1 / h) hi (z.2 / h) hj.le).1
  have hedgevert := (hedges k hEk (z.2 / h) hj (z.1 / h) hi.le).2
  have hhor : (∑ l : Fin h,
      max (-ω ((w.1 : ℤ) + (l.val : ℤ), (w.2 : ℤ))) 0) ≤
        (h : ℝ) * m + δ * q * (h : ℝ) := by
    rw [Fin.sum_univ_eq_sum_range (fun l : ℕ =>
      max (-ω ((w.1 : ℤ) + (l : ℤ), (w.2 : ℤ))) 0)]
    simpa only [w, h, m, Nat.cast_add,
      Nat.mul_comm, Nat.cast_pow, Nat.cast_ofNat] using hedgehor
  have hver : (∑ l : Fin h,
      max (-ω ((w.1 : ℤ), (w.2 : ℤ) + (l.val : ℤ))) 0) ≤
        (h : ℝ) * m + δ * q * (h : ℝ) := by
    rw [Fin.sum_univ_eq_sum_range (fun l : ℕ =>
      max (-ω ((w.1 : ℤ), (w.2 : ℤ) + (l : ℤ))) 0)]
    simpa only [w, h, m, Nat.cast_add,
      Nat.mul_comm, Nat.cast_pow, Nat.cast_ofNat] using hedgevert
  obtain ⟨cpath, split, haxis, _hgreedy, hcharge, hlower⟩ :=
    exists_backwardGreedy_endpoint_connector ω w z ⟨hw₁, hw₂⟩ L hL h hgap₁ hgap₂
  have hprefix := boundary_prefix_pathWeight_le_full_edges
    (fun v => max (-ω v) 0) (fun _ => le_max_right _ _)
    ((w.1 : ℤ), (w.2 : ℤ)) (z - w) cpath split h hgap₁ hgap₂
    haxis ((h : ℝ) * m + δ * q * (h : ℝ)) hhor hver
  have hanimalsz := (hanimals z hzA).2
  change (∑ c : Fin 2 × Fin 2,
    animalMaximum (z.1 + z.2 + 3) (by omega)
      (sparseMinimumField L c ω)) ≤
        8 * (z.1 + z.2 : ℕ) * (C * (∫ x, max (-L - x) 0 ∂μ) + δ)
      at hanimalsz
  have hcharge' : pathWeight (fun v => max (-ω v) 0) cpath ≤
      2 * L * h + pathWeight (fun v => max (-ω v) 0) (cpath.prefixPath split) +
        ∑ c : Fin 2 × Fin 2, animalMaximum (z.1 + z.2 + 3) (by omega)
          (sparseMinimumField L c ω) := by
    have hfield (c : Fin 2 × Fin 2) :
        (fun a : Lattice =>
          min (max (-L - ω ((2 * a.1 + (c.1.val : ℤ),
              2 * a.2 + (c.2.val : ℤ)) - (1, 0))) 0)
            (max (-L - ω ((2 * a.1 + (c.1.val : ℤ),
              2 * a.2 + (c.2.val : ℤ)) - (0, 1))) 0)) =
            sparseMinimumField L c ω := by
      funext a
      simp only [sparseMinimumField_apply, Prod.mk_sub_mk, sub_zero]
    simpa only [hfield] using hcharge
  have hlen : 0 ≤ ((z.1 + z.2 : ℕ) : ℝ) := Nat.cast_nonneg _
  have hqh : (q : ℝ) * (h : ℝ) ≤ ((z.1 + z.2 : ℕ) : ℝ) := by
    exact_mod_cast hzlo
  have hhLen : (h : ℝ) ≤ ((z.1 + z.2 : ℕ) : ℝ) := by
    have hhq : h ≤ q * h := by nlinarith only [hqpos, hh]
    exact_mod_cast hhq.trans hzlo
  have hcost := mul_le_mul_of_nonneg_right hqcost (Nat.cast_nonneg h)
  have hdeltaqh := mul_le_mul_of_nonneg_left hqh hδ.le
  have hdeltaH := mul_le_mul_of_nonneg_left hhLen hδ.le
  have hanimalSmall := mul_le_mul_of_nonneg_left hsmall.le
    (show 0 ≤ 8 * ((z.1 + z.2 : ℕ) : ℝ) by positivity)
  have hray := hrays h hRh (z.1 / h) (z.2 / h) hi.le hj.le
  have hwscale : g ((w.1 : ℝ≥0), (w.2 : ℝ≥0)) =
      (h : ℝ) * g (((z.1 / h : ℕ) : ℝ≥0), ((z.2 / h : ℕ) : ℝ≥0)) := by
    convert hhom (h : ℝ≥0)
      (((z.1 / h : ℕ) : ℝ≥0), ((z.2 / h : ℕ) : ℝ≥0)) using 1 <;>
      simp only [w, Prod.smul_mk, smul_eq_mul, Nat.cast_mul, NNReal.coe_natCast]
  have hray' : g ((w.1 : ℝ≥0), (w.2 : ℝ≥0)) - lastPassage ω 0 w ≤ δ * h := by
    have hscaled : h • (z.1 / h, z.2 / h) = w := rfl
    rw [hscaled, ← hwscale] at hray
    linarith only [(abs_le.mp hray).1]
  have hsh := hshape k z hzlo hzhi'
  have hshape' : g ((z.1 : ℝ≥0), (z.2 : ℝ≥0)) -
      g ((w.1 : ℝ≥0), (w.2 : ℝ≥0)) ≤ δ * ((z.1 + z.2 : ℕ) : ℝ) :=
    (abs_le.mp hsh).2
  have hεlen : 0 ≤ ε * ((z.1 + z.2 : ℕ) : ℝ) := mul_nonneg hε.le hlen
  dsimp only [δ] at hcost hdeltaqh hdeltaH hanimalSmall hanimalsz hray' hshape' hprefix
  nlinarith only [hcharge', hprefix, hlower, hanimalsz, hanimalSmall,
    hcost, hdeltaqh, hdeltaH, hray', hshape', hεlen]

/-- One original-environment event gives the uniform lower sample law for the
same continuous homogeneous witness identified by the floor expectations. -/
theorem ae_eventually_lastPassage_uniform_lower_of_negative_moment
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : Integrable (fun t : ℝ => t) μ)
    (hpos : (∫⁻ t in Ioi (0 : ℝ), (μ (Ioi t)) ^ (1 / 2 : ℝ)) < ∞)
    (p : ℝ) (hp : 1 < p)
    (hmoment : (∫⁻ t, ENNReal.ofReal ((max (-t) 0) ^ p) ∂μ) < ∞)
    (g : Quadrant → ℝ) (hgc : Continuous g)
    (hhom : ∀ (c : ℝ≥0) (x : Quadrant), g (c • x) = (c : ℝ) * g x)
    (hg : ∀ x : Quadrant, Tendsto (fun n : ℕ =>
      (∫ ω : Environment, lastPassage ω 0
        (⌊(n : ℝ) * (x.1 : ℝ)⌋₊, ⌊(n : ℝ) * (x.2 : ℝ)⌋₊)
        ∂environmentLaw μ) / (n : ℝ)) atTop (𝓝 (g x))) :
    ∀ᵐ ω ∂environmentLaw μ, ∀ ε : ℝ, 0 < ε →
      ∃ N : ℕ, 1 ≤ N ∧ ∀ z : ℕ × ℕ, N ≤ z.1 + z.2 →
        g ((z.1 : ℝ≥0), (z.2 : ℝ≥0)) - lastPassage ω 0 z ≤
          ε * ((z.1 + z.2 : ℕ) : ℝ) := by
  have heach (j : ℕ) :=
    ae_eventually_lastPassage_lower_fixed_tolerance μ hμ hpos p hp hmoment
      g hgc hhom hg (1 / ((j : ℝ) + 1)) (by positivity)
  filter_upwards [ae_all_iff.mpr heach] with ω hω
  intro ε hε
  obtain ⟨j, hj⟩ := exists_nat_one_div_lt hε
  obtain ⟨N, hN, hbound⟩ := hω j
  refine ⟨N, hN, ?_⟩
  intro z hz
  exact (hbound z hz).trans
    (mul_le_mul_of_nonneg_right hj.le (Nat.cast_nonneg _))


end LPPDifferentiability
