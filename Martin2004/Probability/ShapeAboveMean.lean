/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Martin2004.Probability.WeakNegativeShape
public import LPP_Foundations.Probability.PassageMeanBounds

import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Probability.StrongLaw
import LPP_Foundations.Model.Paths.Geometry
import LPP_Foundations.Model.Paths.HorizontalFirst

/-! # The shape function lies above the mean weight

Under the weak negative moment and the positive integrated square-root tail,
the shape `g` satisfies `(x.1 + x.2) * E w_0 ≤ g x` at every point of the
closed quadrant. The proof compares the almost-sure limit of the normalized
passage times with the strong-law limit along a fixed path. Homogeneity and
continuity extend the lattice bound through rational points to the full
quadrant.
-/

public section

open MeasureTheory Filter Set ProbabilityTheory
open scoped BigOperators Topology ENNReal NNReal

namespace LPPDifferentiability

/-- The starting point of period `n` of the deterministic path in direction `d`. -/
private def periodStart (d : ℕ × ℕ) (n : ℕ) : Lattice :=
  (((n * d.1 : ℕ) : ℤ), ((n * d.2 : ℕ) : ℤ))

/-- Repeat a translated copy of the horizontal-first path in every period. -/
private def fixedRayVertex (d : ℕ × ℕ) (hd : 0 < d.1 + d.2) (k : ℕ) : Lattice :=
  periodStart d (k / (d.1 + d.2)) +
    (horizontalFirst 0 d).vertex ⟨k % (d.1 + d.2), Nat.lt_succ_of_lt (Nat.mod_lt k hd)⟩

/-- The period formula includes its last vertex, which is the start of the next period. -/
private theorem fixedRayVertex_period (d : ℕ × ℕ) (hd : 0 < d.1 + d.2)
    (q : ℕ) (i : Fin (d.1 + d.2 + 1)) :
    fixedRayVertex d hd ((d.1 + d.2) * q + i.val) =
      periodStart d q + (horizontalFirst 0 d).vertex i := by
  by_cases hi : i.val < d.1 + d.2
  · unfold fixedRayVertex
    simp only [Nat.mul_add_div hd, Nat.div_eq_of_lt hi, Nat.add_zero]
    apply congrArg (fun j => periodStart d q + (horizontalFirst 0 d).vertex j)
    exact Fin.ext ((Nat.mul_add_mod _ _ _).trans (Nat.mod_eq_of_lt hi))
  · have hi' : i = Fin.last (d.1 + d.2) := by
      apply Fin.ext
      simp only [Fin.val_last]
      have := i.isLt
      omega
    subst i
    simp only [Fin.val_last, ← Nat.mul_succ, fixedRayVertex, Nat.mul_div_cancel_left _ hd]
    have hzero : (⟨((d.1 + d.2) * (q + 1)) % (d.1 + d.2),
        Nat.lt_succ_of_lt (Nat.mod_lt _ hd)⟩ : Fin (d.1 + d.2 + 1)) = 0 :=
      Fin.ext (Nat.mul_mod_right _ _)
    rw [hzero, (horizontalFirst 0 d).start, (horizontalFirst 0 d).finish,
      add_zero, zero_add]
    apply Prod.ext <;> simp only [periodStart, Prod.fst_add, Prod.snd_add, Nat.cast_mul,
      Nat.cast_succ] <;> ring

private theorem fixedRayVertex_step (d : ℕ × ℕ) (hd : 0 < d.1 + d.2) (k : ℕ) :
    fixedRayVertex d hd (k + 1) = fixedRayVertex d hd k + (1, 0) ∨
      fixedRayVertex d hd (k + 1) = fixedRayVertex d hd k + (0, 1) := by
  let q := k / (d.1 + d.2)
  let i : Fin (d.1 + d.2) := ⟨k % (d.1 + d.2), Nat.mod_lt k hd⟩
  have hindex : (d.1 + d.2) * q + i.val = k := Nat.div_add_mod _ _
  have hbefore := fixedRayVertex_period d hd q i.castSucc
  have hafter := fixedRayVertex_period d hd q i.succ
  rw [Fin.val_castSucc, hindex] at hbefore
  rw [Fin.val_succ, ← Nat.add_assoc, hindex] at hafter
  rw [hbefore, hafter]
  rcases (horizontalFirst 0 d).step i with h | h
  · exact Or.inl (by rw [h, add_assoc])
  · exact Or.inr (by rw [h, add_assoc])

private theorem fixedRayVertex_injective (d : ℕ × ℕ) (hd : 0 < d.1 + d.2) :
    Function.Injective (fixedRayVertex d hd) := by
  have hlevel (k : ℕ) : (fixedRayVertex d hd k).1 + (fixedRayVertex d hd k).2 = (k : ℤ) := by
    let i : Fin (d.1 + d.2 + 1) :=
      ⟨k % (d.1 + d.2), Nat.lt_succ_of_lt (Nat.mod_lt k hd)⟩
    let p := horizontalFirst 0 d
    calc
      _ = (((d.1 + d.2) * (k / (d.1 + d.2)) : ℕ) : ℤ) +
          ((p.vertex i).1 + (p.vertex i).2) := by
        change (periodStart d _ + p.vertex i).1 + (periodStart d _ + p.vertex i).2 = _
        simp only [periodStart, Prod.fst_add, Prod.snd_add, Nat.cast_mul, Nat.cast_add]
        ring
      _ = (k : ℤ) := by
        rw [p.level i]
        change (((d.1 + d.2) * (k / (d.1 + d.2)) : ℕ) : ℤ) +
          (0 + 0 + ((k % (d.1 + d.2) : ℕ) : ℤ)) = (k : ℤ)
        simp only [zero_add, ← Nat.cast_add, Nat.div_add_mod]
  intro k l h
  exact Int.ofNat.inj ((hlevel k).symm.trans ((congrArg (fun z : Lattice => z.1 + z.2) h).trans
    (hlevel l)))

/-- The first `n` periods are an admissible path to the lattice point `nd`. -/
private def fixedRayPrefix (d : ℕ × ℕ) (hd : 0 < d.1 + d.2) (n : ℕ) :
    Path 0 (n * d.1, n * d.2) where
  vertex i := fixedRayVertex d hd i.val
  start := by
    change fixedRayVertex d hd 0 = 0
    have h := fixedRayVertex_period d hd 0 (0 : Fin (d.1 + d.2 + 1))
    rw [(horizontalFirst 0 d).start, add_zero] at h
    rw [Prod.zero_eq_mk]
    simpa only [Fin.val_zero, mul_zero, add_zero, periodStart, zero_mul, Nat.cast_zero] using h
  finish := by
    change fixedRayVertex d hd (n * d.1 + n * d.2) = 0 + periodStart d n
    rw [← Nat.mul_add, Nat.mul_comm n]
    simpa only [Fin.val_zero, add_zero, zero_add, (horizontalFirst 0 d).start] using
      fixedRayVertex_period d hd n (0 : Fin (d.1 + d.2 + 1))
  step i := fixedRayVertex_step d hd i.val

private theorem fixedRayPrefix_weight (ω : Environment) (d : ℕ × ℕ)
    (hd : 0 < d.1 + d.2) (n : ℕ) :
    pathWeight ω (fixedRayPrefix d hd n) =
      ∑ k ∈ Finset.range (n * (d.1 + d.2)), ω (fixedRayVertex d hd k) := by
  rw [Nat.mul_add]
  exact Fin.sum_univ_eq_sum_range (fun k => ω (fixedRayVertex d hd k)) _

/-- The uniform shape approximation implies the normalized lattice-ray limit. -/
private theorem lastPassage_fixedRay_tendsto (g : Quadrant → ℝ)
    (hgh : ∀ (c : ℝ≥0) (x : Quadrant), g (c * x.1, c * x.2) = (c : ℝ) * g x)
    (ω : Environment)
    (hω : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, 1 ≤ N ∧ ∀ d : ℕ × ℕ, N ≤ d.1 + d.2 →
      |lastPassage ω 0 d - g ((d.1 : ℝ≥0), (d.2 : ℝ≥0))| ≤
        ε * ((d.1 + d.2 : ℕ) : ℝ))
    (d : ℕ × ℕ) (hd : 0 < d.1 + d.2) :
    Tendsto (fun n : ℕ => lastPassage ω 0 (n * d.1, n * d.2) / (n : ℝ)) atTop
      (𝓝 (g ((d.1 : ℝ≥0), (d.2 : ℝ≥0)))) := by
  apply Metric.tendsto_atTop.2
  intro ε hε
  let L : ℝ := (d.1 + d.2 : ℕ)
  have hL : 0 < L := Nat.cast_pos.mpr hd
  obtain ⟨N, hN, hbound⟩ := hω (ε / (2 * L)) (by positivity)
  refine ⟨N, fun n hn => ?_⟩
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr (hN.trans hn)
  have hlevel : N ≤ n * d.1 + n * d.2 := by
    rw [← Nat.mul_add]
    exact hn.trans (Nat.le_mul_of_pos_right n hd)
  have h := hbound (n * d.1, n * d.2) hlevel
  have hhom := hgh (n : ℝ≥0) ((d.1 : ℝ≥0), (d.2 : ℝ≥0))
  simp only [← Nat.cast_mul, NNReal.coe_natCast] at hhom
  dsimp only at h
  rw [hhom, ← Nat.mul_add, Nat.cast_mul] at h
  have herr : lastPassage ω 0 (n * d.1, n * d.2) / (n : ℝ) -
      g ((d.1 : ℝ≥0), (d.2 : ℝ≥0)) =
      (lastPassage ω 0 (n * d.1, n * d.2) -
        (n : ℝ) * g ((d.1 : ℝ≥0), (d.2 : ℝ≥0))) / (n : ℝ) := by
    rw [sub_div, mul_div_cancel_left₀ _ hnR.ne']
  rw [Real.dist_eq, herr, abs_div, abs_of_pos hnR, div_lt_iff₀ hnR]
  calc
    _ ≤ ε / (2 * L) * ((n : ℝ) * L) := h
    _ = ε / 2 * (n : ℝ) := by field_simp [hL.ne']
    _ < ε * (n : ℝ) := mul_lt_mul_of_pos_right (by linarith) hnR

/-- The fixed path has the first-moment limit claimed in (S3). -/
private theorem ae_fixedRayPrefix_weight_tendsto (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : Integrable (fun t : ℝ => t) μ) (d : ℕ × ℕ) (hd : 0 < d.1 + d.2) :
    ∀ᵐ ω ∂environmentLaw μ, Tendsto
      (fun n : ℕ => pathWeight ω (fixedRayPrefix d hd n) / (n : ℝ)) atTop
        (𝓝 (((d.1 + d.2 : ℕ) : ℝ) * ∫ t : ℝ, t ∂μ)) := by
  let X (k : ℕ) (ω : Environment) := ω (fixedRayVertex d hd k)
  have hX := (iIndepFun_environment_eval μ).precomp (fixedRayVertex_injective d hd)
  have hident (k : ℕ) : IdentDistrib (X k) (X 0) (environmentLaw μ) (environmentLaw μ) :=
    ⟨(measurable_environment_eval _).aemeasurable,
      (measurable_environment_eval _).aemeasurable,
      (environmentLaw_map_eval μ _).trans (environmentLaw_map_eval μ _).symm⟩
  have hslln := strong_law_ae_real X (integrable_environment_eval μ hμ _)
    (fun _ _ hij => hX.indepFun hij) hident
  change ∀ᵐ ω ∂environmentLaw μ, Tendsto (fun n : ℕ => (∑ k ∈ Finset.range n, X k ω) / (n : ℝ))
    atTop (𝓝 (∫ ω : Environment, ω (fixedRayVertex d hd 0) ∂environmentLaw μ)) at hslln
  rw [integral_environment_eval μ hμ] at hslln
  have htime : Tendsto (fun n : ℕ => n * (d.1 + d.2)) atTop atTop :=
    tendsto_atTop.2 fun N => (eventually_ge_atTop N).mono fun n hn =>
      hn.trans (Nat.le_mul_of_pos_right n hd)
  filter_upwards [hslln] with ω hω
  have hscaled := (hω.comp htime).const_mul (((d.1 + d.2 : ℕ) : ℝ))
  refine hscaled.congr fun n => ?_
  simp only [Function.comp_apply, fixedRayPrefix_weight, X, Nat.cast_mul]
  rw [← div_div, ← mul_div_assoc, mul_comm (((d.1 + d.2 : ℕ) : ℝ)),
    mul_div_cancel_right₀ _ (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hd))]

/-- Property (S3) of the differentiability paper (final draft, line 298): the
shape is at least the level times the mean weight on the closed quadrant. -/
theorem level_mul_integral_le_shape_of_negative_moment_and_positive_tail
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hneg : ∃ p : ℝ, 1 < p ∧
      (∫⁻ t, ENNReal.ofReal ((max (-t) 0) ^ p) ∂μ) < ∞)
    (hpos : (∫⁻ t in Ioi (0 : ℝ), (μ (Ioi t)) ^ (1 / 2 : ℝ)) < ∞)
    (g : Quadrant → ℝ) (hgc : Continuous g)
    (hgh : ∀ (c : ℝ≥0) (x : Quadrant),
      g (c * x.1, c * x.2) = (c : ℝ) * g x)
    (hgconc : ∀ (x y : Quadrant) (a b : ℝ≥0), a + b = 1 →
      (a : ℝ) * g x + (b : ℝ) * g y ≤
        g (a * x.1 + b * y.1, a * x.2 + b * y.2))
    (hgae : ∀ᵐ ω ∂environmentLaw μ, ∀ ε : ℝ, 0 < ε →
      ∃ N : ℕ, 1 ≤ N ∧ ∀ d : ℕ × ℕ, N ≤ d.1 + d.2 →
        |lastPassage ω 0 d - g ((d.1 : ℝ≥0), (d.2 : ℝ≥0))| ≤
          ε * ((d.1 + d.2 : ℕ) : ℝ))
    (x : Quadrant) :
    ((x.1 : ℝ) + (x.2 : ℝ)) * ∫ t : ℝ, t ∂μ ≤ g x := by
  have _ := hgconc
  have hμ := integrable_id_of_negative_moment_and_positive_tail μ hneg hpos
  let m : ℝ := ∫ t : ℝ, t ∂μ
  -- On a lattice ray, compare the path and passage limits in the same environment.
  have hnat (a b : ℕ) : ((a : ℝ) + (b : ℝ)) * m ≤ g ((a : ℝ≥0), (b : ℝ≥0)) := by
    by_cases hzero : a + b = 0
    · have ha : a = 0 := by omega
      have hb : b = 0 := by omega
      subst a b
      simp only [Nat.cast_zero, add_zero, zero_mul, homogeneous_quadrant_zero g hgh, le_refl]
    · have hlevel : 0 < (a, b).1 + (a, b).2 := Nat.pos_of_ne_zero hzero
      have hpath := ae_fixedRayPrefix_weight_tendsto μ hμ (a, b) hlevel
      obtain ⟨ω, hωshape, hωpath⟩ := (hgae.and hpath).exists
      have hpassage := lastPassage_fixedRay_tendsto g hgh ω hωshape (a, b) hlevel
      have hle := le_of_tendsto_of_tendsto' hωpath hpassage fun n =>
        div_le_div_of_nonneg_right (pathWeight_le_lastPassage ω (fixedRayPrefix (a, b) hlevel n))
          (Nat.cast_nonneg n)
      simpa only [Nat.cast_add] using hle
  -- Homogeneity gives the inequality at every scaled lattice point, including rationals.
  have hscaled (c : ℝ≥0) (a b : ℕ) :
      (((c * (a : ℝ≥0) : ℝ≥0) : ℝ) + ((c * (b : ℝ≥0) : ℝ≥0) : ℝ)) * m ≤
        g (c * (a : ℝ≥0), c * (b : ℝ≥0)) := by
    rw [hgh c ((a : ℝ≥0), (b : ℝ≥0))]
    simp only [NNReal.coe_mul, NNReal.coe_natCast, ← mul_add, mul_assoc]
    exact mul_le_mul_of_nonneg_left (hnat a b) c.2
  -- Rational grid points converge to x in both coordinates, including on the axes.
  let r (a : ℝ≥0) (n : ℕ) : ℝ≥0 := (n : ℝ≥0)⁻¹ * (⌊(a : ℝ) * (n : ℝ)⌋₊ : ℝ≥0)
  have hfloor (a : ℝ≥0) : Tendsto (fun n : ℕ => (r a n : ℝ)) atTop (𝓝 (a : ℝ)) := by
    have h := (tendsto_nat_floor_mul_div_atTop (R := ℝ) a.2).comp tendsto_natCast_atTop_atTop
    refine h.congr fun n => ?_
    change ((⌊(a : ℝ) * (n : ℝ)⌋₊ : ℕ) : ℝ) / (n : ℝ) =
      (((n : ℝ≥0)⁻¹ * (⌊(a : ℝ) * (n : ℝ)⌋₊ : ℝ≥0) : ℝ≥0) : ℝ)
    rw [NNReal.coe_mul, NNReal.coe_inv, NNReal.coe_natCast, NNReal.coe_natCast, div_eq_inv_mul]
  have hr : Tendsto (fun n : ℕ => (r x.1 n, r x.2 n)) atTop (𝓝 x) :=
    (NNReal.tendsto_coe.1 (hfloor x.1)).prodMk_nhds (NNReal.tendsto_coe.1 (hfloor x.2))
  exact le_of_tendsto_of_tendsto' (((hfloor x.1).add (hfloor x.2)).mul_const m)
    ((hgc.tendsto x).comp hr) fun n =>
      hscaled (n : ℝ≥0)⁻¹ ⌊(x.1 : ℝ) * (n : ℝ)⌋₊ ⌊(x.2 : ℝ) * (n : ℝ)⌋₊

/-- The unit-level form of (S3) (final draft, line 298): if `a + b = 1`,
the shape at `(a, b)` is at least the mean weight. -/
theorem integral_le_shape_of_negative_moment_and_positive_tail
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hneg : ∃ p : ℝ, 1 < p ∧
      (∫⁻ t, ENNReal.ofReal ((max (-t) 0) ^ p) ∂μ) < ∞)
    (hpos : (∫⁻ t in Ioi (0 : ℝ), (μ (Ioi t)) ^ (1 / 2 : ℝ)) < ∞)
    (g : Quadrant → ℝ) (hgc : Continuous g)
    (hgh : ∀ (c : ℝ≥0) (x : Quadrant),
      g (c * x.1, c * x.2) = (c : ℝ) * g x)
    (hgconc : ∀ (x y : Quadrant) (a b : ℝ≥0), a + b = 1 →
      (a : ℝ) * g x + (b : ℝ) * g y ≤
        g (a * x.1 + b * y.1, a * x.2 + b * y.2))
    (hgae : ∀ᵐ ω ∂environmentLaw μ, ∀ ε : ℝ, 0 < ε →
      ∃ N : ℕ, 1 ≤ N ∧ ∀ d : ℕ × ℕ, N ≤ d.1 + d.2 →
        |lastPassage ω 0 d - g ((d.1 : ℝ≥0), (d.2 : ℝ≥0))| ≤
          ε * ((d.1 + d.2 : ℕ) : ℝ))
    (a b : ℝ≥0) (hab : a + b = 1) :
    ∫ t : ℝ, t ∂μ ≤ g (a, b) := by
  have h := level_mul_integral_le_shape_of_negative_moment_and_positive_tail
    μ hneg hpos g hgc hgh hgconc hgae (a, b)
  have hab' : (a : ℝ) + (b : ℝ) = 1 := by exact_mod_cast hab
  simpa only [hab', one_mul] using h

end LPPDifferentiability
