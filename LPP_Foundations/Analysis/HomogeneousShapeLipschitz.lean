/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import LPP_Foundations.Analysis.ShapeSupportingFunctionals
import LPP_Foundations.Analysis.ShapeProfileCalculus
import Mathlib.Analysis.Convex.Continuous
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Lipschitz bounds for a homogeneous concave shape

The shape's actual continuity, weighted concavity and nonnegative homogeneity
give a Lipschitz bound on every closed cone strictly inside the quadrant. The
constant is chosen before the points and levels, and the estimate includes the
origin.
-/

public section

open Set
open Metric
open scoped Topology NNReal

namespace LPPDifferentiability

/-- A continuous, weighted-concave, nonnegatively homogeneous function on the
quadrant is Lipschitz on every fixed cone bounded away from both axes. -/
theorem quadrant_homogeneous_shape_lipschitz_on_fraction_cone
    (g : Quadrant → ℝ)
    (hgcont : Continuous g)
    (hgconc : ∀ (x y : Quadrant) (r s : ℝ≥0), r + s = 1 →
      (r : ℝ) * g x + (s : ℝ) * g y ≤ g (r • x + s • y))
    (hhom : ∀ (c : ℝ≥0) (z : Quadrant), g (c • z) = (c : ℝ) * g z)
    (theta : ℝ) (htheta0 : 0 < theta) (_htheta1 : theta < 1 / 2) :
    ∃ L : ℝ, 1 ≤ L ∧ ∀ z w : Quadrant,
      theta * ((z.1 : ℝ) + (z.2 : ℝ)) ≤ (z.1 : ℝ) ∧
      theta * ((z.1 : ℝ) + (z.2 : ℝ)) ≤ (z.2 : ℝ) ∧
      theta * ((w.1 : ℝ) + (w.2 : ℝ)) ≤ (w.1 : ℝ) ∧
      theta * ((w.1 : ℝ) + (w.2 : ℝ)) ≤ (w.2 : ℝ) →
      |g z - g w| ≤ L *
        (|(z.1 : ℝ) - (w.1 : ℝ)| + |(z.2 : ℝ) - (w.2 : ℝ)|) := by
  let level : Quadrant → ℝ := fun z => (z.1 : ℝ) + (z.2 : ℝ)
  let H : ℝ → ℝ := fun t => quadrantExtension g (t, 1 - t)
  have htoQuadrant : Continuous toQuadrant := by
    change Continuous (fun x : ℝ × ℝ => (Real.toNNReal x.1, Real.toNNReal x.2))
    apply continuous_prodMk.mpr
    constructor
    · exact continuous_real_toNNReal.comp continuous_fst
    · exact continuous_real_toNNReal.comp continuous_snd
  have hline : Continuous (fun t : ℝ => (t, 1 - t)) := by
    apply continuous_prodMk.mpr
    constructor
    · exact continuous_id
    · exact continuous_const.sub continuous_id
  have hgext : Continuous (quadrantExtension g) := by
    change Continuous (g ∘ toQuadrant)
    exact hgcont.comp htoQuadrant
  have hHcont : Continuous H := by
    exact hgext.comp hline
  have hHconc : ConcaveOn ℝ (Icc (0 : ℝ) 1) H := by
    simpa [H] using concaveOn_quadrantExtension_profile g hgconc (0 : ℝ)
  have hbound : BddAbove ((fun t : ℝ => |H t|) '' Icc (0 : ℝ) 1) := by
    exact isCompact_Icc.bddAbove_image (continuous_abs.comp hHcont).continuousOn
  obtain ⟨Mraw, hMraw⟩ := bddAbove_def.mp hbound
  let M : ℝ := max 1 Mraw
  have hM : ∀ t ∈ Icc (0 : ℝ) 1, |H t| ≤ M := by
    intro t ht
    have htbound : |H t| ≤ Mraw := hMraw _ ⟨t, ht, rfl⟩
    dsimp [M]
    exact htbound.trans (le_max_right _ _)
  have hMone : 1 ≤ M := by
    dsimp [M]
    exact le_max_left _ _
  have hMnonneg : 0 ≤ M := le_trans (by norm_num) hMone
  have hfracSubset : Icc theta (1 - theta) ⊆ Icc (0 : ℝ) 1 := by
    intro t ht
    constructor
    · linarith [ht.1]
    · linarith [ht.2]
  have hfracBound : ∀ t ∈ Icc theta (1 - theta), |H t| ≤ M := by
    intro t ht
    exact hM t (hfracSubset ht)
  let epsilon : ℝ := theta / 2
  have hepsilon : 0 < epsilon := by
    dsimp [epsilon]
    linarith
  have hballSubset : ball (1 / 2 : ℝ) (1 / 2) ⊆ Icc (0 : ℝ) 1 := by
    intro t ht
    rw [mem_ball, Real.dist_eq] at ht
    have h := abs_lt.mp ht
    constructor <;> linarith
  have hballConc : ConcaveOn ℝ (ball (1 / 2 : ℝ) (1 / 2)) H := by
    refine ⟨convex_ball _ _, ?_⟩
    intro x hx y hy r s hr hs hrs
    exact hHconc.2 (hballSubset hx) (hballSubset hy) hr hs hrs
  let K : ℝ≥0 := (2 * M / epsilon).toNNReal
  have hprofileLip : LipschitzOnWith K H (ball (1 / 2 : ℝ) (1 / 2 - epsilon)) := by
    dsimp [K]
    exact hballConc.lipschitzOnWith_of_abs_le hepsilon (fun t ht =>
      hM t (hballSubset (Metric.mem_ball.2 ht)))
  have hfracSubsetBall : Icc theta (1 - theta) ⊆ ball (1 / 2 : ℝ) (1 / 2 - epsilon) := by
    intro t ht
    rw [mem_ball, Real.dist_eq]
    have habs : |t - 1 / 2| ≤ 1 / 2 - theta :=
      abs_le.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩
    calc
      |t - 1 / 2| ≤ 1 / 2 - theta := habs
      _ < 1 / 2 - epsilon := by
        dsimp [epsilon]
        linarith [htheta0]
  let L0 : ℝ := K
  have hL0nonneg : 0 ≤ L0 := by
    dsimp [L0]
    exact NNReal.coe_nonneg _
  have hprofileBound {t u : ℝ} (ht : t ∈ Icc theta (1 - theta))
      (hu : u ∈ Icc theta (1 - theta)) : |H t - H u| ≤ L0 * |t - u| := by
    have hdist := hprofileLip.dist_le_mul t (hfracSubsetBall ht) u (hfracSubsetBall hu)
    simpa only [Real.dist_eq, L0] using hdist
  have hnormalized (z : Quadrant) (hz : z ≠ 0) :
      0 < level z ∧
      (z.1 : ℝ) / level z ∈ Icc (0 : ℝ) 1 ∧
      g z = level z * H ((z.1 : ℝ) / level z) := by
    rcases quadrant_homogeneous_profile_normalization g hhom 0 z hz with
      ⟨hn, hinterval, hvalue⟩
    constructor
    · simpa [level] using hn
    constructor
    · simpa [level] using hinterval
    · simpa [H, level] using hvalue
  have hprofileFraction (z : Quadrant) (hz : z ≠ 0)
      (hcone : theta * level z ≤ (z.1 : ℝ) ∧ theta * level z ≤ (z.2 : ℝ)) :
      (z.1 : ℝ) / level z ∈ Icc theta (1 - theta) := by
    rcases hnormalized z hz with ⟨hn, -, -⟩
    constructor
    · apply (le_div_iff₀ hn).2
      exact hcone.1
    · apply (div_le_iff₀ hn).2
      dsimp [level] at hn hcone ⊢
      nlinarith [hcone.2]
  let L : ℝ := 2 * L0 + M
  have hL : 1 ≤ L := by
    dsimp [L]
    linarith [hMone, hL0nonneg]
  have hLM : M ≤ L := by
    dsimp [L]
    linarith [hL0nonneg]
  have hlevelDiff (z w : Quadrant) :
      |level z - level w| ≤
        |(z.1 : ℝ) - (w.1 : ℝ)| + |(z.2 : ℝ) - (w.2 : ℝ)| := by
    dsimp [level]
    calc
      |((z.1 : ℝ) + (z.2 : ℝ)) - ((w.1 : ℝ) + (w.2 : ℝ))| =
          |((z.1 : ℝ) - (w.1 : ℝ)) + ((z.2 : ℝ) - (w.2 : ℝ))| := by
            congr 1; ring
      _ ≤ |(z.1 : ℝ) - (w.1 : ℝ)| + |(z.2 : ℝ) - (w.2 : ℝ)| := abs_add_le _ _
  have hquotient (z w : Quadrant) (hz : z ≠ 0) (hw : w ≠ 0) :
      level z * |(z.1 : ℝ) / level z - (w.1 : ℝ) / level w| ≤
        |(z.1 : ℝ) - (w.1 : ℝ)| + |level z - level w| := by
    rcases hnormalized z hz with ⟨hn, -, -⟩
    rcases hnormalized w hw with ⟨hm, -, -⟩
    have hw1nonneg : 0 ≤ (w.1 : ℝ) := NNReal.coe_nonneg _
    have hw1le : (w.1 : ℝ) ≤ level w := by
      dsimp [level]
      nlinarith [NNReal.coe_nonneg w.2]
    have hratio0 : 0 ≤ (w.1 : ℝ) / level w := div_nonneg hw1nonneg hm.le
    have hratio1 : (w.1 : ℝ) / level w ≤ 1 :=
      (div_le_one hm).2 hw1le
    have hratioAbs : |(w.1 : ℝ) / level w| ≤ 1 := by
      rw [abs_of_nonneg hratio0]
      exact hratio1
    have halgebra : level z *
        ((z.1 : ℝ) / level z - (w.1 : ℝ) / level w) =
        ((z.1 : ℝ) - (w.1 : ℝ)) +
          ((w.1 : ℝ) / level w) * (level w - level z) := by
      field_simp [ne_of_gt hn, ne_of_gt hm]
      ring
    calc
      level z * |(z.1 : ℝ) / level z - (w.1 : ℝ) / level w| =
          |level z| * |(z.1 : ℝ) / level z - (w.1 : ℝ) / level w| := by
            rw [abs_of_nonneg hn.le]
      _ = |level z * ((z.1 : ℝ) / level z - (w.1 : ℝ) / level w)| := by
            rw [abs_mul]
      _ = |((z.1 : ℝ) - (w.1 : ℝ)) +
          ((w.1 : ℝ) / level w) * (level w - level z)| := by rw [halgebra]
      _ ≤ |(z.1 : ℝ) - (w.1 : ℝ)| +
          |(w.1 : ℝ) / level w| * |level w - level z| := by
            calc
              |(z.1 : ℝ) - (w.1 : ℝ) +
                  ((w.1 : ℝ) / level w) * (level w - level z)| ≤
                  |(z.1 : ℝ) - (w.1 : ℝ)| +
                    |((w.1 : ℝ) / level w) * (level w - level z)| := abs_add_le _ _
              _ = |(z.1 : ℝ) - (w.1 : ℝ)| +
                  |(w.1 : ℝ) / level w| * |level w - level z| := by rw [abs_mul]
      _ ≤ |(z.1 : ℝ) - (w.1 : ℝ)| + |level w - level z| := by
            have hprod := mul_le_mul_of_nonneg_right hratioAbs (abs_nonneg (level w - level z))
            linarith
      _ = |(z.1 : ℝ) - (w.1 : ℝ)| + |level z - level w| := by
            exact congrArg (fun q : ℝ => |(z.1 : ℝ) - (w.1 : ℝ)| + q)
              (abs_sub_comm (level w) (level z))
  have hordered (z w : Quadrant) (hz : z ≠ 0) (hw : w ≠ 0)
      (hcz : theta * level z ≤ (z.1 : ℝ) ∧ theta * level z ≤ (z.2 : ℝ))
      (hcw : theta * level w ≤ (w.1 : ℝ) ∧ theta * level w ≤ (w.2 : ℝ))
      (hnm : level z ≤ level w) :
      |g z - g w| ≤ L *
        (|(z.1 : ℝ) - (w.1 : ℝ)| + |(z.2 : ℝ) - (w.2 : ℝ)|) := by
    rcases hnormalized z hz with ⟨hn, -, hgz⟩
    rcases hnormalized w hw with ⟨hm, -, hgw⟩
    let n : ℝ := level z
    let m : ℝ := level w
    let t : ℝ := (z.1 : ℝ) / n
    let u : ℝ := (w.1 : ℝ) / m
    have hgz' : g z = n * H t := by simpa [n, t] using hgz
    have hgw' : g w = m * H u := by simpa [m, u] using hgw
    have ht : t ∈ Icc theta (1 - theta) := by
      simpa [n, t] using hprofileFraction z hz hcz
    have hu : u ∈ Icc theta (1 - theta) := by
      simpa [m, u] using hprofileFraction w hw hcw
    have htbound : |H t - H u| ≤ L0 * |t - u| := hprofileBound ht hu
    let d : ℝ := |(z.1 : ℝ) - (w.1 : ℝ)| + |(z.2 : ℝ) - (w.2 : ℝ)|
    have hndiff : |n - m| ≤ d := by
      simpa [n, m, d] using hlevelDiff z w
    have hxdiff : |(z.1 : ℝ) - (w.1 : ℝ)| ≤ d := by
      dsimp [d]
      exact le_add_of_nonneg_right (abs_nonneg _)
    have hquot := hquotient z w hz hw
    have hsum : |(z.1 : ℝ) - (w.1 : ℝ)| + |n - m| ≤ d + d :=
      add_le_add hxdiff hndiff
    have hsplit : n * H t - m * H u = n * (H t - H u) + (n - m) * H u := by
      ring
    calc
      |g z - g w| = |n * H t - m * H u| := by rw [hgz', hgw']
      _ = |n * (H t - H u) + (n - m) * H u| := by rw [hsplit]
      _ ≤ |n * (H t - H u)| + |(n - m) * H u| := abs_add_le _ _
      _ = n * |H t - H u| + |n - m| * |H u| := by
        rw [abs_mul, abs_mul, abs_of_nonneg hn.le]
      _ ≤ n * (L0 * |t - u|) + |n - m| * M := by
        exact add_le_add
          (mul_le_mul_of_nonneg_left htbound hn.le)
          (mul_le_mul_of_nonneg_left (hfracBound u hu) (abs_nonneg (n - m)))
      _ = L0 * (n * |t - u|) + |n - m| * M := by ring
      _ ≤ L0 * (|(z.1 : ℝ) - (w.1 : ℝ)| + |n - m|) + |n - m| * M := by
        exact add_le_add (mul_le_mul_of_nonneg_left hquot hL0nonneg) le_rfl
      _ ≤ L0 * (d + d) + d * M := by
        exact add_le_add
          (mul_le_mul_of_nonneg_left hsum hL0nonneg)
          (mul_le_mul_of_nonneg_right hndiff hMnonneg)
      _ = L * d := by
        dsimp [L]
        ring
  have hzero : g (0 : Quadrant) = 0 :=
    quadrant_smul_homogeneous_at_zero g hhom
  have horigin (z : Quadrant)
      (hcz : theta * level z ≤ (z.1 : ℝ) ∧ theta * level z ≤ (z.2 : ℝ)) :
      |g z - g 0| ≤ L *
        (|(z.1 : ℝ) - 0| + |(z.2 : ℝ) - 0|) := by
    by_cases hz : z = 0
    · subst z
      simp [hzero]
    · rcases hnormalized z hz with ⟨hn, -, hgz⟩
      let t : ℝ := (z.1 : ℝ) / level z
      have ht : t ∈ Icc theta (1 - theta) := by
        simpa [t] using hprofileFraction z hz hcz
      have htbound : |H t| ≤ M := hfracBound t ht
      have hvalue : g z = level z * H t := by simpa [t] using hgz
      have hdist : |(z.1 : ℝ) - 0| + |(z.2 : ℝ) - 0| = level z := by
        simp [level, abs_of_nonneg]
      calc
        |g z - g 0| = level z * |H t| := by
          rw [hzero, hvalue, sub_zero, abs_mul, abs_of_nonneg hn.le]
        _ ≤ level z * M := mul_le_mul_of_nonneg_left htbound hn.le
        _ = M * level z := by ring
        _ ≤ L * level z := mul_le_mul_of_nonneg_right hLM hn.le
        _ = L * (|(z.1 : ℝ) - 0| + |(z.2 : ℝ) - 0|) := by rw [hdist]
  refine ⟨L, hL, ?_⟩
  intro z w hcone
  rcases hcone with ⟨hcz1, hcz2, hcw1, hcw2⟩
  let hcz : theta * level z ≤ (z.1 : ℝ) ∧ theta * level z ≤ (z.2 : ℝ) := ⟨hcz1, hcz2⟩
  let hcw : theta * level w ≤ (w.1 : ℝ) ∧ theta * level w ≤ (w.2 : ℝ) := ⟨hcw1, hcw2⟩
  by_cases hz : z = 0
  · subst z
    have h := horigin w hcw
    simpa [hzero, abs_sub_comm, add_comm] using h
  by_cases hw : w = 0
  · subst w
    exact horigin z hcz
  rcases le_total (level z) (level w) with hlevels | hlevels
  · exact hordered z w hz hw hcz hcw hlevels
  · have h := hordered w z hw hz hcw hcz hlevels
    simpa [abs_sub_comm, add_comm] using h

/-- The same constant controls the source cone around any direction strictly
inside the quadrant. -/
theorem quadrant_homogeneous_shape_lipschitz_on_adapted_cone
    (g : Quadrant → ℝ)
    (hgcont : Continuous g)
    (hgconc : ∀ (x y : Quadrant) (r s : ℝ≥0), r + s = 1 →
      (r : ℝ) * g x + (s : ℝ) * g y ≤ g (r • x + s • y))
    (hhom : ∀ (c : ℝ≥0) (z : Quadrant), g (c • z) = (c : ℝ) * g z)
    (a theta : ℝ) (_ha0 : 0 < a) (_ha1 : a < 1)
    (htheta0 : 0 < theta) (htheta : theta < min a (1 - a)) :
    ∃ L : ℝ, 1 ≤ L ∧ ∀ z w : Quadrant,
      |(1 - a) * (z.1 : ℝ) - a * (z.2 : ℝ)| ≤
        (min a (1 - a) - theta) * ((z.1 : ℝ) + (z.2 : ℝ)) ∧
      |(1 - a) * (w.1 : ℝ) - a * (w.2 : ℝ)| ≤
        (min a (1 - a) - theta) * ((w.1 : ℝ) + (w.2 : ℝ)) →
      |g z - g w| ≤ L *
        (|(z.1 : ℝ) - (w.1 : ℝ)| + |(z.2 : ℝ) - (w.2 : ℝ)|) := by
  have hthetaHalf : theta < 1 / 2 := by
    have hmina : min a (1 - a) ≤ a := min_le_left _ _
    have hminb : min a (1 - a) ≤ 1 - a := min_le_right _ _
    have hthetaA : theta < a := lt_of_lt_of_le htheta hmina
    have hthetaB : theta < 1 - a := lt_of_lt_of_le htheta hminb
    linarith
  rcases quadrant_homogeneous_shape_lipschitz_on_fraction_cone
      g hgcont hgconc hhom theta htheta0 hthetaHalf with ⟨L, hL, hLip⟩
  refine ⟨L, hL, ?_⟩
  intro z w hcone
  rcases hcone with ⟨hzrho, hwrho⟩
  have hlevelz : 0 ≤ (z.1 : ℝ) + (z.2 : ℝ) := by positivity
  have hlevelw : 0 ≤ (w.1 : ℝ) + (w.2 : ℝ) := by positivity
  have hcoordz : theta * ((z.1 : ℝ) + (z.2 : ℝ)) ≤ (z.1 : ℝ) ∧
      theta * ((z.1 : ℝ) + (z.2 : ℝ)) ≤ (z.2 : ℝ) := by
    have hminA : min a (1 - a) ≤ a := min_le_left _ _
    have hminB : min a (1 - a) ≤ 1 - a := min_le_right _ _
    have hgapA : 0 ≤ (a - min a (1 - a)) * ((z.1 : ℝ) + (z.2 : ℝ)) :=
      mul_nonneg (sub_nonneg.mpr hminA) hlevelz
    have hgapB : 0 ≤ ((1 - a) - min a (1 - a)) * ((z.1 : ℝ) + (z.2 : ℝ)) :=
      mul_nonneg (sub_nonneg.mpr hminB) hlevelz
    have hsplit :
        (1 - a) * (z.1 : ℝ) - a * (z.2 : ℝ) =
          (z.1 : ℝ) - a * ((z.1 : ℝ) + (z.2 : ℝ)) := by ring
    rw [hsplit] at hzrho
    have habs := abs_le.mp hzrho
    constructor <;> nlinarith [habs.1, habs.2, hlevelz, hminA, hminB, hgapA, hgapB]
  have hcoordw : theta * ((w.1 : ℝ) + (w.2 : ℝ)) ≤ (w.1 : ℝ) ∧
      theta * ((w.1 : ℝ) + (w.2 : ℝ)) ≤ (w.2 : ℝ) := by
    have hminA : min a (1 - a) ≤ a := min_le_left _ _
    have hminB : min a (1 - a) ≤ 1 - a := min_le_right _ _
    have hgapA : 0 ≤ (a - min a (1 - a)) * ((w.1 : ℝ) + (w.2 : ℝ)) :=
      mul_nonneg (sub_nonneg.mpr hminA) hlevelw
    have hgapB : 0 ≤ ((1 - a) - min a (1 - a)) * ((w.1 : ℝ) + (w.2 : ℝ)) :=
      mul_nonneg (sub_nonneg.mpr hminB) hlevelw
    have hsplit :
        (1 - a) * (w.1 : ℝ) - a * (w.2 : ℝ) =
          (w.1 : ℝ) - a * ((w.1 : ℝ) + (w.2 : ℝ)) := by ring
    rw [hsplit] at hwrho
    have habs := abs_le.mp hwrho
    constructor <;> nlinarith [habs.1, habs.2, hlevelw, hminA, hminB, hgapA, hgapB]
  exact hLip z w ⟨hcoordz.1, hcoordz.2, hcoordw.1, hcoordw.2⟩

end LPPDifferentiability

