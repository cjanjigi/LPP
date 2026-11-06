/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import LPP_Foundations.Model.Paths.Split
public import LPP_Foundations.Analysis.ShapeSupportingFunctionals
public import LPP_Foundations.Model.LastPassage.Basic
import LPP_Foundations.Model.Paths.WeightBounds
import LPP_Foundations.Model.Paths.WeightZero
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Exact source-support algebra for actual terminal-excluded path weights. -/

@[expose] public section

open scoped NNReal

namespace LPPDifferentiability
namespace Path

/-- The source level and signed transverse coordinate are linear on the entire
real plane, so each source support is additive without a quadrant restriction. -/
theorem source_support_add (t G slope : ℝ) (z w : ℝ × ℝ) :
    (fun z : ℝ × ℝ =>
      G * (z.1 + z.2) + slope * ((1 - t) * z.1 - t * z.2)) (z + w) =
      ((fun z : ℝ × ℝ =>
        G * (z.1 + z.2) + slope * ((1 - t) * z.1 - t * z.2)) z) +
      ((fun z : ℝ × ℝ =>
        G * (z.1 + z.2) + slope * ((1 - t) * z.1 - t * z.2)) w) := by
  change G * ((z + w).1 + (z + w).2) +
      slope * ((1 - t) * (z + w).1 - t * (z + w).2) =
    (G * (z.1 + z.2) + slope * ((1 - t) * z.1 - t * z.2)) +
      (G * (w.1 + w.2) + slope * ((1 - t) * w.1 - t * w.2))
  simp only [Prod.fst_add, Prod.snd_add]
  ring

/-- The literal left-slope support is additive on the entire real plane. -/
theorem source_fminus_add (t G dl : ℝ) (z w : ℝ × ℝ) :
    G * ((z + w).1 + (z + w).2) +
      dl * ((1 - t) * (z + w).1 - t * (z + w).2) =
    (G * (z.1 + z.2) + dl * ((1 - t) * z.1 - t * z.2)) +
      (G * (w.1 + w.2) + dl * ((1 - t) * w.1 - t * w.2)) := by
  exact source_support_add t G dl z w

/-- The literal right-slope support is additive on the entire real plane. -/
theorem source_fplus_add (t G dr : ℝ) (z w : ℝ × ℝ) :
    G * ((z + w).1 + (z + w).2) +
      dr * ((1 - t) * (z + w).1 - t * (z + w).2) =
    (G * (z.1 + z.2) + dr * ((1 - t) * z.1 - t * z.2)) +
      (G * (w.1 + w.2) + dr * ((1 - t) * w.1 - t * w.2)) := by
  exact source_support_add t G dr z w

/-- The literal average support is additive on the entire real plane. -/
theorem source_favg_add (t G dl dr : ℝ) (z w : ℝ × ℝ) :
    G * ((z + w).1 + (z + w).2) +
      ((dl + dr) / 2) * ((1 - t) * (z + w).1 - t * (z + w).2) =
    (G * (z.1 + z.2) + ((dl + dr) / 2) * ((1 - t) * z.1 - t * z.2)) +
      (G * (w.1 + w.2) + ((dl + dr) / 2) * ((1 - t) * w.1 - t * w.2) ) := by
  exact source_support_add t G ((dl + dr) / 2) z w

/-- For one actual path and one actual signed weight, the minimum of the two
extreme defects is the average defect minus the source half-gap times the
absolute transverse displacement. -/
theorem path_defect_min_identity (t G dl dr : ℝ) (hgap : dr ≤ dl)
    (ω : Environment) {u : Lattice} {d : ℕ × ℕ} (p : Path u d) :
    min
      (G * ((d.1 : ℝ) + (d.2 : ℝ)) +
        dl * ((1 - t) * (d.1 : ℝ) - t * (d.2 : ℝ)) - pathWeight ω p)
      (G * ((d.1 : ℝ) + (d.2 : ℝ)) +
        dr * ((1 - t) * (d.1 : ℝ) - t * (d.2 : ℝ)) - pathWeight ω p) =
      G * ((d.1 : ℝ) + (d.2 : ℝ)) +
        ((dl + dr) / 2) * ((1 - t) * (d.1 : ℝ) - t * (d.2 : ℝ)) -
        pathWeight ω p -
          ((dl - dr) / 2) *
            |(1 - t) * (d.1 : ℝ) - t * (d.2 : ℝ)| := by
  let r : ℝ := (1 - t) * (d.1 : ℝ) - t * (d.2 : ℝ)
  let havg : ℝ := G * ((d.1 : ℝ) + (d.2 : ℝ)) +
    ((dl + dr) / 2) * r - pathWeight ω p
  let cgap : ℝ := (dl - dr) / 2
  have hcgap : 0 ≤ cgap := by
    dsimp [cgap]
    linarith
  have hminus :
      G * ((d.1 : ℝ) + (d.2 : ℝ)) +
        dl * ((1 - t) * (d.1 : ℝ) - t * (d.2 : ℝ)) - pathWeight ω p =
          havg + cgap * r := by
    dsimp [havg, cgap, r]
    ring
  have hplus :
      G * ((d.1 : ℝ) + (d.2 : ℝ)) +
        dr * ((1 - t) * (d.1 : ℝ) - t * (d.2 : ℝ)) - pathWeight ω p =
          havg - cgap * r := by
    dsimp [havg, cgap, r]
    ring
  rw [hminus, hplus]
  change min (havg + cgap * r) (havg - cgap * r) =
    havg - cgap * |r|
  by_cases hr : 0 ≤ r
  · have hmul : 0 ≤ cgap * r := mul_nonneg hcgap hr
    rw [abs_of_nonneg hr, min_eq_right (by linarith)]
  · have hr' : r ≤ 0 := le_of_not_ge hr
    have hmul : 0 ≤ cgap * -r := mul_nonneg hcgap (neg_nonneg.mpr hr')
    rw [abs_of_nonpos hr', min_eq_left (by linarith)]
    ring

/-- The extreme-defect minimum is bounded above by the average defect. -/
theorem path_defect_min_le_average (t G dl dr : ℝ) (hgap : dr ≤ dl)
    (ω : Environment) {u : Lattice} {d : ℕ × ℕ} (p : Path u d) :
    min
      (G * ((d.1 : ℝ) + (d.2 : ℝ)) +
        dl * ((1 - t) * (d.1 : ℝ) - t * (d.2 : ℝ)) - pathWeight ω p)
      (G * ((d.1 : ℝ) + (d.2 : ℝ)) +
        dr * ((1 - t) * (d.1 : ℝ) - t * (d.2 : ℝ)) - pathWeight ω p) ≤
      G * ((d.1 : ℝ) + (d.2 : ℝ)) +
        ((dl + dr) / 2) * ((1 - t) * (d.1 : ℝ) - t * (d.2 : ℝ)) -
        pathWeight ω p := by
  rw [path_defect_min_identity t G dl dr hgap ω p]
  have hcgap : 0 ≤ (dl - dr) / 2 := by linarith
  exact sub_le_self _ (mul_nonneg hcgap (abs_nonneg _))

/-- Equal source slopes give an affine profile and no loss at the minimum. -/
theorem path_defect_min_eq_average_of_equal_slopes (t G dl dr : ℝ)
    (heq : dl = dr) (ω : Environment) {u : Lattice} {d : ℕ × ℕ}
    (p : Path u d) :
    min
      (G * ((d.1 : ℝ) + (d.2 : ℝ)) +
        dl * ((1 - t) * (d.1 : ℝ) - t * (d.2 : ℝ)) - pathWeight ω p)
      (G * ((d.1 : ℝ) + (d.2 : ℝ)) +
        dr * ((1 - t) * (d.1 : ℝ) - t * (d.2 : ℝ)) - pathWeight ω p) =
      G * ((d.1 : ℝ) + (d.2 : ℝ)) +
        ((dl + dr) / 2) * ((1 - t) * (d.1 : ℝ) - t * (d.2 : ℝ)) -
        pathWeight ω p := by
  subst dr
  rw [path_defect_min_identity t G dl dl le_rfl ω p]
  ring

/-- When the transverse displacement is nonnegative, the right-slope defect
realizes the minimum. -/
theorem path_defect_min_eq_fplus_of_rho_nonneg (t G dl dr : ℝ)
    (hgap : dr ≤ dl) (ω : Environment) {u : Lattice} {d : ℕ × ℕ}
    (p : Path u d)
    (hr : 0 ≤ (1 - t) * (d.1 : ℝ) - t * (d.2 : ℝ)) :
    min
      (G * ((d.1 : ℝ) + (d.2 : ℝ)) +
        dl * ((1 - t) * (d.1 : ℝ) - t * (d.2 : ℝ)) - pathWeight ω p)
      (G * ((d.1 : ℝ) + (d.2 : ℝ)) +
        dr * ((1 - t) * (d.1 : ℝ) - t * (d.2 : ℝ)) - pathWeight ω p) =
      G * ((d.1 : ℝ) + (d.2 : ℝ)) +
        dr * ((1 - t) * (d.1 : ℝ) - t * (d.2 : ℝ)) - pathWeight ω p := by
  rw [path_defect_min_identity t G dl dr hgap ω p]
  rw [abs_of_nonneg hr]
  ring

/-- When the transverse displacement is nonpositive, the left-slope defect
realizes the minimum. -/
theorem path_defect_min_eq_fminus_of_rho_nonpos (t G dl dr : ℝ)
    (hgap : dr ≤ dl) (ω : Environment) {u : Lattice} {d : ℕ × ℕ}
    (p : Path u d)
    (hr : (1 - t) * (d.1 : ℝ) - t * (d.2 : ℝ) ≤ 0) :
    min
      (G * ((d.1 : ℝ) + (d.2 : ℝ)) +
        dl * ((1 - t) * (d.1 : ℝ) - t * (d.2 : ℝ)) - pathWeight ω p)
      (G * ((d.1 : ℝ) + (d.2 : ℝ)) +
        dr * ((1 - t) * (d.1 : ℝ) - t * (d.2 : ℝ)) - pathWeight ω p) =
      G * ((d.1 : ℝ) + (d.2 : ℝ)) +
        dl * ((1 - t) * (d.1 : ℝ) - t * (d.2 : ℝ)) - pathWeight ω p := by
  rw [path_defect_min_identity t G dl dr hgap ω p]
  rw [abs_of_nonpos hr]
  ring

/-- A constant environment with any real value, including a negative one,
contributes exactly once at each collected vertex. -/
theorem path_defect_min_identity_constant_environment (t G dl dr w : ℝ)
    (hgap : dr ≤ dl) {u : Lattice} {d : ℕ × ℕ} (p : Path u d) :
    min
      (G * ((d.1 : ℝ) + (d.2 : ℝ)) +
        dl * ((1 - t) * (d.1 : ℝ) - t * (d.2 : ℝ)) -
          (((d.1 + d.2 : ℕ) : ℝ) * w))
      (G * ((d.1 : ℝ) + (d.2 : ℝ)) +
        dr * ((1 - t) * (d.1 : ℝ) - t * (d.2 : ℝ)) -
          (((d.1 + d.2 : ℕ) : ℝ) * w)) =
      G * ((d.1 : ℝ) + (d.2 : ℝ)) +
        ((dl + dr) / 2) * ((1 - t) * (d.1 : ℝ) - t * (d.2 : ℝ)) -
          (((d.1 + d.2 : ℕ) : ℝ) * w) -
          ((dl - dr) / 2) *
            |(1 - t) * (d.1 : ℝ) - t * (d.2 : ℝ)| := by
  simpa only [pathWeight_const] using
    (path_defect_min_identity t G dl dr hgap
      (fun _ : Lattice => w) p)

/-- A length-zero actual path has zero defect for every linear support slope. -/
theorem path_support_defect_zero (G slope : ℝ) (ω : Environment)
    (u : Lattice) (p : Path u (0, 0)) :
    G * (0 : ℝ) + slope * (0 : ℝ) - pathWeight ω p = 0 := by
  rw [pathWeight_zero]
  simp

/-- For an empty left piece, the actual concatenated defect equals the defect
of the right piece; its joining vertex is collected by that piece. -/
theorem path_support_defect_concat_zero_left (t G slope : ℝ)
    (ω : Environment) {u : Lattice} {e : ℕ × ℕ}
    (p : Path u (0, 0))
    (q : Path (u + ((0 : ℤ), (0 : ℤ))) e) :
    G * ((e.1 : ℝ) + (e.2 : ℝ)) +
        slope * ((1 - t) * (e.1 : ℝ) - t * (e.2 : ℝ)) - pathWeight ω q =
      G * (((0, 0) + e).1 : ℝ) + G * (((0, 0) + e).2 : ℝ) +
        slope * ((1 - t) * ((((0, 0) + e).1) : ℝ) -
          t * ((((0, 0) + e).2) : ℝ)) - pathWeight ω (p.concat q) := by
  rw [pathWeight_concat, pathWeight_zero]
  simp
  ring

/-- For an empty right piece, the actual concatenated defect equals the defect
of the left piece and still excludes the terminal vertex. -/
theorem path_support_defect_concat_zero_right (t G slope : ℝ)
    (ω : Environment) {u : Lattice} {d : ℕ × ℕ}
    (p : Path u d)
    (q : Path (u + ((d.1 : ℤ), (d.2 : ℤ))) (0, 0)) :
    G * ((d.1 : ℝ) + (d.2 : ℝ)) +
        slope * ((1 - t) * (d.1 : ℝ) - t * (d.2 : ℝ)) - pathWeight ω p =
      G * ((d + (0, 0)).1 : ℝ) + G * ((d + (0, 0)).2 : ℝ) +
        slope * ((1 - t) * (((d + (0, 0)).1) : ℝ) -
          t * (((d + (0, 0)).2) : ℝ)) - pathWeight ω (p.concat q) := by
  rw [pathWeight_concat, pathWeight_zero]
  simp
  ring

/-- A generic source support defect adds for the actual concatenated path, with
no sign condition on any environment weight. -/
theorem path_support_defect_concat (t G slope : ℝ) (ω : Environment)
    {u : Lattice} {d e : ℕ × ℕ}
    (p : Path u d)
    (q : Path (u + ((d.1 : ℤ), (d.2 : ℤ))) e) :
    G * (((d + e).1 : ℝ) + ((d + e).2 : ℝ)) +
        slope * ((1 - t) * ((d + e).1 : ℝ) - t * ((d + e).2 : ℝ)) -
        pathWeight ω (p.concat q) =
      (G * ((d.1 : ℝ) + (d.2 : ℝ)) +
          slope * ((1 - t) * (d.1 : ℝ) - t * (d.2 : ℝ)) -
          pathWeight ω p) +
        (G * ((e.1 : ℝ) + (e.2 : ℝ)) +
          slope * ((1 - t) * (e.1 : ℝ) - t * (e.2 : ℝ)) -
          pathWeight ω q) := by
  rw [pathWeight_concat]
  have hdisp :
      (((d + e).1 : ℝ), ((d + e).2 : ℝ)) =
        ((d.1 : ℝ), (d.2 : ℝ)) + ((e.1 : ℝ), (e.2 : ℝ)) := by
    ext <;> simp only [Prod.fst_add, Prod.snd_add, Nat.cast_add]
  change
    (fun z : ℝ × ℝ =>
      G * (z.1 + z.2) + slope * ((1 - t) * z.1 - t * z.2))
        (((d + e).1 : ℝ), ((d + e).2 : ℝ)) -
        (pathWeight ω p + pathWeight ω q) =
      ((fun z : ℝ × ℝ =>
        G * (z.1 + z.2) + slope * ((1 - t) * z.1 - t * z.2))
          ((d.1 : ℝ), (d.2 : ℝ)) - pathWeight ω p) +
        ((fun z : ℝ × ℝ =>
          G * (z.1 + z.2) + slope * ((1 - t) * z.1 - t * z.2))
            ((e.1 : ℝ), (e.2 : ℝ)) - pathWeight ω q)
  rw [hdisp, source_support_add]
  ring

/-- The literal left-slope defect adds under actual path concatenation. -/
alias path_defect_fminus_concat := path_support_defect_concat

/-- The literal right-slope defect adds under actual path concatenation. -/
alias path_defect_fplus_concat := path_support_defect_concat

/-- The literal average-support defect adds under actual path concatenation. -/
theorem path_defect_favg_concat (t G dl dr : ℝ) (ω : Environment)
    {u : Lattice} {d e : ℕ × ℕ}
    (p : Path u d)
    (q : Path (u + ((d.1 : ℤ), (d.2 : ℤ))) e) :
    G * (((d + e).1 : ℝ) + ((d + e).2 : ℝ)) +
        ((dl + dr) / 2) * ((1 - t) * ((d + e).1 : ℝ) - t * ((d + e).2 : ℝ)) -
        pathWeight ω (p.concat q) =
      (G * ((d.1 : ℝ) + (d.2 : ℝ)) +
          ((dl + dr) / 2) * ((1 - t) * (d.1 : ℝ) - t * (d.2 : ℝ)) -
          pathWeight ω p) +
        (G * ((e.1 : ℝ) + (e.2 : ℝ)) +
          ((dl + dr) / 2) * ((1 - t) * (e.1 : ℝ) - t * (e.2 : ℝ)) -
          pathWeight ω q) := by
  exact path_support_defect_concat t G ((dl + dr) / 2) ω p q

/-- A generic source support defect adds over the actual prefix and suffix
segments of a path split at any vertex. The split vertex is counted only in the
suffix weight. -/
theorem path_support_defect_split (t G slope : ℝ) (ω : Environment)
    {u : Lattice} {d : ℕ × ℕ}
    (p : Path u d) (k : Fin (d.1 + d.2 + 1)) :
    G * ((d.1 : ℝ) + (d.2 : ℝ)) +
        slope * ((1 - t) * (d.1 : ℝ) - t * (d.2 : ℝ)) - pathWeight ω p =
      (G * (((p.splitDisplacement k).1 : ℝ) +
          ((p.splitDisplacement k).2 : ℝ)) +
          slope * ((1 - t) * ((p.splitDisplacement k).1 : ℝ) -
            t * ((p.splitDisplacement k).2 : ℝ)) -
          pathWeight ω (p.prefixPath k)) +
        (G * ((((d - p.splitDisplacement k).1 : ℝ) +
          ((d - p.splitDisplacement k).2 : ℝ))) +
          slope * ((1 - t) * (((d - p.splitDisplacement k).1 : ℝ)) -
            t * (((d - p.splitDisplacement k).2 : ℝ)) ) -
          pathWeight ω (p.suffix k)) := by
  rw [pathWeight_split]
  have hdisp :
      ((d.1 : ℝ), (d.2 : ℝ)) =
        (((p.splitDisplacement k).1 : ℝ),
          ((p.splitDisplacement k).2 : ℝ)) +
          (((d - p.splitDisplacement k).1 : ℝ),
            ((d - p.splitDisplacement k).2 : ℝ)) := by
    apply Prod.ext
    · have h := congrArg Prod.fst (p.splitDisplacement_add_sub k)
      have h' :
          (p.splitDisplacement k).1 + (d - p.splitDisplacement k).1 = d.1 := by
        simpa only [Prod.fst_add] using h
      have hr := congrArg (fun n : ℕ => (n : ℝ)) h'.symm
      simpa only [Nat.cast_add, Prod.fst_add] using hr
    · have h := congrArg Prod.snd (p.splitDisplacement_add_sub k)
      have h' :
          (p.splitDisplacement k).2 + (d - p.splitDisplacement k).2 = d.2 := by
        simpa only [Prod.snd_add] using h
      have hr := congrArg (fun n : ℕ => (n : ℝ)) h'.symm
      simpa only [Nat.cast_add, Prod.snd_add] using hr
  change
    (fun z : ℝ × ℝ =>
      G * (z.1 + z.2) + slope * ((1 - t) * z.1 - t * z.2))
        ((d.1 : ℝ), (d.2 : ℝ)) -
        (pathWeight ω (p.prefixPath k) + pathWeight ω (p.suffix k)) =
      ((fun z : ℝ × ℝ =>
        G * (z.1 + z.2) + slope * ((1 - t) * z.1 - t * z.2))
          (((p.splitDisplacement k).1 : ℝ),
            ((p.splitDisplacement k).2 : ℝ)) -
          pathWeight ω (p.prefixPath k)) +
        ((fun z : ℝ × ℝ =>
          G * (z.1 + z.2) + slope * ((1 - t) * z.1 - t * z.2))
            (((d - p.splitDisplacement k).1 : ℝ),
              ((d - p.splitDisplacement k).2 : ℝ)) -
            pathWeight ω (p.suffix k))
  rw [hdisp, source_support_add]
  ring

/-- The literal left-slope defect adds over the actual split segments. -/
alias path_defect_fminus_split := path_support_defect_split

/-- The literal right-slope defect adds over the actual split segments. -/
alias path_defect_fplus_split := path_support_defect_split

/-- The literal average-support defect adds over the actual split segments. -/
theorem path_defect_favg_split (t G dl dr : ℝ) (ω : Environment)
    {u : Lattice} {d : ℕ × ℕ}
    (p : Path u d) (k : Fin (d.1 + d.2 + 1)) :
    G * ((d.1 : ℝ) + (d.2 : ℝ)) +
        ((dl + dr) / 2) * ((1 - t) * (d.1 : ℝ) - t * (d.2 : ℝ)) - pathWeight ω p =
      (G * (((p.splitDisplacement k).1 : ℝ) +
          ((p.splitDisplacement k).2 : ℝ)) +
          ((dl + dr) / 2) * ((1 - t) * ((p.splitDisplacement k).1 : ℝ) -
            t * ((p.splitDisplacement k).2 : ℝ)) -
          pathWeight ω (p.prefixPath k)) +
        (G * ((((d - p.splitDisplacement k).1 : ℝ) +
          ((d - p.splitDisplacement k).2 : ℝ))) +
          ((dl + dr) / 2) * ((1 - t) * (((d - p.splitDisplacement k).1 : ℝ)) -
            t * (((d - p.splitDisplacement k).2 : ℝ)) ) -
          pathWeight ω (p.suffix k)) := by
  exact path_support_defect_split t G ((dl + dr) / 2) ω p k

/-- The actual horizontal-axis defect minimum uses transverse displacement
`n(1-t)` and the same terminal-excluded path weight. -/
theorem path_defect_min_identity_horizontal (t G dl dr : ℝ)
    (hgap : dr ≤ dl) (ω : Environment) {u : Lattice} {n : ℕ}
    (p : Path u (n, 0)) :
    min
      (G * (n : ℝ) + dl * ((1 - t) * (n : ℝ)) - pathWeight ω p)
      (G * (n : ℝ) + dr * ((1 - t) * (n : ℝ)) - pathWeight ω p) =
        G * (n : ℝ) + ((dl + dr) / 2) * ((1 - t) * (n : ℝ)) -
          pathWeight ω p -
            ((dl - dr) / 2) * |(1 - t) * (n : ℝ)| := by
  simpa using (path_defect_min_identity t G dl dr hgap ω p)

/-- The actual vertical-axis defect minimum uses transverse displacement
`-nt` and the same terminal-excluded path weight. -/
theorem path_defect_min_identity_vertical (t G dl dr : ℝ)
    (hgap : dr ≤ dl) (ω : Environment) {u : Lattice} {n : ℕ}
    (p : Path u (0, n)) :
    min
      (G * (n : ℝ) + dl * (-(t * (n : ℝ))) - pathWeight ω p)
      (G * (n : ℝ) + dr * (-(t * (n : ℝ))) - pathWeight ω p) =
        G * (n : ℝ) + ((dl + dr) / 2) * (-(t * (n : ℝ))) -
          pathWeight ω p -
            ((dl - dr) / 2) * |-(t * (n : ℝ))| := by
  simpa using (path_defect_min_identity t G dl dr hgap ω p)

/-- For the literal canonical profile, the source minimum identity uses the
actual one-sided derivatives. Their ordering is proved from concavity. -/
theorem canonical_path_defect_min
    (g : Quadrant → ℝ)
    (hgconc : ∀ (x y : Quadrant) (r s : ℝ≥0), r + s = 1 →
      (r : ℝ) * g x + (s : ℝ) * g y ≤ g (r • x + s • y))
    (a : ℝ) (ha₀ : 0 < a) (ha₁ : a < 1)
    (ω : Environment) {u : Lattice} {d : ℕ × ℕ} (p : Path u d) :
    let H : ℝ → ℝ := fun h => quadrantExtension g (a + h, 1 - a - h)
    let dl := derivWithin H (Set.Iio 0) 0
    let dr := derivWithin H (Set.Ioi 0) 0
    let rho := (1 - a) * (d.1 : ℝ) - a * (d.2 : ℝ)
    let fminus := H 0 * ((d.1 : ℝ) + (d.2 : ℝ)) + dl * rho
    let fplus := H 0 * ((d.1 : ℝ) + (d.2 : ℝ)) + dr * rho
    let favg := H 0 * ((d.1 : ℝ) + (d.2 : ℝ)) + ((dl + dr) / 2) * rho
    min (fminus - pathWeight ω p) (fplus - pathWeight ω p) =
      favg - pathWeight ω p - ((dl - dr) / 2) * |rho| ∧
    min (fminus - pathWeight ω p) (fplus - pathWeight ω p) ≤
      favg - pathWeight ω p := by
  let H : ℝ → ℝ := fun h => quadrantExtension g (a + h, 1 - a - h)
  have hhalf := quadrant_supporting_functionals_half_gap_algebra g hgconc a ha₀ ha₁
  have hgap : derivWithin H (Set.Ioi 0) 0 ≤ derivWithin H (Set.Iio 0) 0 := by
    have hc : 0 ≤ (derivWithin H (Set.Iio 0) 0 -
        derivWithin H (Set.Ioi 0) 0) / 2 := hhalf.1
    linarith only [hc]
  exact ⟨path_defect_min_identity a (H 0) _ _ hgap ω p,
    path_defect_min_le_average a (H 0) _ _ hgap ω p⟩

/-- Both canonical extreme defects dominate the shape minus this path's
weight, which in turn dominates the shape minus the actual passage maximum.
The supporting inequalities are established by the lemmas used in the proof. -/
theorem canonical_path_defect_lower_bounds
    (g : Quadrant → ℝ)
    (hgconc : ∀ (x y : Quadrant) (r s : ℝ≥0), r + s = 1 →
      (r : ℝ) * g x + (s : ℝ) * g y ≤ g (r • x + s • y))
    (hhom : ∀ (c : ℝ≥0) (z : Quadrant), g (c • z) = (c : ℝ) * g z)
    (a : ℝ) (ha₀ : 0 < a) (ha₁ : a < 1)
    (ω : Environment) {u : Lattice} {d : ℕ × ℕ} (p : Path u d) :
    let H : ℝ → ℝ := fun h => quadrantExtension g (a + h, 1 - a - h)
    let dl := derivWithin H (Set.Iio 0) 0
    let dr := derivWithin H (Set.Ioi 0) 0
    let rho := (1 - a) * (d.1 : ℝ) - a * (d.2 : ℝ)
    let fminus := H 0 * ((d.1 : ℝ) + (d.2 : ℝ)) + dl * rho
    let fplus := H 0 * ((d.1 : ℝ) + (d.2 : ℝ)) + dr * rho
    let z : Quadrant := ((d.1 : ℝ≥0), (d.2 : ℝ≥0))
    g z - pathWeight ω p ≤ fminus - pathWeight ω p ∧
    g z - pathWeight ω p ≤ fplus - pathWeight ω p ∧
    g z - lastPassage ω u d ≤ g z - pathWeight ω p := by
  let z : Quadrant := ((d.1 : ℝ≥0), (d.2 : ℝ≥0))
  have hs := (quadrant_supporting_functionals_and_contact
    g hgconc hhom a ha₀ ha₁).1 z
  refine ⟨sub_le_sub_right hs.1 _, sub_le_sub_right hs.2 _, ?_⟩
  exact sub_le_sub_left (pathWeight_le_lastPassage ω p) _

end Path
end LPPDifferentiability
