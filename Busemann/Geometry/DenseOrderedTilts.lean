/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen.
Released under Apache 2.0 license as described in file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Busemann.Frozen.Definitions.SupportTilt
public import Martin2004.Shape.ExpectedRateShape
public import LPP_Foundations.Statements.ShapeDefinitions
public import Mathlib.Topology.Bases
import Busemann.Geometry.NearbyTilts
import Busemann.Geometry.SupportOrder
import Busemann.Frozen.Geometry.LeftExtremeTiltExistsUnique
import LPP_Foundations.Analysis.AbsoluteMomentShape
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Constructions
import Mathlib.Tactic

/-! A shared dense tilt family with ordered approximants, as in JR1810.03580v3, proof 4.8. -/

@[expose] public section

open Set Filter MeasureTheory LPPDifferentiability
open scoped NNReal ENNReal Topology

namespace LPP.Busemann

private theorem exists_increasing_dense_approximants
    {X : Type*} [MetricSpace X] (f : X → ℝ) (hf : Continuous f)
    (D : ℕ → X) (hD : DenseRange D) (x : X)
    (hbelow : ∀ l : ℝ, l < f x → ∀ r : ℝ, 0 < r →
      ∃ y : X, dist y x < r ∧ l < f y ∧ f y < f x) :
    ∃ a : ℕ → ℕ, StrictMono (fun n => f (D (a n))) ∧
      (∀ n, f (D (a n)) < f x) ∧
      Tendsto (fun n => D (a n)) atTop (𝓝 x) := by
  classical
  have hselect (l : ℝ) (hl : l < f x) (r : ℝ) (hr : 0 < r) :
      ∃ i : ℕ, dist (D i) x < r ∧ l < f (D i) ∧ f (D i) < f x := by
    let U : Set X := Metric.ball x r ∩ {y | l < f y} ∩ {y | f y < f x}
    have hopen : IsOpen U :=
      (Metric.isOpen_ball.inter (isOpen_lt continuous_const hf)).inter
        (isOpen_lt hf continuous_const)
    obtain ⟨y, hydist, hylower, hyupper⟩ := hbelow l hl r hr
    have hnonempty : U.Nonempty := ⟨y, ⟨⟨hydist, hylower⟩, hyupper⟩⟩
    have hdense : Dense (Set.range D) := hD
    obtain ⟨z, ⟨i, rfl⟩, hzi⟩ := hdense.exists_mem_open hopen hnonempty
    exact ⟨i, hzi.1.1, hzi.1.2, hzi.2⟩
  obtain ⟨i₀, hi₀dist, _, hi₀side⟩ := hselect (f x - 1) (by linarith) 1 zero_lt_one
  let A : Type := {i : ℕ // f (D i) < f x}
  let initial : A := ⟨i₀, hi₀side⟩
  have hstep (n : ℕ) (i : A) :
      ∃ j : A, dist (D j.1) x < 1 / ((n : ℝ) + 2) ∧ f (D i.1) < f (D j.1) := by
    obtain ⟨j, hjdist, hjlower, hjside⟩ :=
      hselect (f (D i.1)) i.2 (1 / ((n : ℝ) + 2)) (by positivity)
    exact ⟨⟨j, hjside⟩, hjdist, hjlower⟩
  choose next hnext using hstep
  let u : ℕ → A := Nat.rec initial (fun n i => next n i)
  have hmono : StrictMono (fun n => f (D (u n).1)) := by
    apply strictMono_nat_of_lt_succ
    intro n
    exact (hnext n (u n)).2
  have hdist (n : ℕ) : dist (D (u n).1) x < 1 / ((n : ℝ) + 1) := by
    cases n with
    | zero =>
      dsimp only [u, initial]
      rw [Nat.rec_zero]
      simpa only [Nat.cast_zero, zero_add, div_one] using hi₀dist
    | succ n =>
      change dist (D (next n (u n)).1) x < 1 / (((n + 1 : ℕ) : ℝ) + 1)
      have hcast : (((n + 1 : ℕ) : ℝ) + 1) = (n : ℝ) + 2 := by push_cast; ring
      rw [hcast]
      exact (hnext n (u n)).1
  have hconv : Tendsto (fun n => D (u n).1) atTop (𝓝 x) := by
    apply Metric.tendsto_atTop.mpr
    intro ε hε
    have hradius : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have hevent : ∀ᶠ n : ℕ in atTop, 1 / ((n : ℝ) + 1) < ε :=
      hradius.eventually (Iio_mem_nhds hε)
    obtain ⟨N, hN⟩ := eventually_atTop.1 hevent
    exact ⟨N, fun n hn => (hdist n).trans (hN n hn)⟩
  exact ⟨fun n => (u n).1, hmono, fun n => (u n).2, hconv⟩

/-- Under the original nonconstant absolute moment above two, one countable dense
family of actual support tilts approximates every tilt strictly from both sides
in its first coordinate and converges as a full pair. This is the dense-domain
selection used after (4.18) in JR1810.03580v3, proof of Theorem 4.8. -/
theorem exists_dense_ordered_support_family_of_absolute_moment
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hmoment : ∃ p : ℝ, 2 < p ∧ (∫⁻ t, ENNReal.ofReal (|t| ^ p) ∂μ) < ∞)
    (hμ : LPPStatements.NotAPointMass μ) (g : Quadrant → ℝ)
    (hg : IsExpectedRateShape μ g) :
    ∃ D : ℕ → SupportTilt g, DenseRange D ∧
      ∀ h : SupportTilt g, ∃ a b : ℕ → ℕ,
        StrictMono (fun n => (D (a n)).1.1) ∧
        StrictAnti (fun n => (D (b n)).1.1) ∧
        (∀ n, (D (a n)).1.1 < h.1.1 ∧ h.1.1 < (D (b n)).1.1) ∧
        Tendsto (fun n => (D (a n)).1) atTop (𝓝 h.1) ∧
        Tendsto (fun n => (D (b n)).1) atTop (𝓝 h.1) ∧
        StrictAnti (fun n => (D (a n)).1.2) ∧
        StrictMono (fun n => (D (b n)).1.2) ∧
        (∀ n, h.1.2 < (D (a n)).1.2 ∧ (D (b n)).1.2 < h.1.2) := by
  classical
  obtain ⟨_, hhom', hconc'⟩ := expected_rate_shape_geometry_of_absolute_moment μ g hmoment hg
  have hhom : ∀ (c : ℝ≥0) (z : Quadrant), g (c • z) = (c : ℝ) * g z := hhom'
  have hconc : ∀ (x y : Quadrant) (r s : ℝ≥0), r + s = 1 →
      (r : ℝ) * g x + (s : ℝ) * g y ≤ g (r • x + s • y) := hconc'
  -- Nonempty H is needed before selecting a Nat-indexed dense family.
  let midpoint : InteriorDirection := ⟨((1 / 2 : ℝ≥0), (1 / 2 : ℝ≥0)),
    by norm_num, by norm_num, by norm_num⟩
  obtain ⟨h₀, _, _⟩ := exists_unique_left_extreme_tilt g hconc hhom midpoint
  let : Nonempty (SupportTilt g) := ⟨h₀⟩
  obtain ⟨D, hD⟩ := TopologicalSpace.exists_dense_seq (SupportTilt g)
  refine ⟨D, hD, ?_⟩
  intro h
  let f : SupportTilt g → ℝ := fun k => k.1.1
  have hf : Continuous f := continuous_fst.comp continuous_subtype_val
  -- Nearby native supports witness the nonempty relative open slices.
  have hbelow : ∀ l : ℝ, l < f h → ∀ r : ℝ, 0 < r →
      ∃ y : SupportTilt g, dist y h < r ∧ l < f y ∧ f y < f h := by
    intro l hl r hr
    have hgap : 0 < h.1.1 - l := sub_pos.mpr hl
    let ρ := min r (h.1.1 - l) / 2
    have hρ : 0 < ρ := by dsimp only [ρ]; positivity
    have hρr : ρ < r := by
      have hle := min_le_left r (h.1.1 - l)
      dsimp only [ρ]; linarith only [hle, hr]
    have hρgap : ρ < h.1.1 - l := by
      have hle := min_le_right r (h.1.1 - l)
      dsimp only [ρ]; linarith only [hle, hgap]
    obtain ⟨y, _, hy₁, hy₂, _, _, hyside, _, _, _⟩ :=
      exists_nearby_support_tilts_of_absolute_moment μ hmoment hμ g hg h ρ hρ
    have hydist : dist y h < r := by
      rw [Subtype.dist_eq, Prod.dist_eq, Real.dist_eq, Real.dist_eq]
      exact max_lt_iff.mpr ⟨hy₁.trans hρr, hy₂.trans hρr⟩
    have hylower : l < f y := by
      have habs := (abs_lt.mp hy₁).1
      dsimp only [f]
      linarith only [habs, hρgap]
    exact ⟨y, hydist, hylower, hyside⟩
  have habove : ∀ l : ℝ, l < -f h → ∀ r : ℝ, 0 < r →
      ∃ y : SupportTilt g, dist y h < r ∧ l < -f y ∧ -f y < -f h := by
    intro l hl r hr
    have hgap : 0 < -h.1.1 - l := sub_pos.mpr hl
    let ρ := min r (-h.1.1 - l) / 2
    have hρ : 0 < ρ := by dsimp only [ρ]; positivity
    have hρr : ρ < r := by
      have hle := min_le_left r (-h.1.1 - l)
      dsimp only [ρ]; linarith only [hle, hr]
    have hρgap : ρ < -h.1.1 - l := by
      have hle := min_le_right r (-h.1.1 - l)
      dsimp only [ρ]; linarith only [hle, hgap]
    obtain ⟨_, y, _, _, hy₁, hy₂, _, hyside, _, _⟩ :=
      exists_nearby_support_tilts_of_absolute_moment μ hmoment hμ g hg h ρ hρ
    have hydist : dist y h < r := by
      rw [Subtype.dist_eq, Prod.dist_eq, Real.dist_eq, Real.dist_eq]
      exact max_lt_iff.mpr ⟨hy₁.trans hρr, hy₂.trans hρr⟩
    have hylower : l < -f y := by
      have habs := (abs_lt.mp hy₁).2
      dsimp only [f]
      linarith only [habs, hρgap]
    exact ⟨y, hydist, hylower, neg_lt_neg hyside⟩
  obtain ⟨a, haMono, haSide, haConv⟩ :=
    exists_increasing_dense_approximants f hf D hD h hbelow
  obtain ⟨b, hbNegMono, hbNegSide, hbConv⟩ :=
    exists_increasing_dense_approximants (fun k => -f k) hf.neg D hD h habove
  have hbAnti : StrictAnti (fun n => (D (b n)).1.1) := by
    intro m n hmn
    exact neg_lt_neg_iff.mp (hbNegMono hmn)
  have hbSide (n : ℕ) : h.1.1 < (D (b n)).1.1 := neg_lt_neg_iff.mp (hbNegSide n)
  have haSecond : StrictAnti (fun n => (D (a n)).1.2) := by
    intro m n hmn
    exact ((supportTilt_coordinate_order g hhom (D (a m)) (D (a n))).1
      (haMono hmn)).1
  have hbSecond : StrictMono (fun n => (D (b n)).1.2) := by
    intro m n hmn
    exact ((supportTilt_coordinate_order g hhom (D (b n)) (D (b m))).1
      (hbAnti hmn)).1
  have hsecondSides (n : ℕ) : h.1.2 < (D (a n)).1.2 ∧ (D (b n)).1.2 < h.1.2 :=
    ⟨((supportTilt_coordinate_order g hhom (D (a n)) h).1 (haSide n)).1,
      ((supportTilt_coordinate_order g hhom h (D (b n))).1 (hbSide n)).1⟩
  exact ⟨a, b, haMono, hbAnti, fun n => ⟨haSide n, hbSide n⟩,
    continuous_subtype_val.continuousAt.tendsto.comp haConv,
    continuous_subtype_val.continuousAt.tendsto.comp hbConv,
    haSecond, hbSecond, hsecondSides⟩

end LPP.Busemann
