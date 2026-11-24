/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Differentiability.Probability.TravelAssembly
public import Differentiability.Probability.TravelPieceProbability
public import LPP_Foundations.Statements.ShapeDefinitions
import Mathlib.Algebra.Order.Archimedean.Basic

/-!
# The travel estimate on the iid environment space

The unique shape function also satisfies the travel estimate. Its proof combines the
piece estimates of the travel proof over the floor segments of a path.
-/

public section

open MeasureTheory Filter Set
open scoped Topology ENNReal NNReal

namespace LPPDifferentiability

/-- The path event in `lem:travel` of the final draft.
A path from `u` with displacement `d` loses at most `η * s` from the shape and stays
within taxicab distance `δ * s` of the segment joining its endpoints. -/
@[expose] def travelPathEvent (g : Quadrant → ℝ) (η δ s : ℝ)
    (u : Lattice) (d : ℕ × ℕ) : Set Environment :=
  {ω | ∃ q : Path u d,
    g ((d.1 : ℝ≥0), (d.2 : ℝ≥0)) - η * s ≤ pathWeight ω q ∧
    ∀ i, ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧
      |((q.vertex i).1 : ℝ) - ((u.1 : ℝ) + t * (d.1 : ℝ))| +
      |((q.vertex i).2 : ℝ) - ((u.2 : ℝ) + t * (d.2 : ℝ))| ≤ δ * s}

/-- The shape function and the uniform probability bound of `lem:travel` in the final draft.
One probability function works for every deterministic starting point and displacement. -/
theorem exists_unique_shape_with_travel_estimate
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hneg : ∃ p : ℝ, 1 < p ∧
      (∫⁻ t, ENNReal.ofReal ((max (-t) 0) ^ p) ∂μ) < ∞)
    (hpos : (∫⁻ t in Ioi (0 : ℝ), (μ (Ioi t)) ^ (1 / 2 : ℝ)) < ∞) :
    ∃! g : Quadrant → ℝ, LPPStatements.IsShapeFunction μ g ∧
      (∀ (a : ℝ), 0<a → a<1 → ∀ (D : ℝ), 1≤D →
        ∀ (theta : ℝ), 0<theta → theta<min a (1-a) →
        ∀ (η δ : ℝ), 0<η → 0<δ →
        ∃ s1 : ℝ, 1≤s1 ∧ ∃ p : ℝ → ℝ,
          (∀ s, 0≤p s ∧ p s≤1) ∧ Tendsto p atTop (𝓝 1) ∧
          ∀ (s : ℝ) (u : Lattice) (d : ℕ × ℕ), s1≤s →
            s≤((d.1+d.2:ℕ):ℝ) → ((d.1+d.2:ℕ):ℝ)≤D*s →
            |(1-a)*(d.1:ℝ)-a*(d.2:ℝ)| ≤
              (min a (1-a)-theta)*((d.1:ℝ)+(d.2:ℝ)) →
            MeasurableSet (travelPathEvent g η δ s u d) ∧
            p s ≤ (environmentLaw μ).real (travelPathEvent g η δ s u d)) := by
  obtain ⟨g, ⟨hcont, hhom, hconc, happ, hpieces⟩, -⟩ :=
    exists_unique_shape_with_travel_piece_probability μ hneg hpos
  obtain ⟨_, -, hunique⟩ :=
    exists_unique_shape_of_negative_moment_and_positive_tail μ hneg hpos
  have hg : LPPStatements.IsShapeFunction μ g :=
    ⟨hcont, hhom, hconc, (LPPStatements.approximatesLastPassage_iff_positive_threshold μ g).mpr happ⟩
  refine ⟨g, ⟨hg, ?_⟩, ?_⟩
  · intro a ha0 ha1 D hD theta htheta hinterior η δ hη hδ
    obtain ⟨B,hbig⟩ := exists_nat_ge (max 1 (4*D/δ))
    have hBreal : (1:ℝ)≤(B:ℝ) := (le_max_left _ _).trans hbig
    have hB : 1≤B := by exact_mod_cast hBreal
    have hBr : 0<(B:ℝ) := lt_of_lt_of_le zero_lt_one hBreal
    have hBD : 4*D/δ≤(B:ℝ) := (le_max_right _ _).trans hbig
    obtain ⟨L,hL,hassembly⟩ := exists_floorSegment_travel_assembly_constant g hcont
      hconc hhom a theta ha0 ha1 htheta hinterior
    obtain ⟨p,hp,ht,hpieces_at_scale⟩ := hpieces D hD B hB η hη
    let C : ℝ := 2+2*(min a (1-a)-theta/2)
    let s1 : ℝ := max 1 (max (3*(B:ℝ)) (max (4*L*(B:ℝ)/η)
      (max (16/(3*δ)) (C*(B:ℝ)/(theta/2)))))
    refine ⟨s1,le_max_left _ _,p,hp,ht,?_⟩
    intro s u d hs hd hdD hinter
    have hb : 1≤s ∧ 3*(B:ℝ)≤s ∧ 4*L*(B:ℝ)/η≤s ∧
        16/(3*δ)≤s ∧ C*(B:ℝ)/(theta/2)≤s := by
      simpa only [s1,max_le_iff] using hs
    have hs0 : 0≤s := zero_le_one.trans hb.1
    have hcut : theta/2*(((d.1:ℝ)+(d.2:ℝ))/(B:ℝ)) ≥ C := by
      have hc : C*(B:ℝ) ≤ s*(theta/2) :=
        (div_le_iff₀ (by positivity : 0<theta/2)).1 hb.2.2.2.2
      have hsd : s/(B:ℝ) ≤ ((d.1:ℝ)+(d.2:ℝ))/(B:ℝ) :=
        div_le_div_of_nonneg_right (by simpa only [Nat.cast_add] using hd) hBr.le
      have hc' : C ≤ theta/2*(s/(B:ℝ)) := by
        rw [← mul_div_assoc]
        apply (le_div_iff₀ hBr).2
        nlinarith only [hc]
      exact hc'.trans (mul_le_mul_of_nonneg_left hsd (by positivity))
    have hloss : 2*L*(B:ℝ) ≤ η*s/2 := by
      have h := (div_le_iff₀ hη).1 hb.2.2.1
      nlinarith only [h]
    have htube : ((d.1+d.2:ℕ):ℝ)/(B:ℝ)+4 ≤ δ*s := by
      have hbd : 4*D ≤ (B:ℝ)*δ := (div_le_iff₀ hδ).1 hBD
      have hscale : 16 ≤ s*(3*δ) :=
        (div_le_iff₀ (by positivity : 0<3*δ)).1 hb.2.2.2.1
      have hds : D*s/(B:ℝ) ≤ δ*s/4 := by
        apply (div_le_iff₀ hBr).2
        nlinarith only [mul_le_mul_of_nonneg_right hbd hs0]
      calc
        _ ≤ D*s/(B:ℝ)+4 := by
          have hlen := div_le_div_of_nonneg_right hdD hBr.le
          linarith only [hlen]
        _ ≤ δ*s := by linarith only [hds,hscale]
    constructor
    · exact measurableSet_exists_path_weight_property u d
        (g ((d.1:ℝ≥0),(d.2:ℝ≥0))-η*s)
        (fun v : Lattice => ∃ t : ℝ, 0≤t ∧ t≤1 ∧
          |(v.1:ℝ)-((u.1:ℝ)+t*(d.1:ℝ))|+
          |(v.2:ℝ)-((u.2:ℝ)+t*(d.2:ℝ))|≤δ*s)
    · obtain ⟨_hm,_hb,_hfm,hprob⟩ := hpieces_at_scale s u d hb.2.1 hd hdD
      apply hprob.trans
      apply measureReal_mono ?_ (measure_ne_top _ _)
      rintro ω ⟨paths,hpaths⟩
      exact hassembly B hB s η δ u d hinter hcut hloss htube ω paths
        (fun j => (hpaths j).2)
  · rintro f ⟨⟨hfcont, hfhom, hfconc, hfapp⟩, -⟩
    have hf := (LPPStatements.approximatesLastPassage_iff_positive_threshold μ f).mp hfapp
    exact (hunique f ⟨hfcont, hfhom, hfconc, hf⟩).trans
      (hunique g ⟨hcont, hhom, hconc, happ⟩).symm

/-- The travel estimate with the four shape clauses and a positive approximation threshold,
as in the literal form of `lem:travel`. -/
theorem exists_unique_shape_with_travel
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hneg : ∃ p : ℝ, 1 < p ∧
      (∫⁻ t, ENNReal.ofReal ((max (-t) 0) ^ p) ∂μ) < ∞)
    (hpos : (∫⁻ t in Ioi (0 : ℝ), (μ (Ioi t)) ^ (1 / 2 : ℝ)) < ∞) :
    ∃! g : Quadrant → ℝ,
      Continuous g ∧
      (∀ (c : ℝ≥0) (x : Quadrant), g (c*x.1,c*x.2) = (c:ℝ)*g x) ∧
      (∀ (x y : Quadrant) (r t : ℝ≥0), r+t=1 →
        (r:ℝ)*g x+(t:ℝ)*g y ≤ g (r*x.1+t*y.1,r*x.2+t*y.2)) ∧
      (∀ᵐ ω ∂environmentLaw μ, ∀ ε : ℝ, 0 < ε →
        ∃ N : ℕ, 1 ≤ N ∧ ∀ d : ℕ × ℕ, N ≤ d.1+d.2 →
          |lastPassage ω 0 d-g ((d.1:ℝ≥0),(d.2:ℝ≥0))| ≤
            ε*((d.1+d.2:ℕ):ℝ)) ∧
      (∀ (a : ℝ), 0<a → a<1 → ∀ (D : ℝ), 1≤D →
        ∀ (theta : ℝ), 0<theta → theta<min a (1-a) →
        ∀ (η δ : ℝ), 0<η → 0<δ →
        ∃ s1 : ℝ, 1≤s1 ∧ ∃ p : ℝ → ℝ,
          (∀ s, 0≤p s ∧ p s≤1) ∧ Tendsto p atTop (𝓝 1) ∧
          ∀ (s : ℝ) (u : Lattice) (d : ℕ × ℕ), s1≤s →
            s≤((d.1+d.2:ℕ):ℝ) → ((d.1+d.2:ℕ):ℝ)≤D*s →
            |(1-a)*(d.1:ℝ)-a*(d.2:ℝ)| ≤
              (min a (1-a)-theta)*((d.1:ℝ)+(d.2:ℝ)) →
            MeasurableSet {ω : Environment | ∃ q : Path u d,
              g ((d.1:ℝ≥0),(d.2:ℝ≥0))-η*s ≤ pathWeight ω q ∧
              ∀ i, ∃ t : ℝ, 0≤t ∧ t≤1 ∧
                |((q.vertex i).1:ℝ)-((u.1:ℝ)+t*(d.1:ℝ))|+
                |((q.vertex i).2:ℝ)-((u.2:ℝ)+t*(d.2:ℝ))|≤δ*s} ∧
            p s ≤ (environmentLaw μ).real {ω : Environment | ∃ q : Path u d,
              g ((d.1:ℝ≥0),(d.2:ℝ≥0))-η*s ≤ pathWeight ω q ∧
              ∀ i, ∃ t : ℝ, 0≤t ∧ t≤1 ∧
                |((q.vertex i).1:ℝ)-((u.1:ℝ)+t*(d.1:ℝ))|+
                |((q.vertex i).2:ℝ)-((u.2:ℝ)+t*(d.2:ℝ))|≤δ*s}) := by
  obtain ⟨g, ⟨⟨hcont, hhom, hconc, happ⟩, hpaths⟩, hunique⟩ :=
    exists_unique_shape_with_travel_estimate μ hneg hpos
  refine ⟨g, ⟨hcont, hhom, hconc, ?_, hpaths⟩, ?_⟩
  · exact (LPPStatements.approximatesLastPassage_iff_positive_threshold μ g).mp happ
  · rintro f ⟨hfcont, hfhom, hfconc, hfapp, hfpaths⟩
    exact hunique f ⟨⟨hfcont, hfhom, hfconc,
      (LPPStatements.approximatesLastPassage_iff_positive_threshold μ f).mpr hfapp⟩, hfpaths⟩

end LPPDifferentiability
