/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Differentiability.Probability.TopSiteEndpoints
public import Differentiability.Probability.TopSiteShape
import Mathlib.Tactic

/-!
# Rarity of too many top sites in the full strip

This file shows that the event "the full-strip path collects too many sites at the top
of the support" has probability tending to zero at the cubic length.
-/

public section
noncomputable section
open MeasureTheory Filter Set
open scoped Topology NNReal
namespace LPPDifferentiability

/-- The full-strip event is measurable for every real width. -/
theorem measurableSet_closed_strip_top_sites
    (μ : Measure ℝ) (a s φ : ℝ) (n : ℕ) :
    MeasurableSet {ω : Environment | ∃ u : Lattice,
      ∃ q : Σ i : Fin (n+1), Path u (i.val,n-i.val),
        (∀ j, 0 ≤ (q.2.vertex j).1+(q.2.vertex j).2 ∧
          (q.2.vertex j).1+(q.2.vertex j).2 ≤ (n : ℤ) ∧
          |(1-a)*((q.2.vertex j).1 : ℝ)-a*((q.2.vertex j).2 : ℝ)| ≤ 8*s) ∧
        (1-2*φ)*(n : ℝ) < ((q.2.collectedSites.filter (fun z => (ω z : EReal) =
          sSup ((fun t : ℝ => (t : EReal)) '' μ.support))).card : ℝ)} := by
  classical
  simpa only [Set.mem_ofPred_eq] using measurableSet_exists_closed_strip_bad_sites
    {t : ℝ | (t : EReal) = sSup ((fun r : ℝ => (r : EReal)) '' μ.support)}
    (source_top_indicator_event_measurable μ) a s (1-2*φ) n

open Classical in
/-- Assembly of the endpoint union estimate from the shape properties. The final
theorem obtains all of them from the one-dimensional marginal alone. -/
theorem eventually_measure_closed_strip_top_sites_le
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (g : Quadrant → ℝ)
    (hg : Continuous g)
    (hhom : ∀ (c : ℝ≥0) (x : Quadrant), g (c*x.1,c*x.2) = (c : ℝ)*g x)
    (hnonneg : ∀ x : Quadrant, 0 ≤ g x)
    (hi : ∀ (u : Lattice) (d : ℕ × ℕ), Integrable
      (fun ω : Environment => lastPassage (fun z => if (ω z : EReal) =
        sSup ((fun t : ℝ => (t : EReal)) '' μ.support) then 1 else 0) u d)
      (environmentLaw μ))
    (hm : ∀ (u : Lattice) (d : ℕ × ℕ),
      (∫ ω : Environment, lastPassage (fun z => if (ω z : EReal) =
        sSup ((fun t : ℝ => (t : EReal)) '' μ.support) then 1 else 0) u d
          ∂environmentLaw μ) ≤ g ((d.1 : ℝ≥0),(d.2 : ℝ≥0)))
    (a φ : ℝ) (ha0 : 0<a) (ha1 : a<1) (hφ : 0<φ)
    (hgap : g (toQuadrant (a,1-a)) ≤ 1-4*φ) :
    ∀ᶠ s : ℝ in atTop,
      (environmentLaw μ).real {ω : Environment | ∃ u : Lattice,
        ∃ q : Σ i : Fin (Nat.ceil (s^3)+1), Path u (i.val,Nat.ceil (s^3)-i.val),
          (∀ j, 0 ≤ (q.2.vertex j).1+(q.2.vertex j).2 ∧
            (q.2.vertex j).1+(q.2.vertex j).2 ≤ (Nat.ceil (s^3) : ℤ) ∧
            |(1-a)*((q.2.vertex j).1 : ℝ)-a*((q.2.vertex j).2 : ℝ)| ≤ 8*s) ∧
          (1-2*φ)*(Nat.ceil (s^3) : ℝ) <
            ((q.2.collectedSites.filter (fun z => (ω z : EReal) =
              sSup ((fun t : ℝ => (t : EReal)) '' μ.support))).card : ℝ)} ≤
        289*s^2*Real.exp (-(φ^2*s^2/17)) := by
  have hφle : φ ≤ 1/4 := by
    have h0 := hnonneg (toQuadrant (a,1-a))
    linarith only [h0, hgap]
  filter_upwards [eventually_ge_atTop (1 : ℝ),
    eventually_cubic_top_shape_bound g hg hhom a φ ha0 ha1 hφ hgap] with s hs hshape
  let n : ℕ := Nat.ceil (s^3)
  let M : EReal := sSup ((fun t : ℝ => (t : EReal)) '' μ.support)
  let slice : ℤ → Finset Lattice := fun k => (Finset.Icc
    (Int.ceil (a*(k : ℝ)-8*s)) (Int.floor (a*(k : ℝ)+8*s))).image
      (fun i => (i,k-i))
  let R : Finset Lattice := (Finset.Icc (0 : ℤ) (n : ℤ)).biUnion slice
  let P : Finset (Lattice × Lattice) := slice 0 ×ˢ slice (n : ℤ)
  let E : (Lattice × Lattice) → Set Environment := fun uv =>
    {ω | ∃ d : ℕ × ℕ, ∃ p : Path uv.1 d,
      uv.2 = uv.1+((d.1 : ℤ),(d.2 : ℤ)) ∧ (∀ j, p.vertex j ∈ R) ∧
      (1-2*φ)*(n : ℝ) <
        ((p.collectedSites.filter (fun z => (ω z : EReal)=M)).card : ℝ)}
  have hR := cubic_top_tail_region_cardinality_bounds a s hs
  change 0 < (R.card : ℝ) ∧ (R.card : ℝ) ≤ 34*(n : ℝ)*s at hR
  have hRpos : 0 < R.card := Nat.cast_pos.mp hR.1
  have hchain := cubic_top_tail_actual_region_exp_chain a φ s hφ hs
  change Real.exp (-(2*(φ*(n : ℝ))^2/(R.card : ℝ))) ≤
      Real.exp (-(φ^2*(n : ℝ)/(17*s))) ∧
    Real.exp (-(φ^2*(n : ℝ)/(17*s))) ≤ Real.exp (-(φ^2*s^2/17)) at hchain
  have htail (uv : Lattice × Lattice) (huvP : uv ∈ P) :
      (environmentLaw μ).real (E uv) ≤ Real.exp (-(φ^2*s^2/17)) := by
    rcases uv with ⟨u,v⟩
    by_cases huv : u ≤ v
    · have hu := (tiltStripLevelSlice_mem_iff a s 0 u).1
        (Finset.mem_product.mp huvP).1
      have hv := (tiltStripLevelSlice_mem_iff a s (n : ℤ) v).1
        (Finset.mem_product.mp huvP).2
      let d : ℕ × ℕ := ((v.1-u.1).toNat,(v.2-u.2).toNat)
      have hd := tilt_strip_endpoint_displacement_bounds a s n u v huv hu hv
      change d.1+d.2=n ∧ |(1-a)*(d.1 : ℝ)-a*(d.2 : ℝ)| ≤ 16*s at hd
      have hgd := hshape d hd.1 hd.2
      have hb : 0 ≤ (1-3*φ)*(n : ℝ) :=
        mul_nonneg (by linarith only [hφle]) (Nat.cast_nonneg n)
      have ht : 0 ≤ φ*(n : ℝ) := mul_nonneg hφ.le (Nat.cast_nonneg n)
      have hfixed := source_top_tail_of_whole_mean_bound μ R u d
        ((1-3*φ)*(n : ℝ)) (φ*(n : ℝ)) hb ht (hi u d) ((hm u d).trans hgd)
      have hthreshold : (1-3*φ)*(n : ℝ)+φ*(n : ℝ) = (1-2*φ)*(n : ℝ) := by ring
      dsimp only at hfixed
      rw [hthreshold] at hfixed
      have hEq := endpoint_top_event_eq_of_le M R u v ((1-2*φ)*(n : ℝ)) huv
      change E (u,v) = _ at hEq
      rw [hEq]
      exact (hfixed.2.1 hRpos).trans (by
        rw [neg_div]
        exact hchain.1.trans hchain.2)
    · have hEq := endpoint_top_event_eq_empty_of_not_le M R u v
        ((1-2*φ)*(n : ℝ)) huv
      change E (u,v) = ∅ at hEq
      rw [hEq, measureReal_empty]
      exact (Real.exp_pos _).le
  have hEq := closed_strip_top_event_eq_endpoint_union M a s ((1-2*φ)*(n : ℝ)) n
  change _ = ⋃ uv ∈ P, E uv at hEq
  change (environmentLaw μ).real _ ≤ _
  rw [hEq]
  calc
    (environmentLaw μ).real (⋃ uv ∈ P, E uv) ≤
        ∑ uv ∈ P, (environmentLaw μ).real (E uv) := measureReal_biUnion_finset_le P E
    _ ≤ ∑ _uv ∈ P, Real.exp (-(φ^2*s^2/17)) := Finset.sum_le_sum htail
    _ = (P.card : ℝ)*Real.exp (-(φ^2*s^2/17)) := by
      rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ 289*s^2*Real.exp (-(φ^2*s^2/17)) := by
      have hpairs : (P.card : ℝ) ≤ 289*s^2 := by
        simpa only [P, slice, n, Int.cast_zero, Int.cast_natCast] using
          cubic_top_tail_endpoint_pairs_card_le a s hs
      exact mul_le_mul_of_nonneg_right hpairs (Real.exp_pos _).le

open Classical in
/-- From a probability measure alone, there is a top-indicator shape with the
properties listed in the statement. It controls the full-strip top-site event in
every direction, with the off-flat gap shown there. -/
theorem exists_source_top_indicator_shape_with_strip_rarity
    (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    let M : EReal := sSup ((fun t : ℝ => (t : EReal)) '' μ.support)
    let χ : ℝ → ℝ := fun t => if (t : EReal)=M then 1 else 0
    ∃ g : Quadrant → ℝ,
      Continuous g ∧
      (∀ (c : ℝ≥0) (x : Quadrant), g (c*x.1,c*x.2) = (c : ℝ)*g x) ∧
      (∀ (x y : Quadrant) (a b : ℝ≥0), a+b=1 →
        (a : ℝ)*g x+(b : ℝ)*g y ≤ g (a*x.1+b*y.1,a*x.2+b*y.2)) ∧
      (∀ᵐ ω ∂environmentLaw μ, ∀ ε : ℝ, 0<ε → ∃ N : ℕ, 1≤N ∧
        ∀ d : ℕ × ℕ, N≤d.1+d.2 →
          |lastPassage (fun z => χ (ω z)) 0 d-g ((d.1 : ℝ≥0),(d.2 : ℝ≥0))| ≤
            ε*((d.1+d.2 : ℕ) : ℝ)) ∧
      (∀ x : Quadrant, Tendsto (fun n : ℕ =>
        (∫ ω : Environment, lastPassage (fun z => χ (ω z)) 0
          (⌊(n : ℝ)*(x.1 : ℝ)⌋₊,⌊(n : ℝ)*(x.2 : ℝ)⌋₊) ∂environmentLaw μ)/(n : ℝ))
            atTop (𝓝 (g x))) ∧
      (∀ (u : Lattice) (d : ℕ × ℕ), Integrable
        (fun ω : Environment => lastPassage (fun z => χ (ω z)) u d) (environmentLaw μ)) ∧
      (∀ x : Quadrant, 0≤g x ∧ g x≤(x.1 : ℝ)+x.2) ∧
      (∀ (u : Lattice) (d : ℕ × ℕ),
        (∫ ω : Environment, lastPassage (fun z => χ (ω z)) u d ∂environmentLaw μ) ≤
          g ((d.1 : ℝ≥0),(d.2 : ℝ≥0))) ∧
      (∀ x : Quadrant, (∫ t : ℝ, t ∂μ.map χ)*((x.1 : ℝ)+x.2) ≤ g x) ∧
      (M=⊤ → g=fun _ => 0) ∧
      (∀ (a φ : ℝ), 0<a → a<1 → 0<φ → g (toQuadrant (a,1-a)) ≤ 1-4*φ →
        φ≤1/4 ∧
        (∀ s : ℝ, MeasurableSet {ω : Environment | ∃ u : Lattice,
          ∃ q : Σ i : Fin (Nat.ceil (s^3)+1), Path u (i.val,Nat.ceil (s^3)-i.val),
            (∀ j, 0≤(q.2.vertex j).1+(q.2.vertex j).2 ∧
              (q.2.vertex j).1+(q.2.vertex j).2≤(Nat.ceil (s^3) : ℤ) ∧
              |(1-a)*((q.2.vertex j).1 : ℝ)-a*((q.2.vertex j).2 : ℝ)|≤8*s) ∧
            (1-2*φ)*(Nat.ceil (s^3) : ℝ) <
              ((q.2.collectedSites.filter (fun z => (ω z : EReal)=M)).card : ℝ)}) ∧
        (∀ᶠ s : ℝ in atTop, (environmentLaw μ).real {ω : Environment | ∃ u : Lattice,
          ∃ q : Σ i : Fin (Nat.ceil (s^3)+1), Path u (i.val,Nat.ceil (s^3)-i.val),
            (∀ j, 0≤(q.2.vertex j).1+(q.2.vertex j).2 ∧
              (q.2.vertex j).1+(q.2.vertex j).2≤(Nat.ceil (s^3) : ℤ) ∧
              |(1-a)*((q.2.vertex j).1 : ℝ)-a*((q.2.vertex j).2 : ℝ)|≤8*s) ∧
            (1-2*φ)*(Nat.ceil (s^3) : ℝ) <
              ((q.2.collectedSites.filter (fun z => (ω z : EReal)=M)).card : ℝ)} ≤
                289*s^2*Real.exp (-(φ^2*s^2/17))) ∧
        Tendsto (fun s : ℝ => (environmentLaw μ).real {ω : Environment | ∃ u : Lattice,
          ∃ q : Σ i : Fin (Nat.ceil (s^3)+1), Path u (i.val,Nat.ceil (s^3)-i.val),
            (∀ j, 0≤(q.2.vertex j).1+(q.2.vertex j).2 ∧
              (q.2.vertex j).1+(q.2.vertex j).2≤(Nat.ceil (s^3) : ℤ) ∧
              |(1-a)*((q.2.vertex j).1 : ℝ)-a*((q.2.vertex j).2 : ℝ)|≤8*s) ∧
            (1-2*φ)*(Nat.ceil (s^3) : ℝ) <
              ((q.2.collectedSites.filter (fun z => (ω z : EReal)=M)).card : ℝ)})
          atTop (𝓝 0)) := by
  classical
  intro M χ
  obtain ⟨g, hg, hhom, hconc, hsample, hlim, hi, hbound, hm, hlower, htop⟩ :=
    exists_source_top_indicator_shape μ
  refine ⟨g, hg, hhom, hconc, hsample, hlim, hi, hbound, hm, hlower, htop, ?_⟩
  intro a φ ha0 ha1 hφ hgap
  have hφle : φ≤1/4 := by
    have h0 := (hbound (toQuadrant (a,1-a))).1
    linarith only [h0, hgap]
  have htail := eventually_measure_closed_strip_top_sites_le μ g hg hhom
    (fun x => (hbound x).1) hi hm a φ ha0 ha1 hφ hgap
  refine ⟨hφle, (fun s => measurableSet_closed_strip_top_sites μ a s φ _), htail, ?_⟩
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (tendsto_cubic_top_tail_gaussian_prefactor φ hφ)
  · exact Eventually.of_forall fun _ => measureReal_nonneg
  · exact htail

end LPPDifferentiability
end
