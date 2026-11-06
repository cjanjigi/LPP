/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Martin2004.Probability.ExponentialLaw
public import Martin2004.Probability.BurkeDensity

/-!
# The Burke property of one cell of the exponential corner growth model

The Burke property of one cell, the basic step behind the exponential shape. Martin (2004)
uses the exponential shape in the proof of Theorem 2.4; the Burke property is the standard
argument behind it.

Take independent `I ~ Exp(1 - ρ)`, `J ~ Exp(ρ)`, `W ~ Exp(1)` with `0 < ρ < 1`. The map
`(I, J, W) ↦ (W + (I - J)⁺, W + (J - I)⁺, min I J)` preserves their joint law.

Proof (change of variables). The joint law has a density with respect to
Lebesgue measure on `ℝ³`. On the half space `{J ≤ I}` the map is the linear map
`(x, y, w) ↦ (x + (w - y), w, y)`, and on `{I < J}` it is `(x, y, w) ↦ (w, y + (w - x), x)`.
Both preserve Lebesgue measure, map the half space onto `{J' ≤ I'}` respectively `{I' < J'}`,
and leave the density unchanged, because the exponent `-(1 - ρ) x - ρ y - w` is the same
before and after. The two images together cover `ℝ³`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace LPPDifferentiability

/-- The Burke map of one cell: (I, J, W) goes to
(W + (I - J)+, W + (J - I)+, min I J). -/
noncomputable def burkeMap (p : ℝ × ℝ × ℝ) : ℝ × ℝ × ℝ :=
  (p.2.2 + max (p.1 - p.2.1) 0, p.2.2 + max (p.2.1 - p.1) 0, min p.1 p.2.1)

/-- The input law of one cell: independent Exp(1 - rho), Exp(rho), Exp(1). -/
noncomputable def burkeLaw (ρ : ℝ) : Measure (ℝ × ℝ × ℝ) :=
  (expMeasure (1 - ρ)).prod ((expMeasure ρ).prod (expMeasure 1))

/-! ## The density of the cell law -/

/-- The density of `burkeLaw ρ` with respect to Lebesgue measure on `ℝ × ℝ × ℝ`. -/
private noncomputable def cellDensity (ρ : ℝ) (p : ℝ × ℝ × ℝ) : ℝ≥0∞ :=
  exponentialPDF (1 - ρ) p.1 * (exponentialPDF ρ p.2.1 * exponentialPDF 1 p.2.2)

/-- The density at an explicit point, written as three factors. -/
private theorem cellDensity_apply (ρ x y w : ℝ) :
    cellDensity ρ (x, y, w) =
      exponentialPDF (1 - ρ) x * (exponentialPDF ρ y * exponentialPDF 1 w) := rfl

/-- The cell density is measurable. -/
private theorem measurable_cellDensity (ρ : ℝ) : Measurable (cellDensity ρ) := by
  have hm : ∀ r : ℝ, Measurable (exponentialPDF r) := fun r =>
    (measurable_exponentialPDFReal r).ennreal_ofReal
  have h1 : Measurable (fun p : ℝ × ℝ × ℝ => exponentialPDF (1 - ρ) p.1) :=
    (hm _).comp measurable_fst
  have h2 : Measurable (fun p : ℝ × ℝ × ℝ => exponentialPDF ρ p.2.1) :=
    (hm _).comp (measurable_fst.comp measurable_snd)
  have h3 : Measurable (fun p : ℝ × ℝ × ℝ => exponentialPDF 1 p.2.2) :=
    (hm _).comp (measurable_snd.comp measurable_snd)
  exact h1.mul (h2.mul h3)

/-- The density vanishes outside the closed positive octant. -/
private theorem cellDensity_eq_zero {ρ x y w : ℝ} (h : ¬(0 ≤ x ∧ 0 ≤ y ∧ 0 ≤ w)) :
    cellDensity ρ (x, y, w) = 0 := by
  rw [cellDensity_apply]
  by_cases hx : 0 ≤ x
  · by_cases hy : 0 ≤ y
    · have hw : w < 0 := not_le.mp fun hw => h ⟨hx, hy, hw⟩
      rw [exponentialPDF_of_neg hw]
      simp
    · rw [exponentialPDF_of_neg (not_le.mp hy)]
      simp
  · rw [exponentialPDF_of_neg (not_le.mp hx)]
    simp

/-- Inside the closed positive octant the density is
`(1 - ρ) ρ exp (-((1 - ρ) x + ρ y + w))`. -/
private theorem cellDensity_of_nonneg {ρ x y w : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hw : 0 ≤ w) :
    cellDensity ρ (x, y, w) =
      ENNReal.ofReal ((1 - ρ) * ρ * Real.exp (-((1 - ρ) * x + ρ * y + w))) := by
  have hρ' : 0 < 1 - ρ := sub_pos.2 hρ1
  have hexp : Real.exp (-((1 - ρ) * x + ρ * y + w)) =
      Real.exp (-((1 - ρ) * x)) * Real.exp (-(ρ * y)) * Real.exp (-(1 * w)) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  have hreal : (1 - ρ) * ρ * Real.exp (-((1 - ρ) * x + ρ * y + w)) =
      ((1 - ρ) * Real.exp (-((1 - ρ) * x))) *
        ((ρ * Real.exp (-(ρ * y))) * (1 * Real.exp (-(1 * w)))) := by
    rw [hexp]
    ring
  have hA : 0 ≤ (1 - ρ) * Real.exp (-((1 - ρ) * x)) :=
    mul_nonneg hρ'.le (Real.exp_pos _).le
  have hB : 0 ≤ ρ * Real.exp (-(ρ * y)) := mul_nonneg hρ0.le (Real.exp_pos _).le
  rw [cellDensity_apply, exponentialPDF_of_nonneg hx, exponentialPDF_of_nonneg hy,
    exponentialPDF_of_nonneg hw, hreal, ENNReal.ofReal_mul hA, ENNReal.ofReal_mul hB]

/-- On the half space `y ≤ x` the density is unchanged by `(x, y, w) ↦ (x + (w - y), w, y)`. -/
private theorem cellDensity_shiftA {ρ x y w : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hxy : y ≤ x) :
    cellDensity ρ (x + (w - y), w, y) = cellDensity ρ (x, y, w) := by
  by_cases h : 0 ≤ y ∧ 0 ≤ w
  · obtain ⟨hy, hw⟩ := h
    have hexp : -((1 - ρ) * (x + (w - y)) + ρ * w + y) = -((1 - ρ) * x + ρ * y + w) := by
      ring
    have hx1 : 0 ≤ x + (w - y) := by linarith
    rw [cellDensity_of_nonneg hρ0 hρ1 hx1 hw hy,
      cellDensity_of_nonneg hρ0 hρ1 (le_trans hy hxy) hy hw, hexp]
  · have h0 : cellDensity ρ (x + (w - y), w, y) = 0 :=
      cellDensity_eq_zero fun h' => h ⟨h'.2.2, h'.2.1⟩
    have h0' : cellDensity ρ (x, y, w) = 0 :=
      cellDensity_eq_zero fun h' => h ⟨h'.2.1, h'.2.2⟩
    rw [h0, h0']

/-- On the half space `x < y` the density is unchanged by `(x, y, w) ↦ (w, y + (w - x), x)`. -/
private theorem cellDensity_shiftB {ρ x y w : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hxy : x < y) :
    cellDensity ρ (w, y + (w - x), x) = cellDensity ρ (x, y, w) := by
  by_cases h : 0 ≤ x ∧ 0 ≤ w
  · obtain ⟨hx, hw⟩ := h
    have hexp : -((1 - ρ) * w + ρ * (y + (w - x)) + x) = -((1 - ρ) * x + ρ * y + w) := by
      ring
    have hy1 : 0 ≤ y + (w - x) := by linarith
    have hy2 : 0 ≤ y := by linarith
    rw [cellDensity_of_nonneg hρ0 hρ1 hw hy1 hx,
      cellDensity_of_nonneg hρ0 hρ1 hx hy2 hw, hexp]
  · have h0 : cellDensity ρ (w, y + (w - x), x) = 0 :=
      cellDensity_eq_zero fun h' => h ⟨h'.2.2, h'.1⟩
    have h0' : cellDensity ρ (x, y, w) = 0 :=
      cellDensity_eq_zero fun h' => h ⟨h'.1, h'.2.2⟩
    rw [h0, h0']

/-! ## The Burke map on the two half spaces -/

/-- The Burke map is measurable. -/
private theorem measurable_burkeMap : Measurable burkeMap := by
  have hx : Measurable (fun p : ℝ × ℝ × ℝ => p.1) := measurable_fst
  have hy : Measurable (fun p : ℝ × ℝ × ℝ => p.2.1) := measurable_fst.comp measurable_snd
  have hw : Measurable (fun p : ℝ × ℝ × ℝ => p.2.2) := measurable_snd.comp measurable_snd
  show Measurable fun p : ℝ × ℝ × ℝ =>
    (p.2.2 + max (p.1 - p.2.1) 0, p.2.2 + max (p.2.1 - p.1) 0, min p.1 p.2.1)
  exact (hw.add ((hx.sub hy).max measurable_const)).prodMk
    ((hw.add ((hy.sub hx).max measurable_const)).prodMk (hx.min hy))

/-- On the half space `y ≤ x` the Burke map is `(x, y, w) ↦ (x + (w - y), w, y)`. -/
private theorem burkeMap_of_le {x y w : ℝ} (h : y ≤ x) :
    burkeMap (x, y, w) = (x + (w - y), w, y) := by
  simp only [burkeMap, Prod.mk.injEq]
  refine ⟨?_, ?_, min_eq_right h⟩
  · rw [max_eq_left (sub_nonneg.2 h)]
    ring
  · rw [max_eq_right (show y - x ≤ 0 by linarith)]
    ring

/-- On the half space `x < y` the Burke map is `(x, y, w) ↦ (w, y + (w - x), x)`. -/
private theorem burkeMap_of_lt {x y w : ℝ} (h : x < y) :
    burkeMap (x, y, w) = (w, y + (w - x), x) := by
  simp only [burkeMap, Prod.mk.injEq]
  refine ⟨?_, ?_, min_eq_left h.le⟩
  · rw [max_eq_right (show x - y ≤ 0 by linarith)]
    ring
  · rw [max_eq_left (show 0 ≤ y - x by linarith)]
    ring

/-! ## The change of variables -/

/-- Integrals against the cell density are unchanged by the Burke map. -/
private theorem lintegral_burkeMap_mul_cellDensity {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    {g : ℝ × ℝ × ℝ → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ p, g (burkeMap p) * cellDensity ρ p = ∫⁻ p, g p * cellDensity ρ p := by
  -- the two linear maps used here, both preserving Lebesgue measure
  have hP : MeasurePreserving
      (fun p : ℝ × ℝ × ℝ => (p.1 + (p.2.2 - p.2.1), p.2.2, p.2.1))
      (volume : Measure (ℝ × ℝ × ℝ)) volume :=
    measurePreserving_swap_last.comp
      (measurePreserving_shear_first (fun q : ℝ × ℝ => q.2 - q.1)
        (measurable_snd.sub measurable_fst))
  have hQ : MeasurePreserving
      (fun p : ℝ × ℝ × ℝ => (p.2.2, p.2.1 + (p.2.2 - p.1), p.1))
      (volume : Measure (ℝ × ℝ × ℝ)) volume :=
    measurePreserving_swap_first.comp (hP.comp measurePreserving_swap_first)
  -- the integrands restricted to the two half spaces
  obtain ⟨GA, hGA⟩ : ∃ GA : ℝ × ℝ × ℝ → ℝ≥0∞, ∀ q, GA q =
      if q.2.1 ≤ q.1 then g q * cellDensity ρ q else 0 := ⟨_, fun _ => rfl⟩
  obtain ⟨GB, hGB⟩ : ∃ GB : ℝ × ℝ × ℝ → ℝ≥0∞, ∀ q, GB q =
      if q.1 < q.2.1 then g q * cellDensity ρ q else 0 := ⟨_, fun _ => rfl⟩
  have hGAm : Measurable GA := by
    have : GA = fun q => if q.2.1 ≤ q.1 then g q * cellDensity ρ q else 0 := funext hGA
    rw [this]
    exact Measurable.ite
      (measurableSet_le (measurable_fst.comp measurable_snd) measurable_fst)
      (hg.mul (measurable_cellDensity ρ)) measurable_const
  have hGBm : Measurable GB := by
    have : GB = fun q => if q.1 < q.2.1 then g q * cellDensity ρ q else 0 := funext hGB
    rw [this]
    exact Measurable.ite
      (measurableSet_lt measurable_fst (measurable_fst.comp measurable_snd))
      (hg.mul (measurable_cellDensity ρ)) measurable_const
  -- pulled back along the two maps, the restricted integrands are the Burke integrand
  have hA : ∀ p : ℝ × ℝ × ℝ,
      GA (p.1 + (p.2.2 - p.2.1), p.2.2, p.2.1) =
        if p.2.1 ≤ p.1 then g (burkeMap p) * cellDensity ρ p else 0 := by
    rintro ⟨x, y, w⟩
    rw [hGA]
    by_cases h : y ≤ x
    · have h' : w ≤ x + (w - y) := by linarith
      simp only [h', h, ↓reduceIte, burkeMap_of_le (w := w) h,
        cellDensity_shiftA (w := w) hρ0 hρ1 h]
    · have h' : ¬ w ≤ x + (w - y) := fun h' => h (by linarith)
      simp only [h', h, ↓reduceIte]
  have hB : ∀ p : ℝ × ℝ × ℝ,
      GB (p.2.2, p.2.1 + (p.2.2 - p.1), p.1) =
        if p.1 < p.2.1 then g (burkeMap p) * cellDensity ρ p else 0 := by
    rintro ⟨x, y, w⟩
    rw [hGB]
    by_cases h : x < y
    · have h' : w < y + (w - x) := by linarith
      simp only [h', h, ↓reduceIte, burkeMap_of_lt (w := w) h,
        cellDensity_shiftB (w := w) hρ0 hρ1 h]
    · have h' : ¬ w < y + (w - x) := fun h' => h (by linarith)
      simp only [h', h, ↓reduceIte]
  have hsum : ∀ q : ℝ × ℝ × ℝ, GA q + GB q = g q * cellDensity ρ q := by
    intro q
    rw [hGA, hGB]
    by_cases h : q.2.1 ≤ q.1
    · have h' : ¬ q.1 < q.2.1 := not_lt.2 h
      simp only [h, h', ↓reduceIte, add_zero]
    · have h' : q.1 < q.2.1 := not_le.1 h
      simp only [h, h', ↓reduceIte, zero_add]
  have e1 : ∫⁻ p : ℝ × ℝ × ℝ, GA (p.1 + (p.2.2 - p.2.1), p.2.2, p.2.1) = ∫⁻ q, GA q :=
    hP.lintegral_comp hGAm
  have e2 : ∫⁻ p : ℝ × ℝ × ℝ, GB (p.2.2, p.2.1 + (p.2.2 - p.1), p.1) = ∫⁻ q, GB q :=
    hQ.lintegral_comp hGBm
  calc ∫⁻ p, g (burkeMap p) * cellDensity ρ p
      = ∫⁻ p : ℝ × ℝ × ℝ, (GA (p.1 + (p.2.2 - p.2.1), p.2.2, p.2.1) +
          GB (p.2.2, p.2.1 + (p.2.2 - p.1), p.1)) := by
        refine lintegral_congr fun p => ?_
        rw [hA p, hB p]
        by_cases h : p.2.1 ≤ p.1
        · have h' : ¬ p.1 < p.2.1 := not_lt.2 h
          simp only [h, h', ↓reduceIte, add_zero]
        · have h' : p.1 < p.2.1 := not_le.1 h
          simp only [h, h', ↓reduceIte, zero_add]
    _ = (∫⁻ p : ℝ × ℝ × ℝ, GA (p.1 + (p.2.2 - p.2.1), p.2.2, p.2.1)) +
          ∫⁻ p : ℝ × ℝ × ℝ, GB (p.2.2, p.2.1 + (p.2.2 - p.1), p.1) :=
        lintegral_add_left (hGAm.comp hP.measurable) _
    _ = (∫⁻ q, GA q) + ∫⁻ q, GB q := by rw [e1, e2]
    _ = ∫⁻ q, (GA q + GB q) := (lintegral_add_left hGAm _).symm
    _ = ∫⁻ p, g p * cellDensity ρ p := lintegral_congr hsum

/-! ## The Burke property -/

/-- The Burke property. The Burke map preserves the cell law: the three
outputs are again independent with laws Exp(1 - rho), Exp(rho), Exp(1). -/
theorem map_burkeMap_burkeLaw {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) :
    (burkeLaw ρ).map burkeMap = burkeLaw ρ := by
  have hlaw : burkeLaw ρ = (volume : Measure (ℝ × ℝ × ℝ)).withDensity (cellDensity ρ) :=
    expMeasure_prod_prod_eq_withDensity (1 - ρ) ρ 1
  ext s hs
  rw [Measure.map_apply measurable_burkeMap hs, hlaw,
    withDensity_apply _ (measurable_burkeMap hs), withDensity_apply _ hs,
    ← lintegral_indicator (measurable_burkeMap hs), ← lintegral_indicator hs]
  have key := lintegral_burkeMap_mul_cellDensity hρ0 hρ1
    (g := s.indicator 1) (measurable_one.indicator hs)
  calc ∫⁻ a, (burkeMap ⁻¹' s).indicator (cellDensity ρ) a
      = ∫⁻ p, s.indicator 1 (burkeMap p) * cellDensity ρ p :=
        lintegral_congr fun p => by
          by_cases h : burkeMap p ∈ s <;> simp [h]
    _ = ∫⁻ p, s.indicator 1 p * cellDensity ρ p := key
    _ = ∫⁻ a, s.indicator (cellDensity ρ) a :=
        lintegral_congr fun p => by
          by_cases h : p ∈ s <;> simp [h]

/-- Pair form of the Burke property. The two outgoing increments are independent with laws
Exp(1 - rho) and Exp(rho). -/
theorem map_burkePair_burkeLaw {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) :
    (burkeLaw ρ).map (fun p => ((burkeMap p).1, (burkeMap p).2.1)) =
      (expMeasure (1 - ρ)).prod (expMeasure ρ) := by
  calc (burkeLaw ρ).map (fun p => ((burkeMap p).1, (burkeMap p).2.1))
      = ((burkeLaw ρ).map burkeMap).map (Prod.map id Prod.fst) :=
        (Measure.map_map (measurable_id.prodMap measurable_fst) measurable_burkeMap).symm
    _ = (burkeLaw ρ).map (Prod.map id Prod.fst) := by
        rw [map_burkeMap_burkeLaw hρ0 hρ1]
    _ = (expMeasure (1 - ρ)).prod (expMeasure ρ) := by
        unfold burkeLaw
        rw [← Measure.map_prod_map _ _ measurable_id measurable_fst]
        simp

end LPPDifferentiability
