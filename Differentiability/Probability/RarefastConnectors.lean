/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Differentiability.Probability.GeneralIntervals
public import LPP_Foundations.Analysis.ShapeSupportingFunctionals
import Martin2004.Probability.WeakNegativeShape
import LPP_Foundations.Probability.PassageMeasurable
import Mathlib.Tactic

/-!
# Connectors in the coarse-graining for rare fast crossings

Steps 3 and 4 of the proof of Proposition 3.4 of the differentiability preprint. For a forward
neighbour, the connection event asks that every point of the exit interval of a site be joined to
every point of the entry interval of the neighbour by a path with `f_σ`-defect at most `ε s / 2`
that stays within transverse distance `4 S` of the centre of the site. The level interval lemma, the
one-sided contact of the supporting functional and homogeneity give probability at least `p s → 1`.

## References

* C. Janjigian, F. Rassoul-Agha and T. Seppäläinen, *Differentiability of the shape function in
  the planar corner growth model*, preprint.
-/

public section

open MeasureTheory Filter Set
open scoped Topology NNReal ENNReal

namespace LPPDifferentiability

/-- Explicit contact radius: on its own side, the supporting line of slope
`ĝ'(0σ)` exceeds the profile by at most `κ |h|` for `0 < σ h ≤ h₀`. -/
private theorem exists_contact_radius (g : Quadrant → ℝ)
    (hgconc : ∀ (x y : Quadrant) (r s : ℝ≥0), r + s = 1 →
      (r : ℝ) * g x + (s : ℝ) * g y ≤ g (r • x + s • y))
    (hhom : ∀ (c : ℝ≥0) (z : Quadrant), g (c • z) = (c : ℝ) * g z)
    (a σ κ : ℝ) (ha₀ : 0 < a) (ha₁ : a < 1) (hσ : σ = 1 ∨ σ = -1) (hκ : 0 < κ) :
    ∃ h₀ : ℝ, 0 < h₀ ∧ ∀ h : ℝ, 0 < σ * h → σ * h ≤ h₀ →
      quadrantExtension g (a + 0, 1 - a - 0) +
          (if σ = 1 then
              derivWithin (fun h => quadrantExtension g (a + h, 1 - a - h)) (Ioi 0) 0
            else derivWithin (fun h => quadrantExtension g (a + h, 1 - a - h)) (Iio 0) 0) * h -
        quadrantExtension g (a + h, 1 - a - h) ≤ κ * |h| := by
  obtain ⟨-, -, -, -, hcm, hcp⟩ :=
    quadrant_supporting_functionals_and_contact g hgconc hhom a ha₀ ha₁
  rcases hσ with rfl | rfl
  · have hev := hcp.def hκ
    rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at hev
    obtain ⟨δ, hδ, hball⟩ := hev
    refine ⟨δ / 2, half_pos hδ, fun h hpos hle => ?_⟩
    have hh : 0 < h := by linarith
    have hd : dist h 0 < δ := by
      rw [Real.dist_eq, sub_zero, abs_of_pos hh]
      linarith
    have hb := hball hd hh
    simp only [Real.norm_eq_abs, abs_abs] at hb
    rw [ite_eq_left (rfl : (1 : ℝ) = 1)]
    exact le_trans (le_of_eq (by ring)) ((le_abs_self _).trans hb)
  · have hev := hcm.def hκ
    rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at hev
    obtain ⟨δ, hδ, hball⟩ := hev
    refine ⟨δ / 2, half_pos hδ, fun h hpos hle => ?_⟩
    have hh : h < 0 := by linarith
    have hd : dist h 0 < δ := by
      rw [Real.dist_eq, sub_zero, abs_of_neg hh]
      linarith
    have hb := hball hd hh
    simp only [Real.norm_eq_abs, abs_abs] at hb
    rw [ite_eq_right (show ¬((-1 : ℝ) = 1) by norm_num)]
    exact le_trans (le_of_eq (by ring)) ((le_abs_self _).trans hb)

/-- Algebra of the homogeneity step. -/
private theorem gap_core (Q₀ slope κ n ρ F G : ℝ) (hn : 0 < n) (hG : G = n * F)
    (hc : Q₀ + slope * (ρ / n) - F ≤ κ * |ρ / n|) :
    Q₀ * n + slope * ρ - G ≤ κ * |ρ| := by
  have hn0 : n ≠ 0 := hn.ne'
  have hnr : n * (ρ / n) = ρ := mul_div_cancel₀ ρ hn0
  have hna : n * (|ρ| / n) = |ρ| := mul_div_cancel₀ |ρ| hn0
  rw [hG]
  calc Q₀ * n + slope * ρ - n * F = n * (Q₀ + slope * (ρ / n) - F) := by
        linear_combination (-slope) * hnr
    _ ≤ n * (κ * |ρ / n|) := mul_le_mul_of_nonneg_left hc hn.le
    _ = κ * (n * (|ρ| / n)) := by rw [abs_div, abs_of_pos hn]; ring
    _ = κ * |ρ| := by rw [hna]

/-- Homogeneity ((3.11) of the differentiability preprint): for a lattice displacement on its own
side and within the contact radius, `f_σ(z) - g(z) ≤ κ |r(z)|`. -/
private theorem shape_gap_le (g : Quadrant → ℝ)
    (hhom : ∀ (c : ℝ≥0) (z : Quadrant), g (c • z) = (c : ℝ) * g z)
    (a σ Q₀ slope κ h₀ : ℝ)
    (hcontact : ∀ h : ℝ, 0 < σ * h → σ * h ≤ h₀ →
      Q₀ + slope * h - quadrantExtension g (a + h, 1 - a - h) ≤ κ * |h|)
    (m₁ m₂ : ℕ) (hm : 0 < m₁ + m₂)
    (hpos : 0 < σ * ((1 - a) * (m₁ : ℝ) - a * (m₂ : ℝ)))
    (hsmall : σ * ((1 - a) * (m₁ : ℝ) - a * (m₂ : ℝ)) ≤ h₀ * ((m₁ : ℝ) + (m₂ : ℝ))) :
    Q₀ * ((m₁ : ℝ) + (m₂ : ℝ)) + slope * ((1 - a) * (m₁ : ℝ) - a * (m₂ : ℝ)) -
        g ((m₁ : ℝ≥0), (m₂ : ℝ≥0)) ≤ κ * |(1 - a) * (m₁ : ℝ) - a * (m₂ : ℝ)| := by
  have hz : (((m₁ : ℝ≥0), (m₂ : ℝ≥0)) : Quadrant) ≠ 0 := by
    intro h0
    have h1 : (m₁ : ℝ≥0) = 0 := congrArg Prod.fst h0
    have h2 : (m₂ : ℝ≥0) = 0 := congrArg Prod.snd h0
    simp only [Nat.cast_eq_zero] at h1 h2
    omega
  obtain ⟨hn, -, hval⟩ := quadrant_homogeneous_profile_normalization g hhom a _ hz
  simp only [NNReal.coe_natCast] at hn hval
  have h1 : 0 < σ * (((1 - a) * (m₁ : ℝ) - a * (m₂ : ℝ)) / ((m₁ : ℝ) + (m₂ : ℝ))) := by
    rw [← mul_div_assoc]
    exact div_pos hpos hn
  have h2 : σ * (((1 - a) * (m₁ : ℝ) - a * (m₂ : ℝ)) / ((m₁ : ℝ) + (m₂ : ℝ))) ≤ h₀ := by
    rw [← mul_div_assoc, div_le_iff₀ hn]
    exact hsmall
  exact gap_core Q₀ slope κ ((m₁ : ℝ) + (m₂ : ℝ)) ((1 - a) * (m₁ : ℝ) - a * (m₂ : ℝ)) _ _
    hn hval (hcontact _ h1 h2)

/-- Steps 3–4: connector events between the exit interval of a site and the
entry interval of a forward neighbour have probability at least `p s → 1`. -/
theorem exists_rarefast_connector_scale
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
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
    (a : ℝ) (ha₀ : 0 < a) (ha₁ : a < 1)
    (ε σ C₀ : ℝ) (hε : 0 < ε) (hσ : σ = 1 ∨ σ = -1) (hC₀ : 1 ≤ C₀) :
    let H : ℝ → ℝ := fun h => quadrantExtension g (a + h, 1 - a - h)
    let slope : ℝ :=
      if σ = 1 then derivWithin H (Ioi 0) 0 else derivWithin H (Iio 0) 0
    let rho : Lattice → ℝ := fun z => (1 - a) * (z.1 : ℝ) - a * (z.2 : ℝ)
    let f : Lattice → ℝ := fun z => H 0 * ((z.1 : ℝ) + (z.2 : ℝ)) + slope * rho z
    ∃ D₀ : ℝ, C₀ / 2 ≤ D₀ ∧ ∃ s₁ : ℝ, 1 ≤ s₁ ∧ ∃ p : ℝ → ℝ,
      (∀ s, 0 ≤ p s ∧ p s ≤ 1) ∧ Tendsto p atTop (𝓝 1) ∧
      ∀ (s S Y Y' : ℝ) (I : ℤ), s₁ ≤ s → s ≤ S → S ≤ C₀ * s →
        (Y' = Y + σ * S ∨ Y' = Y + 2 * σ * S) →
        let C : Set Environment := {ω | ∀ u u' : Lattice,
          u.1 + u.2 = I → |rho u - Y| ≤ S / 4 →
          u'.1 + u'.2 = I + (⌈D₀ * s⌉₊ : ℤ) → |rho u' - Y'| ≤ S / 4 →
          ∃ e : ℕ × ℕ, ∃ q : Path u e, q.vertex (Fin.last (e.1 + e.2)) = u' ∧
            f (u' - u) - pathWeight ω q ≤ ε * s / 2 ∧
            ∀ i, |rho (q.vertex i) - Y| ≤ 4 * S}
        MeasurableSet C ∧ p s ≤ (environmentLaw μ).real C := by
  intro H slope rho f
  -- One shape: the interval-lemma shape is `g` by uniqueness.
  obtain ⟨g', hg', -⟩ := exists_unique_shape_with_general_intervals μ hneg hpos
  obtain ⟨g₀, -, huniq⟩ :=
    exists_unique_shape_of_negative_moment_and_positive_tail μ hneg hpos
  have hgg : g' = g :=
    (huniq g' ⟨hg'.1, hg'.2.1, hg'.2.2.1, hg'.2.2.2.1⟩).trans
      (huniq g ⟨hgcont, hghom, hgconc, hgshape⟩).symm
  have hint := hg'.2.2.2.2
  rw [hgg] at hint
  have hconc' : ∀ (x y : Quadrant) (r t : ℝ≥0), r + t = 1 →
      (r : ℝ) * g x + (t : ℝ) * g y ≤ g (r • x + t • y) :=
    fun x y r t h => hgconc x y r t h
  have hhom' : ∀ (c : ℝ≥0) (z : Quadrant), g (c • z) = (c : ℝ) * g z :=
    fun c z => hghom c z
  have hC0 : 0 < C₀ := by linarith
  have hθ : 0 < min a (1 - a) := lt_min ha₀ (by linarith)
  -- Step 4: the contact radius `h₀` for `κ = ε / (12 C₀)`.
  obtain ⟨κ, hκdef⟩ : ∃ κ : ℝ, κ = ε / (12 * C₀) := ⟨_, rfl⟩
  have hκ : 0 < κ := by rw [hκdef]; exact div_pos hε (mul_pos (by norm_num) hC0)
  have hκC : κ * C₀ = ε / 12 := by
    rw [hκdef, div_mul_eq_mul_div, div_eq_div_iff (mul_pos (by norm_num) hC0).ne'
      (by norm_num)]
    ring
  obtain ⟨h₀, hh₀, hc₀⟩ := exists_contact_radius g hconc' hhom' a σ κ ha₀ ha₁ hσ hκ
  have hcontact : ∀ h : ℝ, 0 < σ * h → σ * h ≤ h₀ →
      H 0 + slope * h - quadrantExtension g (a + h, 1 - a - h) ≤ κ * |h| := hc₀
  -- The choice of `D₀` (`3 C₀ / D₀ ≤ min {h₀, θ₀/2, 6}`).
  obtain ⟨D₀, hD₀def⟩ : ∃ D₀ : ℝ, D₀ = max 1 (max (C₀ / 2)
      (max (3 * C₀ / h₀) (6 * C₀ / min a (1 - a)))) := ⟨_, rfl⟩
  have hD1 : 1 ≤ D₀ := by rw [hD₀def]; exact le_max_left _ _
  have hDC : C₀ / 2 ≤ D₀ := by rw [hD₀def]; exact le_max_of_le_right (le_max_left _ _)
  have hDh : 3 * C₀ ≤ h₀ * D₀ := by
    have h' : 3 * C₀ / h₀ ≤ D₀ := by
      rw [hD₀def]; exact le_max_of_le_right (le_max_of_le_right (le_max_left _ _))
    rw [div_le_iff₀ hh₀] at h'
    linarith
  have hDθ : 6 * C₀ ≤ min a (1 - a) * D₀ := by
    have h' : 6 * C₀ / min a (1 - a) ≤ D₀ := by
      rw [hD₀def]; exact le_max_of_le_right (le_max_of_le_right (le_max_right _ _))
    rw [div_le_iff₀ hθ] at h'
    linarith
  -- Lemma `lem:intervals` of the differentiability preprint with `D = D₀ + 1`, `θ = θ₀/2`, `η = ε/4`,
  -- `δ = 1/2`.
  obtain ⟨s₁', -, p, hp, hpt, hall⟩ := hint a ha₀ ha₁ (D₀ + 1) (by linarith)
    (min a (1 - a) / 2) (half_pos hθ) (by linarith) (ε / 4) (1 / 2) (div_pos hε (by norm_num))
    (by norm_num)
  refine ⟨D₀, hDC, max s₁' 1, le_max_right _ _, p, hp, hpt, ?_⟩
  intro s S Y Y' I hs hsS hSC hY C
  have hs1 : s₁' ≤ s := (le_max_left _ _).trans hs
  have hs0 : 1 ≤ s := (le_max_right _ _).trans hs
  have hS0 : 0 < S := by linarith
  have hD0 : 0 < D₀ := by linarith
  have hspos : 0 < s := by linarith
  have hεs : 0 ≤ ε * s := (mul_pos hε hspos).le
  have hdlo : D₀ * s ≤ (⌈D₀ * s⌉₊ : ℝ) := Nat.le_ceil _
  have hdhi : (⌈D₀ * s⌉₊ : ℝ) < D₀ * s + 1 := Nat.ceil_lt_add_one (mul_pos hD0 hspos).le
  have hdpos : 0 < ⌈D₀ * s⌉₊ := Nat.ceil_pos.mpr (mul_pos hD0 hspos)
  have hDs : s ≤ D₀ * s := le_mul_of_one_le_left (by linarith) hD1
  have hCD : C₀ * s ≤ 2 * D₀ * s := mul_le_mul_of_nonneg_right (by linarith) (by linarith)
  have hJI : (((I + (⌈D₀ * s⌉₊ : ℤ)) - I : ℤ) : ℝ) = (⌈D₀ * s⌉₊ : ℝ) := by
    push_cast
    ring
  -- The two centres: `S ≤ σ (Y' - Y) ≤ 2 S`, and `|σ x| = |x|`.
  have hYf : S ≤ σ * (Y' - Y) ∧ σ * (Y' - Y) ≤ 2 * S ∧ |Y' - Y| ≤ 2 * S := by
    rcases hσ with rfl | rfl <;> rcases hY with rfl | rfl <;>
      exact ⟨by linarith, by linarith, abs_le.mpr ⟨by linarith, by linarith⟩⟩
  have hσabs : ∀ x : ℝ, |σ * x| = |x| := by
    intro x
    rcases hσ with rfl | rfl <;> simp
  -- Cone condition: `|r(u' - u)| ≤ 5S/2 ≤ (θ₀/2) d`.
  have hθd : min a (1 - a) * (D₀ * s) ≤ min a (1 - a) * (⌈D₀ * s⌉₊ : ℝ) :=
    mul_le_mul_of_nonneg_left hdlo hθ.le
  have hθs : 6 * C₀ * s ≤ min a (1 - a) * D₀ * s :=
    mul_le_mul_of_nonneg_right hDθ (by linarith)
  have hcone : ∀ u v : Lattice,
      (u.1 + u.2 = I ∧ (1 - a) * (u.1 : ℝ) - a * (u.2 : ℝ) ∈ Icc (Y - S / 4) (Y + S / 4)) →
      (v.1 + v.2 = I + (⌈D₀ * s⌉₊ : ℤ) ∧
        (1 - a) * (v.1 : ℝ) - a * (v.2 : ℝ) ∈ Icc (Y' - S / 4) (Y' + S / 4)) →
      |(1 - a) * ((v.1 : ℝ) - (u.1 : ℝ)) - a * ((v.2 : ℝ) - (u.2 : ℝ))| ≤
        (min a (1 - a) - min a (1 - a) / 2) *
          (((I + (⌈D₀ * s⌉₊ : ℤ)) - I : ℤ) : ℝ) := by
    intro u v hu hv
    rw [hJI]
    obtain ⟨-, hu1, hu2⟩ := hu
    obtain ⟨-, hv1, hv2⟩ := hv
    have hYa := abs_le.mp hYf.2.2
    refine abs_le.mpr ⟨by linarith [hYa.1, hYa.2], by linarith [hYa.1, hYa.2]⟩
  obtain ⟨-, hEp⟩ := hall s I (I + (⌈D₀ * s⌉₊ : ℤ)) (Y - S / 4) (Y + S / 4)
    (Y' - S / 4) (Y' + S / 4) hs1 (by omega) (by linarith) (by linarith)
    (by rw [hJI]; linarith) (by rw [hJI]; linarith) (by linarith) (by linarith) hcone
  -- Measurability of the connection event.
  have hCm : MeasurableSet C := by
    refine measurableSet_setOfPred.mpr ?_
    refine Measurable.forall fun u => Measurable.forall fun u' => ?_
    refine Measurable.imp measurable_const (Measurable.imp measurable_const
      (Measurable.imp measurable_const (Measurable.imp measurable_const ?_)))
    refine Measurable.exists fun e => Measurable.exists fun q => ?_
    refine Measurable.and measurable_const (Measurable.and ?_ measurable_const)
    exact measurableSet_setOfPred.mp
      (measurableSet_le (measurable_const.sub (measurable_pathWeight q)) measurable_const)
  refine ⟨hCm, hEp.trans (measureReal_mono ?_)⟩
  intro ω hω
  rw [Set.mem_ofPred_eq] at hω
  simp only [C, Set.mem_ofPred_eq]
  intro u u' hu hur hu' hur'
  have hur₀ : |(1 - a) * (u.1 : ℝ) - a * (u.2 : ℝ) - Y| ≤ S / 4 := hur
  have hur₁ : |(1 - a) * (u'.1 : ℝ) - a * (u'.2 : ℝ) - Y'| ≤ S / 4 := hur'
  have hu0 := abs_le.mp hur₀
  have hu1 := abs_le.mp hur₁
  obtain ⟨q, hend, hwt, hloc⟩ := hω u u'
    ⟨hu, Set.mem_Icc.mpr ⟨by linarith [hu0.1], by linarith [hu0.2]⟩⟩
    ⟨hu', Set.mem_Icc.mpr ⟨by linarith [hu1.1], by linarith [hu1.2]⟩⟩
  refine ⟨_, q, hend, ?_, ?_⟩
  · -- Step 4 defect bound ((3.12) of the differentiability preprint).
    have hfin : u' = u + (((u'.1 - u.1).toNat : ℤ), ((u'.2 - u.2).toNat : ℤ)) :=
      hend.symm.trans q.finish
    have hfst := congrArg Prod.fst hfin
    have hsnd := congrArg Prod.snd hfin
    simp only [Prod.fst_add, Prod.snd_add] at hfst hsnd
    have hmd : (u'.1 - u.1).toNat + (u'.2 - u.2).toNat = ⌈D₀ * s⌉₊ := by omega
    have hmdR : (((u'.1 - u.1).toNat : ℕ) : ℝ) + (((u'.2 - u.2).toNat : ℕ) : ℝ) =
        (⌈D₀ * s⌉₊ : ℝ) := by exact_mod_cast hmd
    have hR1 : (u'.1 : ℝ) = (u.1 : ℝ) + (((u'.1 - u.1).toNat : ℕ) : ℝ) := by
      exact_mod_cast hfst
    have hR2 : (u'.2 : ℝ) = (u.2 : ℝ) + (((u'.2 - u.2).toNat : ℕ) : ℝ) := by
      exact_mod_cast hsnd
    have hρ : (1 - a) * (((u'.1 - u.1).toNat : ℕ) : ℝ) - a * (((u'.2 - u.2).toNat : ℕ) : ℝ) =
        ((1 - a) * (u'.1 : ℝ) - a * (u'.2 : ℝ)) - ((1 - a) * (u.1 : ℝ) - a * (u.2 : ℝ)) := by
      rw [hR1, hR2]
      ring
    have hA := abs_le.mp ((hσabs ((1 - a) * (u'.1 : ℝ) - a * (u'.2 : ℝ) - Y')).le.trans hur₁)
    have hur₂ : |Y - ((1 - a) * (u.1 : ℝ) - a * (u.2 : ℝ))| ≤ S / 4 := by
      rw [abs_sub_comm]; exact hur₀
    have hB := abs_le.mp ((hσabs (Y - ((1 - a) * (u.1 : ℝ) - a * (u.2 : ℝ)))).le.trans hur₂)
    have hσρ : S / 2 ≤ σ * ((1 - a) * (((u'.1 - u.1).toNat : ℕ) : ℝ) - a * (((u'.2 - u.2).toNat : ℕ) : ℝ)) ∧
        σ * ((1 - a) * (((u'.1 - u.1).toNat : ℕ) : ℝ) - a * (((u'.2 - u.2).toNat : ℕ) : ℝ)) ≤ 5 * S / 2 := by
      rw [hρ]
      constructor <;> linarith [hYf.1, hYf.2.1, hA.1, hA.2, hB.1, hB.2]
    have hh₀d : h₀ * (D₀ * s) ≤ h₀ * (⌈D₀ * s⌉₊ : ℝ) := mul_le_mul_of_nonneg_left hdlo hh₀.le
    have hh₀s : 3 * C₀ * s ≤ h₀ * D₀ * s := mul_le_mul_of_nonneg_right hDh (by linarith)
    have hgap := shape_gap_le g hhom' a σ (H 0) slope κ h₀ hcontact
      (u'.1 - u.1).toNat (u'.2 - u.2).toNat (by omega)
      (by linarith [hσρ.1]) (by rw [hmdR]; linarith [hσρ.2])
    have habs : |(1 - a) * (((u'.1 - u.1).toNat : ℕ) : ℝ) - a * (((u'.2 - u.2).toNat : ℕ) : ℝ)| =
        σ * ((1 - a) * (((u'.1 - u.1).toNat : ℕ) : ℝ) - a * (((u'.2 - u.2).toNat : ℕ) : ℝ)) := by
      rw [← hσabs, abs_of_pos (by linarith [hσρ.1])]
    rw [habs] at hgap
    have hk1 : κ * (σ * ((1 - a) * (((u'.1 - u.1).toNat : ℕ) : ℝ) - a * (((u'.2 - u.2).toNat : ℕ) : ℝ))) ≤ κ * (5 * S / 2) :=
      mul_le_mul_of_nonneg_left hσρ.2 hκ.le
    have hk2 : κ * S ≤ κ * (C₀ * s) := mul_le_mul_of_nonneg_left hSC hκ.le
    have hk3 : κ * (C₀ * s) = ε / 12 * s := by rw [← mul_assoc, hκC]
    have hfz : f (u' - u) = H 0 * ((((u'.1 - u.1).toNat : ℕ) : ℝ) + (((u'.2 - u.2).toNat : ℕ) : ℝ)) +
        slope * ((1 - a) * (((u'.1 - u.1).toNat : ℕ) : ℝ) - a * (((u'.2 - u.2).toNat : ℕ) : ℝ)) := by
      show H 0 * ((((u' - u).1 : ℤ) : ℝ) + (((u' - u).2 : ℤ) : ℝ)) +
          slope * ((1 - a) * (((u' - u).1 : ℤ) : ℝ) - a * (((u' - u).2 : ℤ) : ℝ)) = _
      simp only [Prod.fst_sub, Prod.snd_sub, Int.cast_sub]
      rw [hR1, hR2]
      ring
    rw [hfz]
    linarith [hgap, hwt, hk1, hk2, hk3, hεs]
  · -- Location: within `9S/4 + s/2 ≤ 4S` of the centre `Y`.
    intro i
    obtain ⟨t, ht0, ht1, hdist⟩ := hloc i
    show |(1 - a) * ((q.vertex i).1 : ℝ) - a * ((q.vertex i).2 : ℝ) - Y| ≤ 4 * S
    have hX1 : |(1 - a) * (((q.vertex i).1 : ℝ) - ((1 - t) * (u.1 : ℝ) + t * (u'.1 : ℝ)))| ≤
        |((q.vertex i).1 : ℝ) - ((1 - t) * (u.1 : ℝ) + t * (u'.1 : ℝ))| := by
      rw [abs_mul, abs_of_pos (by linarith : (0 : ℝ) < 1 - a)]
      exact mul_le_of_le_one_left (abs_nonneg _) (by linarith)
    have hX2 : |a * (((q.vertex i).2 : ℝ) - ((1 - t) * (u.2 : ℝ) + t * (u'.2 : ℝ)))| ≤
        |((q.vertex i).2 : ℝ) - ((1 - t) * (u.2 : ℝ) + t * (u'.2 : ℝ))| := by
      rw [abs_mul, abs_of_pos ha₀]
      exact mul_le_of_le_one_left (abs_nonneg _) (by linarith)
    have hX1'' := abs_le.mp hX1
    have hX2'' := abs_le.mp hX2
    have hYa := abs_le.mp hYf.2.2
    have hP1 : (1 - t) * ((1 - a) * (u.1 : ℝ) - a * (u.2 : ℝ) - Y) ≤ (1 - t) * (S / 4) :=
      mul_le_mul_of_nonneg_left hu0.2 (by linarith)
    have hP1' : (1 - t) * (-(S / 4)) ≤ (1 - t) * ((1 - a) * (u.1 : ℝ) - a * (u.2 : ℝ) - Y) :=
      mul_le_mul_of_nonneg_left hu0.1 (by linarith)
    have hQ : -(9 * S / 4) ≤ (1 - a) * (u'.1 : ℝ) - a * (u'.2 : ℝ) - Y ∧
        (1 - a) * (u'.1 : ℝ) - a * (u'.2 : ℝ) - Y ≤ 9 * S / 4 :=
      ⟨by linarith [hu1.1, hYa.1], by linarith [hu1.2, hYa.2]⟩
    have hP2 : t * ((1 - a) * (u'.1 : ℝ) - a * (u'.2 : ℝ) - Y) ≤ t * (9 * S / 4) :=
      mul_le_mul_of_nonneg_left hQ.2 ht0
    have hP2' : t * (-(9 * S / 4)) ≤ t * ((1 - a) * (u'.1 : ℝ) - a * (u'.2 : ℝ) - Y) :=
      mul_le_mul_of_nonneg_left hQ.1 ht0
    have hTS : t * S ≤ S := mul_le_of_le_one_left hS0.le ht1
    have hTS0 : 0 ≤ t * S := mul_nonneg ht0 hS0.le
    exact abs_le.mpr
      ⟨by linarith [hX1''.1, hX1''.2, hX2''.1, hX2''.2],
        by linarith [hX1''.1, hX1''.2, hX2''.1, hX2''.2]⟩

end LPPDifferentiability
