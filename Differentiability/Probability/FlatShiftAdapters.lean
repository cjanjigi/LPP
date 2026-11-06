/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import ProbabilityBasics.Probability.SupportTopCDF
public import Differentiability.Probability.TopIndicatorLaw
public import Differentiability.Probability.TopIndicatorShape
public import Differentiability.Probability.FlatShapeNormalization
public import Differentiability.Probability.UniformShapeTranslation
public import LPP_Foundations.Probability.EnvironmentMap
public import Differentiability.Model.OrientedPercolation
public import LPP_Foundations.Frozen.Analysis.QuadrantExtension
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FunProp

/-!
# Changes of weights for the flat segment

These adapters move the top indicator field of a weight law `mu` to the
shifted law `mu.map (x ↦ x + (1 - M))`, where `M` is the top of the support.
The shifted weights are at most `1`, and the top sites become the sites of
weight exactly `1`. The shape of the field and the shape of the shifted
weights differ only by the linear term `(1 - M) * (z.1 + z.2)`, which does
not change differentiability at interior points.
-/

public section

open MeasureTheory Filter Set
open scoped Topology NNReal ENNReal

namespace LPPDifferentiability

/-- Almost everywhere statements transfer along a measurable embedding. -/
private theorem ae_map_of_measurableEmbedding {α β : Type*} [MeasurableSpace α]
    [MeasurableSpace β] (μ : Measure α) {f : α → β} (hf : MeasurableEmbedding f)
    (p : β → Prop) :
    (∀ᵐ y ∂μ.map f, p y) ↔ ∀ᵐ x ∂μ, p (f x) := by
  rw [ae_iff, ae_iff, hf.map_apply]
  rfl

/-- Adding a constant to every site weight, as a measurable equivalence of environments. -/
private def shiftEnvironment (c : ℝ) : Environment ≃ᵐ Environment where
  toFun ω := fun z => ω z + c
  invFun ω := fun z => ω z - c
  left_inv ω := by funext z; simp
  right_inv ω := by funext z; simp
  measurable_toFun := measurable_coordinatewise_environment_map (fun x => x + c) (by fun_prop)
  measurable_invFun := measurable_coordinatewise_environment_map (fun x => x - c) (by fun_prop)

/-- The shifted canonical environment law transfers almost everywhere statements. -/
private theorem ae_environment_shift (μ : Measure ℝ) [IsProbabilityMeasure μ] (c : ℝ)
    (p : Environment → Prop) :
    (∀ᵐ ω' ∂(environmentLaw μ).map (fun ω : Environment => fun z : Lattice => ω z + c), p ω') ↔
      ∀ᵐ ω ∂environmentLaw μ, p (fun z : Lattice => ω z + c) :=
  ae_map_of_measurableEmbedding (environmentLaw μ) (shiftEnvironment c).measurableEmbedding p

/-- A positive atom at the literal endpoint gives a real endpoint carrying that atom. -/
theorem source_top_real_of_atom_pos (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (h : 0 < μ {t : ℝ | (t : EReal) = sSup ((fun s : ℝ => (s : EReal)) '' μ.support)}) :
    ∃ M : ℝ, (M : EReal) = sSup ((fun s : ℝ => (s : EReal)) '' μ.support) ∧
      (∀ᵐ x ∂μ, x ≤ M) ∧
      μ {M} = μ {t : ℝ | (t : EReal) = sSup ((fun s : ℝ => (s : EReal)) '' μ.support)} := by
  obtain ⟨t0, ht0⟩ := nonempty_of_measure_ne_zero h.ne'
  have ht0' : (t0 : EReal) = sSup ((fun s : ℝ => (s : EReal)) '' μ.support) := ht0
  have hset : {t : ℝ | (t : EReal) = sSup ((fun s : ℝ => (s : EReal)) '' μ.support)} = {t0} := by
    ext t
    constructor
    · intro ht
      have ht' : (t : EReal) = sSup ((fun s : ℝ => (s : EReal)) '' μ.support) := ht
      exact Set.mem_singleton_iff.mpr (EReal.coe_eq_coe_iff.mp (ht'.trans ht0'.symm))
    · intro ht
      rw [Set.mem_singleton_iff.mp ht]
      exact ht0'
  refine ⟨t0, ht0', ?_, ?_⟩
  · filter_upwards [source_ae_le_support_sSup μ] with x hx
    rw [← ht0'] at hx
    exact EReal.coe_le_coe_iff.mp hx
  · rw [hset]

/-- A positive flat-segment limit forces a positive atom at the literal endpoint. -/
theorem source_top_atom_pos_of_top_limit_pos (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (a : ℝ) (Gtop : ℝ)
    (htop : Tendsto (fun m : ℕ => (∫ ω : Environment, lastPassage (fun z =>
      if (ω z : EReal) = sSup ((fun t : ℝ => (t : EReal)) '' μ.support) then (1 : ℝ) else 0)
        0 (⌊(m : ℝ) * a⌋₊, ⌊(m : ℝ) * (1 - a)⌋₊) ∂environmentLaw μ) / (m : ℝ))
      atTop (𝓝 Gtop))
    (hG : 0 < Gtop) :
    0 < μ {t : ℝ | (t : EReal) = sSup ((fun s : ℝ => (s : EReal)) '' μ.support)} := by
  by_contra hle
  have hzero : μ {t : ℝ | (t : EReal) = sSup ((fun s : ℝ => (s : EReal)) '' μ.support)} = 0 :=
    le_antisymm (not_lt.mp hle) zero_le
  have hz : ∀ z : Lattice, ∀ᵐ ω ∂environmentLaw μ,
      ¬ ((ω z : EReal) = sSup ((fun s : ℝ => (s : EReal)) '' μ.support)) := by
    intro z
    rw [ae_iff]
    have hm := source_top_indicator_event_measurable μ
    have h1 : environmentLaw μ ((fun ω : Environment => ω z) ⁻¹'
        {t : ℝ | (t : EReal) = sSup ((fun s : ℝ => (s : EReal)) '' μ.support)}) = 0 := by
      rw [← Measure.map_apply (measurable_environment_eval z) hm, environmentLaw_map_eval μ z,
        hzero]
    refine measure_mono_null (fun ω hω => ?_) h1
    exact not_not.mp hω
  have hall : ∀ᵐ ω ∂environmentLaw μ, ∀ z : Lattice,
      ¬ ((ω z : EReal) = sSup ((fun s : ℝ => (s : EReal)) '' μ.support)) :=
    ae_all_iff.mpr hz
  have hint : ∀ m : ℕ, (∫ ω : Environment, lastPassage (fun z =>
      if (ω z : EReal) = sSup ((fun t : ℝ => (t : EReal)) '' μ.support) then (1 : ℝ) else 0)
        0 (⌊(m : ℝ) * a⌋₊, ⌊(m : ℝ) * (1 - a)⌋₊) ∂environmentLaw μ) = 0 := by
    intro m
    have hae : ∀ᵐ ω ∂environmentLaw μ, lastPassage (fun z =>
        if (ω z : EReal) = sSup ((fun t : ℝ => (t : EReal)) '' μ.support) then (1 : ℝ) else 0)
          0 (⌊(m : ℝ) * a⌋₊, ⌊(m : ℝ) * (1 - a)⌋₊) = 0 := by
      filter_upwards [hall] with ω hω
      have hfun : (fun z : Lattice =>
          if (ω z : EReal) = sSup ((fun t : ℝ => (t : EReal)) '' μ.support) then (1 : ℝ) else 0) =
          fun _ => (0 : ℝ) := by
        funext z
        exact ite_eq_right (hω z)
      rw [hfun, lastPassage_const, mul_zero]
    rw [integral_congr_ae hae]
    simp
  have hconst := htop
  simp only [hint, zero_div] at hconst
  exact hG.ne' (tendsto_nhds_unique hconst tendsto_const_nhds)

/-- Shifting the weights by `1 - M` gives the shifted law, its top field, and an upper bound `1`. -/
theorem shifted_law_environment (μ : Measure ℝ) [IsProbabilityMeasure μ] (M : ℝ)
    (hM : (M : EReal) = sSup ((fun s : ℝ => (s : EReal)) '' μ.support))
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (hν : ν = μ.map (fun x => x + (1 - M))) :
    (environmentLaw μ).map (fun ω : Environment => fun z => ω z + (1 - M)) =
        environmentLaw ν ∧
      (∀ ω : Environment, topField (fun z => ω z + (1 - M)) = fun z =>
        if (ω z : EReal) = sSup ((fun s : ℝ => (s : EReal)) '' μ.support) then 1 else 0) ∧
      (∀ᵐ t ∂ν, t ≤ 1) ∧ ν {1} = μ {M} := by
  subst hν
  have hf : Measurable (fun x : ℝ => x + (1 - M)) := by fun_prop
  have hiff : ∀ ω : ℝ, ω + (1 - M) = 1 ↔ (ω : EReal) = (M : EReal) := by
    intro ω
    rw [EReal.coe_eq_coe_iff]
    constructor <;> intro h <;> linarith
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact environmentLaw_map_coordinatewise μ (fun x => x + (1 - M)) hf
  · intro ω
    funext z
    rw [← hM]
    simp only [topField]
    by_cases h : ω z + (1 - M) = 1
    · rw [ite_eq_left h, ite_eq_left ((hiff (ω z)).mp h)]
    · rw [ite_eq_right h, ite_eq_right (fun h' => h ((hiff (ω z)).mpr h'))]
  · apply (ae_map_iff (f := fun x : ℝ => x + (1 - M)) (μ := μ) (p := fun y => y ≤ 1)
      hf.aemeasurable measurableSet_Iic).2
    filter_upwards [source_ae_le_support_sSup μ] with x hx
    rw [← hM] at hx
    have hxM : x ≤ M := EReal.coe_le_coe_iff.mp hx
    show x + (1 - M) ≤ 1
    linarith
  · rw [Measure.map_apply hf (measurableSet_singleton 1)]
    congr 1
    ext x
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    constructor <;> intro h <;> linarith

/-- The top indicator field of the shifted law has a shape, and its expectations converge to it. -/
theorem exists_top_shape_of_shifted_law (μ : Measure ℝ) [IsProbabilityMeasure μ] (M : ℝ)
    (hM : (M : EReal) = sSup ((fun s : ℝ => (s : EReal)) '' μ.support))
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (hν : ν = μ.map (fun x => x + (1 - M))) :
    ∃ gtop : Quadrant → ℝ, Continuous gtop ∧
      (∀ (c : ℝ≥0) (x : Quadrant), gtop (c * x.1, c * x.2) = (c : ℝ) * gtop x) ∧
      (∀ (x y : Quadrant) (r t : ℝ≥0), r + t = 1 →
        (r : ℝ) * gtop x + (t : ℝ) * gtop y ≤ gtop (r * x.1 + t * y.1, r * x.2 + t * y.2)) ∧
      (∀ᵐ ω ∂environmentLaw ν, ∀ ε : ℝ, 0 < ε →
        ∃ N : ℕ, 1 ≤ N ∧ ∀ d : ℕ × ℕ, N ≤ d.1 + d.2 →
          |lastPassage (topField ω) 0 d - gtop ((d.1 : ℝ≥0), (d.2 : ℝ≥0))| ≤
            ε * ((d.1 + d.2 : ℕ) : ℝ)) ∧
      (∀ x : Quadrant, Tendsto (fun n : ℕ =>
        (∫ ω : Environment, lastPassage (fun z =>
          if (ω z : EReal) = sSup ((fun s : ℝ => (s : EReal)) '' μ.support) then (1 : ℝ) else 0)
          0 (⌊(n : ℝ) * (x.1 : ℝ)⌋₊, ⌊(n : ℝ) * (x.2 : ℝ)⌋₊)
          ∂environmentLaw μ) / (n : ℝ))
        atTop (𝓝 (gtop x))) := by
  obtain ⟨g, hgc, hgh, hgcv, hgae, hlim, -⟩ := exists_source_top_indicator_shape μ
  obtain ⟨hlaw, htop, -, -⟩ := shifted_law_environment μ M hM ν hν
  refine ⟨g, hgc, hgh, hgcv, ?_, hlim⟩
  rw [← hlaw]
  refine (ae_environment_shift μ (1 - M) _).2 ?_
  filter_upwards [hgae] with ω hω
  simp only [htop ω]
  exact hω

/-- The shifted shape is the old shape plus the linear term `(1 - M) * (z.1 + z.2)`. -/
theorem shifted_shape_of_shape (μ : Measure ℝ) [IsProbabilityMeasure μ] (M : ℝ)
    (hupper : ∀ᵐ x ∂μ, x ≤ M)
    (hneg : ∃ pneg : ℝ, 1 < pneg ∧
      (∫⁻ t, ENNReal.ofReal ((max (-t) 0) ^ pneg) ∂μ) < ∞)
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (hν : ν = μ.map (fun x => x + (1 - M)))
    (g : Quadrant → ℝ) (hgcont : Continuous g)
    (hghom : ∀ (c : ℝ≥0) (x : Quadrant), g (c * x.1, c * x.2) = (c : ℝ) * g x)
    (hgconc : ∀ (x y : Quadrant) (r t : ℝ≥0), r + t = 1 →
      (r : ℝ) * g x + (t : ℝ) * g y ≤ g (r * x.1 + t * y.1, r * x.2 + t * y.2))
    (hgshape : ∀ᵐ ω ∂environmentLaw μ, ∀ ε : ℝ, 0 < ε →
      ∃ N : ℕ, 1 ≤ N ∧ ∀ d : ℕ × ℕ, N ≤ d.1 + d.2 →
        |lastPassage ω 0 d - g ((d.1 : ℝ≥0), (d.2 : ℝ≥0))| ≤
          ε * ((d.1 + d.2 : ℕ) : ℝ)) :
    let gbar : Quadrant → ℝ := fun z => g z + (1 - M) * ((z.1 : ℝ) + z.2)
    (∃ pneg : ℝ, 1 < pneg ∧ (∫⁻ t, ENNReal.ofReal ((max (-t) 0) ^ pneg) ∂ν) < ∞) ∧
    Continuous gbar ∧
    (∀ (c : ℝ≥0) (x : Quadrant), gbar (c * x.1, c * x.2) = (c : ℝ) * gbar x) ∧
    (∀ (x y : Quadrant) (r t : ℝ≥0), r + t = 1 →
      (r : ℝ) * gbar x + (t : ℝ) * gbar y ≤ gbar (r * x.1 + t * y.1, r * x.2 + t * y.2)) ∧
    (∀ᵐ ω ∂environmentLaw ν, ∀ ε : ℝ, 0 < ε →
      ∃ N : ℕ, 1 ≤ N ∧ ∀ d : ℕ × ℕ, N ≤ d.1 + d.2 →
        |lastPassage ω 0 d - gbar ((d.1 : ℝ≥0), (d.2 : ℝ≥0))| ≤
          ε * ((d.1 + d.2 : ℕ) : ℝ)) := by
  subst hν
  intro gbar
  obtain ⟨p, hp, hmom⟩ := hneg
  have hlevel : Continuous fun z : Quadrant => (z.1 : ℝ) + (z.2 : ℝ) := by fun_prop
  refine ⟨⟨p, hp, (translated_upper_bound_and_negative_moment μ M p hupper hp hmom).2⟩,
    ?_, ?_, ?_, ?_⟩
  · exact hgcont.add (continuous_const.mul hlevel)
  · intro c z
    simp only [gbar]
    rw [hghom c z]
    push_cast
    ring
  · intro x y r t hrt
    simp only [gbar]
    push_cast
    linarith [hgconc x y r t hrt]
  · filter_upwards [(uniform_origin_shape_law_iff_map_add μ g (1 - M)).mp hgshape] with ω hω
    intro ε hε
    obtain ⟨N, hN1, hN⟩ := hω ε hε
    refine ⟨N, hN1, fun d hd => ?_⟩
    have hd' := hN d hd
    simpa only [gbar, NNReal.coe_natCast] using hd'

/-- Adding a multiple of the level to a function does not change differentiability
at a point of the open quadrant. -/
theorem differentiableAt_quadrantExtension_add_level_iff (g : Quadrant → ℝ) (c : ℝ)
    (x : ℝ × ℝ) (hx₁ : 0 < x.1) (hx₂ : 0 < x.2) :
    DifferentiableAt ℝ (quadrantExtension (fun z : Quadrant => g z + c * ((z.1 : ℝ) + z.2))) x ↔
      DifferentiableAt ℝ (quadrantExtension g) x := by
  have hpos1 : ∀ᶠ y in 𝓝 x, 0 < y.1 := (continuous_fst.tendsto x).eventually (lt_mem_nhds hx₁)
  have hpos2 : ∀ᶠ y in 𝓝 x, 0 < y.2 := (continuous_snd.tendsto x).eventually (lt_mem_nhds hx₂)
  have hEq : quadrantExtension (fun z : Quadrant => g z + c * ((z.1 : ℝ) + z.2)) =ᶠ[𝓝 x]
      fun y => quadrantExtension g y + c * (y.1 + y.2) := by
    filter_upwards [hpos1, hpos2] with y hy1 hy2
    simp only [quadrantExtension, toQuadrant, Real.coe_toNNReal _ hy1.le,
      Real.coe_toNNReal _ hy2.le]
  have hL : DifferentiableAt ℝ (fun y : ℝ × ℝ => c * (y.1 + y.2)) x := by fun_prop
  rw [hEq.differentiableAt_iff]
  constructor
  · intro h
    have h' : DifferentiableAt ℝ (fun y : ℝ × ℝ =>
        (quadrantExtension g y + c * (y.1 + y.2)) - c * (y.1 + y.2)) x := h.sub hL
    simpa using h'
  · intro h
    exact h.add hL

end LPPDifferentiability
