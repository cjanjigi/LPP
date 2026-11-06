/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Martin2004.Probability.QuantileRealLaw
public import LPP_Foundations.Frozen.Model.EnvironmentLaw
public import Mathlib.Probability.Independence.InfinitePi

/-!
# Quantile coupling of whole fields

Martin (2004), in the proof of Lemma 4.2, couples two fields in this way. One uniform variable is
attached to each site of the lattice, and the weights of both models are the quantiles of that
same uniform variable.
The quantile used is the project quantile `inf {r : y <= F(r)}`, which is left continuous; Martin's
`sup {x : F(x) <= u}` agrees with it for almost every `u`.

With the left-continuous quantile, `{quantile ≤ x}` is exactly `{u ≤ F(x)}` on
the open unit interval. The mismatch events `{X1 > x, X2 ≤ x}` and
`{X1 ≤ x, X2 > x}` then have probabilities `[F2(x) - F1(x)]_+` and
`[F1(x) - F2(x)]_+`. Martin's proof of Lemma 4.2 writes the paired events
with `≥` and `<`.

The quantile is only almost everywhere measurable on the real line, because it is
unrestricted outside `(0, 1)`. The version `(Ioo 0 1).indicator quantile` is measurable and agrees
with it on the support of the uniform law.
-/

public section

open MeasureTheory Set

namespace LPPDifferentiability

/-- Almost surely every coordinate of the uniform field lies strictly between 0 and 1
(the uniform variables `U(z)` of the proof of Martin (2004), Lemma 4.2). -/
theorem ae_uniform_field_mem_Ioo :
    ∀ᵐ u : Environment ∂(Measure.infinitePi
        (fun _ : Lattice => volume.restrict (Ioo (0 : ℝ) 1))),
      ∀ z : Lattice, u z ∈ Ioo (0 : ℝ) 1 := by
  have : IsProbabilityMeasure (volume.restrict (Ioo (0 : ℝ) 1)) := ⟨by simp⟩
  refine ae_all_iff.2 fun z => ?_
  exact (measurePreserving_eval_infinitePi
    (fun _ : Lattice => volume.restrict (Ioo (0 : ℝ) 1)) z).quasiMeasurePreserving.ae
    (ae_restrict_mem measurableSet_Ioo)

/-- The quantile cut off outside the open unit interval is measurable on the real line. It is
the measurable stand-in for `F^{-1}` in Martin (2004), Lemma 4.2. -/
theorem measurable_indicator_source_quantile (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    Measurable ((Ioo (0 : ℝ) 1).indicator
      (fun y : ℝ => sInf {r : ℝ | y ≤ μ.real (Iic r)})) := by
  refine measurable_of_Iic fun t => ?_
  have hset : (Ioo (0 : ℝ) 1).indicator
        (fun y : ℝ => sInf {r : ℝ | y ≤ μ.real (Iic r)}) ⁻¹' Iic t =
      (Ioo (0 : ℝ) 1 ∩ Iic (μ.real (Iic t))) ∪
        ((Ioo (0 : ℝ) 1)ᶜ ∩ {_y : ℝ | (0 : ℝ) ≤ t}) := by
    ext y
    by_cases hy : y ∈ Ioo (0 : ℝ) 1
    · have h1 : (Ioo (0 : ℝ) 1).indicator
          (fun y : ℝ => sInf {r : ℝ | y ≤ μ.real (Iic r)}) y =
          sInf {r : ℝ | y ≤ μ.real (Iic r)} := indicator_of_mem hy _
      simp only [mem_preimage, mem_Iic, h1, mem_union, mem_inter_iff]
      constructor
      · intro h
        exact Or.inl ⟨hy, (source_quantile_le_iff μ hy).1 h⟩
      · rintro (⟨_, h⟩ | ⟨h, _⟩)
        · exact (source_quantile_le_iff μ hy).2 h
        · exact absurd hy h
    · have h1 : (Ioo (0 : ℝ) 1).indicator
          (fun y : ℝ => sInf {r : ℝ | y ≤ μ.real (Iic r)}) y = 0 :=
        indicator_of_notMem hy _
      simp only [mem_preimage, mem_Iic, h1, mem_union, mem_inter_iff]
      constructor
      · intro h
        exact Or.inr ⟨hy, h⟩
      · rintro (⟨h, _⟩ | ⟨_, h⟩)
        · exact absurd h hy
        · exact h
  rw [hset]
  exact (measurableSet_Ioo.inter measurableSet_Iic).union
    (measurableSet_Ioo.compl.inter (MeasurableSet.const _))

/-- Coupling of whole fields, measurable form (the coupling in the proof of Lemma 4.2): the
coordinatewise quantile of a uniform field on the lattice is a field of independent weights with
law `μ`. -/
theorem map_indicator_source_quantile_field (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    (Measure.infinitePi (fun _ : Lattice => volume.restrict (Ioo (0 : ℝ) 1))).map
      (fun u : Environment => fun z : Lattice =>
        (Ioo (0 : ℝ) 1).indicator
          (fun y : ℝ => sInf {r : ℝ | y ≤ μ.real (Iic r)}) (u z)) =
        environmentLaw μ := by
  have : IsProbabilityMeasure (volume.restrict (Ioo (0 : ℝ) 1)) := ⟨by simp⟩
  have hae : (Ioo (0 : ℝ) 1).indicator
        (fun y : ℝ => sInf {r : ℝ | y ≤ μ.real (Iic r)}) =ᵐ[volume.restrict (Ioo (0 : ℝ) 1)]
      (fun y : ℝ => sInf {r : ℝ | y ≤ μ.real (Iic r)}) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with y hy
    exact indicator_of_mem hy _
  have hmap : (volume.restrict (Ioo (0 : ℝ) 1)).map ((Ioo (0 : ℝ) 1).indicator
      (fun y : ℝ => sInf {r : ℝ | y ≤ μ.real (Iic r)})) = μ := by
    rw [Measure.map_congr hae]
    exact map_source_quantile_real μ
  have hpi := Measure.infinitePi_map_pi
    (μ := fun _ : Lattice => volume.restrict (Ioo (0 : ℝ) 1))
    (f := fun _ : Lattice => (Ioo (0 : ℝ) 1).indicator
      (fun y : ℝ => sInf {r : ℝ | y ≤ μ.real (Iic r)}))
    (fun _ => measurable_indicator_source_quantile μ)
  refine hpi.trans ?_
  unfold environmentLaw
  simp only [hmap]

/-- Coupling of whole fields (the coupling in the proof of Lemma 4.2): applying the quantile to
every coordinate of a uniform field gives independent weights with law `μ`. -/
theorem map_source_quantile_field (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    (Measure.infinitePi (fun _ : Lattice => volume.restrict (Ioo (0 : ℝ) 1))).map
      (fun u : Environment => fun z : Lattice => sInf {r : ℝ | u z ≤ μ.real (Iic r)}) =
        environmentLaw μ := by
  rw [← map_indicator_source_quantile_field μ]
  refine Measure.map_congr ?_
  filter_upwards [ae_uniform_field_mem_Ioo] with u hu
  funext z
  exact (indicator_of_mem (hu z)
    (fun y : ℝ => sInf {r : ℝ | y ≤ μ.real (Iic r)})).symm

/-- For the left-continuous quantiles, comparison with `x` is determined by the
corresponding distribution functions, as in the coupling in Martin (2004), Lemma 4.2. -/
theorem source_quantile_gt_and_le_iff (μ₁ μ₂ : Measure ℝ)
    [IsProbabilityMeasure μ₁] [IsProbabilityMeasure μ₂] {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1)
    (x : ℝ) :
    (x < sInf {r : ℝ | u ≤ μ₁.real (Iic r)} ∧ sInf {r : ℝ | u ≤ μ₂.real (Iic r)} ≤ x) ↔
      (μ₁.real (Iic x) < u ∧ u ≤ μ₂.real (Iic x)) := by
  have h1 := source_quantile_le_iff μ₁ hu (t := x)
  have h2 := source_quantile_le_iff μ₂ hu (t := x)
  constructor
  · rintro ⟨a, b⟩
    exact ⟨not_le.1 fun h => (not_le.2 a) (h1.2 h), h2.1 b⟩
  · rintro ⟨a, b⟩
    exact ⟨not_le.1 fun h => (not_le.2 a) (h1.1 h), h2.2 b⟩

/-- For functions agreeing with the left-continuous quantiles on `(0,1)`, the
mismatch event has probability `P(X1 > x, X2 ≤ x) = [F2(x) - F1(x)]_+`.
This uses the coupling in Martin (2004), Lemma 4.2. -/
theorem volume_real_gt_and_le_of_eq_source_quantile (μ₁ μ₂ : Measure ℝ)
    [IsProbabilityMeasure μ₁] [IsProbabilityMeasure μ₂] (r₁ r₂ : ℝ → ℝ)
    (hr₁ : ∀ t ∈ Ioo (0 : ℝ) 1, r₁ t = sInf {r : ℝ | t ≤ μ₁.real (Iic r)})
    (hr₂ : ∀ t ∈ Ioo (0 : ℝ) 1, r₂ t = sInf {r : ℝ | t ≤ μ₂.real (Iic r)}) (x : ℝ) :
    (volume.restrict (Ioo (0 : ℝ) 1)).real {t : ℝ | x < r₁ t ∧ r₂ t ≤ x} =
      max (μ₂.real (Iic x) - μ₁.real (Iic x)) 0 := by
  have hF₁ : 0 ≤ μ₁.real (Iic x) := measureReal_nonneg
  have hF₂ : μ₂.real (Iic x) ≤ 1 := measureReal_le_one
  have hset : {t : ℝ | x < r₁ t ∧ r₂ t ≤ x} ∩ Ioo (0 : ℝ) 1 =
      Ioc (μ₁.real (Iic x)) (μ₂.real (Iic x)) ∩ Ioo (0 : ℝ) 1 := by
    ext t
    constructor
    · rintro ⟨⟨h1, h2⟩, ht⟩
      rw [hr₁ t ht] at h1
      rw [hr₂ t ht] at h2
      exact ⟨(source_quantile_gt_and_le_iff μ₁ μ₂ ht x).1 ⟨h1, h2⟩, ht⟩
    · rintro ⟨h, ht⟩
      obtain ⟨h1, h2⟩ := (source_quantile_gt_and_le_iff μ₁ μ₂ ht x).2 h
      exact ⟨⟨by rw [hr₁ t ht]; exact h1, by rw [hr₂ t ht]; exact h2⟩, ht⟩
  have hsub : Ioc (μ₁.real (Iic x)) (μ₂.real (Iic x)) ∩ Ioc (0 : ℝ) 1 =
      Ioc (μ₁.real (Iic x)) (μ₂.real (Iic x)) :=
    inter_eq_left.2 fun t ht => ⟨lt_of_le_of_lt hF₁ ht.1, ht.2.trans hF₂⟩
  have hvol : volume (Ioc (μ₁.real (Iic x)) (μ₂.real (Iic x)) ∩ Ioo (0 : ℝ) 1) =
      volume (Ioc (μ₁.real (Iic x)) (μ₂.real (Iic x))) := by
    have h : volume (Ioc (μ₁.real (Iic x)) (μ₂.real (Iic x)) ∩ Ioo (0 : ℝ) 1) =
        volume (Ioc (μ₁.real (Iic x)) (μ₂.real (Iic x)) ∩ Ioc (0 : ℝ) 1) := by
      apply measure_congr
      filter_upwards [Ioo_ae_eq_Ioc (μ := (volume : Measure ℝ)) (a := (0 : ℝ)) (b := 1)]
        with y hy
      simp only [mem_inter_iff]
      exact congrArg (fun p : Prop => y ∈ Ioc (μ₁.real (Iic x)) (μ₂.real (Iic x)) ∧ p) hy
    rw [h, hsub]
  rw [measureReal_def, Measure.restrict_apply' measurableSet_Ioo, hset, hvol,
    ← measureReal_def]
  exact Real.volume_real_Ioc

/-- For the left-continuous quantiles, the mismatch event has probability
`P(X1 > x, X2 ≤ x) = [F2(x) - F1(x)]_+`. -/
theorem volume_real_source_quantile_gt_and_le (μ₁ μ₂ : Measure ℝ)
    [IsProbabilityMeasure μ₁] [IsProbabilityMeasure μ₂] (x : ℝ) :
    (volume.restrict (Ioo (0 : ℝ) 1)).real
        {u : ℝ | x < sInf {r : ℝ | u ≤ μ₁.real (Iic r)} ∧
          sInf {r : ℝ | u ≤ μ₂.real (Iic r)} ≤ x} =
      max (μ₂.real (Iic x) - μ₁.real (Iic x)) 0 :=
  volume_real_gt_and_le_of_eq_source_quantile μ₁ μ₂
    (fun y : ℝ => sInf {r : ℝ | y ≤ μ₁.real (Iic r)})
    (fun y : ℝ => sInf {r : ℝ | y ≤ μ₂.real (Iic r)}) (fun _ _ => rfl) (fun _ _ => rfl) x

end LPPDifferentiability
