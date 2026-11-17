/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Busemann.Frozen.StrongExistence.Definitions.BranchAgreement
public import Busemann.Frozen.StrongExistence.Definitions.ForwardCoalescingClass
public import Busemann.Frozen.StrongExistence.Definitions.MeanTilt
public import Busemann.Frozen.StrongExistence.Definitions.WithinTiltOrder
public import Busemann.Frozen.StrongExistence.Definitions.StrictCrossTiltOrder
public import Busemann.Frozen.StrongExistence.Definitions.OneSidedLimits
public import Busemann.Frozen.StrongExistence.Definitions.SkorokhodRealization

import Busemann.Geometry.CoalescingTiltTimeIndex
import Busemann.Topology.PairedGraphCompactness
import Busemann.Topology.PairedBorelGenerators
import Mathlib.Topology.Sequences
import Mathlib.MeasureTheory.Measure.NullMeasurable
import Lean.Elab.Tactic.Omega

/-! A paired Skorokhod path realizing both original strong-process fields. -/

@[expose] public section
open MeasureTheory Filter LPPDifferentiability
open scoped ENNReal Topology
namespace LPP.Busemann

-- Transfer scalar sequential limits on the tilt set to a product-state limit
-- on one relative side of the actual time set.
private theorem tendsto_time_trace_of_sided_sequences
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (ι : {t : ℝ // t ∈ timeSet μ} → CoalescingTilt μ)
    (hι : ∀ t, timeIndex μ (ι t) = t)
    (hEmbed : Topology.IsEmbedding (timeIndex μ))
    (J : Type*)
    (side : {t : ℝ // t ∈ timeSet μ} → Set {t : ℝ // t ∈ timeSet μ})
    (R : CoalescingTilt μ → CoalescingTilt μ → Prop)
    (hSide : ∀ t s, s ∈ side t → R (ι s) (ι t))
    (F G : CoalescingTilt μ → J → ℝ)
    (hSeq : ∀ h j (hs : ℕ → CoalescingTilt μ),
      (∀ n, R (hs n) h) → Tendsto hs atTop (𝓝 h) →
      Tendsto (fun n => F (hs n) j) atTop (𝓝 (G h j))) :
    ∀ t, Tendsto (fun s => F (ι s)) (𝓝[side t] t) (𝓝 (G (ι t))) := by
  intro t
  apply Filter.tendsto_iff_seq_tendsto.2
  intro u hu
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1
    (tendsto_nhdsWithin_iff.mp hu).2
  have huTail : Tendsto (fun n => u (n + N)) atTop (𝓝 t) :=
    (tendsto_add_atTop_iff_nat N).2 (tendsto_nhdsWithin_iff.mp hu).1
  have hιTail : Tendsto (fun n => ι (u (n + N))) atTop (𝓝 (ι t)) := by
    apply hEmbed.tendsto_nhds_iff.2
    simpa only [Function.comp_def, hι] using huTail
  have hRTail : ∀ n, R (ι (u (n + N))) (ι t) := by
    intro n
    exact hSide t (u (n + N)) (hN _ (by omega))
  have hTail : Tendsto (fun n => F (ι (u (n + N)))) atTop
      (𝓝 (G (ι t))) :=
    tendsto_pi_nhds.2 fun j => hSeq (ι t) j
      (fun n => ι (u (n + N))) hRTail hιTail
  exact (tendsto_add_atTop_iff_nat N).1 hTail

-- The named parameters `hCross`, `hWithin`, `hMean`, `hAgreement` are part of the shared theorem interface.
set_option linter.unusedVariables false in
/-- A closed canonical time set and the six source process properties realize
the same two fields as one measurable paired path on one all-tilt event. -/
theorem skorokhodRealization_of_strong_process_properties
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : LPPStatements.NotAPointMass μ)
    (hmoment : ∃ p : ℝ, 2 < p ∧
      (∫⁻ t, ENNReal.ofReal (|t| ^ p) ∂μ) < ∞)
    (Bm Bp : StrongField μ)
    (hClosed : IsClosed (timeSet μ))
    (hAgreement : BranchAgreement μ Bm Bp)
    (hClass : ForwardCoalescingClass μ Bm Bp)
    (hMean : MeanTilt μ Bm)
    (hWithin : WithinTiltOrder μ Bm Bp)
    (hCross : StrictCrossTiltOrder μ Bm Bp)
    (hLimits : OneSidedLimits μ Bm Bp) :
    SkorokhodRealization μ Bm Bp := by
  classical
  let T := {t : ℝ // t ∈ timeSet μ}
  let J := Lattice × Lattice
  let ι : T → CoalescingTilt μ := fun t =>
    Classical.choose (show ∃ h : CoalescingTilt μ, timeIndex μ h = t by
      obtain ⟨h, hh⟩ := t.property
      refine ⟨h, ?_⟩
      apply Subtype.ext
      exact hh.symm)
  have hι (t : T) : timeIndex μ (ι t) = t := by
    exact Classical.choose_spec
      (show ∃ h : CoalescingTilt μ, timeIndex μ h = t by
        obtain ⟨h, hh⟩ := t.property
        refine ⟨h, ?_⟩
        apply Subtype.ext
        exact hh.symm)
  have hEmbed : Topology.IsEmbedding (timeIndex μ) :=
    timeIndex_isEmbedding μ hμ hmoment
  have hιIndex (h : CoalescingTilt μ) : ι (timeIndex μ h) = h := by
    apply hEmbed.injective
    exact hι (timeIndex μ h)
  have hLeftSide (t s : T) (hst : s ∈ Set.Iio t) :
      (ι s).val.1 < (ι t).val.1 := by
    have hs : (timeIndex μ (ι s)).val < (timeIndex μ (ι t)).val := by
      rw [hι s, hι t]
      exact hst
    exact (timeIndex_lt_iff_first_coordinate_lt μ hμ hmoment (ι s) (ι t)).mp hs
  have hRightSide (t s : T) (hst : s ∈ Set.Ioi t) :
      (ι t).val.1 < (ι s).val.1 := by
    have hs : (timeIndex μ (ι t)).val < (timeIndex μ (ι s)).val := by
      rw [hι s, hι t]
      exact hst
    exact (timeIndex_lt_iff_first_coordinate_lt μ hμ hmoment (ι t) (ι s)).mp hs
  let Fm (ω : Environment) (h : CoalescingTilt μ) (j : J) := Bm h j.1 j.2 ω
  let Fp (ω : Environment) (h : CoalescingTilt μ) (j : J) := Bp h j.1 j.2 ω
  let raw (ω : Environment) : RawPairedTrace (timeSet μ) J :=
    (fun t => Fm ω (ι t), fun t => Fp ω (ι t))
  let G : Set Environment := {ω | ∀ h : CoalescingTilt μ, ∀ x y : Lattice,
    (∀ hs : ℕ → CoalescingTilt μ,
      (∀ n, (hs n).val.1 < h.val.1) → Tendsto hs atTop (𝓝 h) →
      Tendsto (fun n => Bm (hs n) x y ω) atTop (𝓝 (Bm h x y ω)) ∧
      Tendsto (fun n => Bp (hs n) x y ω) atTop (𝓝 (Bm h x y ω))) ∧
    (∀ hs : ℕ → CoalescingTilt μ,
      (∀ n, h.val.1 < (hs n).val.1) → Tendsto hs atTop (𝓝 h) →
      Tendsto (fun n => Bm (hs n) x y ω) atTop (𝓝 (Bp h x y ω)) ∧
      Tendsto (fun n => Bp (hs n) x y ω) atTop (𝓝 (Bp h x y ω)))}
  have hGae : ∀ᵐ ω ∂environmentLaw μ, ω ∈ G := hLimits
  have hRawLeft (ω : Environment) (hω : ω ∈ G) (t : T) :
      Tendsto (raw ω).1 (𝓝[Set.Iio t] t) (𝓝 ((raw ω).1 t)) ∧
      Tendsto (raw ω).2 (𝓝[Set.Iio t] t) (𝓝 ((raw ω).1 t)) := by
    constructor
    · exact tendsto_time_trace_of_sided_sequences μ ι hι hEmbed J
        (fun t => Set.Iio t) (fun h k => h.val.1 < k.val.1)
        hLeftSide (Fm ω) (Fm ω)
        (fun h j hs hStrict hConv => (hω h j.1 j.2).1 hs hStrict hConv |>.1) t
    · exact tendsto_time_trace_of_sided_sequences μ ι hι hEmbed J
        (fun t => Set.Iio t) (fun h k => h.val.1 < k.val.1)
        hLeftSide (Fp ω) (Fm ω)
        (fun h j hs hStrict hConv => (hω h j.1 j.2).1 hs hStrict hConv |>.2) t
  have hRawRight (ω : Environment) (hω : ω ∈ G) (t : T) :
      Tendsto (raw ω).1 (𝓝[Set.Ioi t] t) (𝓝 ((raw ω).2 t)) ∧
      Tendsto (raw ω).2 (𝓝[Set.Ioi t] t) (𝓝 ((raw ω).2 t)) := by
    have hOne := hω
    constructor
    · exact tendsto_time_trace_of_sided_sequences μ ι hι hEmbed J
        (fun t => Set.Ioi t) (fun h k => k.val.1 < h.val.1)
        hRightSide (Fm ω) (Fp ω)
        (fun h j hs hStrict hConv => (hOne h j.1 j.2).2 hs hStrict hConv |>.1) t
    · exact tendsto_time_trace_of_sided_sequences μ ι hι hEmbed J
        (fun t => Set.Ioi t) (fun h k => k.val.1 < h.val.1)
        hRightSide (Fp ω) (Fp ω)
        (fun h j hs hStrict hConv => (hOne h j.1 j.2).2 hs hStrict hConv |>.2) t
  have hCompact (ω : Environment) (hω : ω ∈ G) :
      IsCompact (pairedOrderGraph (timeSet μ) (raw ω)) :=
    pairedOrderGraph_isCompact_of_oneSidedLimits hClosed (raw ω)
      (hRawLeft ω hω) (hRawRight ω hω)
  let zeroRaw : RawPairedTrace (timeSet μ) J := (fun _ _ => 0, fun _ _ => 0)
  have hZeroCompact : IsCompact (pairedOrderGraph (timeSet μ) zeroRaw) := by
    apply pairedOrderGraph_isCompact_of_oneSidedLimits hClosed zeroRaw
    · intro t
      exact ⟨tendsto_const_nhds, tendsto_const_nhds⟩
    · intro t
      exact ⟨tendsto_const_nhds, tendsto_const_nhds⟩
  let zeroPath : PairedSkorokhodPath (timeSet μ) J := ⟨zeroRaw, hZeroCompact⟩
  have hGNull : environmentLaw μ Gᶜ = 0 := (mem_ae_iff).mp hGae
  have hGNullMeas : NullMeasurableSet G (environmentLaw μ) := by
    simpa only [compl_compl] using (NullMeasurableSet.of_null hGNull).compl
  obtain ⟨A, hAG, hAMeas, hAeq⟩ := hGNullMeas.exists_measurable_subset_ae_eq
  have hAae : ∀ᵐ ω ∂environmentLaw μ, ω ∈ A := by
    apply (ae_eq_univ).mp
    exact hAeq.trans ((ae_eq_univ).mpr hGNull)
  let Φ : Environment → PairedSkorokhodPath (timeSet μ) J := fun ω =>
    if hω : ω ∈ A then ⟨raw ω, hCompact ω (hAG hω)⟩ else zeroPath
  obtain ⟨D, hDCount, _hDSides, hBorel⟩ :=
    exists_countable_sided_eval_generators (timeSet μ) J hClosed
  have hBmMeas (h : CoalescingTilt μ) (j : J) : Measurable (Bm h j.1 j.2) := by
    have hSection : Measurable (fun ω : Environment => ((j.1, j.2), ω)) :=
      measurable_const.prodMk measurable_id
    exact ((hClass h).2.1.1.1).comp hSection
  have hBpMeas (h : CoalescingTilt μ) (j : J) : Measurable (Bp h j.1 j.2) := by
    have hSection : Measurable (fun ω : Environment => ((j.1, j.2), ω)) :=
      measurable_const.prodMk measurable_id
    exact (hClass h).1.comp hSection
  have hMinusMeas (t : T) (j : J) :
      Measurable (fun ω => evalMinus (Φ ω) t j) := by
    have hPiece : Measurable (A.piecewise (Bm (ι t) j.1 j.2) (fun _ : Environment => (0 : ℝ))) :=
      (hBmMeas (ι t) j).piecewise hAMeas measurable_const
    convert hPiece using 1
    funext ω
    by_cases hω : ω ∈ A <;> simp [Φ, hω, evalMinus, raw, Fm, zeroPath, zeroRaw]
  have hPlusMeas (t : T) (j : J) :
      Measurable (fun ω => evalPlus (Φ ω) t j) := by
    have hPiece : Measurable (A.piecewise (Bp (ι t) j.1 j.2) (fun _ : Environment => (0 : ℝ))) :=
      (hBpMeas (ι t) j).piecewise hAMeas measurable_const
    convert hPiece using 1
    funext ω
    by_cases hω : ω ∈ A <;> simp [Φ, hω, evalPlus, raw, Fp, zeroPath, zeroRaw]
  have hΦMeas : @Measurable Environment
      (PairedSkorokhodPath (timeSet μ) J)
      (inferInstance : MeasurableSpace Environment)
      (pairedSkorokhodPathBorel (timeSet μ) J) Φ := by
    rw [hBorel]
    apply measurable_generateFrom
    intro U hU
    rcases hU with ⟨t, _htD, j, V, hV, hEq | hEq⟩
    · rw [hEq]
      exact (hMinusMeas t j) hV.measurableSet
    · rw [hEq]
      exact (hPlusMeas t j) hV.measurableSet
  refine ⟨hClosed, Φ, hΦMeas, ?_⟩
  filter_upwards [hAae] with ω hω
  intro h x y
  have hRaw : (Φ ω).val = raw ω := by
    simp [Φ, hω]
  constructor
  · simp only [evalMinus, hRaw, raw, Fm, hιIndex h]
  · simp only [evalPlus, hRaw, raw, Fp, hιIndex h]

end LPP.Busemann
