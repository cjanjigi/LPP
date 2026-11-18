/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Busemann.Process.NativeCocycleTriangleShape
public import Busemann.Process.RealQuantileJointLaw
public import Busemann.Process.RealQuantileCoalescence
public import Busemann.Frozen.Definitions.InvariantCocycleTilt
public import Busemann.Frozen.Definitions.ForwardMeasurable
public import LPP_Foundations.Model.LastPassage.PassageDifferenceLimits
import Busemann.Process.RealQuantileForwardFields
import Busemann.Process.RealQuantileFieldJointLaw
import Busemann.Probability.RecoveringCocycleEdgeMean
import Busemann.Probability.CocycleIntegrability
import LPP_Foundations.Probability.TranslationEquiv
import LPP_Foundations.Probability.FirstMoment
import LPP_Foundations.Probability.PassageMeasurable
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.Tactic

@[expose] public section
open MeasureTheory Filter ProbabilityTheory LPPDifferentiability
open scoped ENNReal Topology
namespace LPP.Busemann

/-- The original coupled cocycle's pinned invariant tilt becomes the ordinary
mean of almost every positive fixed-parameter quantile field, after proving
that field's integrability from its axial shape and recovery. The same sampler
characterizes the field by finite passage differences. Strong Existence,
lm:orig_space, lines 1069–1092. -/
theorem exists_real_quantile_forward_field_with_pinned_mean_ae_parameter
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : LPPStatements.NotAPointMass μ)
    (hmoment : ∃ p : ℝ, 2 < p ∧
      (∫⁻ t, ENNReal.ofReal (|t| ^ p) ∂μ) < ∞)
    (P : Measure ProcessSample) [IsProbabilityMeasure P]
    (hMarginal : P.map processEnvironment = environmentLaw μ)
    (hShift : ∀ z : Lattice, P.map (processShift z) = P)
    (B : Lattice → Lattice → ProcessSample → ℝ)
    (hB : IsGeneralizedBusemann P processShift processEnvironment B)
    (hCoal : HasCoalescingRightmostPaths P B)
    (h : ℝ × ℝ)
    (hPinned : ∀ᵐ a ∂P,
      invariantCocycleTilt P processShift processEnvironment B hB a = h) :
    let κ : Lattice → Kernel Environment (ℕ → Lattice) :=
      fun u => condDistrib
        (fun a : ProcessSample =>
          rightmostCocyclePath (fun x y => B x y a) u)
        processEnvironment P
    ∃ q : Lattice → Environment → unitInterval → (ℕ → Lattice),
      (∀ u : Lattice, Measurable
        (fun a : Environment × unitInterval => q u a.1 a.2)) ∧
      (∀ᵐ ω ∂environmentLaw μ, ∀ (u : Lattice) (s : unitInterval),
        IsLocallyRightmostGeodesic ω u (q u ω s) ∧
        ∀ γ : ℕ → Lattice, IsLocallyRightmostGeodesic ω u γ →
          (pathSoutheastLE (q u ω s) γ ↔
            ENNReal.ofReal (s : ℝ) ≤
              (κ u) ω {η : ℕ → Lattice | pathSoutheastLE η γ})) ∧
      (∀ᵐ (s : unitInterval) ∂(volume : Measure unitInterval),
        0 < (s : ℝ) ∧
        ∃ C : Lattice → Lattice → Environment → ℝ,
          IsGeneralizedBusemann (environmentLaw μ)
            (fun z ω => environmentTranslationEquiv z ω)
            (fun ω : Environment => ω) C ∧
          IsForwardMeasurable C ∧
          (∫ ω, C 0 (1, 0) ω ∂environmentLaw μ) = -h.1 ∧
          (∫ ω, C 0 (0, 1) ω ∂environmentLaw μ) = -h.2 ∧
          ∀ᵐ ω ∂environmentLaw μ, ∀ u : Lattice,
            has_passage_difference_limits ω (q u ω s) (fun x y => C x y ω)) := by
  classical
  let κ : Lattice → Kernel Environment (ℕ → Lattice) :=
    fun u => condDistrib
      (fun a : ProcessSample =>
        rightmostCocyclePath (fun x y => B x y a) u)
      processEnvironment P
  let ν : Measure (Environment × unitInterval) :=
    (environmentLaw μ).prod (volume : Measure unitInterval)
  obtain ⟨q, hqMeas, hqCDF, _hqLaw, _hqCov, _hqCoal, hqForward⟩ :=
    exists_real_quantile_sampler_with_forward_field_ae_parameter
      μ hμ hmoment P hMarginal hShift B hB hCoal
  obtain ⟨R, hRMeas, hRawLaw, hRawLimit⟩ :=
    exists_measurable_real_quantile_field_with_original_joint_law
      μ hμ hmoment P hMarginal B hB hCoal q hqMeas hqCDF

  -- The source's uniform triangle estimate supplies both literal axial slopes.
  have hShiftMP (z : Lattice) : MeasurePreserving (processShift z) P P :=
    ⟨measurable_processShift z, hShift z⟩
  let mProc : MeasurableSpace ProcessSample := inferInstance
  let I : MeasurableSpace ProcessSample :=
    ⨅ z : Lattice, @MeasurableSpace.invariants ProcessSample mProc (processShift z)
  let : MeasurableSpace ProcessSample := mProc
  let u : Fin 2 → ProcessSample → ℝ :=
    fun i => P[B 0 (finiteEdgeStep i) | I]
  let Δ : ℕ → Finset Lattice := fun n =>
    insert 0 (((Finset.Icc (0 : ℤ) (n : ℤ)).product
      (Finset.Icc (0 : ℤ) (n : ℤ))).filter
        (fun x => x.1 + x.2 ≤ (n : ℤ)))
  have hTriangle := ae_uniform_recovering_cocycle_triangle_shape
    μ hmoment P hMarginal hShiftMP B hB.1 hB.2.2 hB.2.1
  change ∀ᵐ b ∂P, Tendsto (fun n : ℕ =>
    (Δ n).sup' (by dsimp [Δ]; exact Finset.insert_nonempty _ _)
      (fun x => |B 0 x b -
        (u 0 b * (x.1 : ℝ) + u 1 b * (x.2 : ℝ))|) / (n : ℝ))
      atTop (𝓝 0) at hTriangle
  change ∀ᵐ b ∂P, (-(u 0 b), -(u 1 b)) = h at hPinned
  have hOriginalSlopes : ∀ᵐ b ∂P,
      Tendsto (fun n : ℕ => B 0 (n • finiteEdgeStep 0) b / (n : ℝ))
        atTop (𝓝 (-h.1)) ∧
      Tendsto (fun n : ℕ => B 0 (n • finiteEdgeStep 1) b / (n : ℝ))
        atTop (𝓝 (-h.2)) := by
    filter_upwards [hTriangle, hPinned] with b ht hp
    have hu0 : u 0 b = -h.1 := by
      have he := congrArg Prod.fst hp
      dsimp at he
      linarith
    have hu1 : u 1 b = -h.2 := by
      have he := congrArg Prod.snd hp
      dsimp at he
      linarith
    have hAxis (i : Fin 2) :
        Tendsto (fun n : ℕ => B 0 (n • finiteEdgeStep i) b / (n : ℝ))
          atTop (𝓝 (u i b)) := by
      have hMem (n : ℕ) : n • finiteEdgeStep i ∈ Δ n := by
        have he : ((n : ℤ), (0 : ℤ)) ∈ Δ n := by
          apply Finset.mem_insert_of_mem
          apply Finset.mem_filter.mpr
          refine ⟨Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, by omega⟩,
            Finset.mem_Icc.mpr ⟨by omega, by omega⟩⟩, ?_⟩
          dsimp
          omega
        have hn : ((0 : ℤ), (n : ℤ)) ∈ Δ n := by
          apply Finset.mem_insert_of_mem
          apply Finset.mem_filter.mpr
          refine ⟨Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, by omega⟩,
            Finset.mem_Icc.mpr ⟨by omega, by omega⟩⟩, ?_⟩
          dsimp
          omega
        fin_cases i
        · simpa [finiteEdgeStep] using he
        · simpa [finiteEdgeStep] using hn
      have hResidual : Tendsto (fun n : ℕ =>
          B 0 (n • finiteEdgeStep i) b / (n : ℝ) - u i b)
          atTop (𝓝 0) := by
        apply Metric.tendsto_atTop.mpr
        intro ε hε
        obtain ⟨N, hN⟩ := eventually_atTop.mp (ht.eventually (gt_mem_nhds hε))
        refine ⟨max 1 N, ?_⟩
        intro n hn
        have hnpos : 0 < n := by omega
        have hnR : 0 < (n : ℝ) := by exact_mod_cast hnpos
        have hpoint := Finset.le_sup'
          (fun x : Lattice => |B 0 x b -
            (u 0 b * (x.1 : ℝ) + u 1 b * (x.2 : ℝ))|) (hMem n)
        have hPoint : |B 0 (n • finiteEdgeStep i) b - u i b * (n : ℝ)| ≤
            (Δ n).sup' (by dsimp [Δ]; exact Finset.insert_nonempty _ _)
              (fun x => |B 0 x b -
                (u 0 b * (x.1 : ℝ) + u 1 b * (x.2 : ℝ))|) := by
          calc
            |B 0 (n • finiteEdgeStep i) b - u i b * (n : ℝ)| =
                |B 0 (n • finiteEdgeStep i) b -
                  (u 0 b * ((n • finiteEdgeStep i).1 : ℝ) +
                    u 1 b * ((n • finiteEdgeStep i).2 : ℝ))| := by
                    fin_cases i <;> simp [finiteEdgeStep]
            _ ≤ _ := hpoint
        have hdiv : B 0 (n • finiteEdgeStep i) b / (n : ℝ) - u i b =
            (B 0 (n • finiteEdgeStep i) b - u i b * (n : ℝ)) / (n : ℝ) := by
          field_simp [hnR.ne']
        rw [Real.dist_eq, sub_zero, hdiv, abs_div, abs_of_pos hnR]
        exact (div_le_div_of_nonneg_right hPoint hnR.le).trans_lt (hN n (by omega))
      simpa only [sub_add_cancel, zero_add] using
        hResidual.add (tendsto_const_nhds (x := u i b))
    exact ⟨by simpa only [hu0] using hAxis 0,
      by simpa only [hu1] using hAxis 1⟩

  -- Encode the two axial limits as a Borel event before using the joint law.
  let Field := Lattice → Lattice → ℝ
  let E : Set (Environment × Field) :=
    {a | Tendsto (fun n : ℕ => a.2 0 (n • finiteEdgeStep 0) / (n : ℝ))
        atTop (𝓝 (-h.1)) ∧
      Tendsto (fun n : ℕ => a.2 0 (n • finiteEdgeStep 1) / (n : ℝ))
        atTop (𝓝 (-h.2))}
  have hFieldCoord (x y : Lattice) :
      Measurable (fun a : Environment × Field => a.2 x y) :=
    (measurable_pi_apply y).comp
      ((measurable_pi_apply x).comp measurable_snd)
  have hEMeas : MeasurableSet E := by
    change MeasurableSet
      {a : Environment × Field |
        Tendsto (fun n : ℕ => a.2 0 (n • finiteEdgeStep 0) / (n : ℝ))
          atTop (𝓝 (-h.1)) ∧
        Tendsto (fun n : ℕ => a.2 0 (n • finiteEdgeStep 1) / (n : ℝ))
          atTop (𝓝 (-h.2))}
    exact (measurableSet_tendsto_fun
      (fun n : ℕ => (hFieldCoord 0 (n • finiteEdgeStep 0)).div_const (n : ℝ))
      measurable_const).inter
      (measurableSet_tendsto_fun
        (fun n : ℕ => (hFieldCoord 0 (n • finiteEdgeStep 1)).div_const (n : ℝ))
        measurable_const)
  let pairP : ProcessSample → Environment × Field :=
    fun b => (processEnvironment b, fun x y => B x y b)
  have hBMeas (x y : Lattice) : Measurable (B x y) := by
    have hArg : Measurable (fun b : ProcessSample => ((x, y), b)) :=
      measurable_const.prodMk measurable_id
    exact hB.1.1.comp hArg
  have hFieldPMeas : Measurable (fun b : ProcessSample =>
      (fun x y : Lattice => B x y b)) := by
    apply Measurable.of_eval
    intro x
    apply Measurable.of_eval
    intro y
    exact hBMeas x y
  have hPairPMeas : Measurable pairP :=
    measurable_fst.prodMk hFieldPMeas
  let pairQ : Environment × unitInterval → Environment × Field :=
    fun a => (a.1, R a)
  have hPairQMeas : Measurable pairQ := measurable_fst.prodMk hRMeas
  have hPEvent : ∀ᵐ b ∂P, pairP b ∈ E := by
    filter_upwards [hOriginalSlopes] with b hb
    exact hb
  have hProductSlopes : ∀ᵐ a ∂ν, pairQ a ∈ E := by
    have hMapEvent : ∀ᵐ t ∂P.map pairP, t ∈ E :=
      (ae_map_iff hPairPMeas.aemeasurable hEMeas).mpr hPEvent
    rw [← hRawLaw] at hMapEvent
    exact (ae_map_iff hPairQMeas.aemeasurable hEMeas).mp hMapEvent
  have hProductSlopesMeas : MeasurableSet {a : Environment × unitInterval |
      pairQ a ∈ E} := hEMeas.preimage hPairQMeas
  have hSlopeSections :
      ∀ᵐ s ∂(volume : Measure unitInterval),
        ∀ᵐ ω ∂environmentLaw μ,
          Tendsto (fun n : ℕ => R (ω, s) 0 (n • finiteEdgeStep 0) / (n : ℝ))
            atTop (𝓝 (-h.1)) ∧
          Tendsto (fun n : ℕ => R (ω, s) 0 (n • finiteEdgeStep 1) / (n : ℝ))
            atTop (𝓝 (-h.2)) := by
    have hForwardSections := Measure.ae_ae_of_ae_prod hProductSlopes
    have hReverse :=
      (Measure.ae_ae_comm hProductSlopesMeas).mp hForwardSections
    filter_upwards [hReverse] with s hs
    filter_upwards [hs] with ω hω
    simpa only [pairQ, E, Set.mem_ofPred_eq] using hω

  -- The raw finite-limit event is measurable by its countable coordinates.
  have hQVertexMeas (u : Lattice) (j : ℕ) :
      Measurable (fun a : Environment × unitInterval => q u a.1 a.2 j) :=
    (measurable_pi_apply j).comp (hqMeas u)
  have hFiniteMeas (u x y : Lattice) (j : ℕ) :
      Measurable (fun a : Environment × unitInterval =>
        lastPassage a.1 x
          (((q u a.1 a.2 j).1 - x.1).toNat,
           ((q u a.1 a.2 j).2 - x.2).toNat) -
        lastPassage a.1 y
          (((q u a.1 a.2 j).1 - y.1).toNat,
           ((q u a.1 a.2 j).2 - y.2).toNat)) := by
    have hPassMeas (z : Lattice) : Measurable
        (fun a : Environment × unitInterval =>
          lastPassage a.1 z
            (((q u a.1 a.2 j).1 - z.1).toNat,
             ((q u a.1 a.2 j).2 - z.2).toNat)) := by
      let displacement : Lattice → ℕ × ℕ :=
        fun v => ((v.1 - z.1).toNat, (v.2 - z.2).toNat)
      have hDisp : Measurable (fun a : Environment × unitInterval =>
          displacement (q u a.1 a.2 j)) :=
        (measurable_of_countable displacement).comp (hQVertexMeas u j)
      have hJoint : Measurable (fun p : (ℕ × ℕ) × Environment =>
          lastPassage p.2 z p.1) := by
        apply measurable_from_prod_countable_right
        intro d
        exact measurable_lastPassage z d
      have hInput : Measurable (fun a : Environment × unitInterval =>
          (displacement (q u a.1 a.2 j), a.1)) :=
        hDisp.prodMk measurable_fst
      simpa only [Function.comp_def, displacement] using hJoint.comp hInput
    exact (hPassMeas x).sub (hPassMeas y)
  have hRCoord (x y : Lattice) :
      Measurable (fun a : Environment × unitInterval => R a x y) :=
    (measurable_pi_apply y).comp
      ((measurable_pi_apply x).comp hRMeas)
  let L : Set (Environment × unitInterval) :=
    {a | ∀ u x y : Lattice, ∀ N : ℕ,
      x ≤ q u a.1 a.2 N → y ≤ q u a.1 a.2 N →
      Tendsto (fun n : ℕ =>
        lastPassage a.1 x
          (((q u a.1 a.2 (N + n)).1 - x.1).toNat,
           ((q u a.1 a.2 (N + n)).2 - x.2).toNat) -
        lastPassage a.1 y
          (((q u a.1 a.2 (N + n)).1 - y.1).toNat,
           ((q u a.1 a.2 (N + n)).2 - y.2).toNat))
        atTop (𝓝 (R a x y))}
  have hLMeas : MeasurableSet L := by
    dsimp only [L]
    simp only [Set.ofPred_forall]
    refine MeasurableSet.iInter fun u => MeasurableSet.iInter fun x =>
      MeasurableSet.iInter fun y => MeasurableSet.iInter fun N => ?_
    have hX : MeasurableSet {a : Environment × unitInterval |
        x ≤ q u a.1 a.2 N} :=
      (Set.to_countable (Set.Ici x)).measurableSet.preimage (hQVertexMeas u N)
    have hY : MeasurableSet {a : Environment × unitInterval |
        y ≤ q u a.1 a.2 N} :=
      (Set.to_countable (Set.Ici y)).measurableSet.preimage (hQVertexMeas u N)
    have hT : MeasurableSet {a : Environment × unitInterval |
        Tendsto (fun n : ℕ =>
          lastPassage a.1 x
            (((q u a.1 a.2 (N + n)).1 - x.1).toNat,
             ((q u a.1 a.2 (N + n)).2 - x.2).toNat) -
          lastPassage a.1 y
            (((q u a.1 a.2 (N + n)).1 - y.1).toNat,
             ((q u a.1 a.2 (N + n)).2 - y.2).toNat))
          atTop (𝓝 (R a x y))} :=
      measurableSet_tendsto_fun
        (fun n => hFiniteMeas u x y (N + n)) (hRCoord x y)
    have hClause : {a : Environment × unitInterval |
        x ≤ q u a.1 a.2 N → y ≤ q u a.1 a.2 N →
        Tendsto (fun n : ℕ =>
          lastPassage a.1 x
            (((q u a.1 a.2 (N + n)).1 - x.1).toNat,
             ((q u a.1 a.2 (N + n)).2 - x.2).toNat) -
          lastPassage a.1 y
            (((q u a.1 a.2 (N + n)).1 - y.1).toNat,
             ((q u a.1 a.2 (N + n)).2 - y.2).toNat))
          atTop (𝓝 (R a x y))} =
        ({a | x ≤ q u a.1 a.2 N} ∩
          {a | y ≤ q u a.1 a.2 N})ᶜ ∪
        {a | Tendsto (fun n : ℕ =>
          lastPassage a.1 x
            (((q u a.1 a.2 (N + n)).1 - x.1).toNat,
             ((q u a.1 a.2 (N + n)).2 - x.2).toNat) -
          lastPassage a.1 y
            (((q u a.1 a.2 (N + n)).1 - y.1).toNat,
             ((q u a.1 a.2 (N + n)).2 - y.2).toNat))
          atTop (𝓝 (R a x y))} := by
      ext a
      simp only [Set.mem_ofPred_eq, Set.mem_union, Set.mem_compl_iff,
        Set.mem_inter_iff]
      tauto
    rw [hClause]
    exact (hX.inter hY).compl.union hT
  have hRawSections :
      ∀ᵐ s ∂(volume : Measure unitInterval),
        ∀ᵐ ω ∂environmentLaw μ,
          ∀ u x y : Lattice, ∀ N : ℕ,
            x ≤ q u ω s N → y ≤ q u ω s N →
            Tendsto (fun n : ℕ =>
              lastPassage ω x
                (((q u ω s (N + n)).1 - x.1).toNat,
                 ((q u ω s (N + n)).2 - x.2).toNat) -
              lastPassage ω y
                (((q u ω s (N + n)).1 - y.1).toNat,
                 ((q u ω s (N + n)).2 - y.2).toNat))
              atTop (𝓝 (R (ω, s) x y)) := by
    have hForwardSections := Measure.ae_ae_of_ae_prod hRawLimit
    have hReverse := (Measure.ae_ae_comm hLMeas).mp hForwardSections
    simpa only [L, ν, has_passage_difference_limits, natDisplacement] using hReverse

  have hμIntegrable : Integrable (fun t : ℝ => t) μ := by
    obtain ⟨p, hp, hpMoment⟩ := hmoment
    have hAbs : Integrable (fun t : ℝ => |t|) μ :=
      integrable_of_nonneg_rpow_lintegral_lt_top μ (fun t => |t|)
        continuous_abs (fun t => abs_nonneg t) p (by linarith) hpMoment
    apply (integrable_norm_iff (measurable_id.aestronglyMeasurable)).mp
    simpa only [Real.norm_eq_abs, id_eq] using hAbs

  refine ⟨q, hqMeas, hqCDF, ?_⟩
  filter_upwards [hqForward, hSlopeSections, hRawSections]
    with s hsForward hsSlopes hsRaw
  obtain ⟨hsPositive, C, hCCocycle, hCRecover, hCForward, hCLimit⟩ := hsForward
  have hRawEqualsC : ∀ᵐ ω ∂environmentLaw μ,
      ∀ x y : Lattice, R (ω, s) x y = C x y ω := by
    filter_upwards [hsRaw, hCLimit, hqCDF] with ω hraw hc hgeo
    intro x y
    let w : Lattice := x ⊔ y
    have hroot : q w ω s 0 = w := (hgeo w s).1.1
    have hx : x ≤ q w ω s 0 := by
      rw [hroot]
      exact le_sup_left
    have hy : y ≤ q w ω s 0 := by
      rw [hroot]
      exact le_sup_right
    exact tendsto_nhds_unique (hraw w x y 0 hx hy) (hc w x y 0 hx hy)
  have hSlopeC0 : ∀ᵐ ω ∂environmentLaw μ,
      Tendsto (fun n : ℕ => C 0 (n • finiteEdgeStep 0) ω / (n : ℝ))
        atTop (𝓝 (-h.1)) := by
    filter_upwards [hsSlopes, hRawEqualsC] with ω hs heq
    simpa only [heq] using hs.1
  have hSlopeC1 : ∀ᵐ ω ∂environmentLaw μ,
      Tendsto (fun n : ℕ => C 0 (n • finiteEdgeStep 1) ω / (n : ℝ))
        atTop (𝓝 (-h.2)) := by
    filter_upwards [hsSlopes, hRawEqualsC] with ω hs heq
    simpa only [heq] using hs.2
  have hEdge0 := integrable_origin_edge_and_mean_of_finite_axial_slope
    μ hμIntegrable C hCCocycle hCRecover 0 (-h.1) hSlopeC0
  have hEdge1 := integrable_origin_edge_and_mean_of_finite_axial_slope
    μ hμIntegrable C hCCocycle hCRecover 1 (-h.2) hSlopeC1
  have hAllIntegrable : ∀ x y : Lattice,
      Integrable (C x y) (environmentLaw μ) := by
    apply integrable_cocycle_of_integrable_origin_edges
      (environmentLaw μ)
      (fun z ω => environmentTranslationEquiv z ω) C
      (measurePreserving_environmentTranslationEquiv μ) hCCocycle
    · simpa only [finiteEdgeStep, Fin.val_zero, ite_true] using hEdge0.1
    · simpa only [finiteEdgeStep, Fin.val_one, one_ne_zero, ite_false] using hEdge1.1
  have hCGeneralized : IsGeneralizedBusemann (environmentLaw μ)
      (fun z ω => environmentTranslationEquiv z ω)
      (fun ω : Environment => ω) C :=
    ⟨hCCocycle, hCRecover, hAllIntegrable⟩
  refine ⟨hsPositive, C, hCGeneralized, hCForward, ?_, ?_, hCLimit⟩
  · simpa only [finiteEdgeStep, Fin.val_zero, ite_true] using hEdge0.2
  · simpa only [finiteEdgeStep, Fin.val_one, one_ne_zero, ite_false] using hEdge1.2

end LPP.Busemann
