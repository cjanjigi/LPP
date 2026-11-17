/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Busemann.Process.NativeFullFamily
public import Mathlib.Topology.Order.Basic
import Busemann.Process.NativeBoundaryEdgeLimitsAux
import Busemann.Geometry.StrictSupportFaceSeparation
import Busemann.Process.ShiftTopology
import LPP_Foundations.Probability.AdjacentAxisDifferenceSums
import LPP_Foundations.Probability.FirstMoment
import LPP_Foundations.Analysis.AbsoluteMomentShape
import ProbabilityBasics.Probability.AbsoluteMomentLowerTail
import Martin2004.Frozen.Martin.Shape
import Martin2004.Shape.MartinShapeExpectedRate
import Mathlib.Probability.IdentDistrib
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.Topology.Instances.NNReal.Lemmas
import Mathlib.Tactic

@[expose] public section
open MeasureTheory ProbabilityTheory Filter LPPDifferentiability
open scoped BigOperators ENNReal Topology

namespace LPP.Busemann

/-- One native full family has both-sign boundary edge limits at every signed
site on the same common event. The longitudinal edge approaches the actual
site weight and the transverse edge diverges to positive infinity, as in the
boundary-cocycle step of GRS arXiv:1510.00860v1, Lemma 5.1, used by JSP (2025)
Lemma 5.1 and Appendix A.1. This asserts no axis-geodesic conclusion. -/
theorem exists_native_full_family_with_boundary_edge_limits
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : LPPStatements.NotAPointMass μ)
    (hmoment : ∃ p : ℝ, 2 < p ∧
      (∫⁻ t, ENNReal.ofReal (|t| ^ p) ∂μ) < ∞) :
    ∃ (g : Quadrant → ℝ) (P : Measure ProcessSample)
      (Bminus Bplus : SupportTilt g → Lattice → Lattice → ProcessSample → ℝ)
      (C : Set ProcessSample),
      IsExpectedRateShape μ g ∧
      P Set.univ = 1 ∧
      P.map processEnvironment = environmentLaw μ ∧
      (∀ z : Lattice, P.map (processShift z) = P) ∧
      Measurable (fun q : SupportTilt g × (Lattice × (Lattice × ProcessSample)) =>
        Bminus q.1 q.2.1 q.2.2.1 q.2.2.2) ∧
      Measurable (fun q : SupportTilt g × (Lattice × (Lattice × ProcessSample)) =>
        Bplus q.1 q.2.1 q.2.2.1 q.2.2.2) ∧
      (∀ I : Set Lattice,
        ProbabilityTheory.IndepFun
          (futureVariables g I Bminus Bplus) (pastVariables I) P) ∧
      (∀ h : SupportTilt g, ∀ x y : Lattice,
        Integrable (Bminus h x y) P ∧ Integrable (Bplus h x y) P) ∧
      (∀ h : SupportTilt g, ∀ x : Lattice,
        (∫ s, Bminus h x (x + ((1 : ℤ), (0 : ℤ))) s ∂P) = -h.1.1 ∧
        (∫ s, Bplus h x (x + ((1 : ℤ), (0 : ℤ))) s ∂P) = -h.1.1 ∧
        (∫ s, Bminus h x (x + ((0 : ℤ), (1 : ℤ))) s ∂P) = -h.1.2 ∧
        (∫ s, Bplus h x (x + ((0 : ℤ), (1 : ℤ))) s ∂P) = -h.1.2) ∧
      MeasurableSet C ∧ P C = 1 ∧
      (∀ z : Lattice, ∀ s ∈ C, processShift z s ∈ C) ∧
      (∀ s ∈ C, ∀ h : SupportTilt g, ∀ x y z : Lattice,
        Bminus h (x + z) (y + z) s = Bminus h x y (processShift z s) ∧
        Bplus h (x + z) (y + z) s = Bplus h x y (processShift z s) ∧
        Bminus h x y s + Bminus h y z s = Bminus h x z s ∧
        Bplus h x y s + Bplus h y z s = Bplus h x z s) ∧
      (∀ s ∈ C, ∀ h : SupportTilt g,
        recovers_environment (processEnvironment s) (fun x y => Bminus h x y s) ∧
        recovers_environment (processEnvironment s) (fun x y => Bplus h x y s)) ∧
      (∀ s ∈ C, ∀ h : SupportTilt g, ∀ x : Lattice,
        Bminus h x (x + ((1 : ℤ), (0 : ℤ))) s ≥
          Bplus h x (x + ((1 : ℤ), (0 : ℤ))) s ∧
        Bminus h x (x + ((0 : ℤ), (1 : ℤ))) s ≤
          Bplus h x (x + ((0 : ℤ), (1 : ℤ))) s) ∧
      (∀ s ∈ C, ∀ h h' : SupportTilt g, h.1.1 < h'.1.1 → ∀ x : Lattice,
        Bplus h x (x + ((1 : ℤ), (0 : ℤ))) s ≥
          Bminus h' x (x + ((1 : ℤ), (0 : ℤ))) s ∧
        Bplus h x (x + ((0 : ℤ), (1 : ℤ))) s ≤
          Bminus h' x (x + ((0 : ℤ), (1 : ℤ))) s) ∧
      (∀ s ∈ C, ∀ h : SupportTilt g, ∀ x y : Lattice,
        ∀ hs : ℕ → SupportTilt g,
          (∀ n, (hs n).1.1 < h.1.1) → Tendsto hs atTop (𝓝 h) →
            Tendsto (fun n => Bminus (hs n) x y s) atTop (𝓝 (Bminus h x y s)) ∧
            Tendsto (fun n => Bplus (hs n) x y s) atTop (𝓝 (Bminus h x y s))) ∧
      (∀ s ∈ C, ∀ h : SupportTilt g, ∀ x y : Lattice,
        ∀ hs : ℕ → SupportTilt g,
          (∀ n, h.1.1 < (hs n).1.1) → Tendsto hs atTop (𝓝 h) →
            Tendsto (fun n => Bminus (hs n) x y s) atTop (𝓝 (Bplus h x y s)) ∧
            Tendsto (fun n => Bplus (hs n) x y s) atTop (𝓝 (Bplus h x y s))) ∧
      (∀ s ∈ C, ∀ h : SupportTilt g, ∀ x y : Lattice,
        Bminus h x y s = Bplus h x y s →
        ∀ hs : ℕ → SupportTilt g, Tendsto hs atTop (𝓝 h) →
          Tendsto (fun n => Bminus (hs n) x y s) atTop (𝓝 (Bminus h x y s)) ∧
          Tendsto (fun n => Bplus (hs n) x y s) atTop (𝓝 (Bminus h x y s))) ∧
      (∀ h : SupportTilt g, ∃ E : Set ProcessSample,
        MeasurableSet E ∧ E ⊆ C ∧ P E = 1 ∧
        ∀ s ∈ E, ∀ x y : Lattice,
          Bminus h x y s = Bplus h x y s) ∧
      (∀ s ∈ C, ∀ x : Lattice,
        ∀ B : SupportTilt g → Lattice → Lattice → ProcessSample → ℝ,
        (B = Bminus ∨ B = Bplus) →
        ∀ ξs : ℕ → InteriorDirection, ∀ hs : ℕ → SupportTilt g,
        (∀ n : ℕ, SupportsAt g (ξs n) (hs n).1) →
          (Tendsto (fun n => (ξs n).1) atTop (𝓝 ((1, 0) : Quadrant)) →
            Tendsto (fun n => B (hs n) x (x + ((1 : ℤ), (0 : ℤ))) s)
              atTop (𝓝 ((processEnvironment s) x)) ∧
            Tendsto (fun n => B (hs n) x (x + ((0 : ℤ), (1 : ℤ))) s)
              atTop atTop) ∧
          (Tendsto (fun n => (ξs n).1) atTop (𝓝 ((0, 1) : Quadrant)) →
            Tendsto (fun n => B (hs n) x (x + ((0 : ℤ), (1 : ℤ))) s)
              atTop (𝓝 ((processEnvironment s) x)) ∧
            Tendsto (fun n => B (hs n) x (x + ((1 : ℤ), (0 : ℤ))) s)
              atTop atTop)) := by
  classical
  -- Choose the actual shape and native family once from the original law.
  obtain ⟨p, hp, hpMoment⟩ := hmoment
  have hmoment : ∃ q : ℝ, 2 < q ∧
      (∫⁻ t, ENNReal.ofReal (|t| ^ q) ∂μ) < ∞ := ⟨p, hp, hpMoment⟩
  have hpos := (ProbabilityBasics.negative_moment_and_positive_tail_of_absolute_moment
    μ hp hpMoment).2
  have hneg := ProbabilityBasics.integrated_sqrt_lower_tail_lt_top_of_absolute_moment
    μ hp hpMoment
  obtain ⟨g, hShape, _⟩ := exists_unique_shape_martin μ hneg hpos
  have hg : IsExpectedRateShape μ g :=
    Martin.martin_shape_tendsto_expected_rate μ hneg hpos g hShape
  obtain ⟨P, Bminus, Bplus, C, hP, hMarginal, hShift, hMeasMinus,
    hMeasPlus, hFuture, hInt, hMeans, hCMeas, hCProb, _hCShift, hCoc,
    hRec, hWithin, hCross, hBelow, hAbove, hEqual, hFixed⟩ :=
    exists_native_full_family μ hμ hmoment g hg
  let : IsProbabilityMeasure P := ⟨hP⟩
  obtain ⟨_, hhom, _⟩ := expected_rate_shape_geometry_of_absolute_moment μ g hmoment hg
  obtain ⟨ξE, ξN, hE, hN, hMonoE, hAntiN, hSupport, _hDirE, _hDirN, hMeanE, hMeanN⟩ :=
    exists_ordered_boundary_contacts μ hmoment g hg
  have hEC : ∀ᵐ s ∂P, s ∈ C := (mem_ae_iff_prob_eq_one hCMeas).mpr hCProb
  have hOrder (s : ProcessSample) (hs : s ∈ C) (h k : SupportTilt g)
      (hhk : h.1.1 ≤ k.1.1) (x : Lattice) :=
    native_unit_bounds_of_order g hhom (fun h x y => Bminus h x y s)
      (fun h x y => Bplus h x y s) (hWithin s hs) (hCross s hs) h k hhk x
  have hLowerM (s : ProcessSample) (hs : s ∈ C) (h : SupportTilt g) (x : Lattice) :
      (processEnvironment s) x ≤ Bminus h x (x + (1, 0)) s ∧
      (processEnvironment s) x ≤ Bminus h x (x + (0, 1)) s := by
    have hr := (hRec s hs h).1 x
    constructor
    · rw [← hr]; exact min_le_left _ _
    · rw [← hr]; exact min_le_right _ _
  have hLowerP (s : ProcessSample) (hs : s ∈ C) (h : SupportTilt g) (x : Lattice) :
      (processEnvironment s) x ≤ Bplus h x (x + (1, 0)) s ∧
      (processEnvironment s) x ≤ Bplus h x (x + (0, 1)) s := by
    have hr := (hRec s hs h).2 x
    constructor
    · rw [← hr]; exact min_le_left _ _
    · rw [← hr]; exact min_le_right _ _
  have hTiltE {i j : ℕ} (hij : i ≤ j) : (hE i).1.1 ≤ (hE j).1.1 := by
    rcases lt_or_eq_of_le hij with hlt | rfl
    · exact support_first_coord_le_of_direction_lt g hhom (ξE i) (ξE j) (hE i) (hE j)
        (hMonoE hlt) (hSupport i).1 (hSupport j).1
    · exact le_rfl
  have hTiltN {i j : ℕ} (hij : i ≤ j) : (hN j).1.1 ≤ (hN i).1.1 := by
    rcases lt_or_eq_of_le hij with hlt | rfl
    · exact support_first_coord_le_of_direction_lt g hhom (ξN j) (ξN i) (hN j) (hN i)
        (hAntiN hlt) (hSupport j).2 (hSupport i).2
    · exact le_rfl
  -- Actual environment marginals identify every site integral and first moment.
  have hAbs : Integrable (fun t : ℝ => |t|) μ :=
    integrable_of_nonneg_rpow_lintegral_lt_top μ _ continuous_abs abs_nonneg p
      (by linarith only [hp]) hpMoment
  have hμInt : Integrable (fun t : ℝ => t) μ :=
    (integrable_norm_iff measurable_id.aestronglyMeasurable).mp
      (by simpa only [Real.norm_eq_abs, id_eq] using hAbs)
  have hEnvMeas : Measurable processEnvironment := measurable_fst
  have hSiteMeas (x : Lattice) : Measurable (fun s => (processEnvironment s) x) :=
    (measurable_pi_apply x).comp hEnvMeas
  have hSiteLaw (x : Lattice) :
      P.map (fun s => (processEnvironment s) x) = μ := by
    calc
      P.map (fun s => (processEnvironment s) x) =
          (P.map processEnvironment).map (fun ω => ω x) :=
        (Measure.map_map (measurable_pi_apply x) hEnvMeas).symm
      _ = μ := by rw [hMarginal, environmentLaw_map_eval]
  have hSiteIdent (x : Lattice) : IdentDistrib (fun s => (processEnvironment s) x)
      (fun t : ℝ => t) P μ :=
    ⟨(hSiteMeas x).aemeasurable, measurable_id.aemeasurable, by
      change P.map (fun s => (processEnvironment s) x) = μ.map id
      rw [Measure.map_id]
      exact hSiteLaw x⟩
  have hSiteInt (x : Lattice) : Integrable (fun s => (processEnvironment s) x) P :=
    (hSiteIdent x).symm.integrable_snd hμInt
  have hSiteMean (x : Lattice) :
      (∫ s, (processEnvironment s) x ∂P) = ∫ t : ℝ, t ∂μ := (hSiteIdent x).integral_eq
  -- Monotone integrable native edges converge to their recovery lower bound.
  have hEastAE (x : Lattice) : ∀ᵐ s ∂P,
      Tendsto (fun n => Bminus (hE n) x (x + (1, 0)) s) atTop
        (𝓝 ((processEnvironment s) x)) := by
    apply tendsto_of_integral_tendsto_of_antitone
      (fun n => (hInt (hE n) x (x + (1, 0))).1) (hSiteInt x)
    · simpa only [fun n => (hMeans (hE n) x).1, hSiteMean x] using hMeanE
    · filter_upwards [hEC] with s hs i j hij
      exact (hOrder s hs (hE i) (hE j) (hTiltE hij) x).1
    · filter_upwards [hEC] with s hs n
      exact (hLowerM s hs (hE n) x).1
  have hNorthAE (x : Lattice) : ∀ᵐ s ∂P,
      Tendsto (fun n => Bplus (hN n) x (x + (0, 1)) s) atTop
        (𝓝 ((processEnvironment s) x)) := by
    apply tendsto_of_integral_tendsto_of_antitone
      (fun n => (hInt (hN n) x (x + (0, 1))).2) (hSiteInt x)
    · simpa only [fun n => (hMeans (hN n) x).2.2.2, hSiteMean x] using hMeanN
    · filter_upwards [hEC] with s hs i j hij
      exact (hOrder s hs (hN j) (hN i) (hTiltN hij) x).2.2.2
    · filter_upwards [hEC] with s hs n
      exact (hLowerP s hs (hN n) x).2
  obtain ⟨ERow, hERowMeas, hERowProb, hRow⟩ :=
    exists_full_event_unbounded_adjacent_axis_difference_sums μ hμ hmoment
  have hRowMeas : MeasurableSet (processEnvironment ⁻¹' ERow) :=
    hERowMeas.preimage hEnvMeas
  have hRowFull : P (processEnvironment ⁻¹' ERow) = 1 := by
    rw [← Measure.map_apply hEnvMeas hERowMeas, hMarginal]
    exact hERowProb
  have hRowAE : ∀ᵐ s ∂P, processEnvironment s ∈ ERow :=
    (mem_ae_iff_prob_eq_one hRowMeas).mpr hRowFull
  have hFixedMeasM (h : SupportTilt g) (x y : Lattice) : Measurable (Bminus h x y) :=
    hMeasMinus.comp (show Measurable (fun s : ProcessSample => (h, (x, (y, s)))) by fun_prop)
  have hFixedMeasP (h : SupportTilt g) (x y : Lattice) : Measurable (Bplus h x y) :=
    hMeasPlus.comp (show Measurable (fun s : ProcessSample => (h, (x, (y, s)))) by fun_prop)
  let A : Set ProcessSample := C ∩ (processEnvironment ⁻¹' ERow) ∩
    {s | ∀ x : Lattice,
      Tendsto (fun n => Bminus (hE n) x (x + (1, 0)) s) atTop (𝓝 ((processEnvironment s) x)) ∧
      Tendsto (fun n => Bplus (hN n) x (x + (0, 1)) s) atTop (𝓝 ((processEnvironment s) x))}
  have hAMeas : MeasurableSet A := by
    apply (hCMeas.inter hRowMeas).inter
    rw [Set.ofPred_forall]
    exact MeasurableSet.iInter fun x =>
      (measurableSet_tendsto_fun (fun n => hFixedMeasM (hE n) x (x + (1, 0))) (hSiteMeas x)).inter
        (measurableSet_tendsto_fun (fun n => hFixedMeasP (hN n) x (x + (0, 1))) (hSiteMeas x))
  have hAAE : ∀ᵐ s ∂P, s ∈ A := by
    have hAll := ae_all_iff.mpr (fun x => (hEastAE x).and (hNorthAE x))
    filter_upwards [hEC, hRowAE, hAll] with s hs hR hL
    exact ⟨⟨hs, hR⟩, hL⟩
  have hAProb : P A = 1 := (mem_ae_iff_prob_eq_one hAMeas).mp hAAE
  -- Countable signed shifts make the same event full and shift closed.
  let C' : Set ProcessSample := {s | ∀ z : Lattice, processShift z s ∈ A}
  have hC'Meas : MeasurableSet C' := by
    rw [show C' = ⋂ z : Lattice, (processShift z) ⁻¹' A by ext s; simp [C']]
    exact MeasurableSet.iInter fun z => hAMeas.preimage (measurable_processShift z)
  have hC'Prob : P C' = 1 := by
    apply (mem_ae_iff_prob_eq_one hC'Meas).mp
    apply ae_all_iff.mpr
    intro z
    apply (mem_ae_iff_prob_eq_one (hAMeas.preimage (measurable_processShift z))).mpr
    rw [← Measure.map_apply (measurable_processShift z) hAMeas, hShift z]
    exact hAProb
  have hInA (s : ProcessSample) (hs : s ∈ C') : s ∈ A := by
    have h := hs 0
    rw [processShift_zero] at h
    exact h
  have hInC (s : ProcessSample) (hs : s ∈ C') : s ∈ C := (hInA s hs).1.1
  have hC'Shift (z : Lattice) (s : ProcessSample) (hs : s ∈ C') : processShift z s ∈ C' := by
    intro w
    rw [← processShift_add]
    exact hs (w + z)
  -- Countable comparisons squeeze every supported approach, for either sign.
  have hLongE (s : ProcessSample) (hs : s ∈ C')
      (B : SupportTilt g → Lattice → Lattice → ProcessSample → ℝ)
      (hB : B = Bminus ∨ B = Bplus)
      (ξs : ℕ → InteriorDirection) (hs' : ℕ → SupportTilt g)
      (hsupp : ∀ n, SupportsAt g (ξs n) (hs' n).1)
      (hξ : Tendsto (fun n => (ξs n).1) atTop (𝓝 ((1, 0) : Quadrant))) (x : Lattice) :
      Tendsto (fun n => B (hs' n) x (x + (1, 0)) s) atTop (𝓝 ((processEnvironment s) x)) := by
    apply tendsto_of_eventual_upper_comparisons _
      (fun k => Bminus (hE k) x (x + (1, 0)) s) _
    · intro n
      rcases hB with rfl | rfl
      · exact (hLowerM s (hInC s hs) (hs' n) x).1
      · exact (hLowerP s (hInC s hs) (hs' n) x).1
    · exact ((hInA s hs).2 x).1
    · intro k
      have hq : ((ξE k).1.1 : ℝ) < 1 := by
        have hp2 : (0 : ℝ) < (ξE k).1.2 := by exact_mod_cast (ξE k).2.2.1
        linarith only [(ξE k).2.2.2, hp2]
      have ht : Tendsto (fun n => ((ξs n).1.1 : ℝ)) atTop (𝓝 1) :=
        NNReal.tendsto_coe.mpr hξ.fst_nhds
      filter_upwards [ht.eventually (Ioi_mem_nhds hq)] with n hn
      have ho := support_first_coord_le_of_direction_lt g hhom (ξE k) (ξs n) (hE k) (hs' n)
        hn (hSupport k).1 (hsupp n)
      have hUnit := hOrder s (hInC s hs) (hE k) (hs' n) ho x
      rcases hB with rfl | rfl
      · exact hUnit.1
      · exact hUnit.2.1
  have hLongN (s : ProcessSample) (hs : s ∈ C')
      (B : SupportTilt g → Lattice → Lattice → ProcessSample → ℝ)
      (hB : B = Bminus ∨ B = Bplus)
      (ξs : ℕ → InteriorDirection) (hs' : ℕ → SupportTilt g)
      (hsupp : ∀ n, SupportsAt g (ξs n) (hs' n).1)
      (hξ : Tendsto (fun n => (ξs n).1) atTop (𝓝 ((0, 1) : Quadrant))) (x : Lattice) :
      Tendsto (fun n => B (hs' n) x (x + (0, 1)) s) atTop (𝓝 ((processEnvironment s) x)) := by
    apply tendsto_of_eventual_upper_comparisons _
      (fun k => Bplus (hN k) x (x + (0, 1)) s) _
    · intro n
      rcases hB with rfl | rfl
      · exact (hLowerM s (hInC s hs) (hs' n) x).2
      · exact (hLowerP s (hInC s hs) (hs' n) x).2
    · exact ((hInA s hs).2 x).2
    · intro k
      have hq : (0 : ℝ) < (ξN k).1.1 := by exact_mod_cast (ξN k).2.1
      have ht : Tendsto (fun n => ((ξs n).1.1 : ℝ)) atTop (𝓝 0) :=
        NNReal.tendsto_coe.mpr hξ.fst_nhds
      filter_upwards [ht.eventually (Iio_mem_nhds hq)] with n hn
      have ho := support_first_coord_le_of_direction_lt g hhom (ξs n) (ξN k) (hs' n) (hN k)
        hn (hsupp n) (hSupport k).2
      have hUnit := hOrder s (hInC s hs) (hs' n) (hN k) ho x
      rcases hB with rfl | rfl
      · exact hUnit.2.2.1
      · exact hUnit.2.2.2
  -- Retain every old native clause on the refined event and the SAME fields.
  refine ⟨g, P, Bminus, Bplus, C', hg, hP, hMarginal, hShift, hMeasMinus,
    hMeasPlus, hFuture, hInt, hMeans, hC'Meas, hC'Prob, hC'Shift,
    (fun s hs => hCoc s (hInC s hs)), (fun s hs => hRec s (hInC s hs)),
    (fun s hs => hWithin s (hInC s hs)), (fun s hs => hCross s (hInC s hs)),
    (fun s hs => hBelow s (hInC s hs)), (fun s hs => hAbove s (hInC s hs)),
    (fun s hs => hEqual s (hInC s hs)), ?_, ?_⟩
  · intro h
    obtain ⟨E, hEMeas, _hEC, hEProb, hEq⟩ := hFixed h
    refine ⟨E ∩ C', hEMeas.inter hC'Meas, fun _ hs => hs.2, ?_, fun s hs => hEq s hs.1⟩
    have hC'AE : ∀ᵐ s ∂P, s ∈ C' :=
      (mem_ae_iff_prob_eq_one hC'Meas).mpr hC'Prob
    rw [Set.inter_comm E C']
    exact (Measure.measure_inter_eq_of_ae (μ := P) (t := C') (s := E) hC'AE).trans hEProb
  · intro s hs x B hB ξs hs' hsupp
    have hAdd (n : ℕ) : is_additive (fun x y => B (hs' n) x y s) := by
      intro x y z
      rcases hB with rfl | rfl
      · exact (hCoc s (hInC s hs) (hs' n) x y z).2.2.1
      · exact (hCoc s (hInC s hs) (hs' n) x y z).2.2.2
    constructor
    · intro hξ
      refine ⟨hLongE s hs B hB ξs hs' hsupp hξ x, ?_⟩
      apply transverse_tendsto_atTop_of_longitudinal (processEnvironment s)
        (fun n x y => B (hs' n) x y s) (1, 0) (0, 1) hAdd
      · intro n y
        rcases hB with rfl | rfl
        · exact (hLowerM s (hInC s hs) (hs' n) y).2
        · exact (hLowerP s (hInC s hs) (hs' n) y).2
      · exact hLongE s hs B hB ξs hs' hsupp hξ
      · intro y K
        obtain ⟨n, hn⟩ := (hRow (processEnvironment s) (hInA s hs).1.2 y K).1
        refine ⟨n, ?_⟩
        simpa [Prod.smul_mk, Prod.add_def, Nat.cast_add, Nat.cast_one] using hn
    · intro hξ
      refine ⟨hLongN s hs B hB ξs hs' hsupp hξ x, ?_⟩
      apply transverse_tendsto_atTop_of_longitudinal (processEnvironment s)
        (fun n x y => B (hs' n) x y s) (0, 1) (1, 0) hAdd
      · intro n y
        rcases hB with rfl | rfl
        · exact (hLowerM s (hInC s hs) (hs' n) y).1
        · exact (hLowerP s (hInC s hs) (hs' n) y).1
      · exact hLongN s hs B hB ξs hs' hsupp hξ
      · intro y K
        obtain ⟨n, hn⟩ := (hRow (processEnvironment s) (hInA s hs).1.2 y K).2
        refine ⟨n, ?_⟩
        simpa [Prod.smul_mk, Prod.add_def, Nat.cast_add, Nat.cast_one] using hn

end LPP.Busemann
