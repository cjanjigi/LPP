/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LPP_Foundations.Statements.ShapeDefinitions
import Busemann.Process.NativeFullFamily
import Busemann.Process.NativeUniformPassageBounds
import Busemann.Process.FullEventCocycles
import Busemann.Process.Shifts
import Busemann.Geometry.NativeGeometry
import Busemann.Geometry.NativeSupportGaps
import Busemann.Geometry.StrictSupportFaceSeparation
import LPP_Foundations.Probability.PassageMeasurable
import LPP_Foundations.Analysis.AbsoluteMomentShape
import ProbabilityBasics.Probability.AbsoluteMomentLowerTail
import Martin2004.Probability.MartinRealExpectedRate
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic

/-! Original-law uniform neighboring-start passage bounds in every interior cone. -/

@[expose] public section
open MeasureTheory Filter LPPDifferentiability
open scoped ENNReal NNReal

namespace LPP.Busemann

private abbrev ConeBounds (ω : LPPDifferentiability.Environment) (x : Lattice) (ε : ℚ) : Prop :=
  ∃ C N : ℕ, 0 < N ∧
    ∀ d : ℕ × ℕ, N ≤ d.1 + d.2 →
      (ε : ℝ) ≤ (d.1 : ℝ) / ((d.1 + d.2 : ℕ) : ℝ) →
      (d.1 : ℝ) / ((d.1 + d.2 : ℕ) : ℝ) ≤ 1 - (ε : ℝ) →
      0 < d.1 ∧ 0 < d.2 ∧
      |lastPassage ω x d - lastPassage ω (x + (1, 0)) (d.1 - 1, d.2)| ≤ (C : ℝ) ∧
      |lastPassage ω x d - lastPassage ω (x + (0, 1)) (d.1, d.2 - 1)| ≤ (C : ℝ)

-- Prove the actual countable predicate measurable before any marginal transfer.
private theorem measurableSet_coneBounds (x : Lattice) (ε : ℚ) :
    MeasurableSet {ω : LPPDifferentiability.Environment | ConeBounds ω x ε} := by
  classical
  have hPair (C : ℕ) (d : ℕ × ℕ) :
      MeasurableSet {ω : LPPDifferentiability.Environment |
        0 < d.1 ∧ 0 < d.2 ∧
        |lastPassage ω x d - lastPassage ω (x + (1, 0)) (d.1 - 1, d.2)| ≤ (C : ℝ) ∧
        |lastPassage ω x d - lastPassage ω (x + (0, 1)) (d.1, d.2 - 1)| ≤ (C : ℝ)} := by
    have hE := measurableSet_le
      ((measurable_lastPassage x d).sub
        (measurable_lastPassage (x + (1, 0)) (d.1 - 1, d.2))).abs
      (measurable_const : Measurable (fun _ : LPPDifferentiability.Environment => (C : ℝ)))
    have hN := measurableSet_le
      ((measurable_lastPassage x d).sub
        (measurable_lastPassage (x + (0, 1)) (d.1, d.2 - 1))).abs
      (measurable_const : Measurable (fun _ : LPPDifferentiability.Environment => (C : ℝ)))
    exact (MeasurableSet.const _).inter ((MeasurableSet.const _).inter (hE.inter hN))
  unfold ConeBounds
  simp only [Set.ofPred_exists]
  refine MeasurableSet.iUnion fun C => MeasurableSet.iUnion fun N => ?_
  have hAll : MeasurableSet {ω : LPPDifferentiability.Environment |
      ∀ d : ℕ × ℕ, N ≤ d.1 + d.2 →
        (ε : ℝ) ≤ (d.1 : ℝ) / ((d.1 + d.2 : ℕ) : ℝ) →
        (d.1 : ℝ) / ((d.1 + d.2 : ℕ) : ℝ) ≤ 1 - (ε : ℝ) →
        0 < d.1 ∧ 0 < d.2 ∧
        |lastPassage ω x d - lastPassage ω (x + (1, 0)) (d.1 - 1, d.2)| ≤ (C : ℝ) ∧
        |lastPassage ω x d - lastPassage ω (x + (0, 1)) (d.1, d.2 - 1)| ≤ (C : ℝ)} := by
    simp only [Set.ofPred_forall]
    exact MeasurableSet.iInter fun d => MeasurableSet.iInter fun _ =>
      MeasurableSet.iInter fun _ => MeasurableSet.iInter fun _ => hPair C d
  exact (MeasurableSet.const _).inter hAll

private theorem measurableSet_all_coneBounds :
    MeasurableSet {ω : LPPDifferentiability.Environment |
      ∀ x : Lattice, ∀ ε : ℚ, 0 < ε → ε < 1 / 2 → ConeBounds ω x ε} := by
  simp only [Set.ofPred_forall]
  exact MeasurableSet.iInter fun x => MeasurableSet.iInter fun ε =>
    MeasurableSet.iInter fun _ => MeasurableSet.iInter fun _ => measurableSet_coneBounds x ε

private def interiorDirection (a : ℝ) (ha0 : 0 < a) (ha1 : a < 1) : InteriorDirection :=
  ⟨(⟨a, ha0.le⟩, ⟨1 - a, (sub_pos.mpr ha1).le⟩),
    by exact_mod_cast ha0, by exact_mod_cast (sub_pos.mpr ha1), by change a + (1 - a) = 1; ring⟩

/-- Original-law almost-sure uniform cone bounds, before measurable-event and
signed-shift closure assembly. The native fields and support brackets are
produced internally from the original weight-law assumptions.
Strong Existence, g602, lines 1663–1666. -/
theorem ae_uniform_interior_neighbor_bounds
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : LPPStatements.NotAPointMass μ)
    (hmoment : ∃ p : ℝ, 2 < p ∧
      (∫⁻ t, ENNReal.ofReal (|t| ^ p) ∂μ) < ∞) :
    ∀ᵐ ω : LPPDifferentiability.Environment ∂environmentLaw μ, ∀ x : Lattice, ∀ ε : ℚ,
        0 < ε → ε < 1 / 2 →
        ∃ C N : ℕ, 0 < N ∧
          ∀ d : ℕ × ℕ, N ≤ d.1 + d.2 →
            (ε : ℝ) ≤ (d.1 : ℝ) / ((d.1 + d.2 : ℕ) : ℝ) →
            (d.1 : ℝ) / ((d.1 + d.2 : ℕ) : ℝ) ≤ 1 - (ε : ℝ) →
            0 < d.1 ∧ 0 < d.2 ∧
            |lastPassage ω x d -
              lastPassage ω (x + ((1 : ℤ), (0 : ℤ))) (d.1 - 1, d.2)| ≤ (C : ℝ) ∧
            |lastPassage ω x d -
              lastPassage ω (x + ((0 : ℤ), (1 : ℤ))) (d.1, d.2 - 1)| ≤ (C : ℝ) := by
  classical
  -- The expected-rate witness follows from the original moment, not a shape premise.
  obtain ⟨p, hp, hpInt⟩ := hmoment
  have hMoment : ∃ p : ℝ, 2 < p ∧
      (∫⁻ t, ENNReal.ofReal (|t| ^ p) ∂μ) < ∞ := ⟨p, hp, hpInt⟩
  have hpos := (ProbabilityBasics.negative_moment_and_positive_tail_of_absolute_moment
    μ hp hpInt).2
  have hneg := ProbabilityBasics.integrated_sqrt_lower_tail_lt_top_of_absolute_moment
    μ hp hpInt
  obtain ⟨g, hgData, _⟩ := exists_unique_lastPassage_real_expected_rate_of_martin_tails
    μ hneg hpos
  have hg : IsExpectedRateShape μ g := hgData.1
  have hnonconstant : ¬ ∃ c : ℝ, ∀ᵐ t ∂μ, t = c :=
    (LPPStatements.notAPointMass_iff_not_ae_const μ).mp hμ
  obtain ⟨hgcont, hhom, hconc⟩ :=
    expected_rate_shape_geometry_of_absolute_moment μ g hMoment hg
  obtain ⟨hL, hR, leftEndpoint, rightEndpoint, hExtreme, hInterval⟩ :=
    exists_native_extreme_tilts_and_face_endpoints μ hμ hMoment g hg
  -- Retain one native law and the actual minus field at every selected support.
  obtain ⟨P, Bm, Bp, E, hP, hMarginal, hShiftMap, hMeasM, _, _, hInt, hMeans,
    hEMeas, hEProb, _, hCoc, hRec, _⟩ := exists_native_full_family μ hμ hMoment g hg
  let : IsProbabilityMeasure P := ⟨hP⟩
  have hShift (z : Lattice) : MeasurePreserving (processShift z) P P :=
    ⟨measurable_processShift z, hShiftMap z⟩
  have hBm := cocycle_and_recovery_ae_of_full_event g P Bm E hEMeas hEProb hMeasM
    (fun s hs h x y z => ⟨(hCoc s hs h x y z).1, (hCoc s hs h x y z).2.2.1⟩)
    (fun s hs h => (hRec s hs h).1)
  have hBmInt (h : SupportTilt g) (x y : Lattice) : Integrable (Bm h x y) P :=
    (hInt h x y).1
  have hBmMean (h : SupportTilt g) (j : Fin 2) :
      (∫ s, Bm h 0 (finiteEdgeStep j) s ∂P) = -finiteTiltCoordinate h.1 j := by
    fin_cases j
    · simpa [finiteEdgeStep, finiteTiltCoordinate] using (hMeans h 0).1
    · simpa [finiteEdgeStep, finiteTiltCoordinate] using (hMeans h 0).2.2.1
  -- Only two AE comparisons per rational margin are intersected.
  have hEach (ε : ℚ) : ∀ᵐ s ∂P, ∀ x : Lattice,
      0 < ε → ε < 1 / 2 → ConeBounds (processEnvironment s) x ε := by
    by_cases hε : 0 < ε ∧ ε < 1 / 2
    · have he0 : 0 < (ε : ℝ) := by exact_mod_cast hε.1
      have heHalf : (ε : ℝ) < 1 / 2 := by
        have hCast : (ε : ℝ) < ((1 / 2 : ℚ) : ℝ) :=
          (Rat.cast_lt (K := ℝ)).mpr hε.2
        simpa only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using hCast
      let qL := interiorDirection (ε : ℝ) he0 (by linarith only [heHalf])
      let qR := interiorDirection (1 - (ε : ℝ)) (by linarith only [heHalf])
        (by linarith only [he0])
      have hl0 : 0 < ((leftEndpoint qL).1.1 : ℝ) :=
        NNReal.coe_pos.mpr (leftEndpoint qL).2.1
      have hl1 : ((leftEndpoint qL).1.1 : ℝ) < 1 := by
        have h2 : 0 < ((leftEndpoint qL).1.2 : ℝ) :=
          NNReal.coe_pos.mpr (leftEndpoint qL).2.2.1
        linarith only [(leftEndpoint qL).2.2.2, h2]
      have hr0 : 0 < ((rightEndpoint qR).1.1 : ℝ) :=
        NNReal.coe_pos.mpr (rightEndpoint qR).2.1
      have hr1 : ((rightEndpoint qR).1.1 : ℝ) < 1 := by
        have h2 : 0 < ((rightEndpoint qR).1.2 : ℝ) :=
          NNReal.coe_pos.mpr (rightEndpoint qR).2.2.1
        linarith only [(rightEndpoint qR).2.2.2, h2]
      let tL := interiorDirection (((leftEndpoint qL).1.1 : ℝ) / 2)
        (by positivity) (by linarith only [hl1])
      let tR := interiorDirection ((((rightEndpoint qR).1.1 : ℝ) + 1) / 2)
        (by linarith only [hr0]) (by linarith only [hr1])
      have hLeftFace : ∀ ζ ∈ supportFace g (hL qL),
          ((leftEndpoint qL).1.1 : ℝ) ≤ (ζ.1.1 : ℝ) := by
        intro ζ hζ
        exact_mod_cast ((hInterval qL ζ).mp (Or.inl hζ)).1
      have hRightFace : ∀ ζ ∈ supportFace g (hR qR),
          (ζ.1.1 : ℝ) ≤ ((rightEndpoint qR).1.1 : ℝ) := by
        intro ζ hζ
        exact_mod_cast ((hInterval qR ζ).mp (Or.inr hζ)).2
      have hGapL := support_tilt_strict_axis_gaps_of_absolute_moment
        μ hMoment hnonconstant g hg (hL tL)
      have hGapR := support_tilt_strict_axis_gaps_of_absolute_moment
        μ hMoment hnonconstant g hg (hR tR)
      obtain ⟨θL, _, hθL1, hθLq, hθLface⟩ :=
        exists_strict_threshold_left_of_minimal_support_face
          g hgcont hconc hhom qL (leftEndpoint qL) tL (hL qL) (hL tL)
          (hExtreme qL).1 (fun k hk => ((hExtreme qL).2.2 k hk).1)
          hLeftFace (hExtreme tL).1
          (by change ((leftEndpoint qL).1.1 : ℝ) / 2 < _; linarith only [hl0])
          hGapL.1 hGapL.2
      obtain ⟨θR, hθR0, hθR1, hqθR, hθRface⟩ :=
        exists_strict_threshold_right_of_maximal_support_face
          g hgcont hconc hhom qR (rightEndpoint qR) tR (hR qR) (hR tR)
          (hExtreme qR).2.1 (fun k hk => ((hExtreme qR).2.2 k hk).2)
          hRightFace (hExtreme tR).2.1
          (by change _ < (((rightEndpoint qR).1.1 : ℝ) + 1) / 2; linarith only [hr1])
          hGapR.1 hGapR.2
      have hθL0 : 0 < θL :=
        lt_trans (NNReal.coe_pos.mpr tL.2.1) (hθLface tL (hExtreme tL).1)
      change θL < (ε : ℝ) at hθLq
      change 1 - (ε : ℝ) < θR at hqθR
      have hLeft := ae_native_uniform_passage_difference_bounds_right_of_support_face
        μ hMoment hnonconstant P hMarginal hShift (Bm (hL tL))
        (hBm (hL tL)).1 (hBmInt (hL tL)) (hBm (hL tL)).2
        g hg tL (hL tL) (hExtreme tL).1
        (Or.inl (fun k hk => ((hExtreme tL).2.2 k hk).1)) (hBmMean (hL tL))
        θL hθL0 hθL1.le hθLface
      have hRight := ae_native_uniform_passage_difference_bounds_left_of_support_face
        μ hMoment hnonconstant P hMarginal hShift (Bm (hR tR))
        (hBm (hR tR)).1 (hBmInt (hR tR)) (hBm (hR tR)).2
        g hg tR (hR tR) (hExtreme tR).2.1
        (Or.inr (fun k hk => ((hExtreme tR).2.2 k hk).2)) (hBmMean (hR tR))
        θR hθR0 hθR1 hθRface
      filter_upwards [hLeft, hRight] with s hsLeft hsRight
      intro x _ _
      obtain ⟨NL, hNL⟩ := hsLeft x
      obtain ⟨NR, hNR⟩ := hsRight x
      let aE := Bm (hL tL) x (x + (1, 0)) s
      let bE := Bm (hR tR) x (x + (1, 0)) s
      let aN := Bm (hL tL) x (x + (0, 1)) s
      let bN := Bm (hR tR) x (x + (0, 1)) s
      obtain ⟨C, hC⟩ := exists_nat_gt (|aE| + |bE| + |aN| + |bN|)
      have haE : |aE| ≤ (C : ℝ) := by
        linarith only [hC, abs_nonneg bE, abs_nonneg aN, abs_nonneg bN]
      have hbE : |bE| ≤ (C : ℝ) := by
        linarith only [hC, abs_nonneg aE, abs_nonneg aN, abs_nonneg bN]
      have haN : |aN| ≤ (C : ℝ) := by
        linarith only [hC, abs_nonneg aE, abs_nonneg bE, abs_nonneg bN]
      have hbN : |bN| ≤ (C : ℝ) := by
        linarith only [hC, abs_nonneg aE, abs_nonneg bE, abs_nonneg aN]
      refine ⟨C, max NL NR + 1, by omega, ?_⟩
      intro d hd hLow hHigh
      have hlen : 0 < d.1 + d.2 := by omega
      have hden : 0 < ((d.1 + d.2 : ℕ) : ℝ) := by exact_mod_cast hlen
      have hLow' := (le_div_iff₀ hden).mp hLow
      have hHigh' := (div_le_iff₀ hden).mp hHigh
      have hprod : 0 < (ε : ℝ) * ((d.1 + d.2 : ℕ) : ℝ) := mul_pos he0 hden
      have hd1 : 0 < d.1 := by exact_mod_cast (lt_of_lt_of_le hprod hLow')
      have hd2 : 0 < d.2 := by
        have hcast : ((d.1 + d.2 : ℕ) : ℝ) = (d.1 : ℝ) + (d.2 : ℝ) := Nat.cast_add _ _
        have hpos : 0 < (d.2 : ℝ) := by nlinarith only [hHigh', hprod, hcast]
        exact_mod_cast hpos
      have hLBounds := hNL d (by omega) (hθLq.le.trans hLow)
      have hRBounds := hNR d (by omega) (hHigh.trans hqθR.le)
      have hEastLo : bE ≤ lastPassage (processEnvironment s) x d -
          lastPassage (processEnvironment s) (x + (1, 0)) (d.1 - 1, d.2) :=
        hRBounds.2.1 hd1
      have hEastHi : lastPassage (processEnvironment s) x d -
          lastPassage (processEnvironment s) (x + (1, 0)) (d.1 - 1, d.2) ≤ aE :=
        hLBounds.2.1 hd1
      have hNorthLo : aN ≤ lastPassage (processEnvironment s) x d -
          lastPassage (processEnvironment s) (x + (0, 1)) (d.1, d.2 - 1) :=
        hLBounds.2.2 hd2
      have hNorthHi : lastPassage (processEnvironment s) x d -
          lastPassage (processEnvironment s) (x + (0, 1)) (d.1, d.2 - 1) ≤ bN :=
        hRBounds.2.2 hd2
      exact ⟨hd1, hd2,
        abs_le.mpr ⟨(abs_le.mp hbE).1.trans hEastLo, hEastHi.trans (abs_le.mp haE).2⟩,
        abs_le.mpr ⟨(abs_le.mp haN).1.trans hNorthLo, hNorthHi.trans (abs_le.mp hbN).2⟩⟩
    · exact ae_of_all P (fun _s _x h0 h1 => False.elim (hε ⟨h0, h1⟩))
  have hCommon : ∀ᵐ s ∂P, ∀ ε : ℚ, ∀ x : Lattice,
      0 < ε → ε < 1 / 2 → ConeBounds (processEnvironment s) x ε :=
    ae_all_iff.mpr hEach
  have hNative : ∀ᵐ s ∂P, ∀ x : Lattice, ∀ ε : ℚ,
      0 < ε → ε < 1 / 2 → ConeBounds (processEnvironment s) x ε := by
    filter_upwards [hCommon] with s hs
    intro x ε
    exact hs ε x
  have hTransfer : ∀ᵐ ω : LPPDifferentiability.Environment ∂P.map processEnvironment,
      ∀ x : Lattice, ∀ ε : ℚ, 0 < ε → ε < 1 / 2 → ConeBounds ω x ε :=
    (ae_map_iff (measurable_fst : Measurable processEnvironment).aemeasurable
      measurableSet_all_coneBounds).mpr hNative
  rw [hMarginal] at hTransfer
  exact hTransfer

end LPP.Busemann
