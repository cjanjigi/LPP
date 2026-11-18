/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Busemann.Process.NativeOrderedSeed
public import LPP_Foundations.Statements.ShapeDefinitions
public import LPP_Foundations.Statements.WeightMoments
public import Busemann.Process.BackwardIndependence
public import Busemann.Frozen.Definitions.Recovery
import Busemann.Geometry.DenseOrderedTilts
import Busemann.Process.EnvelopeCocycles
import Busemann.Process.UnitEnvelopeMeans
import Busemann.Process.EnvelopeContinuity
import Busemann.Process.EnvelopeFutureIndependence
import Mathlib.Tactic

/-! The native full tilt family on one ordered weak-limit law. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter LPPDifferentiability
open scoped BigOperators ENNReal Topology

namespace LPP.Busemann

/-- The original native moment assumptions give one full tilt family with the
process clauses of JR1810.03580v3, Theorem 4.8 after (4.18)-(4.20). Geometry and
endpoint squeezing are separate conclusions and are not asserted here. -/
theorem exists_native_full_family
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : LPPStatements.NotAPointMass μ)
    (hmoment : LPPStatements.HasAbsoluteMomentAbove μ 2)
    (g : Quadrant → ℝ) (hg : IsExpectedRateShape μ g) :
    ∃ (P : Measure ProcessSample)
      (Bminus Bplus : SupportTilt g → Lattice → Lattice → ProcessSample → ℝ)
      (C : Set ProcessSample),
      P Set.univ = 1 ∧
      P.map processEnvironment = environmentLaw μ ∧
      (∀ z : Lattice, P.map (processShift z) = P) ∧
      Measurable (fun q : SupportTilt g × (Lattice × (Lattice × ProcessSample)) =>
        Bminus q.1 q.2.1 q.2.2.1 q.2.2.2) ∧
      Measurable (fun q : SupportTilt g × (Lattice × (Lattice × ProcessSample)) =>
        Bplus q.1 q.2.1 q.2.2.1 q.2.2.2) ∧
      HasBackwardIndependence g P Bminus Bplus ∧
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
          Bminus h x y s = Bplus h x y s) := by
  classical
  -- Choose the native dense family once and retain its actual cofinal data.
  obtain ⟨D, _, hDenseApprox⟩ :=
    exists_dense_ordered_support_family_of_absolute_moment μ hmoment hμ g hg
  have happrox : ∀ h : SupportTilt g, ∃ a b : ℕ → ℕ,
      StrictMono (fun n => (D (a n)).1.1) ∧
      StrictAnti (fun n => (D (b n)).1.1) ∧
      (∀ n, (D (a n)).1.1 < h.1.1 ∧ h.1.1 < (D (b n)).1.1) ∧
      Tendsto (fun n => (D (a n)).1) atTop (𝓝 h.1) ∧
      Tendsto (fun n => (D (b n)).1) atTop (𝓝 h.1) := by
    intro h
    obtain ⟨a, b, hma, hmb, hab, hla, hlb, _⟩ := hDenseApprox h
    exact ⟨a, b, hma, hmb, hab, hla, hlb⟩
  -- This single native witness supplies the law, raw means and whole raw future law.
  obtain ⟨P, _, _, _, _, hMarginal, hShift, hRaw, _, _, _, _,
    C0, hC0Def, hC0Meas, hC0Prob, _, _, _, hRawIndep, _, _, _, hQProb⟩ :=
      exists_native_ordered_countable_seed μ hmoment g hg D
  -- Use the retained event's exact characterization; no event is reselected.
  subst C0
  let X : ℕ → Lattice → Fin 2 → ProcessSample → ℝ :=
    fun j x i s => s.2 j x i
  let Q : Set ProcessSample := {s | ∀ j k x,
    (D j).1.1 ≤ (D k).1.1 →
      X k x 0 s ≤ X j x 0 s ∧ X j x 1 s ≤ X k x 1 s}
  let Eminus : SupportTilt g → Lattice → Fin 2 → ProcessSample → EReal :=
    fun h x i s => if i = 0 then
      ⨅ j, if (D j).1.1 < h.1.1 then (X j x i s : EReal) else ⊤
    else ⨆ j, if (D j).1.1 < h.1.1 then (X j x i s : EReal) else ⊥
  let Eplus : SupportTilt g → Lattice → Fin 2 → ProcessSample → EReal :=
    fun h x i s => if i = 0 then
      ⨆ j, if h.1.1 < (D j).1.1 then (X j x i s : EReal) else ⊥
    else ⨅ j, if h.1.1 < (D j).1.1 then (X j x i s : EReal) else ⊤
  let eMinus := fun h x i s => (Eminus h x i s).toReal
  let ePlus := fun h x i s => (Eplus h x i s).toReal
  let S : (ℤ → ℝ) → ℤ → ℤ → ℝ := fun f a b =>
    if a ≤ b then ∑ k ∈ Finset.Ico a b, f k
    else -(∑ k ∈ Finset.Ico b a, f k)
  let Rminus : SupportTilt g → Lattice → Lattice → ProcessSample → ℝ :=
    fun h x y s =>
      S (fun k => eMinus h (k, x.2) 0 s) x.1 y.1 +
        S (fun k => eMinus h (y.1, k) 1 s) x.2 y.2
  let Rplus : SupportTilt g → Lattice → Lattice → ProcessSample → ℝ :=
    fun h x y s =>
      S (fun k => ePlus h (k, x.2) 0 s) x.1 y.1 +
        S (fun k => ePlus h (y.1, k) 1 s) x.2 y.2
  let C0 : Set ProcessSample := {s |
    (∀ j x, X j x 0 s + X j (x + (1, 0)) 1 s =
      X j x 1 s + X j (x + (0, 1)) 0 s) ∧
    (∀ j x, min (X j x 0 s) (X j x 1 s) = s.1 x)}
  let C : Set ProcessSample := C0 ∩ Q
  obtain ⟨_, _, _, _, _, _, _, hWithinUnit, hCrossUnit, _, _⟩ :=
    countable_unit_envelopes_measurable_finite_and_cofinal g D happrox
  obtain ⟨hCMeas, hCShift, hRminusMeas, hRplusMeas, hUnitMinusRaw, hUnitPlusRaw, hOnC⟩ :=
    envelope_signed_cocycle_reconstruction g D happrox
  have hUnitMinus (s : ProcessSample) (h : SupportTilt g) (x : Lattice) :
      Rminus h x (x + (1, 0)) s = eMinus h x 0 s ∧
      Rminus h x (x + (0, 1)) s = eMinus h x 1 s := hUnitMinusRaw s h x
  have hUnitPlus (s : ProcessSample) (h : SupportTilt g) (x : Lattice) :
      Rplus h x (x + (1, 0)) s = ePlus h x 0 s ∧
      Rplus h x (x + (0, 1)) s = ePlus h x 1 s := hUnitPlusRaw s h x
  obtain ⟨hUnitData, hFixedUnit⟩ :=
    unit_envelope_means_and_fixed_tilt_equality g D happrox (P : Measure ProcessSample)
      (fun j x i => (hRaw j x i).1) (fun j x i => (hRaw j x i).2) hQProb
  have hCProb : (P : Measure ProcessSample) C = 1 := by
    calc
      _ = (P : Measure ProcessSample) Q :=
        Measure.measure_inter_eq_of_ae ((mem_ae_iff_prob_eq_one hC0Meas).2 hC0Prob)
      _ = 1 := hQProb
  -- Reuse the proved integrability theorem for the literal signed path sums.
  have hIntMinus : ∀ h x y, Integrable (Rminus h x y) (P : Measure ProcessSample) :=
    integrable_lattice_coordinate_path_sum (P : Measure ProcessSample) eMinus
      (fun h x i => (hUnitData h x i).1)
  have hIntPlus : ∀ h x y, Integrable (Rplus h x y) (P : Measure ProcessSample) :=
    integrable_lattice_coordinate_path_sum (P : Measure ProcessSample) ePlus
      (fun h x i => (hUnitData h x i).2.1)
  have hMeans : ∀ h : SupportTilt g, ∀ x : Lattice,
      (∫ s, Rminus h x (x + (1, 0)) s ∂(P : Measure ProcessSample)) = -h.1.1 ∧
      (∫ s, Rplus h x (x + (1, 0)) s ∂(P : Measure ProcessSample)) = -h.1.1 ∧
      (∫ s, Rminus h x (x + (0, 1)) s ∂(P : Measure ProcessSample)) = -h.1.2 ∧
      (∫ s, Rplus h x (x + (0, 1)) s ∂(P : Measure ProcessSample)) = -h.1.2 := by
    intro h x
    refine ⟨?_, ?_, ?_, ?_⟩
    · calc
        _ = ∫ s, eMinus h x 0 s ∂(P : Measure ProcessSample) :=
          integral_congr_ae (ae_of_all _ fun s => (hUnitMinus s h x).1)
        _ = -h.1.1 := (hUnitData h x 0).2.2.1
    · calc
        _ = ∫ s, ePlus h x 0 s ∂(P : Measure ProcessSample) :=
          integral_congr_ae (ae_of_all _ fun s => (hUnitPlus s h x).1)
        _ = -h.1.1 := (hUnitData h x 0).2.2.2
    · calc
        _ = ∫ s, eMinus h x 1 s ∂(P : Measure ProcessSample) :=
          integral_congr_ae (ae_of_all _ fun s => (hUnitMinus s h x).2)
        _ = -h.1.2 := (hUnitData h x 1).2.2.1
    · calc
        _ = ∫ s, ePlus h x 1 s ∂(P : Measure ProcessSample) :=
          integral_congr_ae (ae_of_all _ fun s => (hUnitPlus s h x).2)
        _ = -h.1.2 := (hUnitData h x 1).2.2.2
  have hFuture : HasBackwardIndependence g (P : Measure ProcessSample) Rminus Rplus :=
    envelope_cocycles_future_indep_past g D happrox (P : Measure ProcessSample) hRawIndep
  obtain ⟨hBelow, hAbove, hEqual⟩ := signed_envelopes_tendsto g D happrox
  -- Equality is asserted on a full event for each FIXED h, not one event over all h.
  have hFixed : ∀ h : SupportTilt g, ∃ E : Set ProcessSample,
      MeasurableSet E ∧ E ⊆ C ∧ (P : Measure ProcessSample) E = 1 ∧
      ∀ s ∈ E, ∀ x y : Lattice, Rminus h x y s = Rplus h x y s := by
    intro h
    obtain ⟨E, hEmeas, hEQ, hEprob, hEunit⟩ := hFixedUnit h
    refine ⟨C0 ∩ E, hC0Meas.inter hEmeas, ?_, ?_, ?_⟩
    · rintro s ⟨hs0, hsE⟩
      exact ⟨hs0, hEQ hsE⟩
    · calc
        (P : Measure ProcessSample) (C0 ∩ E) = (P : Measure ProcessSample) E :=
          Measure.measure_inter_eq_of_ae ((mem_ae_iff_prob_eq_one hC0Meas).2 hC0Prob)
        _ = 1 := hEprob
    · intro s hs x y
      have he : ∀ x i, eMinus h x i s = ePlus h x i s := hEunit s hs.2
      simp only [Rminus, Rplus, S, he]
  refine ⟨(P : Measure ProcessSample), Rminus, Rplus, C,
    measure_univ, hMarginal, ?_, hRminusMeas, hRplusMeas, hFuture,
    ?_, hMeans, hCMeas, hCProb, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hFixed⟩
  · intro z
    exact (hShift z).map_eq
  · intro h x y
    exact ⟨hIntMinus h x y, hIntPlus h x y⟩
  · intro z s hs
    exact (hCShift z s).2 hs
  · intro s hs h x y z
    obtain ⟨hCovM, hCovP, hAddM, hAddP, _, _⟩ := hOnC s hs h
    exact ⟨hCovM x y z, hCovP x y z, hAddM x y z, hAddP x y z⟩
  · intro s hs h
    obtain ⟨_, _, _, _, hRecM, hRecP⟩ := hOnC s hs h
    exact ⟨hRecM, hRecP⟩
  · intro s hs h x
    rw [(hUnitMinus s h x).1, (hUnitPlus s h x).1,
      (hUnitMinus s h x).2, (hUnitPlus s h x).2]
    exact hWithinUnit s hs.2 h x
  · intro s hs h k hhk x
    rw [(hUnitPlus s h x).1, (hUnitMinus s k x).1,
      (hUnitPlus s h x).2, (hUnitMinus s k x).2]
    exact hCrossUnit s hs.2 h k hhk x
  · intro s hs h x y v hv hlim
    exact hBelow s hs.2 h x y v hv hlim
  · intro s hs h x y v hv hlim
    exact hAbove s hs.2 h x y v hv hlim
  · intro s hs h x y heq v hlim
    exact hEqual s hs.2 h x y heq v hlim

end LPP.Busemann
