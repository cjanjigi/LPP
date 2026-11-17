/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Busemann.Process.UnitEnvelopes
public import Busemann.Frozen.Definitions.FiniteTiltCoordinate
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic

/-! Means and fixed-tilt equality of literal countable unit envelopes. -/

@[expose] public section

open MeasureTheory Filter LPPDifferentiability
open scoped Topology

namespace LPP.Busemann

private theorem abs_bound_of_bracket (a b v : ℝ)
    (hv : (a ≤ v ∧ v ≤ b) ∨ (b ≤ v ∧ v ≤ a)) : |v| ≤ |a| + |b| := by
  apply abs_le.mpr
  have ha := le_abs_self a
  have hb := le_abs_self b
  have hna := neg_abs_le a
  have hnb := neg_abs_le b
  have ha0 := abs_nonneg a
  have hb0 := abs_nonneg b
  rcases hv with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> constructor <;> linarith

/-- Integrable ordered raw unit fields with their exact means yield integrable
one-sided unit envelopes with those means and equality on a full event for
each fixed tilt, following the monotone-convergence step in the proof of
JR arXiv:1810.03580v3, Theorem 4.8. -/
theorem unit_envelope_means_and_fixed_tilt_equality
(g : Quadrant → ℝ) (D : ℕ → SupportTilt g)
(happrox : ∀ h : SupportTilt g, ∃ a b : ℕ → ℕ,
  StrictMono (fun n => (D (a n)).1.1) ∧ StrictAnti (fun n => (D (b n)).1.1) ∧
  (∀ n, (D (a n)).1.1 < h.1.1 ∧ h.1.1 < (D (b n)).1.1) ∧
  Tendsto (fun n => (D (a n)).1) atTop (𝓝 h.1) ∧
  Tendsto (fun n => (D (b n)).1) atTop (𝓝 h.1))
(P : Measure ProcessSample) [IsProbabilityMeasure P]
(hInt : ∀ j x i, Integrable (fun s : ProcessSample => s.2 j x i) P)
(hMean : ∀ j x i, (∫ s : ProcessSample, s.2 j x i ∂P) = -finiteTiltCoordinate (D j).1 i)
(hQ : P {s : ProcessSample | ∀ j k x, (D j).1.1 ≤ (D k).1.1 →
  s.2 k x 0 ≤ s.2 j x 0 ∧ s.2 j x 1 ≤ s.2 k x 1} = 1) :
let X : ℕ → Lattice → Fin 2 → ProcessSample → ℝ := fun j x i s => s.2 j x i
let Q : Set ProcessSample := {s | ∀ j k x,
  (D j).1.1 ≤ (D k).1.1 → X k x 0 s ≤ X j x 0 s ∧ X j x 1 s ≤ X k x 1 s}
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
(∀ h x i, Integrable (eMinus h x i) P ∧ Integrable (ePlus h x i) P ∧
  (∫ s, eMinus h x i s ∂P) = -finiteTiltCoordinate h.1 i ∧
  (∫ s, ePlus h x i s ∂P) = -finiteTiltCoordinate h.1 i) ∧
(∀ h, ∃ E : Set ProcessSample, MeasurableSet E ∧ E ⊆ Q ∧ P E = 1 ∧
  ∀ s ∈ E, ∀ x i, eMinus h x i s = ePlus h x i s)
 := by
  classical
  let X : ℕ → Lattice → Fin 2 → ProcessSample → ℝ := fun j x i s => s.2 j x i
  let Q : Set ProcessSample := {s | ∀ j k x,
    (D j).1.1 ≤ (D k).1.1 → X k x 0 s ≤ X j x 0 s ∧ X j x 1 s ≤ X k x 1 s}
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
  have hknown := countable_unit_envelopes_measurable_finite_and_cofinal g D happrox
  obtain ⟨hQmeas, _, _, _, hMm, hPm, hfinite, hwithin, _, hlower, hupper⟩ := hknown
  have hQae : ∀ᵐ s ∂P, s ∈ Q := (mem_ae_iff_prob_eq_one hQmeas).2 hQ
  have hsecM (h : SupportTilt g) (x : Lattice) (i : Fin 2) : Measurable (eMinus h x i) := by
    have hm : Measurable (fun s : ProcessSample => (h, x, i, s)) := by fun_prop
    exact hMm.comp hm
  have hsecP (h : SupportTilt g) (x : Lattice) (i : Fin 2) : Measurable (ePlus h x i) := by
    have hm : Measurable (fun s : ProcessSample => (h, x, i, s)) := by fun_prop
    exact hPm.comp hm
  change (∀ h x i, Integrable (eMinus h x i) P ∧ Integrable (ePlus h x i) P ∧
    (∫ s, eMinus h x i s ∂P) = -finiteTiltCoordinate h.1 i ∧
    (∫ s, ePlus h x i s ∂P) = -finiteTiltCoordinate h.1 i) ∧
    (∀ h, ∃ E : Set ProcessSample, MeasurableSet E ∧ E ⊆ Q ∧ P E = 1 ∧
      ∀ s ∈ E, ∀ x i, eMinus h x i s = ePlus h x i s)
  have hresult (h : SupportTilt g) (x : Lattice) (i : Fin 2) :
      Integrable (eMinus h x i) P ∧ Integrable (ePlus h x i) P ∧
      (∫ s, eMinus h x i s ∂P) = -finiteTiltCoordinate h.1 i ∧
      (∫ s, ePlus h x i s ∂P) = -finiteTiltCoordinate h.1 i := by
    obtain ⟨a, b, hma, hmb, hab, hla, hlb⟩ := happrox h
    let bound : ProcessSample → ℝ := fun s => |X (a 0) x i s| + |X (b 0) x i s|
    have hboundInt : Integrable bound P := ((hInt (a 0) x i).abs).add ((hInt (b 0) x i).abs)
    -- Both actual dense sequences stay between the same two raw values.
    have hbracket (s : ProcessSample) (hs : s ∈ Q) (n : ℕ) :
        ((X (a 0) x i s ≤ X (a n) x i s ∧ X (a n) x i s ≤ X (b 0) x i s) ∨
          (X (b 0) x i s ≤ X (a n) x i s ∧ X (a n) x i s ≤ X (a 0) x i s)) ∧
        ((X (a 0) x i s ≤ X (b n) x i s ∧ X (b n) x i s ≤ X (b 0) x i s) ∨
          (X (b 0) x i s ≤ X (b n) x i s ∧ X (b n) x i s ≤ X (a 0) x i s)) := by
      have haa : (D (a 0)).1.1 ≤ (D (a n)).1.1 := hma.monotone (Nat.zero_le n)
      have hbb : (D (b n)).1.1 ≤ (D (b 0)).1.1 := hmb.antitone (Nat.zero_le n)
      have hab0 : (D (a 0)).1.1 ≤ (D (b n)).1.1 := ((hab 0).1.trans (hab n).2).le
      have hanb : (D (a n)).1.1 ≤ (D (b 0)).1.1 := ((hab n).1.trans (hab 0).2).le
      fin_cases i
      · exact ⟨Or.inr ⟨(hs (a n) (b 0) x hanb).1, (hs (a 0) (a n) x haa).1⟩,
          Or.inr ⟨(hs (b n) (b 0) x hbb).1, (hs (a 0) (b n) x hab0).1⟩⟩
      · exact ⟨Or.inl ⟨(hs (a 0) (a n) x haa).2, (hs (a n) (b 0) x hanb).2⟩,
          Or.inl ⟨(hs (a 0) (b n) x hab0).2, (hs (b n) (b 0) x hbb).2⟩⟩
    have hlimA : ∀ᵐ s ∂P, Tendsto (fun n => X (a n) x i s) atTop (𝓝 (eMinus h x i s)) := by
      filter_upwards [hQae] with s hs
      exact hlower s hs h a hma (fun n => (hab n).1) hla x i
    have hlimB : ∀ᵐ s ∂P, Tendsto (fun n => X (b n) x i s) atTop (𝓝 (ePlus h x i s)) := by
      filter_upwards [hQae] with s hs
      exact hupper s hs h b hmb (fun n => (hab n).2) hlb x i
    have hlimBoundA : ∀ᵐ s ∂P, ‖eMinus h x i s‖ ≤ bound s := by
      filter_upwards [hQae] with s hs
      have hlim := hlower s hs h a hma (fun n => (hab n).1) hla x i
      have ha : ∀ n, |X (a n) x i s| ≤ bound s := fun n =>
        abs_bound_of_bracket _ _ _ (hbracket s hs n).1
      have ht : Tendsto (fun n => |X (a n) x i s|) atTop (𝓝 |eMinus h x i s|) := hlim.abs
      simpa only [Real.norm_eq_abs] using le_of_tendsto' ht ha
    have hlimBoundB : ∀ᵐ s ∂P, ‖ePlus h x i s‖ ≤ bound s := by
      filter_upwards [hQae] with s hs
      have hlim := hupper s hs h b hmb (fun n => (hab n).2) hlb x i
      have hb : ∀ n, |X (b n) x i s| ≤ bound s := fun n =>
        abs_bound_of_bracket _ _ _ (hbracket s hs n).2
      have ht : Tendsto (fun n => |X (b n) x i s|) atTop (𝓝 |ePlus h x i s|) := hlim.abs
      simpa only [Real.norm_eq_abs] using le_of_tendsto' ht hb
    have hMi : Integrable (eMinus h x i) P := hboundInt.mono' (hsecM h x i).aestronglyMeasurable hlimBoundA
    have hPi : Integrable (ePlus h x i) P := hboundInt.mono' (hsecP h x i).aestronglyMeasurable hlimBoundB
    -- Use the samplewise order of the raw fields with the same monotone
    -- convergence theorem as the envelope-mean step in JR Theorem 4.8.
    have hmeanA_lim : Tendsto (fun n => ∫ s, X (a n) x i s ∂P) atTop
        (𝓝 (∫ s, eMinus h x i s ∂P)) := by
      fin_cases i
      · refine integral_tendsto_of_tendsto_of_antitone
          (fun n => hInt (a n) x 0) hMi ?_ hlimA
        filter_upwards [hQae] with s hs
        intro n m hnm
        exact (hs (a n) (a m) x (hma.monotone hnm)).1
      · refine integral_tendsto_of_tendsto_of_monotone
          (fun n => hInt (a n) x 1) hMi ?_ hlimA
        filter_upwards [hQae] with s hs
        intro n m hnm
        exact (hs (a n) (a m) x (hma.monotone hnm)).2
    have hmeanB_lim : Tendsto (fun n => ∫ s, X (b n) x i s ∂P) atTop
        (𝓝 (∫ s, ePlus h x i s ∂P)) := by
      fin_cases i
      · refine integral_tendsto_of_tendsto_of_monotone
          (fun n => hInt (b n) x 0) hPi ?_ hlimB
        filter_upwards [hQae] with s hs
        intro n m hnm
        exact (hs (b m) (b n) x (hmb.antitone hnm)).1
      · refine integral_tendsto_of_tendsto_of_antitone
          (fun n => hInt (b n) x 1) hPi ?_ hlimB
        filter_upwards [hQae] with s hs
        intro n m hnm
        exact (hs (b m) (b n) x (hmb.antitone hnm)).2
    have htiltA : Tendsto (fun n => -finiteTiltCoordinate (D (a n)).1 i) atTop
        (𝓝 (-finiteTiltCoordinate h.1 i)) := by
      fin_cases i
      · simpa [finiteTiltCoordinate] using ((continuous_fst.tendsto h.1).comp hla).neg
      · simpa [finiteTiltCoordinate] using ((continuous_snd.tendsto h.1).comp hla).neg
    have htiltB : Tendsto (fun n => -finiteTiltCoordinate (D (b n)).1 i) atTop
        (𝓝 (-finiteTiltCoordinate h.1 i)) := by
      fin_cases i
      · simpa [finiteTiltCoordinate] using ((continuous_fst.tendsto h.1).comp hlb).neg
      · simpa [finiteTiltCoordinate] using ((continuous_snd.tendsto h.1).comp hlb).neg
    have hseqA : (fun n => ∫ s, X (a n) x i s ∂P) =
        (fun n => -finiteTiltCoordinate (D (a n)).1 i) := by funext n; exact hMean (a n) x i
    have hseqB : (fun n => ∫ s, X (b n) x i s ∂P) =
        (fun n => -finiteTiltCoordinate (D (b n)).1 i) := by funext n; exact hMean (b n) x i
    rw [hseqA] at hmeanA_lim
    rw [hseqB] at hmeanB_lim
    exact ⟨hMi, hPi, tendsto_nhds_unique hmeanA_lim htiltA,
      tendsto_nhds_unique hmeanB_lim htiltB⟩
  refine ⟨hresult, ?_⟩
  intro h
  let E : Set ProcessSample := Q ∩ ⋂ x : Lattice, ⋂ i : Fin 2,
    {s | eMinus h x i s = ePlus h x i s}
  have hEmeas : MeasurableSet E := by
    apply hQmeas.inter
    exact MeasurableSet.iInter fun x => MeasurableSet.iInter fun i =>
      measurableSet_eq_fun (hsecM h x i) (hsecP h x i)
  have heq (x : Lattice) (i : Fin 2) : ∀ᵐ s ∂P, eMinus h x i s = ePlus h x i s := by
    fin_cases i
    · have hle : ePlus h x 0 ≤ᵐ[P] eMinus h x 0 := by
        filter_upwards [hQae] with s hs
        exact (hwithin s hs h x).1
      have hi := hresult h x 0
      exact ((integral_eq_iff_of_ae_le hi.2.1 hi.1 hle).1 (hi.2.2.2.trans hi.2.2.1.symm)).symm
    · have hle : eMinus h x 1 ≤ᵐ[P] ePlus h x 1 := by
        filter_upwards [hQae] with s hs
        exact (hwithin s hs h x).2
      have hi := hresult h x 1
      exact (integral_eq_iff_of_ae_le hi.1 hi.2.1 hle).1 (hi.2.2.1.trans hi.2.2.2.symm)
  have hEae : ∀ᵐ s ∂P, s ∈ E := by
    filter_upwards [hQae, ae_all_iff.2 (fun x => ae_all_iff.2 (fun i => heq x i))] with s hs he
    exact ⟨hs, by simpa only [Set.mem_iInter, Set.mem_ofPred_eq] using he⟩
  refine ⟨E, hEmeas, Set.inter_subset_left, (mem_ae_iff_prob_eq_one hEmeas).mp hEae, ?_⟩
  intro s hs x i
  exact (Set.mem_iInter.mp (Set.mem_iInter.mp hs.2 x) i)

end LPP.Busemann
