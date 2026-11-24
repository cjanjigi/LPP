/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Differentiability.FinalDraft.Grid.GeneralGlobalProbability
public import Differentiability.FinalDraft.Grid.RecordTrials
public import LPP_Foundations.Statements.ShapeDefinitions
public import Differentiability.FinalDraft.SelectedGridPaths.Bounds
public import Differentiability.FinalDraft.SelectedGridPaths.Coarse.Connection
public import Differentiability.FinalDraft.SelectedGridPaths.Measurable
public import Differentiability.Probability.CharacteristicLengths
import Differentiability.FinalDraft.SelectedGridPaths.Fine
import Differentiability.Analysis.GridScaleCounts
import Martin2004.Probability.ShapeAboveMean
import ProbabilityBasics.Probability.PositiveMomentTail
import Mathlib.Tactic

/-! # The general-weight grid theorem with the actual staircase family

The four components of the event are those of `rk:gridprob-general` and Appendix B item U7
of `differentiability_final_draft.tex`. The path clauses retain the two endpoint windows
of `rk:endpoints-general`, with the fine and coarse constructions of items U2 and U4.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal

namespace LPPDifferentiability

open StairGeometry SelectedGridPaths

/-- The current draft's four-way grid event with the actual selected paths (P_k). -/
noncomputable def generalGridGoodEvent
    (a G K cstar A R C₁ ε₀ Cm : ℝ) (m : ℕ → ℕ) (k J K₁ K₂ K₃ : ℕ) : Set Environment :=
  generalGridGoodEventForPaths
    (fun i b => pathFamily a cstar A R C₁ m i K₁ K₃ b)
    a G K cstar A R C₁ ε₀ Cm m k J K₁ K₂ K₃

/-- Membership in the four-way event tests the grid cells, geometry, actual selected weights,
and upper cap on the working region. -/
theorem mem_generalGridGoodEvent_iff
    (a G K cstar A R C₁ ε₀ Cm : ℝ) (m : ℕ → ℕ) (k J K₁ K₂ K₃ : ℕ) (ω : Environment) :
    ω ∈ generalGridGoodEvent a G K cstar A R C₁ ε₀ Cm m k J K₁ K₂ K₃ ↔
      let Q := workingRegion a A R C₁ m k
      let T := threshold ε₀ K₂ k
      let t := ε₀ * (2 : ℝ) ^ k / (k : ℝ)
      ((ω ∈ generalGridCellsGood a G K cstar A R k J (m k) ∧
        ω ∈ goodEvent (slopeCutoff a) K₁ K₃ T Q) ∧
        (∀ q ∈ pathFamily a cstar A R C₁ m k K₁ K₃ (siteMask ω T),
          -2 * Cm * ((q.2.1.1 + q.2.1.2 : ℕ) : ℝ) - t / 2 ≤ pathWeight ω q.2.2)) ∧
        ∀ z ∈ Q, ω z ≤ t := by
  dsimp only
  have hmask : (fun z => if ω z < -threshold ε₀ K₂ k then true else false) =
      siteMask ω (threshold ε₀ K₂ k) := by
    funext z
    by_cases hz : ω z < -threshold ε₀ K₂ k <;> simp [siteMask, hz]
  unfold generalGridGoodEvent generalGridGoodEventForPaths gridStaircaseWeightEvent gridUpperCap
  simp only [mem_inter_iff, mem_ofPred_eq, hmask]

/-- The four-way event with the actual selected family is measurable at every scale. -/
theorem measurableSet_generalGridGoodEvent
    (a G K cstar A R C₁ ε₀ Cm : ℝ) (m : ℕ → ℕ) (k J K₁ K₂ K₃ : ℕ) :
    MeasurableSet (generalGridGoodEvent a G K cstar A R C₁ ε₀ Cm m k J K₁ K₂ K₃) :=
  measurableSet_generalGridGoodEventForPaths _
    (fun i => measurableSet_pathFamily_fibre a cstar A R C₁ m i K₁ K₃)
    a G K cstar A R C₁ ε₀ Cm m k J K₁ K₂ K₃

private theorem gamma_covered_in_window
    {ω : Environment} {T a A R C₁ : ℝ} {m : ℕ → ℕ} {k K₁ K₃ : ℕ} {u : Lattice} {I : ℤ}
    (ha₀ : 0 < a) (ha₁ : a < 1) (hK₁ : 1 ≤ K₁) (hK₃ : 1 ≤ K₃) (hC₁ : 0 ≤ C₁)
    (hmargin : (deviationBound K₁ K₃ : ℝ) + 1 ≤ (2 : ℝ) ^ k)
    (hgeo : ω ∈ goodEvent (slopeCutoff a) K₁ K₃ T (workingRegion a A R C₁ m k))
    (hu : |(lev u : ℝ)| ≤ (A + 5) * (2 : ℝ) ^ m k)
    (huR : |transverse a u| ≤ R * (2 : ℝ) ^ k)
    (hI : |(I : ℝ)| ≤ (A + 5) * (2 : ℝ) ^ m k) :
    let Q := workingRegion a A R C₁ m k
    let b := siteMask ω T
    (lev u ≤ I → ¬ (reachSet ω T u).Finite → gammaDefined Q b a u I) ∧
    (I ≤ lev u → -T ≤ ω u → ¬ (reachBackSet ω T u).Finite → gammaDefined Q b a u I) := by
  intro Q b
  let θ := slopeCutoff a
  have ⟨hθ, hθ', haL, haR, _, _⟩ :=
    coarse_direction_facts a (50 / min a (1 - a)) θ rfl ha₀ ha₁ rfl
  have hq₁ : θ ≤ a := by linarith only [hθ, haL]
  have hq₂ : a ≤ 1 - θ := by linarith only [hθ, haR]
  have hsize : 0 ≤ (2 * C₁ + 9) * (2 : ℝ) ^ k := by positivity
  have cover (v : Lattice) (hv : |(lev v : ℝ)| ≤ (A + 5) * (2 : ℝ) ^ m k)
      (hdev : |transverse a v - transverse a u| ≤ (deviationBound K₁ K₃ : ℝ) + 1) :
      v ∈ Q := by
    refine ⟨hv, ?_⟩
    change |transverse a v| ≤ (R + 2 * C₁ + 10) * (2 : ℝ) ^ k
    have h := abs_add_le (transverse a v - transverse a u) (transverse a u)
    rw [sub_add_cancel] at h
    linarith only [h, hdev, huR, hmargin, hsize]
  have huQ : u ∈ Q := cover u hu (by rw [sub_self, abs_zero]; positivity)
  constructor
  · intro hlev hnt
    let V := forwardTrapped ω T
    let x := GreedyAttachment.vertex u a V
    let n := (I - lev u).toNat
    have hn : (n : ℤ) = I - lev u := Int.toNat_of_nonneg (sub_nonneg.mpr hlev)
    have hmar (s : ℕ) (hs : s ≤ n)
        (hd : |GreedyAttachment.deviation u a s (x s)| ≤ (deviationBound K₁ K₃ : ℝ) + 1) :
        x s ∈ Q := by
      have he : lev (x s) = lev u + (s : ℤ) := GreedyAttachment.level u a V s
      have hlo : (lev u : ℝ) ≤ (lev (x s) : ℝ) := by exact_mod_cast (show lev u ≤ lev (x s) by omega)
      have hhi : (lev (x s) : ℝ) ≤ (I : ℝ) := by exact_mod_cast (show lev (x s) ≤ I by omega)
      refine cover _ (abs_le.mpr ⟨(abs_le.mp hu).1.trans hlo, hhi.trans (abs_le.mp hI).2⟩) ?_
      have hr := GreedyAttachment.transverse_deviation_eq u (x s) a a s he
      simp only [sub_self, mul_zero, add_zero] at hr
      simpa only [transverse, hr] using hd
    have hpath := greedy_forward_in_region ω T θ K₃ K₁ Q hθ hθ' hK₃ hK₁ hgeo u huQ hnt a hq₁ hq₂ n hmar
    refine Or.inl ⟨hlev, ?_, fun s hs => ?_⟩
    · rw [show b = siteMask ω T from rfl, forwardTrapped_mask]
      exact hnt
    · rw [forwardStream, show b = siteMask ω T from rfl, forwardTrapped_mask]
      exact (hpath s hs).1
  · intro hlev hbad hnt
    let W : Set Lattice := {z | -z ∈ backwardBlocked ω T}
    let x := GreedyAttachment.vertex (-u) a W
    let n := (lev u - I).toNat
    have hn : (n : ℤ) = lev u - I := Int.toNat_of_nonneg (sub_nonneg.mpr hlev)
    have hmar (s : ℕ) (hs : s ≤ n)
        (hd : |GreedyAttachment.deviation (-u) a s (x s)| ≤ (deviationBound K₁ K₃ : ℝ) + 1) :
        -x s ∈ Q := by
      have he : lev (x s) = lev (-u) + (s : ℤ) := GreedyAttachment.level (-u) a W s
      have hv : lev (-x s) = lev u - (s : ℤ) := by
        simp only [lev, Prod.fst_neg, Prod.snd_neg] at he ⊢
        omega
      have hlo : (I : ℝ) ≤ (lev (-x s) : ℝ) := by exact_mod_cast (show I ≤ lev (-x s) by omega)
      have hhi : (lev (-x s) : ℝ) ≤ (lev u : ℝ) := by exact_mod_cast (show lev (-x s) ≤ lev u by omega)
      refine cover _ (abs_le.mpr ⟨(abs_le.mp hI).1.trans hlo, hhi.trans (abs_le.mp hu).2⟩) ?_
      have hr₀ := GreedyAttachment.transverse_deviation_eq (-u) (x s) a a s he
      simp only [sub_self, mul_zero, add_zero, Prod.fst_neg, Prod.snd_neg, Int.cast_neg] at hr₀
      have hr : transverse a (-x s) - transverse a u = -GreedyAttachment.deviation (-u) a s (x s) := by
        rw [← hr₀]
        simp only [transverse, Prod.fst_neg, Prod.snd_neg, Int.cast_neg]
        ring
      rwa [hr, abs_neg]
    have hpath := greedy_backward_in_region ω T θ K₃ K₁ Q hθ hθ' hK₃ hK₁ hgeo u huQ hbad hnt a hq₁ hq₂ n hmar
    refine Or.inr ⟨hlev, ?_, fun s hs => ?_⟩
    · rw [show b = siteMask ω T from rfl, backwardBlocked_mask]
      exact fun h => h.elim (not_lt_of_ge hbad) hnt
    · rw [backwardStream, show b = siteMask ω T from rfl, backwardBlocked_mask]
      exact (hpath s hs).1

/-- On the actual four-way event the paper's two partial staircase clauses hold.
The fine branch charges its actual segment. The coarse branch uses the successful fixed cap
at the bin of (r(u)) and charges the actual arrival, first meeting, and suffix paths. -/
theorem grid_vertex_clause_of_generalGridGoodEvent
    {ω : Environment} {a G dl dr K Cm cstar A R C₁ ε₀ : ℝ}
    {m : ℕ → ℕ} {k J K₁ K₂ K₃ : ℕ}
    (ha₀ : 0 < a) (ha₁ : a < 1) (hR : 0 < R) (hε₀ : 0 < ε₀)
    (hK₁ : 1 ≤ K₁) (hK₃ : 1 ≤ K₃) (hJ : 1 ≤ J)
    (hK : 1 ≤ K) (hdl : |dl| ≤ K) (hdr : |dr| ≤ K)
    (hCm : 0 ≤ Cm) (hGC : 0 ≤ G + 2 * Cm) (hcs : cstar = 50 / min a (1 - a))
    (hC₁ : 8 * cstar * (G + 2 * Cm) + 2 * K + 2 * (trimLength (slopeCutoff a) K₁ K₃ : ℝ) +
      3 * cstar + 1 ≤ C₁)
    (hjstar : ⌈((m k : ℝ) - 1) / 4⌉₊ ≤ k)
    (hmargin : 4 * ((deviationBound K₁ K₃ : ℝ) + (trimLength (slopeCutoff a) K₁ K₃ : ℝ) +
      (arrivalBoxSize (slopeCutoff a) K₁ K₃ : ℝ)) ≤ (width k ⌈((m k : ℝ) - 1) / 4⌉₊ : ℝ))
    (hcost : 2 * (deviationBound K₁ K₃ : ℝ) * K + 4 * (trimLength (slopeCutoff a) K₁ K₃ : ℝ) * Cm ≤
      (width k ⌈((m k : ℝ) - 1) / 4⌉₊ : ℝ))
    (hω : ω ∈ generalGridGoodEvent a G K cstar A R C₁ ε₀ Cm m k J K₁ K₂ K₃) :
    GridVertexClause ω (threshold ε₀ K₂ k) (ε₀ * (2 : ℝ) ^ k / (k : ℝ))
      a G dl dr C₁ A R k J m reachSet reachBackSet := by
  let T := threshold ε₀ K₂ k
  let t := ε₀ * (2 : ℝ) ^ k / (k : ℝ)
  let Q := workingRegion a A R C₁ m k
  let b := siteMask ω T
  let r := trimLength (slopeCutoff a) K₁ K₃
  let Δ := deviationBound K₁ K₃
  let L := arrivalBoxSize (slopeCutoff a) K₁ K₃
  obtain ⟨⟨⟨hcells, hgeo⟩, hweight⟩, -⟩ :=
    (mem_generalGridGoodEvent_iff a G K cstar A R C₁ ε₀ Cm m k J K₁ K₂ K₃ ω).mp hω
  have hc : 100 ≤ cstar := (coarse_direction_facts a cstar (slopeCutoff a) rfl ha₀ ha₁ hcs).2.2.2.2.2
  have hr : 0 ≤ (r : ℝ) := Nat.cast_nonneg _
  have hL : 0 ≤ (L : ℝ) := Nat.cast_nonneg _
  have hΔ : 1 ≤ (Δ : ℝ) := by
    exact_mod_cast (show 1 ≤ deviationBound K₁ K₃ by unfold deviationBound; omega)
  have ht : 0 ≤ t := by dsimp only [t]; positivity
  have hCfine : 8 * cstar * (G + 2 * Cm) + 1 ≤ C₁ := by
    change 8 * cstar * (G + 2 * Cm) + 2 * K + 2 * (r : ℝ) + 3 * cstar + 1 ≤ C₁ at hC₁
    linarith only [hC₁, hr, hK, hc]
  have hCone : 1 ≤ C₁ := by linarith only [hCfine, mul_nonneg (show 0 ≤ 8 * cstar by linarith only [hc]) hGC]
  intro u hu huR j hJj hj I hdiv hI
  let l := mesh (m k) j
  let w := width k j
  let P := (j : ℝ) ^ 2 * (w : ℝ)
  let H := (A + 5) * (2 : ℝ) ^ m k
  have hw : 0 < (w : ℝ) := by dsimp [w, width]; positivity
  have hH : 0 ≤ (2 : ℝ) ^ m k := by positivity
  have huH : |(lev u : ℝ)| ≤ H := by dsimp only [H]; linarith only [hu, hH]
  have hIH : |(I : ℝ)| ≤ H := by dsimp only [H]; linarith only [hI, hH]
  have hmesh : (l : ℝ) ≤ (2 : ℝ) ^ m k := by exact_mod_cast grid_mesh_le (m k) j
  have hupperH : |((I + (l : ℤ) : ℤ) : ℝ)| ≤ H := by
    rw [Int.cast_add, Int.cast_natCast]
    calc
      _ ≤ |(I : ℝ)| + |(l : ℝ)| := abs_add_le _ _
      _ ≤ H := by rw [abs_of_nonneg (show 0 ≤ (l : ℝ) from Nat.cast_nonneg l)]; dsimp only [H]; linarith only [hI, hmesh]
  have huQ : u ∈ Q := ⟨huH, by
    change |transverse a u| ≤ (R + 2 * C₁ + 10) * (2 : ℝ) ^ k
    exact le_trans huR (mul_le_mul_of_nonneg_right (by linarith only [hCone]) (by positivity))⟩
  have hwlarge : (width k ⌈((m k : ℝ) - 1) / 4⌉₊ : ℝ) ≤ (w : ℝ) := by
    exact_mod_cast Nat.pow_le_pow_right (show 0 < 2 by decide)
      (show k - ⌈((m k : ℝ) - 1) / 4⌉₊ ≤ k - j by omega)
  have hwupper : (w : ℝ) ≤ (2 : ℝ) ^ k := by
    exact_mod_cast Nat.pow_le_pow_right (show 0 < 2 by decide) (Nat.sub_le k j)
  have hwide := hmargin.trans hwlarge
  have hprice := hcost.trans hwlarge
  have hmargin' : (Δ : ℝ) + 1 ≤ (2 : ℝ) ^ k := by
    change 4 * ((Δ : ℝ) + (r : ℝ) + (L : ℝ)) ≤ (w : ℝ) at hwide
    linarith only [hΔ, hr, hL, hwide, hwupper]
  have hj₁ : 1 ≤ j := hJ.trans hJj
  have hjmem : j ∈ scales (m k) := Finset.mem_Icc.mpr ⟨hj₁, hj⟩
  have hImem : I ∈ gridLevels A (m k) j := mem_gridLevels.mpr ⟨hdiv, hI⟩
  have hconnect (hleft : gammaDefined Q b a u I) (hright : gammaDefined Q b a u (I + (l : ℤ))) :
      GridConnection ω a G dl dr (C₁ * P + 2 * t) (C₁ * P) u
        (gammaPoint b a u I) (gammaPoint b a u (I + (l : ℤ))) := by
    by_cases hfine : (l : ℝ) < 8 * (cstar * P)
    · have hjR : (1 : ℝ) ≤ j := by exact_mod_cast hj₁
      have hwP : (w : ℝ) ≤ P := by
        dsimp only [P]
        simpa only [one_mul] using mul_le_mul_of_nonneg_right (one_le_pow₀ hjR (n := 2)) hw.le
      have hfineWidth : 2 * (Δ : ℝ) * K ≤ P := by
        have hrCm : 0 ≤ 4 * (r : ℝ) * Cm := by positivity
        change 2 * (Δ : ℝ) * K + 4 * (r : ℝ) * Cm ≤ (w : ℝ) at hprice
        linarith only [hrCm, hprice, hwP]
      exact fine_gridConnection ω T t a G dl dr K Cm cstar C₁ A R m k K₁ K₃ j u I
        ha₀ ha₁ hK₁ hK₃ ht hK hdl hdr hGC hCfine hCone hfineWidth huQ hjmem hImem hfine
        hgeo hweight hleft hright
    · let h : ℤ := ⌊transverse a u / (w : ℝ)⌋
      have hlo : (h : ℝ) * (w : ℝ) ≤ transverse a u := (le_div_iff₀ hw).mp (Int.floor_le _)
      have hhi : transverse a u < ((h : ℝ) + 1) * (w : ℝ) :=
        (div_lt_iff₀ hw).mp (Int.lt_floor_add_one _)
      have hbin : h ∈ gridBins R k j := (mem_gridBins hR.le).mpr ⟨_, hlo, hhi, huR⟩
      have hcell := hcells j hJj hj I hdiv hI h ⟨transverse a u, by
        simpa only [w, width, Nat.cast_pow, Nat.cast_ofNat] using hlo, by
        simpa only [w, width, Nat.cast_pow, Nat.cast_ofNat] using hhi, huR⟩
      have hcoarse : 8 * cstar * P ≤ (l : ℝ) := by simpa only [mul_assoc] using le_of_not_gt hfine
      rw [generalGridCellGood, ite_eq_left hcoarse] at hcell
      obtain ⟨ν, htrial⟩ := mem_iUnion.mp hcell
      let C : CoarseBlock a cstar A R C₁ m k u :=
        ⟨j, I, h, ν, huQ, hjmem, hImem, hbin, ⟨hlo, hhi⟩, le_of_not_gt hfine⟩
      exact C.coarse_gridConnection ω T t G dl dr K Cm ha₀ ha₁ hK₁ hK₃ (hj.trans hjstar)
        ht hcs hdl hdr hCm hGC huR htrial hweight hC₁ hwide hprice hgeo hleft hright
  have havail {i : ℤ} (hi : |(i : ℝ)| ≤ H) :=
    gamma_covered_in_window ha₀ ha₁ hK₁ hK₃ (le_trans zero_le_one hCone) hmargin' hgeo huH huR hi
  have hl : (0 : ℤ) ≤ (l : ℤ) := by positivity
  constructor
  · rintro ⟨hbad, hnt⟩ _ hright z₀ z₁ hz₀ hz₁
    have hleft : I ≤ lev u := by change I + (l : ℤ) ≤ lev u at hright; omega
    have h := hconnect ((havail hIH).2 hleft hbad hnt) ((havail hupperH).2 hright hbad hnt)
    rw [gammaPoint_eq_backward _ _ _ _ hleft, gammaPoint_eq_backward _ _ _ _ hright,
      backwardStream] at h
    simp only [backwardStream, backwardBlocked_mask, b] at h
    rw [hz₀, hz₁]
    exact h
  · intro hnt hleft _ z₀ z₁ hz₀ hz₁
    have hright : lev u ≤ I + (l : ℤ) := by change lev u ≤ I at hleft; omega
    have h := hconnect ((havail hIH).1 hleft hnt) ((havail hupperH).1 hright hnt)
    rw [gammaPoint_eq_forward _ _ _ _ hleft, gammaPoint_eq_forward _ _ _ _ hright,
      forwardStream] at h
    simp only [forwardTrapped_mask, b] at h
    rw [hz₀, hz₁]
    exact h

/-- Lemma `lem:grid` for general weights on already identified characteristic record scales.
The source width growth discharges the numerical margins uniformly over the tested scales. -/
theorem general_grid_connections_on_records
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (p' : ℝ) (hp' : 1 < p')
    (hmom' : (∫⁻ x, ENNReal.ofReal ((max (-x) 0) ^ p') ∂μ) < ∞)
    (p : ℝ) (hp : 4 < p)
    (hmom : (∫⁻ x, ENNReal.ofReal ((max x 0) ^ p) ∂μ) < ∞)
    (a G dl dr K cstar A R C₁ ε₀ q0 : ℝ)
    (ha₀ : 0 < a) (ha₁ : a < 1) (hA : 0 < A) (hR : 0 < R) (hε₀ : 0 < ε₀) (hq0 : 0 < q0)
    (K₁ K₂ K₃ : ℕ) (hK₁ : 1 ≤ K₁) (hK₂ : 1 ≤ K₂) (hK₃ : 1 ≤ K₃)
    (hK₃p : 4 < (K₃ : ℝ) * p') (hK₁p : 4 < ((K₁ : ℝ) + 1) * p')
    (hK₂p : 24 < (K₂ : ℝ) * (p' - 1))
    (hK : 1 ≤ K) (hdl : |dl| ≤ K) (hdr : |dr| ≤ K)
    (hGC : 0 ≤ G + 2 * (∫ x, max (-x) 0 ∂μ)) (hcs : cstar = 50 / min a (1 - a))
    (hC₁ : 8 * cstar * (G + 2 * (∫ x, max (-x) 0 ∂μ)) + 2 * K +
      2 * (trimLength (slopeCutoff a) K₁ K₃ : ℝ) + 3 * cstar + 1 ≤ C₁)
    (k0 J : ℕ) (hk0 : 0 < k0) (hJ : 1 ≤ J) (m : ℕ → ℕ) (record : Set ℕ)
    (hm3 : ∀ k : ℕ, k0 ≤ k → m k ≤ 3 * k)
    (hrecord : ∀ k ∈ record, k0 ≤ k)
    (htrial : gridRecordTrials μ a G K q0 k0 m record) :
    let Cm := ∫ x, max (-x) 0 ∂μ
    let E (k : ℕ) := generalGridGoodEvent a G K cstar A R C₁ ε₀ Cm m k J K₁ K₂ K₃
    ∀ᶠ k : ℕ in atTop ⊓ 𝓟 record,
      (environmentLaw μ).real (E k)ᶜ ≤ 2 * generalGridBeta A R q0 J ∧
      ∀ ω ∈ E k, GridVertexClause ω (threshold ε₀ K₂ k) (ε₀ * (2 : ℝ) ^ k / (k : ℝ))
        a G dl dr C₁ A R k J m reachSet reachBackSet := by
  intro Cm E
  let θ := slopeCutoff a
  let Δ := deviationBound K₁ K₃
  let r := trimLength θ K₁ K₃
  let L := arrivalBoxSize θ K₁ K₃
  let paths := fun k b => pathFamily a cstar A R C₁ m k K₁ K₃ b
  have hCm : 0 ≤ Cm := integral_nonneg fun _ => le_max_right _ _
  have hcstar : 1 ≤ cstar :=
    (by norm_num : (1 : ℝ) ≤ 100).trans (coarse_direction_facts a cstar θ rfl ha₀ ha₁ hcs).2.2.2.2.2
  have hC : 0 ≤ C₁ := by
    have hr : 0 ≤ (r : ℝ) := Nat.cast_nonneg _
    have hG : 0 ≤ 8 * cstar * (G + 2 * Cm) := mul_nonneg (by linarith only [hcstar]) hGC
    change 8 * cstar * (G + 2 * Cm) + 2 * K + 2 * (r : ℝ) + 3 * cstar + 1 ≤ C₁ at hC₁
    linarith only [hC₁, hG, hK, hr, hcstar]
  have hvalid : ∀ᶠ k : ℕ in atTop ⊓ 𝓟 record, ∀ b,
      ((paths k b).card : ℝ) ≤ ((2 : ℝ) ^ k) ^ (11 : ℝ) ∧
      ∀ q ∈ paths k b,
        ((q.2.1.1 + q.2.1.2 : ℕ) : ℝ) ≤ 8 * cstar * (k : ℝ) ^ 2 * (2 : ℝ) ^ k ∧
        (∀ i, q.2.2.vertex i ∈ workingRegion a A R C₁ m k) ∧
        ∀ z ∈ q.2.2.collectedSites, b z = false := by
    have hb := pathFamily_bounds_eventually (a := a) m K₁ K₃ hA hR hC (zero_lt_one.trans_le hcstar)
    refine eventually_inf_principal.mpr ?_
    filter_upwards [hb] with k hb hk
    obtain ⟨hcard, hlen⟩ := hb (hm3 k (hrecord k hk))
    intro b
    refine ⟨?_, fun q hq => ⟨hlen b q hq, pathFamily_region_mask hq⟩⟩
    rw [show (11 : ℝ) = ((11 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    exact hcard b
  have hprob := general_grid_good_event_failure_eventually_le μ p' hp' hmom' p hp hmom
    a G K cstar A R C₁ ε₀ q0 ha₀ ha₁ hcstar hA hR hC hε₀ hq0
    K₁ K₂ K₃ hK₁ hK₂ hK₃ hK₃p hK₁p hK₂p k0 J hk0 hJ m record
    (fun k hk _ => hm3 k hk) htrial paths
    (fun k => measurableSet_pathFamily_fibre a cstar A R C₁ m k K₁ K₃) hvalid
  obtain ⟨kW, hkW⟩ := grid_pow_sub_jstar_ge (4 * ((Δ : ℝ) + (r : ℝ) + (L : ℝ))) k0 m hm3
  obtain ⟨kC, hkC⟩ := grid_pow_sub_jstar_ge (2 * (Δ : ℝ) * K + 4 * (r : ℝ) * Cm) k0 m hm3
  have hlarge : ∀ᶠ k : ℕ in atTop ⊓ 𝓟 record, max (4 * k0 + 3) (max kW kC) ≤ k :=
    (eventually_ge_atTop _).filter_mono inf_le_left
  filter_upwards [hprob, hlarge] with k hpk hk
  refine ⟨hpk, fun ω hω => ?_⟩
  have hk' : 4 * k0 + 3 ≤ k := le_trans (le_max_left _ _) hk
  have hmk := hm3 k (by omega)
  have hjs := (grid_scale_index_bounds rfl hmk hk' hk0 le_rfl).1
  exact grid_vertex_clause_of_generalGridGoodEvent ha₀ ha₁ hR hε₀ hK₁ hK₃ hJ hK hdl hdr
    hCm hGC hcs hC₁ hjs (hkW k (by omega)) (hkC k (by omega)) hω

/-- The actual general-weight grid theorem of `lem:grid`, `rk:grid-general`, and
`rk:gridprob-general`. Its record scales and crossing probabilities come from
`characteristic_length_records`. The two path clauses and the probability bound concern
the same measurable four-way event. -/
theorem general_weight_grid_connection_theorem
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (p' : ℝ) (hp' : 1 < p')
    (hmom' : (∫⁻ x, ENNReal.ofReal ((max (-x) 0) ^ p') ∂μ) < ∞)
    (p : ℝ) (hp : 4 < p)
    (hmom : (∫⁻ x, ENNReal.ofReal ((max x 0) ^ p) ∂μ) < ∞)
    (g : Quadrant → ℝ) (hg : LPPStatements.IsShapeFunction μ g)
    (a : ℝ) (ha₀ : 0 < a) (ha₁ : a < 1) (Gtop : ℝ)
    (htop : Tendsto (fun n : ℕ => (∫ ω : Environment, lastPassage (fun z =>
      if (ω z : EReal) = sSup ((fun t : ℝ => (t : EReal)) '' μ.support) then (1 : ℝ) else 0)
        0 (⌊(n : ℝ) * a⌋₊, ⌊(n : ℝ) * (1 - a)⌋₊) ∂environmentLaw μ) / (n : ℝ))
      atTop (𝓝 Gtop))
    (hgap : Gtop < 1) (q0 : ℝ) (hq0₀ : 0 < q0) (hq0₁ : q0 < 1)
    (K₁ K₂ K₃ : ℕ) (hK₁ : 1 ≤ K₁) (hK₂ : 1 ≤ K₂) (hK₃ : 1 ≤ K₃)
    (hK₃p : 4 < (K₃ : ℝ) * p') (hK₁p : 4 < ((K₁ : ℝ) + 1) * p')
    (hK₂p : 24 < (K₂ : ℝ) * (p' - 1)) :
    let H : ℝ → ℝ := fun h => quadrantExtension g (a + h, 1 - a - h)
    let dl := derivWithin H (Iio 0) 0
    let dr := derivWithin H (Ioi 0) 0
    let K : ℝ := 100 * (1 + |dl| + |dr|)
    let G := H 0
    let Cm := ∫ x, max (-x) 0 ∂μ
    let cstar : ℝ := 50 / min a (1 - a)
    let C₁ := 8 * cstar * (G + 2 * Cm) + 2 * K + 2 * (trimLength (slopeCutoff a) K₁ K₃ : ℝ) +
      3 * cstar + 1
    let P : ℕ → ℕ → ℝ := fun k n => (environmentLaw μ).real {ω : Environment |
      ∃ u : Lattice, u.1 + u.2 = 0 ∧ ∃ e : ℕ × ℕ, e.1 + e.2 = n ∧ ∃ q : Path u e,
        (∀ i, |(1 - a) * ((q.vertex i).1 : ℝ) - a * ((q.vertex i).2 : ℝ)| ≤ 8 * (2 : ℝ) ^ k) ∧
        G * (n : ℝ) - K * (2 : ℝ) ^ k < pathWeight ω q}
    ∃ (k0 : ℕ) (m nk : ℕ → ℕ) (record : Set ℕ),
      0 < k0 ∧ record.Infinite ∧
      Tendsto (fun k : ℕ => (2 : ℝ) ^ m k / 2 ^ k) atTop atTop ∧
      (∀ k, k0 ≤ k →
        (∃ n : ℕ, (2 : ℝ) ^ m k / 2 < n ∧ (n : ℝ) ≤ 2 ^ m k ∧ P k n ≤ q0) ∧
        (∀ j : ℕ, (∃ n : ℕ, (2 : ℝ) ^ j / 2 < n ∧ (n : ℝ) ≤ 2 ^ j ∧ P k n ≤ q0) →
          m k ≤ j) ∧
        m k ≤ 3 * k ∧
        (∀ n : ℕ, 1 ≤ n → (n : ℝ) < 2 ^ m k / 2 → q0 < P k n) ∧
        ((2 : ℝ) ^ m k / 2 < nk k ∧ (nk k : ℝ) ≤ 2 ^ m k ∧ P k (nk k) ≤ q0 ∧
          ∀ n : ℕ, (2 : ℝ) ^ m k / 2 < n → (n : ℝ) ≤ 2 ^ m k → P k (nk k) ≤ P k n)) ∧
      (∀ k ∈ record, k0 ≤ k ∧ ∀ j : ℕ, j ≤ k - k0 →
        (2 : ℝ) ^ m k / 2 ^ (4 * j) ≤ 2 ^ m (k - j)) ∧
      gridRecordTrials μ a G K q0 k0 m record ∧
      ∀ A R : ℝ, 0 < A → 0 < R →
        Tendsto (generalGridBeta A R q0) atTop (𝓝 0) ∧
        ∀ (ε₀ : ℝ), 0 < ε₀ → ∀ J : ℕ, 1 ≤ J →
          let E := fun k => generalGridGoodEvent a G K cstar A R C₁ ε₀ Cm m k J K₁ K₂ K₃
          (∀ k, MeasurableSet (E k)) ∧
          ∃ k1 : ℕ, ∀ k ∈ record, k1 ≤ k →
            (environmentLaw μ).real (E k)ᶜ ≤ 2 * generalGridBeta A R q0 J ∧
            ∀ ω ∈ E k, GridVertexClause ω (threshold ε₀ K₂ k) (ε₀ * (2 : ℝ) ^ k / (k : ℝ))
              a G dl dr C₁ A R k J m reachSet reachBackSet := by
  obtain ⟨hgcont, hghom, hgconc, hshape⟩ := hg
  have hgshape := (LPPStatements.approximatesLastPassage_iff_positive_threshold μ g).mp hshape
  intro H dl dr K G Cm cstar C₁ P
  have hneg : ∃ p : ℝ, 1 < p ∧ (∫⁻ x, ENNReal.ofReal ((max (-x) 0) ^ p) ∂μ) < ∞ :=
    ⟨p', hp', hmom'⟩
  have hpos := positive_integrated_sqrt_tail_lt_top_of_moment μ
    ((by norm_num : (2 : ℝ) < 4).trans hp) hmom
  obtain ⟨k0, hk0, m, nk, record, hmtop, hclauses, hinf, hrecord, htrial⟩ :=
    characteristic_length_records μ hneg hpos g hgcont hghom hgconc hgshape a ha₀ ha₁ Gtop
      htop hgap q0 hq0₀ hq0₁
  have hG : G = g (toQuadrant (a, 1 - a)) := by
    simp only [G, H, quadrantExtension, add_zero, sub_zero]
  have htrial' : gridRecordTrials μ a G K q0 k0 m record := by
    rw [hG]
    exact htrial
  have hm3 (k : ℕ) (hk : k0 ≤ k) : m k ≤ 3 * k := (hclauses k hk).2.2.1
  have hab : a.toNNReal + (1 - a).toNNReal = 1 := by
    rw [← Real.toNNReal_add ha₀.le (by linarith)]
    norm_num
  have hEG : (∫ x : ℝ, x ∂μ) ≤ G := by
    rw [hG]
    exact integral_le_shape_of_negative_moment_and_positive_tail μ hneg hpos g hgcont hghom
      hgconc hgshape a.toNNReal (1 - a).toNNReal hab
  have hCm : 0 ≤ Cm := integral_nonneg fun x => le_max_right _ _
  have hGC : 0 ≤ G + 2 * Cm := by linarith only [hEG, hCm, neg_integral_neg_part_le_integral_grid μ]
  have hK : 1 ≤ K := by dsimp only [K]; linarith only [abs_nonneg dl, abs_nonneg dr]
  have hdl : |dl| ≤ K := by dsimp only [K]; linarith only [abs_nonneg dl, abs_nonneg dr]
  have hdr : |dr| ≤ K := by dsimp only [K]; linarith only [abs_nonneg dl, abs_nonneg dr]
  refine ⟨k0, m, nk, record, hk0, hinf, hmtop, ?_, hrecord, htrial', fun A R hA hR =>
    ⟨general_grid_beta_tendsto A R q0, fun ε₀ hε₀ J hJ => ?_⟩⟩
  · dsimp only [P]
    rw [hG]
    exact hclauses
  · refine ⟨fun k => measurableSet_generalGridGoodEvent a G K cstar A R C₁ ε₀ Cm m k J K₁ K₂ K₃, ?_⟩
    obtain ⟨k1, hk1⟩ := eventually_atTop.mp (eventually_inf_principal.mp
      (general_grid_connections_on_records μ p' hp' hmom' p hp hmom a G dl dr K cstar A R C₁ ε₀ q0
        ha₀ ha₁ hA hR hε₀ hq0₀ K₁ K₂ K₃ hK₁ hK₂ hK₃ hK₃p hK₁p hK₂p
        hK hdl hdr hGC rfl le_rfl k0 J hk0 hJ m record hm3 (fun k hk => (hrecord k hk).1) htrial'))
    exact ⟨k1, fun k hk hlarge => hk1 k hlarge hk⟩

/-- The general-weight theorem of `lem:grid` with the four shape assumptions written out. -/
theorem general_grid_theorem
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (p' : ℝ) (hp' : 1 < p')
    (hmom' : (∫⁻ x, ENNReal.ofReal ((max (-x) 0) ^ p') ∂μ) < ∞)
    (p : ℝ) (hp : 4 < p)
    (hmom : (∫⁻ x, ENNReal.ofReal ((max x 0) ^ p) ∂μ) < ∞)
    (g : Quadrant → ℝ) (hgcont : Continuous g)
    (hghom : ∀ (c : ℝ≥0) (x : Quadrant), g (c * x.1, c * x.2) = (c : ℝ) * g x)
    (hgconc : ∀ (x y : Quadrant) (r t : ℝ≥0), r + t = 1 →
      (r : ℝ) * g x + (t : ℝ) * g y ≤ g (r * x.1 + t * y.1, r * x.2 + t * y.2))
    (hgshape : ∀ᵐ ω ∂environmentLaw μ, ∀ ε : ℝ, 0 < ε →
      ∃ N : ℕ, 1 ≤ N ∧ ∀ d : ℕ × ℕ, N ≤ d.1 + d.2 →
        |lastPassage ω 0 d - g ((d.1 : ℝ≥0), (d.2 : ℝ≥0))| ≤ ε * ((d.1 + d.2 : ℕ) : ℝ))
    (a : ℝ) (ha₀ : 0 < a) (ha₁ : a < 1) (Gtop : ℝ)
    (htop : Tendsto (fun n : ℕ => (∫ ω : Environment, lastPassage (fun z =>
      if (ω z : EReal) = sSup ((fun t : ℝ => (t : EReal)) '' μ.support) then (1 : ℝ) else 0)
        0 (⌊(n : ℝ) * a⌋₊, ⌊(n : ℝ) * (1 - a)⌋₊) ∂environmentLaw μ) / (n : ℝ))
      atTop (𝓝 Gtop))
    (hgap : Gtop < 1) (q0 : ℝ) (hq0₀ : 0 < q0) (hq0₁ : q0 < 1)
    (K₁ K₂ K₃ : ℕ) (hK₁ : 1 ≤ K₁) (hK₂ : 1 ≤ K₂) (hK₃ : 1 ≤ K₃)
    (hK₃p : 4 < (K₃ : ℝ) * p') (hK₁p : 4 < ((K₁ : ℝ) + 1) * p')
    (hK₂p : 24 < (K₂ : ℝ) * (p' - 1)) :
    let H : ℝ → ℝ := fun h => quadrantExtension g (a + h, 1 - a - h)
    let dl := derivWithin H (Iio 0) 0
    let dr := derivWithin H (Ioi 0) 0
    let K : ℝ := 100 * (1 + |dl| + |dr|)
    let G := H 0
    let Cm := ∫ x, max (-x) 0 ∂μ
    let cstar : ℝ := 50 / min a (1 - a)
    let C₁ := 8 * cstar * (G + 2 * Cm) + 2 * K + 2 * (trimLength (slopeCutoff a) K₁ K₃ : ℝ) +
      3 * cstar + 1
    let P : ℕ → ℕ → ℝ := fun k n => (environmentLaw μ).real {ω : Environment |
      ∃ u : Lattice, u.1 + u.2 = 0 ∧ ∃ e : ℕ × ℕ, e.1 + e.2 = n ∧ ∃ q : Path u e,
        (∀ i, |(1 - a) * ((q.vertex i).1 : ℝ) - a * ((q.vertex i).2 : ℝ)| ≤ 8 * (2 : ℝ) ^ k) ∧
        G * (n : ℝ) - K * (2 : ℝ) ^ k < pathWeight ω q}
    ∃ (k0 : ℕ) (m nk : ℕ → ℕ) (record : Set ℕ),
      0 < k0 ∧ record.Infinite ∧
      Tendsto (fun k : ℕ => (2 : ℝ) ^ m k / 2 ^ k) atTop atTop ∧
      (∀ k, k0 ≤ k →
        (∃ n : ℕ, (2 : ℝ) ^ m k / 2 < n ∧ (n : ℝ) ≤ 2 ^ m k ∧ P k n ≤ q0) ∧
        (∀ j : ℕ, (∃ n : ℕ, (2 : ℝ) ^ j / 2 < n ∧ (n : ℝ) ≤ 2 ^ j ∧ P k n ≤ q0) →
          m k ≤ j) ∧
        m k ≤ 3 * k ∧
        (∀ n : ℕ, 1 ≤ n → (n : ℝ) < 2 ^ m k / 2 → q0 < P k n) ∧
        ((2 : ℝ) ^ m k / 2 < nk k ∧ (nk k : ℝ) ≤ 2 ^ m k ∧ P k (nk k) ≤ q0 ∧
          ∀ n : ℕ, (2 : ℝ) ^ m k / 2 < n → (n : ℝ) ≤ 2 ^ m k → P k (nk k) ≤ P k n)) ∧
      (∀ k ∈ record, k0 ≤ k ∧ ∀ j : ℕ, j ≤ k - k0 →
        (2 : ℝ) ^ m k / 2 ^ (4 * j) ≤ 2 ^ m (k - j)) ∧
      gridRecordTrials μ a G K q0 k0 m record ∧
      ∀ A R : ℝ, 0 < A → 0 < R →
        Tendsto (generalGridBeta A R q0) atTop (𝓝 0) ∧
        ∀ (ε₀ : ℝ), 0 < ε₀ → ∀ J : ℕ, 1 ≤ J →
          let E := fun k => generalGridGoodEvent a G K cstar A R C₁ ε₀ Cm m k J K₁ K₂ K₃
          (∀ k, MeasurableSet (E k)) ∧
          ∃ k1 : ℕ, ∀ k ∈ record, k1 ≤ k →
            (environmentLaw μ).real (E k)ᶜ ≤ 2 * generalGridBeta A R q0 J ∧
            ∀ ω ∈ E k, GridVertexClause ω (threshold ε₀ K₂ k) (ε₀ * (2 : ℝ) ^ k / (k : ℝ))
              a G dl dr C₁ A R k J m reachSet reachBackSet := by
  have hg : LPPStatements.IsShapeFunction μ g :=
    ⟨hgcont, hghom, hgconc,
      (LPPStatements.approximatesLastPassage_iff_positive_threshold μ g).mpr hgshape⟩
  exact general_weight_grid_connection_theorem μ p' hp' hmom' p hp hmom g hg
    a ha₀ ha₁ Gtop htop hgap q0 hq0₀ hq0₁ K₁ K₂ K₃ hK₁ hK₂ hK₃ hK₃p hK₁p hK₂p

end LPPDifferentiability
