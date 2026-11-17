/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Busemann.Process.RightmostPathCoordinateEscape
import Busemann.Process.RightmostPathMeasurability
import Busemann.Process.RightmostPathCovariance
import LPP_Foundations.Model.Paths.BoundaryHits
import LPP_Foundations.Probability.HighWeightColumns
import Mathlib.Tactic

/-! Both published normalizations of a positive pair of disjoint rightmost rays. -/

@[expose] public section
open MeasureTheory Filter LPPDifferentiability
open scoped ENNReal Topology

namespace LPP.Busemann

private theorem pair_restart (C : Lattice → Lattice → ℝ) (x : Lattice) (n r : ℕ) :
    rightmostCocyclePath C (rightmostCocyclePath C x n) r =
      rightmostCocyclePath C x (n + r) := by
  change (rightmostCocycleSuccessor C)^[r] ((rightmostCocycleSuccessor C)^[n] x) =
    (rightmostCocycleSuccessor C)^[n + r] x
  rw [Nat.add_comm n r, Function.iterate_add_apply]

private theorem pair_step (C : Lattice → Lattice → ℝ) (x : Lattice) (n : ℕ) :
    rightmostCocyclePath C x (n + 1) = rightmostCocyclePath C x n + (1, 0) ∨
      rightmostCocyclePath C x (n + 1) = rightmostCocyclePath C x n + (0, 1) := by
  simpa only [rightmostCocyclePath, Function.iterate_succ_apply'] using
    rightmostCocycleSuccessor_step C (rightmostCocyclePath C x n)

-- Actual last departures give ordered, disjoint restarted rays and height bounds.
private theorem pair_ordered_departures
    (C : Lattice → Lattice → ℝ) (a b : Lattice)
    (hA : Tendsto (fun n => (rightmostCocyclePath C a n).1) atTop atTop)
    (hB : Tendsto (fun n => (rightmostCocyclePath C b n).1) atTop atTop)
    (hDisjoint : ∀ r s : ℕ, rightmostCocyclePath C a r ≠ rightmostCocyclePath C b s)
    (M : ℤ) (haM : a.1 ≤ M) (hbM : b.1 ≤ M) :
    ∃ z w : Lattice, z.1 = M ∧ w.1 = M ∧ z.2 < w.2 ∧
      (∀ r s : ℕ, rightmostCocyclePath C z r ≠ rightmostCocyclePath C w s) ∧
      rightmostCocycleSuccessor C z = z + (1, 0) ∧
      rightmostCocycleSuccessor C w = w + (1, 0) ∧
      (∀ t, (rightmostCocyclePath C a t).1 = M →
        (rightmostCocyclePath C a t).2 ≤ w.2) ∧
      (∀ t, (rightmostCocyclePath C b t).1 = M →
        (rightmostCocyclePath C b t).2 ≤ w.2) ∧
      ((∃ n, rightmostCocyclePath C a n = w) ∨
        ∃ n, rightmostCocyclePath C b n = w) := by
  obtain ⟨na, hXa, hEa, _, hYa⟩ := up_right_path_last_east_departure
    (rightmostCocyclePath C a) (pair_step C a) hA M
      (by simpa only [rightmostCocyclePath, Function.iterate_zero_apply] using haM)
  obtain ⟨nb, hXb, hEb, _, hYb⟩ := up_right_path_last_east_departure
    (rightmostCocyclePath C b) (pair_step C b) hB M
      (by simpa only [rightmostCocyclePath, Function.iterate_zero_apply] using hbM)
  let x := rightmostCocyclePath C a na
  let y := rightmostCocyclePath C b nb
  have hEastX : rightmostCocycleSuccessor C x = x + (1, 0) := by
    simpa only [x, rightmostCocyclePath, Function.iterate_succ_apply'] using hEa
  have hEastY : rightmostCocycleSuccessor C y = y + (1, 0) := by
    simpa only [y, rightmostCocyclePath, Function.iterate_succ_apply'] using hEb
  have hAvoid : ∀ r s : ℕ,
      rightmostCocyclePath C x r ≠ rightmostCocyclePath C y s := by
    intro r s hMeet
    apply hDisjoint (na + r) (nb + s)
    simpa only [x, y, pair_restart] using hMeet
  have hHeightNe : x.2 ≠ y.2 := by
    intro hHeight
    exact hDisjoint na nb (Prod.ext (hXa.trans hXb.symm) hHeight)
  rcases lt_or_gt_of_ne hHeightNe with hxy | hyx
  · refine ⟨x, y, hXa, hXb, hxy, hAvoid, hEastX, hEastY, ?_, hYb, Or.inr ⟨nb, rfl⟩⟩
    intro t ht
    exact (hYa t ht).trans hxy.le
  · refine ⟨y, x, hXb, hXa, hyx, ?_, hEastY, hEastX, hYa, ?_, Or.inl ⟨na, rfl⟩⟩
    · intro r s hMeet
      exact hAvoid s r hMeet.symm
    · intro t ht
      exact (hYb t ht).trans hyx.le

-- Translation of ordered departures is purely pointwise and retains cross-time avoidance.
private theorem pair_translate_ordered
    {Ω : Type*} (T : Lattice → Ω → Ω) (B : Lattice → Lattice → Ω → ℝ)
    (ω : Ω) (z w : Lattice)
    (hCov : ∀ x y v : Lattice, B (x + v) (y + v) ω = B x y (T v ω))
    (hColumn : z.1 = w.1) (hHeight : z.2 < w.2)
    (hAvoid : ∀ r s : ℕ,
      rightmostCocyclePath (fun x y => B x y ω) z r ≠
        rightmostCocyclePath (fun x y => B x y ω) w s)
    (hEastZ : rightmostCocycleSuccessor (fun x y => B x y ω) z = z + (1, 0))
    (hEastW : rightmostCocycleSuccessor (fun x y => B x y ω) w = w + (1, 0)) :
    ∃ m : ℕ, 0 < m ∧ w = z + (0, (m : ℤ)) ∧
      (∀ r s : ℕ,
        rightmostCocyclePath (fun x y => B x y (T z ω)) 0 r ≠
          rightmostCocyclePath (fun x y => B x y (T z ω)) (0, (m : ℤ)) s) ∧
      rightmostCocycleSuccessor (fun x y => B x y (T z ω)) 0 = (1, 0) ∧
      rightmostCocycleSuccessor (fun x y => B x y (T z ω)) (0, (m : ℤ)) =
        (0, (m : ℤ)) + (1, 0) := by
  let m := (w.2 - z.2).toNat
  have hmCast : (m : ℤ) = w.2 - z.2 := Int.toNat_of_nonneg (by omega)
  have hm : 0 < m := by omega
  have hPoint : w = z + (0, (m : ℤ)) := by
    apply Prod.ext
    · simp only [Prod.fst_add, add_zero]
      exact hColumn.symm
    · simp only [Prod.snd_add]
      omega
  have hStart : (0, (m : ℤ)) + z = w := by rw [add_comm, ← hPoint]
  let C : Lattice → Lattice → ℝ := fun x y => B x y ω
  let D : Lattice → Lattice → ℝ := fun x y => B x y (T z ω)
  have hDC : ∀ x y, D x y = C (x + z) (y + z) := fun x y => (hCov x y z).symm
  refine ⟨m, hm, hPoint, ?_, ?_, ?_⟩
  · intro r s hMeet
    apply hAvoid r s
    have hL : rightmostCocyclePath D 0 r + z = rightmostCocyclePath C z r := by
      simpa only [zero_add] using rightmostCocyclePath_translate C D z hDC 0 r
    have hU : rightmostCocyclePath D (0, (m : ℤ)) s + z =
        rightmostCocyclePath C w s := by
      simpa only [hStart] using rightmostCocyclePath_translate C D z hDC (0, (m : ℤ)) s
    exact hL.symm.trans ((congrArg (fun v : Lattice => v + z) hMeet).trans hU)
  · apply add_right_cancel (b := z)
    calc
      rightmostCocycleSuccessor D 0 + z = rightmostCocycleSuccessor C z := by
        simpa only [zero_add] using rightmostCocycleSuccessor_translate C D z hDC 0
      _ = z + (1, 0) := hEastZ
      _ = (1, 0) + z := add_comm _ _
  · apply add_right_cancel (b := z)
    calc
      rightmostCocycleSuccessor D (0, (m : ℤ)) + z = rightmostCocycleSuccessor C w := by
        simpa only [hStart] using rightmostCocycleSuccessor_translate C D z hDC (0, (m : ℤ))
      _ = w + (1, 0) := hEastW
      _ = ((0, (m : ℤ)) + (1, 0)) + z := by rw [← hStart]; ac_rfl

private theorem pair_measurable_components
    {Ω : Type*} [MeasurableSpace Ω]
    (B : Lattice → Lattice → Ω → ℝ) (hMeas : ∀ x y, Measurable (B x y)) (m : ℕ) :
    MeasurableSet {ω | ∀ r s : ℕ,
      rightmostCocyclePath (fun x y => B x y ω) 0 r ≠
        rightmostCocyclePath (fun x y => B x y ω) (0, (m : ℤ)) s} ∧
    MeasurableSet {ω | rightmostCocycleSuccessor (fun x y => B x y ω) 0 = (1, 0)} ∧
    MeasurableSet {ω | rightmostCocycleSuccessor (fun x y => B x y ω) (0, (m : ℤ)) =
      (0, (m : ℤ)) + (1, 0)} := by
  refine ⟨?_, measurableSet_eq_fun (measurable_rightmostCocycleSuccessor B hMeas 0)
    measurable_const, measurableSet_eq_fun
      (measurable_rightmostCocycleSuccessor B hMeas (0, (m : ℤ))) measurable_const⟩
  simp only [Set.ofPred_forall]
  exact MeasurableSet.iInter fun r => MeasurableSet.iInter fun s =>
    (measurableSet_eq_fun (measurable_rightmostCocyclePath B hMeas 0 r)
      (measurable_rightmostCocyclePath B hMeas (0, (m : ℤ)) s)).compl

private theorem pair_ae_covariance
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (T : Lattice → Ω → Ω)
    (B : Lattice → Lattice → Ω → ℝ) (hB : is_shift_covariant_cocycle P T B) :
    ∀ᵐ ω ∂P, ∀ x y z : Lattice, B (x + z) (y + z) ω = B x y (T z ω) :=
  ae_all_iff.mpr fun x => ae_all_iff.mpr fun y => ae_all_iff.mpr fun z => hB.2.1 x y z

-- Countable preimages suffice; no measurable choice of a random exit is needed.
private theorem pair_positive_stationary_event
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (T : Lattice → Ω → Ω)
    (hShift : ∀ z : Lattice, MeasurePreserving (T z) P P)
    (E : ℕ → Set Ω) (hE : ∀ m, MeasurableSet (E m))
    (D : Set Ω) (hPositive : 0 < P D)
    (hCover : ∀ᵐ ω ∂P, ω ∈ D → ∃ z : Lattice, ∃ m : ℕ, 0 < m ∧ T z ω ∈ E m) :
    ∃ m : ℕ, 0 < m ∧ 0 < P (E m) := by
  by_contra hNo
  have hZero (m : ℕ) (hm : 0 < m) : P (E m) = 0 := by
    by_contra h
    exact hNo ⟨m, hm, bot_lt_iff_ne_bot.mpr h⟩
  have hAvoid : ∀ᵐ ω ∂P, ∀ z : Lattice, ∀ m : ℕ, 0 < m → T z ω ∉ E m := by
    apply ae_all_iff.mpr
    intro z
    apply ae_all_iff.mpr
    intro m
    by_cases hm : 0 < m
    · have hPre : P ((T z) ⁻¹' E m) = 0 := by
        rw [(hShift z).measure_preimage (hE m).nullMeasurableSet, hZero m hm]
      filter_upwards [measure_eq_zero_iff_ae_notMem.mp hPre] with ω hω
      intro _
      exact hω
    · exact Filter.Eventually.of_forall fun _ hpos => False.elim (hm hpos)
  have hDZero : P D = 0 := measure_eq_zero_iff_ae_notMem.mpr (by
    filter_upwards [hCover, hAvoid] with ω hω hNot
    intro hD
    obtain ⟨z, m, hm, hEω⟩ := hω hD
    exact hNot z m hm hEω)
  exact (ne_of_gt hPositive) hDZero

/-- Normalize disjoint rays using a high point above their actual last departures.
This is Case 1 of GRS, arXiv:1510.00860v1, Appendix A, lines 1520–1533. -/
theorem exists_positive_normalized_rightmost_pair_with_high_weight
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : LPPStatements.NotAPointMass μ)
    (hmoment : ∃ p : ℝ, 2 < p ∧
      (∫⁻ t, ENNReal.ofReal (|t| ^ p) ∂μ) < ∞)
    {Ω : Type*} [TopologicalSpace Ω] [PolishSpace Ω]
    [MeasurableSpace Ω] [BorelSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (T : Lattice → Ω → Ω) (weights : Ω → LPPDifferentiability.Environment)
    (hzero : ∀ ω : Ω, T 0 ω = ω)
    (hadd : ∀ z w : Lattice, ∀ ω : Ω, T (z + w) ω = T z (T w ω))
    (hShift : ∀ z : Lattice, MeasurePreserving (T z) P P)
    (hWeightsMeas : Measurable weights)
    (hMarginal : P.map weights = environmentLaw μ)
    (hWeightsShift : ∀ z x : Lattice, ∀ ω : Ω,
      weights (T z ω) x = weights ω (z + x))
    (B : Lattice → Lattice → Ω → ℝ)
    (hB : is_shift_covariant_cocycle P T B)
    (hRec : recovers_weight_map_ae P weights B)
    (hInt₁ : Integrable (B 0 (1, 0)) P)
    (hInt₂ : Integrable (B 0 (0, 1)) P)
    (a b : Lattice)
    (hPositive : 0 < P {ω : Ω | ∀ r s : ℕ,
      rightmostCocyclePath (fun x y => B x y ω) a r ≠
        rightmostCocyclePath (fun x y => B x y ω) b s})
    (K : ℝ) (hHigh : 0 < μ (Set.Ioi K)) :
    ∃ m : ℕ, 0 < m ∧
      MeasurableSet {ω : Ω |
        (∀ r s : ℕ,
          rightmostCocyclePath (fun x y => B x y ω) 0 r ≠
            rightmostCocyclePath (fun x y => B x y ω) (0, (m : ℤ)) s) ∧
        rightmostCocycleSuccessor (fun x y => B x y ω) 0 = (1, 0) ∧
        rightmostCocycleSuccessor (fun x y => B x y ω) (0, (m : ℤ)) =
          (0, (m : ℤ)) + (1, 0) ∧
        ∃ r : ℕ, m < r ∧ K < weights ω (0, (r : ℤ))} ∧
      0 < P {ω : Ω |
        (∀ r s : ℕ,
          rightmostCocyclePath (fun x y => B x y ω) 0 r ≠
            rightmostCocyclePath (fun x y => B x y ω) (0, (m : ℤ)) s) ∧
        rightmostCocycleSuccessor (fun x y => B x y ω) 0 = (1, 0) ∧
        rightmostCocycleSuccessor (fun x y => B x y ω) (0, (m : ℤ)) =
          (0, (m : ℤ)) + (1, 0) ∧
        ∃ r : ℕ, m < r ∧ K < weights ω (0, (r : ℤ))} := by
  classical
  have hMeas (x y : Lattice) : Measurable (B x y) := by
    have hs : Measurable (fun ω : Ω => ((x, y), ω)) := measurable_const.prodMk measurable_id
    exact hB.1.comp hs
  let E (m : ℕ) : Set Ω := {ω : Ω |
        (∀ r s : ℕ,
          rightmostCocyclePath (fun x y => B x y ω) 0 r ≠
            rightmostCocyclePath (fun x y => B x y ω) (0, (m : ℤ)) s) ∧
        rightmostCocycleSuccessor (fun x y => B x y ω) 0 = (1, 0) ∧
        rightmostCocycleSuccessor (fun x y => B x y ω) (0, (m : ℤ)) =
          (0, (m : ℤ)) + (1, 0) ∧
        ∃ r : ℕ, m < r ∧ K < weights ω (0, (r : ℤ))}
  have hEMeas (m : ℕ) : MeasurableSet (E m) := by
    obtain ⟨hD, hZ, hM⟩ := pair_measurable_components B hMeas m
    have hHighMeas : MeasurableSet {ω : Ω | ∃ r : ℕ, m < r ∧
        K < weights ω (0, (r : ℤ))} := by
      simp only [Set.ofPred_exists]
      apply MeasurableSet.iUnion
      intro r
      by_cases hmr : m < r
      · simpa only [hmr, true_and, Function.comp_def] using measurableSet_lt measurable_const
          ((measurable_environment_eval (0, (r : ℤ))).comp hWeightsMeas)
      · simp [hmr]
    exact hD.inter (hZ.inter (hM.inter hHighMeas))
  let D : Set Ω := {ω | ∀ r s : ℕ,
    rightmostCocyclePath (fun x y => B x y ω) a r ≠
      rightmostCocyclePath (fun x y => B x y ω) b s}
  have hEscape := ae_rightmostCocyclePath_tendsto_coordinates_of_action
    μ hμ hmoment P T weights hzero hadd hShift hWeightsMeas hMarginal
    hWeightsShift B hB hRec hInt₁ hInt₂
  -- The high-column event is pulled back through the actual iid marginal.
  have hHighMap : ∀ᵐ η ∂P.map weights, ∀ H : ℤ, ∃ q : ℕ, H < (q : ℤ) ∧
      ∀ L : ℤ, ∃ r : ℕ, L < (r : ℤ) ∧ K < η ((q : ℤ), (r : ℤ)) := by
    rw [hMarginal]
    exact ae_arbitrarily_far_columns_with_unbounded_high_weights μ K hHigh
  have hHighAE := ae_of_ae_map hWeightsMeas.aemeasurable hHighMap
  have hCover : ∀ᵐ ω ∂P, ω ∈ D → ∃ z : Lattice, ∃ m : ℕ, 0 < m ∧ T z ω ∈ E m := by
    filter_upwards [hEscape, pair_ae_covariance P T B hB, hHighAE] with ω hEsc hCov hColumns
    intro hDisjoint
    let C : Lattice → Lattice → ℝ := fun x y => B x y ω
    change ∀ r s : ℕ, rightmostCocyclePath C a r ≠ rightmostCocyclePath C b s at hDisjoint
    obtain ⟨q, hq, hColumn⟩ := hColumns (max 0 (max a.1 b.1))
    have haMax := le_max_left a.1 b.1
    have hbMax := le_max_right a.1 b.1
    have hOuterMax := le_max_right (0 : ℤ) (max a.1 b.1)
    obtain ⟨z, w, hZq, hWq, hZW, hAvoid, hEZ, hEW, hBA, hBB, hWTrace⟩ :=
      pair_ordered_departures C a b (hEsc a).1 (hEsc b).1 hDisjoint (q : ℤ)
        (by omega) (by omega)
    -- Last-departure bounds put this high point above BOTH original traces.
    obtain ⟨r, hr, hWeight⟩ := hColumn w.2
    have hAboveA (t : ℕ) (ht : (rightmostCocyclePath C a t).1 = (q : ℤ)) :
        (rightmostCocyclePath C a t).2 < (r : ℤ) := lt_of_le_of_lt (hBA t ht) hr
    have hAboveB (t : ℕ) (ht : (rightmostCocyclePath C b t).1 = (q : ℤ)) :
        (rightmostCocyclePath C b t).2 < (r : ℤ) := lt_of_le_of_lt (hBB t ht) hr
    have hAboveW : w.2 < (r : ℤ) := by
      rcases hWTrace with ⟨t, ht⟩ | ⟨t, ht⟩
      · have hOn : (rightmostCocyclePath C a t).1 = (q : ℤ) := by rw [ht]; exact hWq
        simpa only [ht] using hAboveA t hOn
      · have hOn : (rightmostCocyclePath C b t).1 = (q : ℤ) := by rw [ht]; exact hWq
        simpa only [ht] using hAboveB t hOn
    obtain ⟨m, hm, hPoint, hPair, hEast0, hEastM⟩ := pair_translate_ordered T B ω z w
      hCov (hZq.trans hWq.symm) hZW hAvoid hEZ hEW
    let rNew := ((r : ℤ) - z.2).toNat
    have hRCast : (rNew : ℤ) = (r : ℤ) - z.2 := Int.toNat_of_nonneg (by omega)
    have hMHeight : w.2 = z.2 + (m : ℤ) := by
      simpa only [Prod.snd_add] using congrArg Prod.snd hPoint
    have hmr : m < rNew := by omega
    have hShiftWeight : K < weights (T z ω) (0, (rNew : ℤ)) := by
      rw [hWeightsShift]
      have hSite : z + (0, (rNew : ℤ)) = ((q : ℤ), (r : ℤ)) := by
        apply Prod.ext
        · simp only [Prod.fst_add, add_zero]
          exact hZq
        · simp only [Prod.snd_add]
          omega
      rw [hSite]
      exact hWeight
    exact ⟨z, m, hm, hPair, hEast0, hEastM, rNew, hmr, hShiftWeight⟩
  obtain ⟨m, hm, hPos⟩ := pair_positive_stationary_event P T hShift E hEMeas D hPositive hCover
  exact ⟨m, hm, hEMeas m, hPos⟩

/-- Normalize disjoint rays on a fixed column, without a high-weight condition.
This is Case 2 of GRS, arXiv:1510.00860v1, Appendix A, lines 1673–1687. -/
theorem exists_positive_normalized_rightmost_pair
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : LPPStatements.NotAPointMass μ)
    (hmoment : ∃ p : ℝ, 2 < p ∧
      (∫⁻ t, ENNReal.ofReal (|t| ^ p) ∂μ) < ∞)
    {Ω : Type*} [TopologicalSpace Ω] [PolishSpace Ω]
    [MeasurableSpace Ω] [BorelSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (T : Lattice → Ω → Ω) (weights : Ω → LPPDifferentiability.Environment)
    (hzero : ∀ ω : Ω, T 0 ω = ω)
    (hadd : ∀ z w : Lattice, ∀ ω : Ω, T (z + w) ω = T z (T w ω))
    (hShift : ∀ z : Lattice, MeasurePreserving (T z) P P)
    (hWeightsMeas : Measurable weights)
    (hMarginal : P.map weights = environmentLaw μ)
    (hWeightsShift : ∀ z x : Lattice, ∀ ω : Ω,
      weights (T z ω) x = weights ω (z + x))
    (B : Lattice → Lattice → Ω → ℝ)
    (hB : is_shift_covariant_cocycle P T B)
    (hRec : recovers_weight_map_ae P weights B)
    (hInt₁ : Integrable (B 0 (1, 0)) P)
    (hInt₂ : Integrable (B 0 (0, 1)) P)
    (a b : Lattice)
    (hPositive : 0 < P {ω : Ω | ∀ r s : ℕ,
      rightmostCocyclePath (fun x y => B x y ω) a r ≠
        rightmostCocyclePath (fun x y => B x y ω) b s}) :
    ∃ m : ℕ, 0 < m ∧
      MeasurableSet {ω : Ω |
        (∀ r s : ℕ,
          rightmostCocyclePath (fun x y => B x y ω) 0 r ≠
            rightmostCocyclePath (fun x y => B x y ω) (0, (m : ℤ)) s) ∧
        rightmostCocycleSuccessor (fun x y => B x y ω) 0 = (1, 0) ∧
        rightmostCocycleSuccessor (fun x y => B x y ω) (0, (m : ℤ)) =
          (0, (m : ℤ)) + (1, 0)} ∧
      0 < P {ω : Ω |
        (∀ r s : ℕ,
          rightmostCocyclePath (fun x y => B x y ω) 0 r ≠
            rightmostCocyclePath (fun x y => B x y ω) (0, (m : ℤ)) s) ∧
        rightmostCocycleSuccessor (fun x y => B x y ω) 0 = (1, 0) ∧
        rightmostCocycleSuccessor (fun x y => B x y ω) (0, (m : ℤ)) =
          (0, (m : ℤ)) + (1, 0)} := by
  classical
  have hMeas (x y : Lattice) : Measurable (B x y) := by
    have hs : Measurable (fun ω : Ω => ((x, y), ω)) := measurable_const.prodMk measurable_id
    exact hB.1.comp hs
  let E (m : ℕ) : Set Ω := {ω : Ω |
        (∀ r s : ℕ,
          rightmostCocyclePath (fun x y => B x y ω) 0 r ≠
            rightmostCocyclePath (fun x y => B x y ω) (0, (m : ℤ)) s) ∧
        rightmostCocycleSuccessor (fun x y => B x y ω) 0 = (1, 0) ∧
        rightmostCocycleSuccessor (fun x y => B x y ω) (0, (m : ℤ)) =
          (0, (m : ℤ)) + (1, 0)}
  have hEMeas (m : ℕ) : MeasurableSet (E m) := by
    obtain ⟨hD, hZ, hM⟩ := pair_measurable_components B hMeas m
    exact hD.inter (hZ.inter hM)
  let D : Set Ω := {ω | ∀ r s : ℕ,
    rightmostCocyclePath (fun x y => B x y ω) a r ≠
      rightmostCocyclePath (fun x y => B x y ω) b s}
  have hEscape := ae_rightmostCocyclePath_tendsto_coordinates_of_action
    μ hμ hmoment P T weights hzero hadd hShift hWeightsMeas hMarginal
    hWeightsShift B hB hRec hInt₁ hInt₂
  -- Case 2 uses a fixed signed column, with no preliminary threshold.
  let q : ℤ := max a.1 b.1 + 1
  have hCover : ∀ᵐ ω ∂P, ω ∈ D → ∃ z : Lattice, ∃ m : ℕ, 0 < m ∧ T z ω ∈ E m := by
    filter_upwards [hEscape, pair_ae_covariance P T B hB] with ω hEsc hCov
    intro hDisjoint
    let C : Lattice → Lattice → ℝ := fun x y => B x y ω
    change ∀ r s : ℕ, rightmostCocyclePath C a r ≠ rightmostCocyclePath C b s at hDisjoint
    have haMax := le_max_left a.1 b.1
    have hbMax := le_max_right a.1 b.1
    obtain ⟨z, w, hZq, hWq, hZW, hAvoid, hEZ, hEW, _, _, _⟩ :=
      pair_ordered_departures C a b (hEsc a).1 (hEsc b).1 hDisjoint q
        (by dsimp only [q]; omega) (by dsimp only [q]; omega)
    obtain ⟨m, hm, _, hPair, hEast0, hEastM⟩ := pair_translate_ordered T B ω z w
      hCov (hZq.trans hWq.symm) hZW hAvoid hEZ hEW
    exact ⟨z, m, hm, hPair, hEast0, hEastM⟩
  obtain ⟨m, hm, hPos⟩ := pair_positive_stationary_event P T hShift E hEMeas D hPositive hCover
  exact ⟨m, hm, hEMeas m, hPos⟩

end LPP.Busemann
