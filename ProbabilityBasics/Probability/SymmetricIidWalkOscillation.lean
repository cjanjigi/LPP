/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Probability.IdentDistrib
public import Mathlib.Probability.Independence.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Probability.Independence.ZeroOne
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.BorelCantelli
import Mathlib.MeasureTheory.Group.Arithmetic
import Mathlib.MeasureTheory.MeasurableSpace.MeasurablyGenerated
import Mathlib.Tactic

/-! A limited symmetric iid walk oscillation argument by independent positive
blocks, the tail zero-one law, and reflection symmetry. -/

@[expose] public section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal BigOperators

namespace ProbabilityBasics

private theorem unbounded_iff_nat (S : ℕ → ℝ) :
    (∀ K : ℝ, ∃ n : ℕ, K < S n) ↔
      ∀ M : ℕ, ∃ n : ℕ, (M : ℝ) < S n := by
  constructor
  · intro h M
    exact h M
  · intro h K
    obtain ⟨M, hM⟩ := exists_nat_gt K
    obtain ⟨n, hn⟩ := h M
    exact ⟨n, lt_trans hM hn⟩

private theorem unbounded_sum_shift_iff (f : ℕ → ℝ) (N : ℕ) :
    (∀ K : ℝ, ∃ n : ℕ, K < ∑ j ∈ Finset.range n, f j) ↔
      ∀ K : ℝ, ∃ n : ℕ, K < ∑ j ∈ Finset.range n, f (N + j) := by
  let S (n : ℕ) := ∑ j ∈ Finset.range n, f j
  constructor
  · intro h K
    obtain ⟨r, _hr, hmax⟩ := (Finset.range (N + 1)).exists_max_image S (by simp)
    obtain ⟨m, hm⟩ := h (max (S r) (S N + K))
    have hNm : N ≤ m := by
      by_contra hnot
      have hmem : m ∈ Finset.range (N + 1) := Finset.mem_range.mpr (by omega)
      have hupper := hmax m hmem
      have hstrict : S r < S m := lt_of_le_of_lt (le_max_left _ _) hm
      exact (not_lt_of_ge hupper) hstrict
    have hsplit : S m = S N + ∑ j ∈ Finset.range (m - N), f (N + j) := by
      calc
        S m = S (N + (m - N)) := congrArg S (Nat.add_sub_of_le hNm).symm
        _ = S N + ∑ j ∈ Finset.range (m - N), f (N + j) :=
          Finset.sum_range_add f N (m - N)
    have hlarge : S N + K < S m := lt_of_le_of_lt (le_max_right _ _) hm
    rw [hsplit] at hlarge
    exact ⟨m - N, by linarith⟩
  · intro h K
    obtain ⟨n, hn⟩ := h (K - S N)
    refine ⟨N + n, ?_⟩
    rw [Finset.sum_range_add]
    change K < S N + _
    linarith

private theorem measurableSet_unbounded_sums
    {Ω : Type*} [MeasurableSpace Ω] (X : ℕ → Ω → ℝ)
    (hMeas : ∀ n : ℕ, Measurable (X n)) :
    MeasurableSet {ω | ∀ K : ℝ, ∃ n : ℕ,
      K < ∑ j ∈ Finset.range n, X j ω} := by
  have heq : {ω | ∀ K : ℝ, ∃ n : ℕ, K < ∑ j ∈ Finset.range n, X j ω} =
      {ω | ∀ M : ℕ, ∃ n : ℕ, (M : ℝ) < ∑ j ∈ Finset.range n, X j ω} := by
    ext ω
    exact unbounded_iff_nat (fun n => ∑ j ∈ Finset.range n, X j ω)
  rw [heq]
  simp only [Set.ofPred_forall, Set.ofPred_exists]
  exact MeasurableSet.iInter fun M => MeasurableSet.iUnion fun n =>
    measurableSet_lt measurable_const ((Finset.range n).measurable_fun_sum fun j _ => hMeas j)

private theorem measure_unbounded_sums_zero_or_one
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ) (hMeas : ∀ n : ℕ, Measurable (X n))
    (hIndep : iIndepFun X P) :
    P {ω | ∀ K : ℝ, ∃ n : ℕ, K < ∑ j ∈ Finset.range n, X j ω} = 0 ∨
      P {ω | ∀ K : ℝ, ∃ n : ℕ, K < ∑ j ∈ Finset.range n, X j ω} = 1 := by
  let s : ℕ → MeasurableSpace Ω :=
    fun n => MeasurableSpace.comap (X n) inferInstance
  have hTail : MeasurableSet[Filter.limsup s atTop]
      {ω | ∀ K : ℝ, ∃ n : ℕ, K < ∑ j ∈ Finset.range n, X j ω} := by
    rw [Filter.limsup_eq_iInf_iSup_of_nat, MeasurableSpace.measurableSet_iInf]
    intro N
    let mTail : MeasurableSpace Ω := ⨆ i ≥ N, s i
    let : MeasurableSpace Ω := mTail
    have hCoordinate (j : ℕ) : Measurable (X (N + j)) := by
      have hle : s (N + j) ≤ mTail :=
        le_iSup_of_le (N + j) (le_iSup_of_le (by omega : N ≤ N + j) le_rfl)
      exact (comap_measurable (X (N + j))).mono hle le_rfl
    have hShift := measurableSet_unbounded_sums (fun j => X (N + j)) hCoordinate
    have heq : {ω | ∀ K : ℝ, ∃ n : ℕ, K < ∑ j ∈ Finset.range n, X j ω} =
        {ω | ∀ K : ℝ, ∃ n : ℕ, K < ∑ j ∈ Finset.range n, X (N + j) ω} := by
      ext ω
      exact unbounded_sum_shift_iff (fun j => X j ω) N
    rw [heq]
    exact hShift
  exact measure_zero_or_one_of_measurableSet_limsup_atTop
    (fun n => (hMeas n).comap_le) hIndep.iIndep hTail

private theorem identDistrib_walk_neg
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ) (hMeas : ∀ n : ℕ, Measurable (X n))
    (hIndep : iIndepFun X P)
    (hIdent : ∀ n : ℕ, IdentDistrib (X n) (X 0) P P)
    (hSymm : IdentDistrib (X 0) (fun ω => -(X 0 ω)) P P) :
    IdentDistrib (fun ω n => X n ω) (fun ω n => -(X n ω)) P P := by
  have hNegMeas (n : ℕ) : Measurable (fun ω => -(X n ω)) := (hMeas n).neg
  have hNegIndep : iIndepFun (fun n ω => -(X n ω)) P :=
    hIndep.comp (fun _ (r : ℝ) => -r) (fun _ => measurable_neg)
  refine ⟨(measurable_pi_iff.mpr hMeas).aemeasurable,
    (measurable_pi_iff.mpr hNegMeas).aemeasurable, ?_⟩
  rw [hIndep.map_fun_eq_infinitePi_map hMeas,
    hNegIndep.map_fun_eq_infinitePi_map hNegMeas]
  congr 1
  funext n
  exact ((hIdent n).trans
    (hSymm.trans ((hIdent n).comp measurable_neg).symm)).map_eq

private theorem measure_unbounded_sums_neg_eq
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ) (hMeas : ∀ n : ℕ, Measurable (X n))
    (hIndep : iIndepFun X P)
    (hIdent : ∀ n : ℕ, IdentDistrib (X n) (X 0) P P)
    (hSymm : IdentDistrib (X 0) (fun ω => -(X 0 ω)) P P) :
    P {ω | ∀ K : ℝ, ∃ n : ℕ, K < ∑ j ∈ Finset.range n, X j ω} =
      P {ω | ∀ K : ℝ, ∃ n : ℕ, K < ∑ j ∈ Finset.range n, -(X j ω)} := by
  exact (identDistrib_walk_neg P X hMeas hIndep hIdent hSymm).measure_mem_eq
    (measurableSet_unbounded_sums (fun n (a : ℕ → ℝ) => a n) measurable_pi_apply)

private theorem positive_threshold_of_symmetric_nonzero
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → ℝ) (hSymm : IdentDistrib X (fun ω => -(X ω)) P P)
    (hNonzero : ¬ ∀ᵐ ω ∂P, X ω = 0) :
    ∃ a : ℝ, 0 < a ∧ 0 < P {ω | a ≤ X ω} := by
  classical
  have hPositive : P {ω | 0 < X ω} ≠ 0 := by
    intro hzero
    have hEq := hSymm.measure_mem_eq (s := Set.Ioi (0 : ℝ)) measurableSet_Ioi
    change P {ω | 0 < X ω} = P {ω | 0 < -(X ω)} at hEq
    have hNegative : P {ω | X ω < 0} = 0 := by
      simpa only [neg_pos] using hEq.symm.trans hzero
    have hNonpos : ∀ᵐ ω ∂P, X ω ≤ 0 := by
      rw [ae_iff]
      simpa only [not_le] using hzero
    have hNonneg : ∀ᵐ ω ∂P, 0 ≤ X ω := by
      rw [ae_iff]
      simpa only [not_le] using hNegative
    apply hNonzero
    filter_upwards [hNonpos, hNonneg] with ω hle hge
    exact le_antisymm hle hge
  let A (n : ℕ) : Set Ω := {ω | 1 / ((n : ℝ) + 1) < X ω}
  have hUnion : (⋃ n : ℕ, A n) = {ω | 0 < X ω} := by
    ext ω
    constructor
    · intro h
      obtain ⟨n, hn⟩ := Set.mem_iUnion.mp h
      exact lt_trans (by positivity : (0 : ℝ) < 1 / ((n : ℝ) + 1)) hn
    · intro h
      change 0 < X ω at h
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt h
      exact Set.mem_iUnion.mpr ⟨n, hn⟩
  obtain ⟨n, hn⟩ := exists_measure_pos_of_not_measure_iUnion_null
    (show P (⋃ n : ℕ, A n) ≠ 0 by rw [hUnion]; exact hPositive)
  refine ⟨1 / ((n : ℝ) + 1), by positivity, ?_⟩
  apply lt_of_lt_of_le hn
  apply measure_mono
  intro ω h
  change 1 / ((n : ℝ) + 1) < X ω at h
  change 1 / ((n : ℝ) + 1) ≤ X ω
  exact le_of_lt h

private theorem abs_escape_of_positive_runs (f : ℕ → ℝ) (a : ℝ) (ha : 0 < a)
    (hRuns : ∀ L : ℕ, 0 < L → ∃ k : ℕ,
      ∀ j : Fin L, a ≤ f (k * L + j.val)) :
    ∀ K : ℝ, ∃ n : ℕ, K < |∑ j ∈ Finset.range n, f j| := by
  classical
  intro K
  by_contra hnot
  push Not at hnot
  obtain ⟨L, hL⟩ := exists_nat_gt (max ((2 * K) / a) 0)
  have hLreal : (0 : ℝ) < (L : ℝ) := lt_of_le_of_lt (le_max_right _ _) hL
  have hLpos : 0 < L := by exact_mod_cast hLreal
  have hLarge : 2 * K < (L : ℝ) * a :=
    (div_lt_iff₀ ha).mp (lt_of_le_of_lt (le_max_left _ _) hL)
  obtain ⟨k, hk⟩ := hRuns L hLpos
  have hRunSum : (L : ℝ) * a ≤ ∑ j ∈ Finset.range L, f (k * L + j) := by
    calc
      (L : ℝ) * a = ∑ j ∈ Finset.range L, a := by simp
      _ ≤ ∑ j ∈ Finset.range L, f (k * L + j) :=
        Finset.sum_le_sum fun j hj => hk ⟨j, Finset.mem_range.mp hj⟩
  have hSplit := Finset.sum_range_add f (k * L) L
  have hEnd := (abs_le.mp (hnot (k * L + L))).2
  have hStart := (abs_le.mp (hnot (k * L))).1
  linarith

private theorem positive_block_probability
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ) (hIndep : iIndepFun X P)
    (hIdent : ∀ n : ℕ, IdentDistrib (X n) (X 0) P P)
    (L k : ℕ) (a : ℝ) :
    P {ω | ∀ j : Fin L, a ≤ X (k * L + j.val) ω} =
      (P {ω | a ≤ X 0 ω}) ^ L := by
  classical
  have hBlockIndep : iIndepFun (fun j : Fin L => X (k * L + j.val)) P :=
    hIndep.precomp (by
      intro i j h
      apply Fin.ext
      change k * L + i.val = k * L + j.val at h
      exact Nat.add_left_cancel h)
  have hProduct := hBlockIndep.measure_inter_preimage_eq_mul
    (Finset.univ : Finset (Fin L)) (sets := fun _ => Set.Ici a)
    (fun _ _ => measurableSet_Ici)
  have hSet : (⋂ j ∈ (Finset.univ : Finset (Fin L)),
      X (k * L + j.val) ⁻¹' Set.Ici a) =
        {ω | ∀ j : Fin L, a ≤ X (k * L + j.val) ω} := by
    ext ω
    simp
  rw [hSet] at hProduct
  calc
    P {ω | ∀ j : Fin L, a ≤ X (k * L + j.val) ω} =
        ∏ j : Fin L, P (X (k * L + j.val) ⁻¹' Set.Ici a) := hProduct
    _ = ∏ _j : Fin L, P {ω | a ≤ X 0 ω} :=
      Finset.prod_congr rfl fun j _ =>
        (hIdent (k * L + j.val)).measure_mem_eq measurableSet_Ici
    _ = (P {ω | a ≤ X 0 ω}) ^ L := by simp

-- Finite induction gives independence of the entire block-event family.
-- Each induction step groups all earlier coordinates against the new block.
private theorem independent_positive_block_events
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ) (hMeas : ∀ n : ℕ, Measurable (X n))
    (hIndep : iIndepFun X P) (L : ℕ) (hL : 0 < L) (a : ℝ) :
    iIndepSet (fun k : ℕ =>
      {ω | ∀ j : Fin L, a ≤ X (k * L + j.val) ω}) P := by
  classical
  let s (i : ℕ) : MeasurableSpace Ω := MeasurableSpace.comap (X i) inferInstance
  let m (S : Set ℕ) : MeasurableSpace Ω := ⨆ i ∈ {i : ℕ | i / L ∈ S}, s i
  let B (k : ℕ) : Set Ω := {ω | ∀ j : Fin L, a ≤ X (k * L + j.val) ω}
  have hMeasB (k : ℕ) : MeasurableSet (B k) := by
    change MeasurableSet {ω | ∀ j : Fin L, a ≤ X (k * L + j.val) ω}
    rw [Set.ofPred_forall]
    exact MeasurableSet.iInter fun j => measurableSet_le measurable_const (hMeas _)
  have hBlockMeas (S : Set ℕ) (k : ℕ) (hk : k ∈ S) :
      MeasurableSet[m S] (B k) := by
    let : MeasurableSpace Ω := m S
    change MeasurableSet {ω | ∀ j : Fin L, a ≤ X (k * L + j.val) ω}
    rw [Set.ofPred_forall]
    apply MeasurableSet.iInter
    intro j
    have hQuot : (k * L + j.val) / L = k := by
      rw [Nat.mul_comm k L, Nat.mul_add_div hL, Nat.div_eq_of_lt j.isLt, Nat.add_zero]
    have hle : s (k * L + j.val) ≤ m S :=
      le_iSup_of_le (k * L + j.val)
        (le_iSup_of_le (show (k * L + j.val) / L ∈ S by rw [hQuot]; exact hk) le_rfl)
    have hCoordinate : Measurable (X (k * L + j.val)) :=
      (comap_measurable (X (k * L + j.val))).mono hle le_rfl
    exact measurableSet_le measurable_const hCoordinate
  apply (iIndepSet_iff_meas_biInter hMeasB).mpr
  intro t
  induction t using Finset.induction_on with
  | empty => simp
  | @insert k t hk ih =>
    have hDisjoint : Disjoint {i : ℕ | i / L ∈ (t : Set ℕ)}
        {i : ℕ | i / L ∈ ({k} : Set ℕ)} := by
      apply Set.disjoint_left.mpr
      intro i hi hj
      have heq : i / L = k := hj
      exact hk (heq ▸ hi)
    have hGroups : Indep (m (t : Set ℕ)) (m ({k} : Set ℕ)) P :=
      indep_iSup_of_disjoint (fun i => (hMeas i).comap_le) hIndep.iIndep hDisjoint
    have hPast : MeasurableSet[m (t : Set ℕ)] (⋂ i ∈ t, B i) :=
      MeasurableSet.iInter fun i => MeasurableSet.iInter fun hi => hBlockMeas t i hi
    have hProduct := (Indep_iff _ _ P).mp hGroups _ _ hPast
      (hBlockMeas {k} k (by simp))
    have hSet : (⋂ i ∈ insert k t, B i) = (⋂ i ∈ t, B i) ∩ B k := by
      ext ω
      simp only [Set.mem_iInter, Finset.mem_insert, forall_eq_or_imp, Set.mem_inter_iff]
      exact and_comm
    rw [hSet, hProduct, ih, Finset.prod_insert hk]
    exact mul_comm _ _

private theorem ae_exists_positive_block_of_independent_events
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ) (hMeas : ∀ n : ℕ, Measurable (X n))
    (hIndep : iIndepFun X P)
    (hIdent : ∀ n : ℕ, IdentDistrib (X n) (X 0) P P)
    (L : ℕ) (a : ℝ) (hMass : 0 < P {ω | a ≤ X 0 ω})
    (hBlocks : iIndepSet (fun k : ℕ =>
      {ω | ∀ j : Fin L, a ≤ X (k * L + j.val) ω}) P) :
    ∀ᵐ ω ∂P, ∃ k : ℕ, ∀ j : Fin L, a ≤ X (k * L + j.val) ω := by
  let B (k : ℕ) : Set Ω := {ω | ∀ j : Fin L, a ≤ X (k * L + j.val) ω}
  have hMeasB (k : ℕ) : MeasurableSet (B k) := by
    rw [show B k = ⋂ j : Fin L, {ω | a ≤ X (k * L + j.val) ω} by ext ω; simp [B]]
    exact MeasurableSet.iInter fun j => measurableSet_le measurable_const (hMeas _)
  have hProb (k : ℕ) : P (B k) = (P {ω | a ≤ X 0 ω}) ^ L :=
    positive_block_probability P X hIndep hIdent L k a
  have hDiverges : (∑' k : ℕ, P (B k)) = ∞ := by
    simp_rw [hProb]
    exact ENNReal.tsum_const_eq_top_of_ne_zero (pow_ne_zero L (ne_of_gt hMass))
  have hFull : P (Filter.limsup B atTop) = 1 :=
    measure_limsup_eq_one hMeasB hBlocks hDiverges
  have hAE : ∀ᵐ ω ∂P, ω ∈ Filter.limsup B atTop :=
    (mem_ae_iff_prob_eq_one (MeasurableSet.measurableSet_limsup hMeasB)).mpr hFull
  filter_upwards [hAE] with ω hω
  exact (Filter.mem_limsup_iff_frequently_mem.mp hω).exists

private theorem ae_positive_escape_of_ae_abs_escape
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ) (hMeas : ∀ n : ℕ, Measurable (X n))
    (hIndep : iIndepFun X P)
    (hIdent : ∀ n : ℕ, IdentDistrib (X n) (X 0) P P)
    (hSymm : IdentDistrib (X 0) (fun ω => -(X 0 ω)) P P)
    (hEscape : ∀ᵐ ω ∂P, ∀ K : ℝ, ∃ n : ℕ,
      K < |∑ j ∈ Finset.range n, X j ω|) :
    ∀ᵐ ω ∂P, ∀ K : ℝ, ∃ n : ℕ, K < ∑ j ∈ Finset.range n, X j ω := by
  classical
  rcases measure_unbounded_sums_zero_or_one P X hMeas hIndep with hZero | hOne
  · have hNegZero : P {ω | ∀ K : ℝ, ∃ n : ℕ,
        K < ∑ j ∈ Finset.range n, -(X j ω)} = 0 :=
      (measure_unbounded_sums_neg_eq P X hMeas hIndep hIdent hSymm).symm.trans hZero
    have hNotPositive : ∀ᵐ ω ∂P, ¬ (∀ K : ℝ, ∃ n : ℕ,
        K < ∑ j ∈ Finset.range n, X j ω) := by
      rw [ae_iff]
      simpa only [not_not] using hZero
    have hNotNegative : ∀ᵐ ω ∂P, ¬ (∀ K : ℝ, ∃ n : ℕ,
        K < ∑ j ∈ Finset.range n, -(X j ω)) := by
      rw [ae_iff]
      simpa only [not_not] using hNegZero
    filter_upwards [hEscape, hNotPositive, hNotNegative] with ω hEsc hPos hNeg
    exfalso
    push Not at hPos hNeg
    obtain ⟨U, hU⟩ := hPos
    obtain ⟨V, hV⟩ := hNeg
    obtain ⟨n, hn⟩ := hEsc (max U V)
    have hLow : -V ≤ ∑ j ∈ Finset.range n, X j ω := by
      have hv := hV n
      rw [Finset.sum_neg_distrib] at hv
      linarith
    have hBound : |∑ j ∈ Finset.range n, X j ω| ≤ max U V :=
      abs_le.mpr ⟨by have hv := le_max_right U V; linarith,
        (hU n).trans (le_max_left U V)⟩
    exact (not_lt_of_ge hBound) hn
  · exact (mem_ae_iff_prob_eq_one (measurableSet_unbounded_sums X hMeas)).mpr hOne

/-- A nondegenerate symmetric iid real walk has arbitrarily large positive
partial sums almost surely. Independent positive blocks, tail zero-one, and
reflection supply the limited walk step used in GRS, arXiv:1510.00860v1,
Lemma 5.1, separately for each adjacent-axis orientation. -/
theorem ae_unbounded_above_sum_of_symmetric_iid
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ)
    (hMeas : ∀ n : ℕ, Measurable (X n))
    (hIndep : iIndepFun X P)
    (hIdent : ∀ n : ℕ, IdentDistrib (X n) (X 0) P P)
    (hSymm : IdentDistrib (X 0) (fun ω => -(X 0 ω)) P P)
    (hNonzero : ¬ ∀ᵐ ω ∂P, X 0 ω = 0) :
    ∀ᵐ ω ∂P, ∀ K : ℝ, ∃ n : ℕ,
      K < ∑ j ∈ Finset.range n, X j ω := by
  obtain ⟨a, ha, hMass⟩ := positive_threshold_of_symmetric_nonzero P (X 0) hSymm hNonzero
  have hRuns : ∀ᵐ ω ∂P, ∀ L : ℕ, 0 < L → ∃ k : ℕ,
      ∀ j : Fin L, a ≤ X (k * L + j.val) ω := by
    apply ae_all_iff.mpr
    intro L
    by_cases hL : 0 < L
    · filter_upwards [ae_exists_positive_block_of_independent_events P X hMeas hIndep
        hIdent L a hMass (independent_positive_block_events P X hMeas hIndep L hL a)]
        with ω hω
      exact fun _ => hω
    · exact ae_of_all P fun _ h => (hL h).elim
  have hEscape : ∀ᵐ ω ∂P, ∀ K : ℝ, ∃ n : ℕ,
      K < |∑ j ∈ Finset.range n, X j ω| := by
    filter_upwards [hRuns] with ω hω
    exact abs_escape_of_positive_runs (fun j => X j ω) a ha hω
  exact ae_positive_escape_of_ae_abs_escape P X hMeas hIndep hIdent hSymm hEscape

end ProbabilityBasics
