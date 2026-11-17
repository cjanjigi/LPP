/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.MeasureTheory.Measure.Map
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
public import Mathlib.Data.Finset.Basic
import Mathlib.MeasureTheory.Function.EssSup
import Mathlib.Topology.Instances.EReal.Lemmas
import Mathlib.Data.Rat.Encodable
import Mathlib.MeasureTheory.Measure.Restrict
import Mathlib.Order.Filter.Finite

/-! The essential-infimum dichotomy for retaining a positive finite-boundary event. -/

@[expose] public section

open MeasureTheory Filter

namespace ProbabilityBasics

private theorem rational_cut_below_finite_values
    {ι : Type*} (b : EReal) (hb : b < ⊤) (F : Finset ι) (f : ι → ℝ) :
    (∀ j ∈ F, b < (f j : EReal)) →
      ∃ q : ℚ, b < ((q : ℝ) : EReal) ∧ ∀ j ∈ F, (q : ℝ) < f j := by
  classical
  induction F using Finset.induction_on with
  | empty =>
      intro _
      obtain ⟨q, hbq, _⟩ := EReal.exists_rat_btwn_of_lt hb
      exact ⟨q, hbq, by simp⟩
  | @insert j F _ ih =>
      intro hF
      have hOld : ∀ k ∈ F, b < (f k : EReal) :=
        fun k hk => hF k (Finset.mem_insert_of_mem hk)
      obtain ⟨q0, hbq0, hq0⟩ := ih hOld
      have hJ : b < (f j : EReal) := hF j (Finset.mem_insert_self j F)
      obtain ⟨q, hbq, hqMin⟩ := EReal.exists_rat_btwn_of_lt (lt_min hbq0 hJ)
      have hqOld : (q : ℝ) < (q0 : ℝ) :=
        EReal.coe_lt_coe_iff.mp (lt_of_lt_of_le hqMin (min_le_left _ _))
      have hqJ : (q : ℝ) < f j :=
        EReal.coe_lt_coe_iff.mp (lt_of_lt_of_le hqMin (min_le_right _ _))
      refine ⟨q, hbq, ?_⟩
      intro k hk
      rcases Finset.mem_insert.mp hk with rfl | hk
      · exact hqJ
      · exact hqOld.trans (hq0 k hk)

private theorem lower_tail_pos_of_essInf_lt
    (μ : Measure ℝ) (K : ℝ)
    (hK : essInf (fun t : ℝ => (t : EReal)) μ < (K : EReal)) :
    0 < μ (Set.Iic K) := by
  apply pos_iff_ne_zero.mpr
  intro hZero
  have hStrict : ∀ᵐ (t : ℝ) ∂μ, K < t := by
    apply ae_iff.mpr
    have hSet : {t : ℝ | ¬ K < t} = Set.Iic K := by
      ext t
      simp only [Set.mem_ofPred_eq, not_lt, Set.mem_Iic]
    rw [hSet]
    exact hZero
  have hLower : ∀ᵐ (t : ℝ) ∂μ, (K : EReal) ≤ (t : EReal) := by
    filter_upwards [hStrict] with t ht
    exact EReal.coe_le_coe_iff.mpr ht.le
  have hInf : (K : EReal) ≤ essInf (fun t : ℝ => (t : EReal)) μ :=
    le_essInf_of_ae_le (K : EReal) hLower
  exact (not_le_of_gt hK) hInf

/-- Either the common real law has an attained finite essential lower bound,
or a deterministic positive lower-tail cut keeps positive mass in an arbitrary
positive event while all selected boundary variables lie strictly above the cut.
This is the threshold selection in Georgiou, Rassoul-Agha and Seppäläinen,
arXiv:1510.00860v1, Appendix A, lines 1517–1519 and 1673–1685. -/
theorem exists_lower_bound_atom_or_positive_finite_boundary_cut
    {Ω ι : Type*} [MeasurableSpace Ω]
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Y : ι → Ω → ℝ) (hY : ∀ j, Measurable (Y j))
    (hLaw : ∀ j, P.map (Y j) = μ)
    (A : Set Ω) (hA : MeasurableSet A) (hAPos : 0 < P A)
    (F : Finset ι) :
    (∃ K : ℝ, (∀ᵐ t ∂μ, K ≤ t) ∧ 0 < μ {K}) ∨
      ∃ K : ℝ, 0 < μ (Set.Iic K) ∧
        0 < P (A ∩ {ω | ∀ j ∈ F, K < Y j ω}) := by
  classical
  let b : EReal := essInf (fun t : ℝ => (t : EReal)) μ
  have hBound : ∀ᵐ (t : ℝ) ∂μ, b ≤ (t : EReal) :=
    ae_essInf_le (f := fun t : ℝ => (t : EReal)) (μ := μ)
  have hbTop : b ≠ ⊤ := by
    obtain ⟨t, ht⟩ := hBound.exists
    intro hTop
    rw [hTop] at ht
    exact (not_le_of_gt (EReal.coe_lt_top t)) ht
  have hbLtTop : b < ⊤ := lt_top_iff_ne_top.mpr hbTop

  -- Strict scalar lower bounds pull back through the actual common marginals.
  have hCutCase (hStrict : ∀ᵐ (t : ℝ) ∂μ, b < (t : EReal)) :
      ∃ K : ℝ, 0 < μ (Set.Iic K) ∧
        0 < P (A ∩ {ω | ∀ j ∈ F, K < Y j ω}) := by
    let Q : Type := {q : ℚ // b < ((q : ℝ) : EReal)}
    let B : Q → Set Ω := fun q => {ω | ∀ j ∈ F, (q.1 : ℝ) < Y j ω}
    have hBoundary : ∀ᵐ ω ∂P, ∀ j ∈ F, b < (Y j ω : EReal) := by
      apply (Filter.eventually_all_finset F).mpr
      intro j _
      have hMapped : ∀ᵐ (t : ℝ) ∂P.map (Y j), b < (t : EReal) := by
        rw [hLaw j]
        exact hStrict
      exact (Measure.tendsto_ae_map (μ := P) (hY j).aemeasurable).eventually hMapped
    have hCover : ∀ᵐ ω ∂P, ω ∈ ⋃ q : Q, B q := by
      filter_upwards [hBoundary] with ω hω
      obtain ⟨q, hbq, hq⟩ :=
        rational_cut_below_finite_values b hbLtTop F (fun j => Y j ω) hω
      exact Set.mem_iUnion.mpr ⟨(⟨q, hbq⟩ : Q), hq⟩

    -- Countable exhaustion is applied inside A; A need not be independent of Y.
    have hRestricted : (Set.univ : Set Ω) ≤ᵐ[P.restrict A] ⋃ q : Q, B q := by
      filter_upwards [ae_restrict_of_ae hCover] with ω hω
      exact fun _ => hω
    have hRestrictedPos : 0 < (P.restrict A) Set.univ := by
      simpa only [Measure.restrict_apply_univ] using hAPos
    have hUnionPos : 0 < (P.restrict A) (⋃ q : Q, B q) :=
      lt_of_lt_of_le hRestrictedPos (measure_mono_ae hRestricted)
    obtain ⟨q, hqPos⟩ := exists_measure_pos_of_not_measure_iUnion_null hUnionPos.ne'
    refine ⟨(q.1 : ℝ), lower_tail_pos_of_essInf_lt μ (q.1 : ℝ) q.2, ?_⟩
    rw [Measure.restrict_apply' hA, Set.inter_comm] at hqPos
    exact hqPos

  -- Negative infinite infimum and finite nonattainment both give strict AE bounds.
  by_cases hbBot : b = ⊥
  · right
    apply hCutCase
    exact Filter.Eventually.of_forall (fun (t : ℝ) => by rw [hbBot]; exact EReal.bot_lt_coe t)
  · have hReal : (b.toReal : EReal) = b := EReal.coe_toReal hbTop hbBot
    have hLowerReal : ∀ᵐ (t : ℝ) ∂μ, b.toReal ≤ t := by
      filter_upwards [hBound] with t ht
      apply EReal.coe_le_coe_iff.mp
      simpa only [hReal] using ht
    by_cases hAtom : 0 < μ {b.toReal}
    · exact Or.inl ⟨b.toReal, hLowerReal, hAtom⟩
    · right
      apply hCutCase
      have hZero : μ {b.toReal} = 0 := nonpos_iff_eq_zero.mp (not_lt.mp hAtom)
      have hNotEqual : ∀ᵐ (t : ℝ) ∂μ, t ≠ b.toReal := by
        apply ae_iff.mpr
        have hSet : {t : ℝ | ¬ t ≠ b.toReal} = {b.toReal} := by
          ext t
          simp only [Set.mem_ofPred_eq, not_not, Set.mem_singleton_iff]
        rw [hSet]
        exact hZero
      filter_upwards [hLowerReal, hNotEqual] with t hle hne
      have hlt : b.toReal < t := by
        by_contra hNot
        exact hne (le_antisymm (not_lt.mp hNot) hle)
      have hEReal : (b.toReal : EReal) < (t : EReal) := EReal.coe_lt_coe_iff.mpr hlt
      simpa only [hReal] using hEReal

end ProbabilityBasics
