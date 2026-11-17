/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Busemann.Frozen.Definitions.OutsideSigma
public import Busemann.Frozen.Definitions.RecoveryAE
public import Busemann.Frozen.Definitions.Additive
public import Busemann.Process.RightmostPaths
import Busemann.Process.CorridorHighSitesPartition
import Busemann.Process.OutsideFieldMeasurability
import ProbabilityBasics.Probability.ConditionalModification
import Busemann.Process.RightmostPathFiniteLowering
import Busemann.Process.RightmostPathVerticalOrder
import Mathlib.Tactic

/-! Positive conditional corridor modification and measurable shielding. -/

@[expose] public section

open MeasureTheory LPPDifferentiability
open scoped BigOperators ENNReal

namespace LPP.Busemann

/-- A fixed-cutoff finite-block conditional positivity assumption gives a positive
measurable event of low, additive, recovering samples with a shielded middle tail.
Old same-fiber witnesses and their high-site sets are retained almost surely.
This is the probabilistic assembly of GRS arXiv:1510.00860v1, Appendix A,
Lemma A.2 and A.4, reading lines 1441–1474 and 1581–1632. -/
theorem exists_positive_shielded_ray_event_of_finite_block_condExp
    {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (weights : Ω → LPPDifferentiability.Environment)
    (hWeightsMeas : Measurable weights)
    (B : Lattice → Lattice → Ω → ℝ)
    (hBMeas : ∀ x y : Lattice, Measurable (B x y))
    (hAdd : ∀ᵐ s ∂P, is_additive (fun x y => B x y s))
    (hRec : recovers_weight_map_ae P weights B)
    (K : ℝ)
    (hFiniteBlock : ∀ V : Finset Lattice, ∀ᵐ s ∂P,
        0 < (MeasureTheory.condExp (outsideSigma weights B V) P
          (Set.indicator {s : Ω | ∀ z ∈ V, weights s z ≤ K}
            (fun _ => (1 : ℝ)))) s)
    (m ell M1 M2 : ℕ) (hm : 0 < m) (hmell : m < ell)
    (hM1 : 0 < M1) (hTop : ell < M2)
    (A : Set Ω) (hAMeas : MeasurableSet A) (hAPos : 0 < P A)
    (hGeometry : ∀ s ∈ A,
      (∀ r t : ℕ,
        rightmostCocyclePath (fun x y => B x y s) 0 r ≠
          rightmostCocyclePath (fun x y => B x y s) (0, (m : ℤ)) t) ∧
      (∀ r t : ℕ,
        rightmostCocyclePath (fun x y => B x y s) (0, (m : ℤ)) r ≠
          rightmostCocyclePath (fun x y => B x y s) (0, (ell : ℤ)) t) ∧
      rightmostCocyclePath (fun x y => B x y s) 0 (M1 + M2) =
        ((M1 : ℤ), (M2 : ℤ)) ∧
      ∃ (a1 a2 H : ℤ) (nM nU nE : ℕ),
        rightmostCocyclePath (fun x y => B x y s) (0, (m : ℤ)) nM =
          (a2, (M2 : ℤ)) ∧
        rightmostCocyclePath (fun x y => B x y s) (0, (ell : ℤ)) nU =
          (a1, (M2 : ℤ)) ∧
        rightmostCocyclePath (fun x y => B x y s) (0, (ell : ℤ)) nE =
          ((M1 : ℤ), H))
    (hWeights : ∀ s ∈ A,
      (∀ j : ℤ, 0 ≤ j → j < (ell : ℤ) → K ≤ weights s (0, j)) ∧
      ((((M2 : ℤ) - (ell : ℤ) : ℤ) : ℝ) * K <
        ∑ j ∈ Finset.Ico (ell : ℤ) (M2 : ℤ), weights s (0, j)) ∧
      (∀ i : ℤ, 0 ≤ i → i ≤ (M1 : ℤ) → K ≤ weights s (i, (M2 : ℤ)))) :
    let F : Finset Lattice :=
      (Finset.Icc (1 : ℤ) ((M1 : ℤ) - 1)).product
        (Finset.Icc (1 : ℤ) ((M2 : ℤ) - 1))
    ∃ V : Finset Lattice, ∃ D : Set Ω,
      MeasurableSet D ∧ 0 < P D ∧
      (∀ᵐ sNew ∂P, sNew ∈ D → ∃ sOld ∈ A,
        is_additive (fun x y => B x y sOld) ∧
        recovers_environment (weights sOld) (fun x y => B x y sOld) ∧
        (∀ z : Lattice, z ∈ V ↔
          z ∈ F ∧ 0 < z.1 ∧ z.2 < (M2 : ℤ) ∧
          (∃ n : ℕ, (n : ℤ) = z.1 + z.2 ∧
            (rightmostCocyclePath (fun x y => B x y sOld) 0 n).2 < z.2 ∧
            (n < ell ∨ z.2 <
              (rightmostCocyclePath (fun x y => B x y sOld)
                (0, (ell : ℤ)) (n - ell)).2)) ∧
          K < weights sOld z) ∧
        outsideWeightsAndCocycleIncrements weights B V sOld =
          outsideWeightsAndCocycleIncrements weights B V sNew) ∧
      (∀ sNew ∈ D,
        (∀ z ∈ V, weights sNew z ≤ K) ∧
        is_additive (fun x y => B x y sNew) ∧
        recovers_environment (weights sNew) (fun x y => B x y sNew) ∧
        ∃ a2 : ℤ, 0 < a2 ∧ a2 < (M1 : ℤ) ∧
          ∀ v : Lattice,
            v ∉ Set.Icc (0 : Lattice) ((M1 : ℤ), (M2 : ℤ)) →
            (v.1 ≤ 0 ∨ v.2 ≤ 0) → ∀ N k : ℕ,
              rightmostCocyclePath (fun x y => B x y sNew) v N ≠
                rightmostCocyclePath (fun x y => B x y sNew)
                  (a2, (M2 : ℤ)) k) := by
  classical
  dsimp only
  let F : Finset Lattice :=
    (Finset.Icc (1 : ℤ) ((M1 : ℤ) - 1)).product
      (Finset.Icc (1 : ℤ) ((M2 : ℤ) - 1))
  have hWeightCoordinate (z : Lattice) : Measurable (fun s => weights s z) :=
    (measurable_pi_apply z).comp hWeightsMeas
  -- The good event is measurable in the original ambient field.
  let G : Set Ω := {s | is_additive (fun x y => B x y s) ∧
    recovers_environment (weights s) (fun x y => B x y s)}
  have hAddMeas : MeasurableSet {s : Ω | is_additive (fun x y => B x y s)} := by
    simp only [is_additive, Set.ofPred_forall]
    exact MeasurableSet.iInter fun x => MeasurableSet.iInter fun y =>
      MeasurableSet.iInter fun z =>
        measurableSet_eq_fun ((hBMeas x y).add (hBMeas y z)) (hBMeas x z)
  have hRecoverMeas : MeasurableSet {s : Ω |
      recovers_environment (weights s) (fun x y => B x y s)} := by
    simp only [recovers_environment, Set.ofPred_forall]
    exact MeasurableSet.iInter fun x =>
      measurableSet_eq_fun
        ((hBMeas x (x + (1, 0))).min (hBMeas x (x + (0, 1))))
        (hWeightCoordinate x)
  have hGMeas : MeasurableSet G := hAddMeas.inter hRecoverMeas
  have hGAE : ∀ᵐ s ∂P, s ∈ G := by
    filter_upwards [hAdd, hRec] with s hsAdd hsRec
    exact ⟨hsAdd, hsRec⟩
  have hGoodOldPos : 0 < P (G ∩ A) := by
    rw [Measure.measure_inter_eq_of_ae hGAE]
    exact hAPos
  -- The partition keeps the OLD high-site characteristic pointwise.
  let characteristic (s : Ω) (z : Lattice) : Prop :=
    z ∈ F ∧ 0 < z.1 ∧ z.2 < (M2 : ℤ) ∧
      (∃ n : ℕ, (n : ℤ) = z.1 + z.2 ∧
        (rightmostCocyclePath (fun x y => B x y s) 0 n).2 < z.2 ∧
        (n < ell ∨ z.2 <
          (rightmostCocyclePath (fun x y => B x y s)
            (0, (ell : ℤ)) (n - ell)).2)) ∧ K < weights s z
  obtain ⟨V, hPartition⟩ := exists_positive_fixed_corridor_high_sites
    P weights hWeightsMeas B hBMeas F ell (M2 : ℤ) K
    (G ∩ A) (hGMeas.inter hAMeas) hGoodOldPos
  let A_V : Set Ω := (G ∩ A) ∩ {s | ∀ z, z ∈ V ↔ characteristic s z}
  change MeasurableSet A_V ∧ 0 < P A_V at hPartition
  obtain ⟨hAVMeas, hAVPos⟩ := hPartition
  -- Use the literal outside array; no local measurable-space instance is installed.
  let phi := outsideWeightsAndCocycleIncrements weights B V
  have hphi : Measurable phi :=
    Measurable.of_comap_le
      (outsideSigma_le weights B V hWeightCoordinate hBMeas)
  let RV : Set Ω := {s | ∀ z ∈ V, weights s z ≤ K}
  have hRVMeas : MeasurableSet RV := by
    simp only [RV, Set.ofPred_forall]
    exact MeasurableSet.iInter fun z => MeasurableSet.iInter fun _ =>
      measurableSet_le (hWeightCoordinate z) measurable_const
  obtain ⟨s₀, _hs₀⟩ := nonempty_of_measure_ne_zero hAPos.ne'
  let : Nonempty Ω := ⟨s₀⟩
  let : Countable (OutsideIndex V) := by
    unfold OutsideIndex
    infer_instance
  obtain ⟨D0, hD0Meas, hD0Pos, hAssociated⟩ :=
    ProbabilityBasics.exists_positive_same_fiber_event P hphi A_V RV
      hAVMeas hRVMeas hAVPos (hFiniteBlock V)
  -- Shielding is a countable literal event, not a projection of old witnesses.
  let S : Set Ω := {s | ∃ a2 : ℤ, 0 < a2 ∧ a2 < (M1 : ℤ) ∧
    ∀ v : Lattice, v ∉ Set.Icc (0 : Lattice) ((M1 : ℤ), (M2 : ℤ)) →
      (v.1 ≤ 0 ∨ v.2 ≤ 0) → ∀ N k : ℕ,
        rightmostCocyclePath (fun x y => B x y s) v N ≠
          rightmostCocyclePath (fun x y => B x y s) (a2, (M2 : ℤ)) k}
  have hAvoidMeas (a2 : ℤ) : MeasurableSet {s : Ω |
      ∀ v : Lattice, v ∉ Set.Icc (0 : Lattice) ((M1 : ℤ), (M2 : ℤ)) →
        (v.1 ≤ 0 ∨ v.2 ≤ 0) → ∀ N k : ℕ,
          rightmostCocyclePath (fun x y => B x y s) v N ≠
            rightmostCocyclePath (fun x y => B x y s) (a2, (M2 : ℤ)) k} := by
    simp only [Set.ofPred_forall]
    exact MeasurableSet.iInter fun v => MeasurableSet.iInter fun _ =>
      MeasurableSet.iInter fun _ => MeasurableSet.iInter fun N =>
        MeasurableSet.iInter fun k =>
          (measurableSet_eq_fun (measurable_rightmostCocyclePath B hBMeas v N)
            (measurable_rightmostCocyclePath B hBMeas (a2, (M2 : ℤ)) k)).compl
  have hSMeas : MeasurableSet S := by
    simp only [S, Set.ofPred_exists]
    apply MeasurableSet.iUnion
    intro a2
    have hPosMeas : MeasurableSet {s : Ω | 0 < a2} := by
      by_cases h : 0 < a2 <;> simp only [h, Set.ofPred_true, Set.ofPred_false,
        MeasurableSet.univ, MeasurableSet.empty]
    have hBoundMeas : MeasurableSet {s : Ω | a2 < (M1 : ℤ)} := by
      by_cases h : a2 < (M1 : ℤ) <;> simp only [h, Set.ofPred_true, Set.ofPred_false,
        MeasurableSet.univ, MeasurableSet.empty]
    exact hPosMeas.inter (hBoundMeas.inter (hAvoidMeas a2))
  -- All geometric work is delegated to the physical A.4 theorem.
  have hFinalAE : ∀ᵐ sNew ∂P, sNew ∈ D0 → sNew ∈ RV ∩ (G ∩ S) := by
    filter_upwards [hAssociated, hGAE] with sNew hAssoc hNewGood
    intro hsNew
    obtain ⟨hNewLow, sOld, hOld, hSame⟩ := hAssoc hsNew
    refine ⟨hNewLow, hNewGood, ?_⟩
    obtain ⟨hLM, hMU, hNorthL, a1, a2, H, nM, nU, nE,
      hNorthM, hNorthU, hEastU⟩ := hGeometry sOld hOld.1.2
    let C : Lattice → Lattice → ℝ := fun x y => B x y sOld
    let CNew : Lattice → Lattice → ℝ := fun x y => B x y sNew
    have hTopZ : (ell : ℤ) < (M2 : ℤ) := by exact_mod_cast hTop
    obtain ⟨R, hR, hRBox, _hRAvoid⟩ :=
      exists_finite_rightmost_path_corridor C ell (M1 : ℤ) (M2 : ℤ)
        (M1 + M2) hNorthL
    have hWidthPredCast : ((M1 - 1 : ℕ) : ℤ) = (M1 : ℤ) - 1 := by
      rw [Nat.cast_sub (Nat.succ_le_iff.mpr hM1), Nat.cast_one]
    -- The box bounds identify the clipped OLD characteristic with R.
    have hV : ∀ z : Lattice, z ∈ V ↔ z ∈ R ∧ K < weights sOld z := by
      intro z
      constructor
      · intro hz
        obtain ⟨_hzF, hx, hy, hn, hK⟩ := (hOld.2 z).mp hz
        exact ⟨(hR z).mpr ⟨hx, hy, hn⟩, hK⟩
      · rintro ⟨hzR, hK⟩
        obtain ⟨hx, hy, hn⟩ := (hR z).mp hzR
        have hb := hRBox z hzR
        apply (hOld.2 z).mpr
        refine ⟨?_, hx, hy, hn, hK⟩
        apply Finset.mem_product.mpr
        constructor
        · rw [← hWidthPredCast]
          exact Finset.mem_Icc.mpr (by omega)
        · exact Finset.mem_Icc.mpr (by omega)
    have hOutsideWeights (z : Lattice) (hz : z ∉ V) :
        weights sNew z = weights sOld z := by
      have hh := congrFun hSame (Sum.inl ⟨z, hz⟩)
      exact hh.symm
    have hOutsideEdges (y : Lattice) (hy : y ∈ outsideLowerOrthants V)
        (e : Fin 2) : CNew y (y + finiteEdgeStep e) = C y (y + finiteEdgeStep e) := by
      have hh := congrFun hSame (Sum.inr (⟨y, hy⟩, e))
      exact hh.symm
    obtain ⟨hPrefix, hTail, hNorthWeights⟩ := hWeights sOld hOld.1.2
    have hShield := rightmost_middle_tail_avoids_west_or_south_of_finite_lowering
      (weights sOld) (weights sNew) C CNew hOld.1.1.1 hNewGood.1
      hOld.1.1.2 hNewGood.2 m ell hm hmell
      (M1 : ℤ) (M2 : ℤ) a1 a2 H hTopZ (M1 + M2) nM nU nE
      hNorthL hNorthM hNorthU hEastU hLM hMU R hR V K hV hNewLow
      hOutsideWeights hOutsideEdges hPrefix hTail hNorthWeights
    have hOrder := rightmostCocyclePath_height_order_and_north_hit_order
      C m ell hm hmell (M1 : ℤ) (M2 : ℤ) a1 a2 hTopZ
      (M1 + M2) nM nU hNorthL hNorthM hNorthU hLM hMU
    exact ⟨a2, lt_of_le_of_lt hOrder.2.2.1 hOrder.2.2.2.1,
      hOrder.2.2.2.2, hShield⟩
  -- The measurable cutdown makes new low/good/shielding properties pointwise.
  let D : Set Ω := D0 ∩ (RV ∩ (G ∩ S))
  have hDMeas : MeasurableSet D :=
    hD0Meas.inter (hRVMeas.inter (hGMeas.inter hSMeas))
  have hDEq : D =ᵐ[P] D0 := by
    filter_upwards [hFinalAE] with s hs
    exact propext ⟨fun h => h.1, fun h => ⟨h, hs h⟩⟩
  have hDPos : 0 < P D := by
    rw [measure_congr hDEq]
    exact hD0Pos
  refine ⟨V, D, hDMeas, hDPos, ?_, ?_⟩
  · filter_upwards [hAssociated] with sNew hAssoc
    intro hsNew
    obtain ⟨_hLow, sOld, hOld, hSame⟩ := hAssoc hsNew.1
    exact ⟨sOld, hOld.1.2, hOld.1.1.1, hOld.1.1.2, hOld.2, hSame⟩
  · intro sNew hsNew
    exact ⟨hsNew.2.1, hsNew.2.2.1.1, hsNew.2.2.1.2, hsNew.2.2.2⟩

end LPP.Busemann
