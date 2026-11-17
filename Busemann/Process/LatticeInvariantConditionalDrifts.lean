/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Busemann.Process.DirectionalDrifts
public import Busemann.Frozen.Definitions.LatticeInvariantSigma
public import Mathlib.MeasureTheory.MeasurableSpace.Invariants
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Busemann.Process.LatticeDirectionalDrifts
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic

/-! The full-action directional drift is the invariant conditional mean. -/

@[expose] public section

open MeasureTheory Filter LPPDifferentiability
open scoped Topology

namespace LPP.Busemann

private theorem cocycle_setIntegral_normalized_of_invariant
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (T : Lattice → Ω → Ω)
    (hShift : ∀ z : Lattice, MeasurePreserving (T z) P P)
    (B : Lattice → Lattice → Ω → ℝ)
    (hB : is_shift_covariant_cocycle P T B)
    (hInt : ∀ x y, Integrable (B x y) P)
    (A : Set Ω) (hA : MeasurableSet A)
    (hAinv : ∀ z : Lattice, T z ⁻¹' A = A)
    (e : Lattice) (n : ℕ) (hn : 0 < n) :
    (∫ s in A, B 0 (n • e) s / (n : ℝ) ∂P) = ∫ s in A, B 0 e s ∂P := by
  have hmeas : Measurable (B 0 e) := by
    have hmap : Measurable (fun s : Ω => (((0 : Lattice), e), s)) :=
      measurable_const.prodMk measurable_id
    exact hB.1.comp hmap
  -- Strict invariance of A transports the actual restricted integral.
  have htransport (z : Lattice) :
      (∫ s in A, B 0 e (T z s) ∂P) = ∫ s in A, B 0 e s ∂P := by
    have hm : AEStronglyMeasurable (B 0 e) (P.map (T z)) := by
      rw [(hShift z).map_eq]
      exact hmeas.aestronglyMeasurable
    have heq := setIntegral_map (μ := P) (g := T z) hA hm
      (hShift z).aemeasurable
    rw [(hShift z).map_eq, hAinv z] at heq
    exact heq.symm
  have hzero : (fun s => B 0 0 s) =ᵐ[P] fun _ => (0 : ℝ) := by
    filter_upwards [hB.2.2] with s hs
    have hz := hs 0 0 0
    change B 0 0 s + B 0 0 s = B 0 0 s at hz
    linarith only [hz]
  have hrecursion (k : ℕ) : (fun s => B 0 ((k + 1) • e) s) =ᵐ[P]
      fun s => B 0 (k • e) s + B 0 e (T (k • e) s) := by
    filter_upwards [hB.2.2, hB.2.1 0 e (k • e)] with s hs hc
    have ha := hs 0 (k • e) (k • e + e)
    change B 0 (k • e) s + B (k • e) (k • e + e) s = B 0 (k • e + e) s at ha
    have hc' : B (k • e) (k • e + e) s = B 0 e (T (k • e) s) := by
      simpa only [zero_add, add_comm e (k • e)] using hc
    rw [hc'] at ha
    simpa only [succ_nsmul] using ha.symm
  -- Induction gives every invariant-set numerator mean, including index zero.
  have hnum (k : ℕ) :
      (∫ s in A, B 0 (k • e) s ∂P) = (k : ℝ) * ∫ s in A, B 0 e s ∂P := by
    induction k with
    | zero =>
      simp only [zero_nsmul, Nat.cast_zero, zero_mul]
      exact integral_eq_zero_of_ae (ae_restrict_of_ae hzero)
    | succ k ih =>
      calc
        _ = (∫ s in A, B 0 (k • e) s + B 0 e (T (k • e) s) ∂P) :=
          integral_congr_ae (ae_restrict_of_ae (hrecursion k))
        _ = (∫ s in A, B 0 (k • e) s ∂P) +
            ∫ s in A, B 0 e (T (k • e) s) ∂P :=
          integral_add (hInt 0 (k • e)).integrableOn
            ((hShift (k • e)).integrable_comp_of_integrable (hInt 0 e)).integrableOn
        _ = (k : ℝ) * (∫ s in A, B 0 e s ∂P) + ∫ s in A, B 0 e s ∂P := by
          rw [ih, htransport]
        _ = ((k + 1 : ℕ) : ℝ) * ∫ s in A, B 0 e s ∂P := by
          push_cast
          ring
  rw [integral_div, hnum n]
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
  field_simp [hn0]

/-- For an arbitrary measure-preserving lattice action and integrable
shift-covariant cocycle, the full-action invariant directional drifts are the
conditional means of the actual unit increments. This is JR arXiv:1810.03580v3,
Appendix B, Lemma B.4, source reading lines 2688–2705; no ergodicity is
assumed. -/
theorem exists_full_action_directional_drifts_condExp_of_action
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (T : Lattice → Ω → Ω)
    (hzero : ∀ s : Ω, T 0 s = s)
    (hadd : ∀ (z w : Lattice) (s : Ω), T (z + w) s = T z (T w s))
    (hShift : ∀ z : Lattice, MeasurePreserving (T z) P P)
    (B : Lattice → Lattice → Ω → ℝ)
    (hB : is_shift_covariant_cocycle P T B)
    (hInt : ∀ x y, Integrable (B x y) P) :
    let mΩ0 : MeasurableSpace Ω := inferInstance
    let I : MeasurableSpace Ω := @latticeInvariantSigma Ω mΩ0 T
    letI : MeasurableSpace Ω := mΩ0
    ∃ u : Fin 2 → Ω → ℝ,
      ((∀ i : Fin 2,
        Measurable (u i) ∧ Integrable (u i) P ∧
        (∀ᵐ s ∂P, Tendsto
          (fun n : ℕ => B 0 (n • finiteEdgeStep i) s / (n : ℝ))
          atTop (𝓝 (u i s))) ∧
        (∫ s, u i s ∂P) = ∫ s, B 0 (finiteEdgeStep i) s ∂P ∧
        Tendsto (fun n : ℕ => ∫ s,
          |B 0 (n • finiteEdgeStep i) s / (n : ℝ) - u i s| ∂P)
          atTop (𝓝 0)) ∧
       (∀ (i : Fin 2) (z : Lattice) (s : Ω),
         u i (T z s) = u i s)) ∧
      (∀ i : Fin 2, u i =ᵐ[P] P[B 0 (finiteEdgeStep i) | I]) := by
  classical
  let mΩ0 : MeasurableSpace Ω := inferInstance
  let I : MeasurableSpace Ω := @latticeInvariantSigma Ω mΩ0 T
  let : MeasurableSpace Ω := mΩ0
  change ∃ u : Fin 2 → Ω → ℝ,
      ((∀ i : Fin 2,
        Measurable (u i) ∧ Integrable (u i) P ∧
        (∀ᵐ s ∂P, Tendsto
          (fun n : ℕ => B 0 (n • finiteEdgeStep i) s / (n : ℝ))
          atTop (𝓝 (u i s))) ∧
        (∫ s, u i s ∂P) = ∫ s, B 0 (finiteEdgeStep i) s ∂P ∧
        Tendsto (fun n : ℕ => ∫ s,
          |B 0 (n • finiteEdgeStep i) s / (n : ℝ) - u i s| ∂P)
          atTop (𝓝 0)) ∧
       (∀ (i : Fin 2) (z : Lattice) (s : Ω),
         u i (T z s) = u i s)) ∧
      (∀ i : Fin 2, u i =ᵐ[P] P[B 0 (finiteEdgeStep i) | I])
  -- Retain one drift family and its entire original ambient-space package.
  obtain ⟨u, hdata, hinv⟩ := exists_full_action_directional_drifts_of_action
    P T hzero hadd hShift B hB hInt
  have hm : I ≤ mΩ0 := by
    change (⨅ z : Lattice, @MeasurableSpace.invariants Ω mΩ0 (T z)) ≤ mΩ0
    exact (iInf_le _ 0).trans (MeasurableSpace.invariants_le (T (0 : Lattice)))
  let : IsFiniteMeasure (P.trim hm) := inferInstance
  let : SigmaFinite (P.trim hm) := inferInstance
  have hset (A : Set Ω) (hA : MeasurableSet[I] A) :
      MeasurableSet A ∧ ∀ z : Lattice, T z ⁻¹' A = A := by
    refine ⟨hm A hA, ?_⟩
    intro z
    exact (MeasurableSpace.measurableSet_invariants.mp
      ((MeasurableSpace.measurableSet_iInf.mp hA) z)).2
  have huI (i : Fin 2) : Measurable[I] (u i) := by
    intro S hS
    apply MeasurableSpace.measurableSet_iInf.mpr
    intro z
    apply MeasurableSpace.measurableSet_invariants.mpr
    refine ⟨(hdata i).1 hS, ?_⟩
    ext s
    change u i (T z s) ∈ S ↔ u i s ∈ S
    rw [hinv i z s]
  have hCE (i : Fin 2) : u i =ᵐ[P] P[B 0 (finiteEdgeStep i) | I] := by
    have huInt : Integrable (u i) P := (hdata i).2.1
    let X : ℕ → Ω → ℝ := fun n s =>
      B 0 (n • finiteEdgeStep i) s / (n : ℝ)
    have hXInt (n : ℕ) : Integrable (X n) P :=
      (hInt 0 (n • finiteEdgeStep i)).div_const (n : ℝ)
    -- Restricted means follow from the actual L1 limit, for EVERY invariant set.
    have hrestricted (A : Set Ω) (hA : MeasurableSet[I] A) :
        (∫ s in A, u i s ∂P) = ∫ s in A, B 0 (finiteEdgeStep i) s ∂P := by
      obtain ⟨hAm, hAi⟩ := hset A hA
      have hnormalized (n : ℕ) (hn : 0 < n) :
          (∫ s in A, X n s ∂P) = ∫ s in A, B 0 (finiteEdgeStep i) s ∂P :=
        cocycle_setIntegral_normalized_of_invariant P T hShift B hB hInt
          A hAm hAi (finiteEdgeStep i) n hn
      have hbound (n : ℕ) :
          |(∫ s in A, X n s ∂P) - ∫ s in A, u i s ∂P| ≤
            ∫ s, |X n s - u i s| ∂P := by
        calc
          _ = |∫ s in A, X n s - u i s ∂P| := by
            rw [integral_sub (hXInt n).integrableOn huInt.integrableOn]
          _ ≤ ∫ s in A, |X n s - u i s| ∂P := by
            simpa only [Real.norm_eq_abs] using
              (norm_integral_le_integral_norm (fun s => X n s - u i s)
                (μ := P.restrict A))
          _ ≤ ∫ s, |X n s - u i s| ∂P :=
            setIntegral_le_integral ((hXInt n).sub huInt).abs
              (ae_of_all P fun s => abs_nonneg (X n s - u i s))
      have hL1 : Tendsto (fun n : ℕ => ∫ s, |X n s - u i s| ∂P)
          atTop (𝓝 0) := (hdata i).2.2.2.2
      have heq : (∫ s in A, B 0 (finiteEdgeStep i) s ∂P) =
          ∫ s in A, u i s ∂P := by
        by_contra hne
        have hgap : 0 < |(∫ s in A, B 0 (finiteEdgeStep i) s ∂P) -
            ∫ s in A, u i s ∂P| := abs_pos.mpr (sub_ne_zero.mpr hne)
        have hsmall := hL1.eventually (gt_mem_nhds hgap)
        obtain ⟨n, hn, hnsmall⟩ := ((eventually_gt_atTop (0 : ℕ)).and hsmall).exists
        have hb := hbound n
        rw [hnormalized n hn] at hb
        exact (not_lt_of_ge hb) hnsmall
      exact heq.symm
    apply ae_eq_condExp_of_forall_setIntegral_eq hm (hInt 0 (finiteEdgeStep i))
    · intro A _ _
      exact huInt.integrableOn
    · intro A hA _
      exact hrestricted A hA
    · exact (huI i).aestronglyMeasurable
  exact ⟨u, ⟨hdata, hinv⟩, hCE⟩

end LPP.Busemann
