/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Differentiability.Probability.LevelSigma
public import LPP_Foundations.Probability.Stationarity
public import LPP_Foundations.Probability.TranslationEquiv
public import Mathlib.Probability.IdentDistrib
public import Mathlib.Probability.Independence.Basic
import Differentiability.Probability.AugmentedMeasurability

/-!
# Independence across a level after a random translation

Weights at levels at most `m` are independent of weights at levels above `m`. A random
translation that lands on level `m` and is determined by the lower levels can be replaced,
one value at a time, by a fixed translation. A functional of the environment that ignores
levels at most `0`, read from the random site, is then independent of the lower levels and
has the law of the original functional.

Section 2.3 of the differentiability preprint does not contain this statement. It is proved
here by conditioning on the countably many values of the translation.
-/

@[expose] public section

namespace LPPDifferentiability

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal

/-- The information carried by the weight at the single site `z`. -/
@[instance_reducible] private def coordSigma (z : Lattice) : MeasurableSpace Environment :=
  MeasurableSpace.comap (fun ω : Environment => ω z) inferInstance

/-- The information carried by the weights at all sites of level above `m`. -/
@[instance_reducible] private def levelsAbove (m : ℤ) : MeasurableSpace Environment :=
  ⨆ z ∈ {z : Lattice | m < z.1 + z.2}, coordSigma z

private theorem measurable_of_eval_coords {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (f : Ω → Environment) (hf : ∀ z, Measurable fun ω => f ω z) : Measurable f :=
  Measurable.of_eval hf

private theorem coordSigma_le (z : Lattice) :
    coordSigma z ≤ (inferInstance : MeasurableSpace Environment) :=
  (measurable_environment_eval z).comap_le

private theorem coordSigma_le_levelsAbove (m : ℤ) (w : Lattice) (hw : m < w.1 + w.2) :
    coordSigma w ≤ levelsAbove m :=
  le_iSup₂ (f := fun (w : Lattice) (_ : w ∈ {z : Lattice | m < z.1 + z.2}) => coordSigma w)
    w hw

/-- Reading the environment from a fixed site `t` on level `m`, a functional that ignores
levels at most `0` depends only on the weights at levels above `m`. -/
private theorem measurable_translate_levelsAbove (m : ℤ) (t : Lattice) (ht : t.1 + t.2 = m)
    {β : Type*} [MeasurableSpace β] (F : Environment → β) (hF : Measurable F)
    (hloc : ∀ ω ω' : Environment, (∀ z : Lattice, 0 < z.1 + z.2 → ω z = ω' z) →
      F ω = F ω') :
    Measurable[levelsAbove m] (fun ω : Environment => F (fun z => ω (t + z))) := by
  have hΦ : Measurable[levelsAbove m]
      (fun ω : Environment => fun z : Lattice => if 0 < z.1 + z.2 then ω (t + z) else 0) := by
    refine measurable_of_eval_coords (mΩ := levelsAbove m) _ fun z => ?_
    by_cases hz : 0 < z.1 + z.2
    · simp only [ite_eq_left hz]
      have hw : m < (t + z).1 + (t + z).2 := by
        simp only [Prod.fst_add, Prod.snd_add]
        omega
      exact Measurable.of_comap_le (coordSigma_le_levelsAbove m (t + z) hw)
    · simp only [ite_eq_right hz]
      exact measurable_const
  have heq : (fun ω : Environment => F (fun z => ω (t + z))) =
      fun ω : Environment => F (fun z : Lattice => if 0 < z.1 + z.2 then ω (t + z) else 0) := by
    funext ω
    refine hloc _ _ fun z hz => ?_
    simp only [ite_eq_left hz]
  rw [heq]
  exact hF.comp hΦ

/-- Independence across a level after a random translation. Let `T` be a
random site on level `m` that is determined by the weights at levels at most `m`, and let `F`
be a measurable functional of the environment that ignores levels at most `0`. Reading the
environment from `T` gives a functional that is independent of every function of the lower
levels, and that has the law of `F`. -/
theorem indepFun_identDistrib_shift_of_levelsAtMost
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (m : ℤ)
    (T : Environment → Lattice) (hT : Measurable[levelsAtMost m] T)
    (hTlevel : ∀ ω, (T ω).1 + (T ω).2 = m)
    {β : Type*} [MeasurableSpace β] (F : Environment → β) (hF : Measurable F)
    (hloc : ∀ ω ω' : Environment, (∀ z : Lattice, 0 < z.1 + z.2 → ω z = ω' z) →
      F ω = F ω')
    {γ : Type*} [MeasurableSpace γ] (G : Environment → γ)
    (hG : Measurable[levelsAtMost m] G) :
    IndepFun G (fun ω => F (fun z => ω (T ω + z))) (environmentLaw ν) ∧
      IdentDistrib (fun ω => F (fun z => ω (T ω + z))) F
        (environmentLaw ν) (environmentLaw ν) := by
  have hTm : Measurable T := hT.mono (levelsAtMost_le m) le_rfl
  have hΨ : Measurable fun ω : Environment => fun z : Lattice => ω (T ω + z) := by
    refine Measurable.of_eval fun z => ?_
    have h1 : Measurable fun p : Lattice × Environment => p.2 (p.1 + z) :=
      measurable_from_prod_countable_right fun t => measurable_pi_apply (t + z)
    exact h1.comp (hTm.prodMk measurable_id)
  have hFΨ : Measurable fun ω : Environment => F (fun z => ω (T ω + z)) := hF.comp hΨ
  have hθ : ∀ t : Lattice, Measurable fun ω : Environment => fun z : Lattice => ω (t + z) :=
    fun t => Measurable.of_eval fun z => measurable_pi_apply (t + z)
  have hindep : Indep (levelsAtMost m) (levelsAbove m) (environmentLaw ν) := by
    have hI : iIndep coordSigma (environmentLaw ν) := (iIndepFun_environment_eval ν).iIndep
    have hST : Disjoint {z : Lattice | z.1 + z.2 ≤ m} {z : Lattice | m < z.1 + z.2} :=
      Set.disjoint_left.2 fun z h1 h2 => by
        have h1' : z.1 + z.2 ≤ m := h1
        have h2' : m < z.1 + z.2 := h2
        omega
    exact indep_iSup_of_disjoint coordSigma_le hI hST
  -- the factorization, for a lower event `E` and a measurable set `B`
  have key : ∀ B : Set β, MeasurableSet B → ∀ E : Set Environment,
      MeasurableSet[levelsAtMost m] E →
      environmentLaw ν (E ∩ (fun ω : Environment => F (fun z => ω (T ω + z))) ⁻¹' B) =
        environmentLaw ν E * environmentLaw ν (F ⁻¹' B) := by
    intro B hB E hE
    have hEm : MeasurableSet E := levelsAtMost_le m _ hE
    obtain ⟨D, hD⟩ : ∃ D : Lattice → Set Environment, ∀ t, D t = T ⁻¹' {t} :=
      ⟨fun t => T ⁻¹' {t}, fun _ => rfl⟩
    obtain ⟨H, hH⟩ : ∃ H : Lattice → Set Environment, ∀ t,
        H t = (fun ω : Environment => F (fun z => ω (t + z))) ⁻¹' B :=
      ⟨fun t => (fun ω : Environment => F (fun z => ω (t + z))) ⁻¹' B, fun _ => rfl⟩
    have hDlow : ∀ t, MeasurableSet[levelsAtMost m] (D t) := fun t => by
      rw [hD]
      exact hT (measurableSet_singleton t)
    have hDm : ∀ t, MeasurableSet (D t) := fun t => levelsAtMost_le m _ (hDlow t)
    have hHm : ∀ t, MeasurableSet (H t) := fun t => by
      rw [hH]
      exact (hF.comp (hθ t)) hB
    have hHP : ∀ t, environmentLaw ν (H t) = environmentLaw ν (F ⁻¹' B) := fun t => by
      rw [hH]
      calc environmentLaw ν ((fun ω : Environment => F (fun z => ω (t + z))) ⁻¹' B)
          = ((environmentLaw ν).map (fun ω : Environment => fun z : Lattice => ω (t + z)))
              (F ⁻¹' B) := by
            rw [Measure.map_apply (hθ t) (hF hB)]
            rfl
        _ = environmentLaw ν (F ⁻¹' B) := by rw [environmentLaw_map_translation]
    have hterm : ∀ t, environmentLaw ν (E ∩ D t ∩ H t) =
        environmentLaw ν (E ∩ D t) * environmentLaw ν (F ⁻¹' B) := fun t => by
      by_cases ht : t.1 + t.2 = m
      · rw [← hHP t]
        refine (Indep_iff _ _ _).1 hindep (E ∩ D t) (H t) (hE.inter (hDlow t)) ?_
        rw [hH]
        exact measurable_translate_levelsAbove m t ht F hF hloc hB
      · have hempty : D t = ∅ := by
          rw [hD]
          ext ω
          simp only [mem_preimage, mem_singleton_iff, mem_empty_iff_false, iff_false]
          intro h
          have hlev := hTlevel ω
          rw [h] at hlev
          exact ht hlev
        simp [hempty]
    have hunion1 : E ∩ (fun ω : Environment => F (fun z => ω (T ω + z))) ⁻¹' B =
        ⋃ t, E ∩ D t ∩ H t := by
      ext ω
      constructor
      · rintro ⟨hEω, hCω⟩
        refine mem_iUnion.2 ⟨T ω, ⟨hEω, ?_⟩, ?_⟩
        · rw [hD]
          exact rfl
        · rw [hH]
          exact hCω
      · intro hω
        obtain ⟨t, ⟨hEω, hDω⟩, hHω⟩ := mem_iUnion.1 hω
        rw [hD] at hDω
        rw [hH] at hHω
        have hTω : T ω = t := hDω
        subst hTω
        exact ⟨hEω, hHω⟩
    have hunion2 : E = ⋃ t, E ∩ D t := by
      ext ω
      constructor
      · intro hEω
        refine mem_iUnion.2 ⟨T ω, hEω, ?_⟩
        rw [hD]
        exact rfl
      · intro hω
        obtain ⟨t, hEω, _⟩ := mem_iUnion.1 hω
        exact hEω
    have hpair1 : Pairwise (Function.onFun Disjoint fun t => E ∩ D t ∩ H t) := by
      intro s t hst
      show Disjoint (E ∩ D s ∩ H s) (E ∩ D t ∩ H t)
      refine Set.disjoint_left.2 fun ω h1 h2 => hst ?_
      have ha : ω ∈ D s := h1.1.2
      have hb : ω ∈ D t := h2.1.2
      rw [hD] at ha hb
      exact (show T ω = s from ha).symm.trans (show T ω = t from hb)
    have hpair2 : Pairwise (Function.onFun Disjoint fun t => E ∩ D t) := by
      intro s t hst
      show Disjoint (E ∩ D s) (E ∩ D t)
      refine Set.disjoint_left.2 fun ω h1 h2 => hst ?_
      have ha : ω ∈ D s := h1.2
      have hb : ω ∈ D t := h2.2
      rw [hD] at ha hb
      exact (show T ω = s from ha).symm.trans (show T ω = t from hb)
    calc environmentLaw ν (E ∩ (fun ω : Environment => F (fun z => ω (T ω + z))) ⁻¹' B)
        = environmentLaw ν (⋃ t, E ∩ D t ∩ H t) := by rw [hunion1]
      _ = ∑' t, environmentLaw ν (E ∩ D t ∩ H t) :=
          measure_iUnion hpair1 fun t => (hEm.inter (hDm t)).inter (hHm t)
      _ = ∑' t, environmentLaw ν (E ∩ D t) * environmentLaw ν (F ⁻¹' B) := tsum_congr hterm
      _ = (∑' t, environmentLaw ν (E ∩ D t)) * environmentLaw ν (F ⁻¹' B) :=
          ENNReal.tsum_mul_right
      _ = environmentLaw ν (⋃ t, E ∩ D t) * environmentLaw ν (F ⁻¹' B) := by
          rw [measure_iUnion hpair2 fun t => hEm.inter (hDm t)]
      _ = environmentLaw ν E * environmentLaw ν (F ⁻¹' B) := by rw [← hunion2]
  have hlaw : ∀ B : Set β, MeasurableSet B →
      environmentLaw ν ((fun ω : Environment => F (fun z => ω (T ω + z))) ⁻¹' B) =
        environmentLaw ν (F ⁻¹' B) := fun B hB => by
    have h := key B hB univ MeasurableSet.univ
    simpa using h
  refine ⟨?_, ?_⟩
  · refine (IndepFun_iff _ _ _).2 fun s t hs ht => ?_
    obtain ⟨A, hA, rfl⟩ := MeasurableSpace.measurableSet_comap.1 hs
    obtain ⟨B, hB, rfl⟩ := MeasurableSpace.measurableSet_comap.1 ht
    rw [key B hB (G ⁻¹' A) (hG hA), hlaw B hB]
  · refine ⟨hFΨ.aemeasurable, hF.aemeasurable, ?_⟩
    refine Measure.ext fun B hB => ?_
    rw [Measure.map_apply hFΨ hB, Measure.map_apply hF hB]
    exact hlaw B hB

end LPPDifferentiability
