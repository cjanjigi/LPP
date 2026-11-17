/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Busemann.Geometry.GeodesicSupremum

@[expose] public section
open LPPDifferentiability
namespace LPP.Busemann

-- The named parameter `hβstep` is part of the shared theorem interface.
set_option linter.unusedVariables false in
/-- A nonempty lower cut of same-root locally rightmost geodesics below a
rooted up-right path has an actual greatest geodesic and the same lower cut. -/
theorem exists_greatest_geodesic_below_rooted_upRight_path
    (ω : Environment) (u : Lattice) (β : ℕ → Lattice)
    (hβroot : β 0 = u)
    (hβstep : ∀ n : ℕ,
      β (n + 1) = β n + ((1 : ℤ), (0 : ℤ)) ∨
        β (n + 1) = β n + ((0 : ℤ), (1 : ℤ)))
    (hne : ∃ γ : ℕ → Lattice,
      IsLocallyRightmostGeodesic ω u γ ∧ pathSoutheastLE γ β) :
    ∃ q : ℕ → Lattice,
      IsLocallyRightmostGeodesic ω u q ∧
      pathSoutheastLE q β ∧
      ∀ γ : ℕ → Lattice, IsLocallyRightmostGeodesic ω u γ →
        (pathSoutheastLE γ β ↔ pathSoutheastLE γ q) := by
  classical
  -- The two coordinates of southeast comparison point in opposite directions.
  let R : (ℕ → Lattice) → (ℕ → Lattice) → Prop :=
    fun a b => ∀ n : ℕ, (a n).1 ≤ (b n).1 ∧ (b n).2 ≤ (a n).2
  let G : Set (ℕ → Lattice) :=
    {a | IsLocallyRightmostGeodesic ω u a}
  let C : Set (ℕ → Lattice) := G ∩ {a | R a β}
  have hGcompact : IsCompact G := isCompact_locallyRightmostGeodesics ω u
  have hCutClosed : IsClosed {a : ℕ → Lattice | R a β} := by
    change IsClosed {a : ℕ → Lattice |
      ∀ n : ℕ, (a n).1 ≤ (β n).1 ∧ (β n).2 ≤ (a n).2}
    rw [Set.ofPred_forall]
    apply isClosed_iInter
    intro n
    have hfirst : Continuous (fun a : ℕ → Lattice => (a n).1) :=
      continuous_fst.comp (continuous_apply n)
    have hsecond : Continuous (fun a : ℕ → Lattice => (a n).2) :=
      continuous_snd.comp (continuous_apply n)
    exact (isClosed_le hfirst continuous_const).inter
      (isClosed_le continuous_const hsecond)
  have hCcompact : IsCompact C := hGcompact.inter_right hCutClosed
  have hCvalid (a : ℕ → Lattice) (ha : a ∈ C) :
      IsLocallyRightmostGeodesic ω u a := ha.1
  have hCnonempty : C.Nonempty := by
    obtain ⟨a, ha, hab⟩ := hne
    have hroot : a 0 = β 0 := ha.1.trans hβroot.symm
    exact ⟨a, ha, (pathSoutheastLE_iff_all_times_of_same_root a β hroot).mp hab⟩
  -- Every upper section is closed in the existing path product topology.
  have hConeClosed (a : ℕ → Lattice) : IsClosed {b | R a b} := by
    change IsClosed {b : ℕ → Lattice |
      ∀ n : ℕ, (a n).1 ≤ (b n).1 ∧ (b n).2 ≤ (a n).2}
    rw [Set.ofPred_forall]
    apply isClosed_iInter
    intro n
    have hfirst : Continuous (fun b : ℕ → Lattice => (b n).1) :=
      continuous_fst.comp (continuous_apply n)
    have hsecond : Continuous (fun b : ℕ → Lattice => (b n).2) :=
      continuous_snd.comp (continuous_apply n)
    exact (isClosed_le continuous_const hfirst).inter
      (isClosed_le hsecond continuous_const)
  have hRrefl (a : ℕ → Lattice) : R a a :=
    fun _ => ⟨le_rfl, le_rfl⟩
  have hRtrans (a b c : ℕ → Lattice) (hab : R a b) (hbc : R b c) :
      R a c := by
    intro n
    exact ⟨(hab n).1.trans (hbc n).1,
      (hbc n).2.trans (hab n).2⟩
  have hRtotal (a b : ℕ → Lattice) (ha : a ∈ C) (hb : b ∈ C) :
      R a b ∨ R b a := by
    have hroot : a 0 = b 0 := (hCvalid a ha).1.trans (hCvalid b hb).1.symm
    rcases pathSoutheastLE_total_of_isLocallyRightmostGeodesic
      ω u a b (hCvalid a ha) (hCvalid b hb) with hab | hba
    · exact Or.inl ((pathSoutheastLE_iff_all_times_of_same_root a b hroot).mp hab)
    · exact Or.inr ((pathSoutheastLE_iff_all_times_of_same_root b a hroot.symm).mp hba)
  -- A finite part has one of its own members above all its members.
  have hFiniteUpper (s : Finset C) :
      ∃ b : C, ∀ a ∈ s, R a.val b.val := by
    induction s using Finset.induction_on with
    | empty =>
        obtain ⟨b, hb⟩ := hCnonempty
        refine ⟨⟨b, hb⟩, ?_⟩
        intro a ha
        exact False.elim (Finset.notMem_empty a ha)
    | @insert a s _ ih =>
        obtain ⟨b, hb⟩ := ih
        rcases hRtotal a.val b.val a.property b.property with hab | hba
        · refine ⟨b, ?_⟩
          intro c hc
          rcases Finset.mem_insert.mp hc with rfl | hc
          · exact hab
          · exact hb c hc
        · refine ⟨a, ?_⟩
          intro c hc
          rcases Finset.mem_insert.mp hc with rfl | hc
          · exact hRrefl c.val
          · exact hRtrans c.val b.val a.val (hb c hc) hba
  have hFinite (s : Finset C) :
      (C ∩ ⋂ a ∈ s, {b | R a.val b}).Nonempty := by
    obtain ⟨b, hb⟩ := hFiniteUpper s
    exact ⟨b.val, b.property,
      Set.mem_iInter₂.mpr (fun a ha => hb a ha)⟩
  obtain ⟨q, hqC, hqCone⟩ := hCcompact.inter_iInter_nonempty
    (fun a : C => {b | R a.val b})
    (fun a => hConeClosed a.val) hFinite
  have hqAbove (a : ℕ → Lattice) (ha : a ∈ C) : R a q :=
    Set.mem_iInter.mp hqCone ⟨a, ha⟩
  have hqValid : IsLocallyRightmostGeodesic ω u q := hCvalid q hqC
  have hqBelowBarrier : pathSoutheastLE q β := by
    have hroot : q 0 = β 0 := hqValid.1.trans hβroot.symm
    exact (pathSoutheastLE_iff_all_times_of_same_root q β hroot).mpr hqC.2
  refine ⟨q, hqValid, hqBelowBarrier, ?_⟩
  intro γ hγ
  constructor
  · intro hγβ
    have hrootβ : γ 0 = β 0 := hγ.1.trans hβroot.symm
    have hγC : γ ∈ C :=
      ⟨hγ, (pathSoutheastLE_iff_all_times_of_same_root γ β hrootβ).mp hγβ⟩
    have hrootq : γ 0 = q 0 := hγ.1.trans hqValid.1.symm
    exact (pathSoutheastLE_iff_all_times_of_same_root γ q hrootq).mpr
      (hqAbove γ hγC)
  · intro hγq
    have hrootq : γ 0 = q 0 := hγ.1.trans hqValid.1.symm
    have hγqR := (pathSoutheastLE_iff_all_times_of_same_root γ q hrootq).mp hγq
    have hrootβ : γ 0 = β 0 := hγ.1.trans hβroot.symm
    exact (pathSoutheastLE_iff_all_times_of_same_root γ β hrootβ).mpr
      (hRtrans γ q β hγqR hqC.2)

end LPP.Busemann
