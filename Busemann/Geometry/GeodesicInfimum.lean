/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Busemann.Geometry.GeodesicCompactness
public import Busemann.Geometry.GeodesicOrder
public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Topology.Instances.Int
import Mathlib.Tactic

/-! Greatest lower bounds of nonempty families of actual same-root geodesics. -/

@[expose] public section

open LPPDifferentiability

namespace LPP.Busemann

/-- At a common root, the southeast order is the comparison at every finite
time. This is the finite-prefix order compatibility used in the infimum step
of Strong Existence, public source lines 801–802. -/
theorem pathSoutheastLE_iff_all_times_of_same_root
    (γ δ : ℕ → Lattice) (hroot : γ 0 = δ 0) :
    pathSoutheastLE γ δ ↔
      ∀ n : ℕ, (γ n).1 ≤ (δ n).1 ∧ (δ n).2 ≤ (γ n).2 := by
  constructor
  · intro h n
    exact h n n (by rw [hroot])
  · intro h m n hlevel
    rw [hroot] at hlevel
    have hmn : m = n := by omega
    subst n
    exact h m

private theorem same_root_order_antisymm
    (γ δ : ℕ → Lattice) (hroot : γ 0 = δ 0)
    (hγδ : pathSoutheastLE γ δ) (hδγ : pathSoutheastLE δ γ) : γ = δ := by
  have hf := (pathSoutheastLE_iff_all_times_of_same_root γ δ hroot).mp hγδ
  have hb := (pathSoutheastLE_iff_all_times_of_same_root δ γ hroot.symm).mp hδγ
  funext n
  exact Prod.ext (le_antisymm (hf n).1 (hb n).1)
    (le_antisymm (hb n).2 (hf n).2)

private theorem finite_upper_member_of_total {α : Type*}
    (S : Set α) (R : α → α → Prop) (hne : S.Nonempty)
    (hrefl : ∀ a ∈ S, R a a)
    (htrans : ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, R a b → R b c → R a c)
    (htotal : ∀ a ∈ S, ∀ b ∈ S, R a b ∨ R b a)
    (s : Finset S) : ∃ b : S, ∀ a ∈ s, R a.val b.val := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    obtain ⟨b, hb⟩ := hne
    refine ⟨⟨b, hb⟩, ?_⟩
    intro a ha
    exact False.elim (Finset.notMem_empty a ha)
  | @insert a s _ ih =>
    obtain ⟨b, hb⟩ := ih
    rcases htotal a.val a.property b.val b.property with hab | hba
    · refine ⟨b, ?_⟩
      intro c hc
      rcases Finset.mem_insert.mp hc with rfl | hc
      · exact hab
      · exact hb c hc
    · refine ⟨a, ?_⟩
      intro c hc
      rcases Finset.mem_insert.mp hc with rfl | hc
      · exact hrefl c.val c.property
      · exact htrans c.val c.property b.val b.property a.val a.property
          (hb c hc) hba

private theorem greatest_of_compact_total {α : Type*} [TopologicalSpace α]
    (S : Set α) (R : α → α → Prop) (hc : IsCompact S) (hne : S.Nonempty)
    (hrefl : ∀ a ∈ S, R a a)
    (htrans : ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, R a b → R b c → R a c)
    (htotal : ∀ a ∈ S, ∀ b ∈ S, R a b ∨ R b a)
    (hclosed : ∀ a ∈ S, IsClosed {b | R a b}) :
    ∃ b ∈ S, ∀ a ∈ S, R a b := by
  classical
  have hfinite (s : Finset S) :
      (S ∩ ⋂ a ∈ s, {b | R a.val b}).Nonempty := by
    obtain ⟨b, hb⟩ := finite_upper_member_of_total S R hne hrefl htrans htotal s
    exact ⟨b.val, b.property, Set.mem_iInter₂.mpr (fun a ha => hb a ha)⟩
  obtain ⟨b, hbS, hbCone⟩ := hc.inter_iInter_nonempty
    (fun a : S => {b | R a.val b}) (fun a => hclosed a.val a.property) hfinite
  refine ⟨b, hbS, ?_⟩
  intro a ha
  exact Set.mem_iInter.mp hbCone ⟨a, ha⟩

/-- Every nonempty family of locally rightmost geodesics from one signed root
has a unique greatest lower bound among actual geodesics. This is the first
geometric infimum step in Strong Existence, public source lines 725 and
801–802. -/
theorem exists_unique_geodesic_infimum
    (ω : Environment) (u : Lattice) (F : Set (ℕ → Lattice))
    (hne : F.Nonempty)
    (hvalid : ∀ γ ∈ F, IsLocallyRightmostGeodesic ω u γ) :
    ∃! q : ℕ → Lattice,
      IsLocallyRightmostGeodesic ω u q ∧
      (∀ γ ∈ F, pathSoutheastLE q γ) ∧
      (∀ δ : ℕ → Lattice, IsLocallyRightmostGeodesic ω u δ →
        (∀ γ ∈ F, pathSoutheastLE δ γ) → pathSoutheastLE δ q) := by
  classical
  let G : Set (ℕ → Lattice) := {γ | IsLocallyRightmostGeodesic ω u γ}
  let R : (ℕ → Lattice) → (ℕ → Lattice) → Prop :=
    fun γ δ => ∀ n : ℕ, (γ n).1 ≤ (δ n).1 ∧ (δ n).2 ≤ (γ n).2
  have hGcompact : IsCompact G := isCompact_locallyRightmostGeodesics ω u
  have hRrefl (S : Set (ℕ → Lattice)) : ∀ a ∈ S, R a a :=
    fun _ _ _ => ⟨le_rfl, le_rfl⟩
  have hRtrans (S : Set (ℕ → Lattice)) :
      ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, R a b → R b c → R a c := by
    intro a _ b _ c _ hab hbc n
    exact ⟨(hab n).1.trans (hbc n).1, (hbc n).2.trans (hab n).2⟩
  have hRtotal (S : Set (ℕ → Lattice))
      (hS : ∀ γ ∈ S, IsLocallyRightmostGeodesic ω u γ) :
      ∀ a ∈ S, ∀ b ∈ S, R a b ∨ R b a := by
    intro a ha b hb
    have hroot : a 0 = b 0 := (hS a ha).1.trans (hS b hb).1.symm
    rcases pathSoutheastLE_total_of_isLocallyRightmostGeodesic
      ω u a b (hS a ha) (hS b hb) with h | h
    · exact Or.inl ((pathSoutheastLE_iff_all_times_of_same_root a b hroot).mp h)
    · exact Or.inr ((pathSoutheastLE_iff_all_times_of_same_root b a hroot.symm).mp h)
  have hClosedUpper (a : ℕ → Lattice) : IsClosed {b | R a b} := by
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
  have hClosedLower (a : ℕ → Lattice) : IsClosed {b | R b a} := by
    change IsClosed {b : ℕ → Lattice |
      ∀ n : ℕ, (b n).1 ≤ (a n).1 ∧ (a n).2 ≤ (b n).2}
    rw [Set.ofPred_forall]
    apply isClosed_iInter
    intro n
    have hfirst : Continuous (fun b : ℕ → Lattice => (b n).1) :=
      continuous_fst.comp (continuous_apply n)
    have hsecond : Continuous (fun b : ℕ → Lattice => (b n).2) :=
      continuous_snd.comp (continuous_apply n)
    exact (isClosed_le hfirst continuous_const).inter
      (isClosed_le continuous_const hsecond)
  let K : Set (ℕ → Lattice) := G ∩ ⋂ a : F, {b | R b a.val}
  have hFinite (s : Finset F) :
      (G ∩ ⋂ a ∈ s, {b | R b a.val}).Nonempty := by
    obtain ⟨b, hb⟩ := finite_upper_member_of_total F (fun a b => R b a)
      hne (hRrefl F) (by
        intro a ha b hb c hc hab hbc n
        exact ⟨(hbc n).1.trans (hab n).1, (hab n).2.trans (hbc n).2⟩)
      (by
        intro a ha b hb
        rcases hRtotal F hvalid a ha b hb with h | h
        · exact Or.inr h
        · exact Or.inl h) s
    exact ⟨b.val, hvalid b.val b.property,
      Set.mem_iInter₂.mpr (fun a ha => hb a ha)⟩
  have hKnonempty : K.Nonempty := by
    obtain ⟨q, hqG, hqCone⟩ := hGcompact.inter_iInter_nonempty
      (fun a : F => {b | R b a.val})
      (fun a => hClosedLower a.val) hFinite
    exact ⟨q, hqG, hqCone⟩
  have hKcompact : IsCompact K := by
    exact hGcompact.inter_right (isClosed_iInter fun a : F => hClosedLower a.val)
  have hKvalid : ∀ γ ∈ K, IsLocallyRightmostGeodesic ω u γ :=
    fun _ hγ => hγ.1
  obtain ⟨q, hqK, hqGreat⟩ := greatest_of_compact_total K R
    hKcompact hKnonempty (hRrefl K) (hRtrans K)
    (hRtotal K hKvalid) (fun a _ => hClosedUpper a)
  have hqLower (a : ℕ → Lattice) (ha : a ∈ F) : pathSoutheastLE q a := by
    have hroot : q 0 = a 0 := (hKvalid q hqK).1.trans (hvalid a ha).1.symm
    exact (pathSoutheastLE_iff_all_times_of_same_root q a hroot).mpr
      (Set.mem_iInter.mp hqK.2 ⟨a, ha⟩)
  have hqGreatest (δ : ℕ → Lattice)
      (hδ : IsLocallyRightmostGeodesic ω u δ)
      (hδlower : ∀ a ∈ F, pathSoutheastLE δ a) : pathSoutheastLE δ q := by
    have hδK : δ ∈ K := by
      refine ⟨hδ, ?_⟩
      apply Set.mem_iInter.mpr
      intro a
      have hroot : δ 0 = a.val 0 := hδ.1.trans (hvalid a.val a.property).1.symm
      exact (pathSoutheastLE_iff_all_times_of_same_root δ a.val hroot).mp
        (hδlower a.val a.property)
    have hroot : δ 0 = q 0 := hδ.1.trans (hKvalid q hqK).1.symm
    exact (pathSoutheastLE_iff_all_times_of_same_root δ q hroot).mpr
      (hqGreat δ hδK)
  refine ⟨q, ⟨hKvalid q hqK, hqLower, hqGreatest⟩, ?_⟩
  rintro δ ⟨hδ, hδLower, hδGreatest⟩
  exact same_root_order_antisymm δ q
    (hδ.1.trans (hKvalid q hqK).1.symm)
    (hqGreatest δ hδ hδLower) (hδGreatest q (hKvalid q hqK) hqLower)

end LPP.Busemann
