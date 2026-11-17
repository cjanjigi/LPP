/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Busemann.Geometry.LocallyRightmostGeodesic
import Busemann.Geometry.GeodesicOrder
import Busemann.Geometry.GeodesicCompactness
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Instances.Int
import Mathlib.Tactic

/-! Unique greatest locally rightmost ray extensions of realized finite prefixes. -/

@[expose] public section

open LPPDifferentiability

namespace LPP.Busemann

private theorem same_root_southeast_iff (γ δ : ℕ → Lattice)
    (hroot : γ 0 = δ 0) :
    pathSoutheastLE γ δ ↔
      ∀ n : ℕ, (γ n).1 ≤ (δ n).1 ∧ (δ n).2 ≤ (γ n).2 := by
  constructor
  · intro h n
    apply h n n
    rw [hroot]
  · intro h m n hlevel
    rw [hroot] at hlevel
    have hmn : m = n := by omega
    subst n
    exact h m

private theorem same_root_southeast_antisymm (γ δ : ℕ → Lattice)
    (hroot : γ 0 = δ 0) (hγδ : pathSoutheastLE γ δ)
    (hδγ : pathSoutheastLE δ γ) : γ = δ := by
  have hforward := (same_root_southeast_iff γ δ hroot).mp hγδ
  have hbackward := (same_root_southeast_iff δ γ hroot.symm).mp hδγ
  funext n
  exact Prod.ext (le_antisymm (hforward n).1 (hbackward n).1)
    (le_antisymm (hbackward n).2 (hforward n).2)

private theorem finite_upper_bound_of_total {α : Type*}
    (S : Set α) (R : α → α → Prop) (hNonempty : S.Nonempty)
    (hrefl : ∀ a ∈ S, R a a)
    (htrans : ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, R a b → R b c → R a c)
    (htotal : ∀ a ∈ S, ∀ b ∈ S, R a b ∨ R b a)
    (s : Finset S) : ∃ b : S, ∀ a ∈ s, R a.val b.val := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    obtain ⟨b, hb⟩ := hNonempty
    refine ⟨⟨b, hb⟩, ?_⟩
    intro a ha
    exact False.elim (Finset.notMem_empty a ha)
  | @insert a s _ha ih =>
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
      · exact htrans c.val c.property b.val b.property a.val a.property (hb c hc) hba

private theorem greatest_of_compact_total {α : Type*} [TopologicalSpace α]
    (S : Set α) (R : α → α → Prop) (hCompact : IsCompact S)
    (hNonempty : S.Nonempty)
    (hrefl : ∀ a ∈ S, R a a)
    (htrans : ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, R a b → R b c → R a c)
    (htotal : ∀ a ∈ S, ∀ b ∈ S, R a b ∨ R b a)
    (hClosed : ∀ a ∈ S, IsClosed {b | R a b}) :
    ∃ b ∈ S, ∀ a ∈ S, R a b := by
  classical
  -- Finite total families have an upper bound within the original set.
  have hFinite (s : Finset S) :
      (S ∩ ⋂ a ∈ s, {b | R a.val b}).Nonempty := by
    obtain ⟨b, hb⟩ := finite_upper_bound_of_total S R hNonempty hrefl htrans htotal s
    refine ⟨b.val, b.property, ?_⟩
    exact Set.mem_iInter₂.mpr (fun a ha => hb a ha)
  -- Compactness meets every closed upper cone simultaneously.
  obtain ⟨b, hbS, hbCone⟩ := hCompact.inter_iInter_nonempty
    (fun a : S => {b | R a.val b}) (fun a => hClosed a.val a.property) hFinite
  refine ⟨b, hbS, ?_⟩
  intro a ha
  exact Set.mem_iInter.mp hbCone ⟨a, ha⟩

private theorem isClosed_prefix_cylinder {u : Lattice} {d : ℕ × ℕ}
    (p : Path u d) :
    IsClosed {γ : ℕ → Lattice |
      ∀ k : Fin (d.1 + d.2 + 1), γ k.val = p.vertex k} := by
  rw [Set.ofPred_forall]
  exact isClosed_iInter fun k => isClosed_eq (continuous_apply k.val) continuous_const

private theorem unique_greatest_of_compact_geodesic_set
    (ω : Environment) (u : Lattice) (S : Set (ℕ → Lattice))
    (hCompact : IsCompact S) (hNonempty : S.Nonempty)
    (hValid : ∀ γ ∈ S, IsLocallyRightmostGeodesic ω u γ) :
    ∃! ρ : ℕ → Lattice, ρ ∈ S ∧ ∀ γ ∈ S, pathSoutheastLE γ ρ := by
  let R : (ℕ → Lattice) → (ℕ → Lattice) → Prop :=
    fun γ δ => ∀ n : ℕ, (γ n).1 ≤ (δ n).1 ∧ (δ n).2 ≤ (γ n).2
  have hClosed (γ : ℕ → Lattice) : IsClosed {δ | R γ δ} := by
    change IsClosed {δ : ℕ → Lattice |
      ∀ n : ℕ, (γ n).1 ≤ (δ n).1 ∧ (δ n).2 ≤ (γ n).2}
    rw [Set.ofPred_forall]
    apply isClosed_iInter
    intro n
    have hFirst : Continuous (fun δ : ℕ → Lattice => (δ n).1) :=
      continuous_fst.comp (continuous_apply n)
    have hSecond : Continuous (fun δ : ℕ → Lattice => (δ n).2) :=
      continuous_snd.comp (continuous_apply n)
    exact (isClosed_le continuous_const hFirst).inter
      (isClosed_le hSecond continuous_const)
  have hRefl : ∀ γ ∈ S, R γ γ := fun _ _ _ => ⟨le_rfl, le_rfl⟩
  have hTrans : ∀ γ ∈ S, ∀ δ ∈ S, ∀ η ∈ S, R γ δ → R δ η → R γ η := by
    intro γ _hγ δ _hδ η _hη hγδ hδη n
    exact ⟨le_trans (hγδ n).1 (hδη n).1, le_trans (hδη n).2 (hγδ n).2⟩
  have hTotal : ∀ γ ∈ S, ∀ δ ∈ S, R γ δ ∨ R δ γ := by
    intro γ hγ δ hδ
    have hRoot : γ 0 = δ 0 := (hValid γ hγ).1.trans (hValid δ hδ).1.symm
    rcases pathSoutheastLE_total_of_isLocallyRightmostGeodesic
      ω u γ δ (hValid γ hγ) (hValid δ hδ) with h | h
    · exact Or.inl ((same_root_southeast_iff γ δ hRoot).mp h)
    · exact Or.inr ((same_root_southeast_iff δ γ hRoot.symm).mp h)
  obtain ⟨ρ, hρ, hGreat⟩ := greatest_of_compact_total S R hCompact hNonempty
    hRefl hTrans hTotal (fun γ _ => hClosed γ)
  have hGreatRaw : ∀ γ ∈ S, pathSoutheastLE γ ρ := by
    intro γ hγ
    have hRoot : γ 0 = ρ 0 := (hValid γ hγ).1.trans (hValid ρ hρ).1.symm
    exact (same_root_southeast_iff γ ρ hRoot).mpr (hGreat γ hγ)
  refine ⟨ρ, ⟨hρ, hGreatRaw⟩, ?_⟩
  rintro δ ⟨hδ, hδGreat⟩
  exact same_root_southeast_antisymm δ ρ
    ((hValid δ hδ).1.trans (hValid ρ hρ).1.symm)
    (hGreatRaw δ hδ) (hδGreat ρ hρ)

/-- Every finite prefix realized by a locally rightmost ray has a unique
 greatest ray extension. Strong Existence, lines 725–732
 and 1439–1449. The prefix class, including a zero-length prefix, is nonempty. -/
theorem exists_unique_greatest_locallyRightmostGeodesic_extension
    (ω : Environment) (u : Lattice) (d : ℕ × ℕ) (p : Path u d)
    (hNonempty : ∃ γ : ℕ → Lattice,
      IsLocallyRightmostGeodesic ω u γ ∧
        ∀ k : Fin (d.1 + d.2 + 1), γ k.val = p.vertex k) :
    ∃! ρ : ℕ → Lattice,
      IsLocallyRightmostGeodesic ω u ρ ∧
      (∀ k : Fin (d.1 + d.2 + 1), ρ k.val = p.vertex k) ∧
      ∀ γ : ℕ → Lattice,
        IsLocallyRightmostGeodesic ω u γ →
        (∀ k : Fin (d.1 + d.2 + 1), γ k.val = p.vertex k) →
        pathSoutheastLE γ ρ
 := by
  let S : Set (ℕ → Lattice) := {γ | IsLocallyRightmostGeodesic ω u γ ∧
    ∀ k : Fin (d.1 + d.2 + 1), γ k.val = p.vertex k}
  -- The actual fixed-environment compact ray set meets a closed prefix cylinder.
  have hCompact : IsCompact S :=
    (isCompact_locallyRightmostGeodesics ω u).inter_right (isClosed_prefix_cylinder p)
  have hRealized : S.Nonempty := hNonempty
  -- Closed upper cones and same-root totality yield a unique greatest member.
  obtain ⟨ρ, hρ, hUnique⟩ := unique_greatest_of_compact_geodesic_set
    ω u S hCompact hRealized (fun _ hγ => hγ.1)
  refine ⟨ρ, ⟨hρ.1.1, hρ.1.2, ?_⟩, ?_⟩
  · intro γ hγ hprefix
    exact hρ.2 γ ⟨hγ, hprefix⟩
  · rintro δ ⟨hδ, hprefix, hgreat⟩
    exact hUnique δ ⟨⟨hδ, hprefix⟩, fun γ hγ => hgreat γ hγ.1 hγ.2⟩

end LPP.Busemann
