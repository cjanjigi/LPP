/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, and Timo Seppäläinen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Busemann.Geometry.GeodesicInfimum
import Mathlib.Topology.Sequences
import Mathlib.Topology.Instances.Int
import Mathlib.Topology.Compactness.Compact

/-! Approximate the greatest lower bound of actual geodesics in the product path topology. -/

@[expose] public section
open Filter LPPDifferentiability
open scoped Topology
namespace LPP.Busemann

private theorem finite_lower_member_of_total {α : Type*}
    (K : Set α) (R : α → α → Prop) (hne : K.Nonempty)
    (hrefl : ∀ a ∈ K, R a a)
    (htrans : ∀ a ∈ K, ∀ b ∈ K, ∀ c ∈ K, R a b → R b c → R a c)
    (htotal : ∀ a ∈ K, ∀ b ∈ K, R a b ∨ R b a)
    (s : Finset K) : ∃ b : K, ∀ a ∈ s, R b.val a.val := by
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
    · refine ⟨a, ?_⟩
      intro c hc
      rcases Finset.mem_insert.mp hc with rfl | hc
      · exact hrefl c.val c.property
      · exact htrans a.val a.property b.val b.property c.val c.property
          hab (hb c hc)
    · refine ⟨b, ?_⟩
      intro c hc
      rcases Finset.mem_insert.mp hc with rfl | hc
      · exact hba
      · exact hb c hc

private theorem least_member_of_compact_total {α : Type*} [TopologicalSpace α]
    (K : Set α) (R : α → α → Prop) (hc : IsCompact K) (hne : K.Nonempty)
    (hrefl : ∀ a ∈ K, R a a)
    (htrans : ∀ a ∈ K, ∀ b ∈ K, ∀ c ∈ K, R a b → R b c → R a c)
    (htotal : ∀ a ∈ K, ∀ b ∈ K, R a b ∨ R b a)
    (hclosed : ∀ a ∈ K, IsClosed {b | R b a}) :
    ∃ b ∈ K, ∀ a ∈ K, R b a := by
  classical
  have hfinite (s : Finset K) :
      (K ∩ ⋂ a ∈ s, {b | R b a.val}).Nonempty := by
    obtain ⟨b, hb⟩ := finite_lower_member_of_total K R hne hrefl htrans htotal s
    exact ⟨b.val, b.property, Set.mem_iInter₂.mpr (fun a ha => hb a ha)⟩
  obtain ⟨b, hbK, hbCone⟩ := hc.inter_iInter_nonempty
    (fun a : K => {b | R b a.val}) (fun a => hclosed a.val a.property) hfinite
  refine ⟨b, hbK, ?_⟩
  intro a ha
  exact Set.mem_iInter.mp hbCone ⟨a, ha⟩

/-- A greatest lower bound of a nonempty family of actual same-root
geodesics is approached from above by a decreasing sequence in that family,
for the existing product topology on infinite lattice paths. This is the
geometric approximation needed in Strong Existence, public source lines
810–814. -/
theorem exists_descending_geodesics_tendsto_infimum
    (ω : Environment) (u : Lattice) (F : Set (ℕ → Lattice))
    (hne : F.Nonempty)
    (hvalid : ∀ γ ∈ F, IsLocallyRightmostGeodesic ω u γ)
    (q : ℕ → Lattice)
    (hqvalid : IsLocallyRightmostGeodesic ω u q)
    (hqlower : ∀ γ ∈ F, pathSoutheastLE q γ)
    (hqgreatest : ∀ δ : ℕ → Lattice,
      IsLocallyRightmostGeodesic ω u δ →
      (∀ γ ∈ F, pathSoutheastLE δ γ) → pathSoutheastLE δ q) :
    ∃ ρ : ℕ → (ℕ → Lattice),
      (∀ n : ℕ, ρ n ∈ F) ∧
      (∀ n : ℕ, pathSoutheastLE (ρ (n + 1)) (ρ n)) ∧
      Tendsto ρ atTop (𝓝 q) := by
  classical
  let G : Set (ℕ → Lattice) := {γ | IsLocallyRightmostGeodesic ω u γ}
  let K : Set (ℕ → Lattice) := closure F
  let R : (ℕ → Lattice) → (ℕ → Lattice) → Prop :=
    fun a b => ∀ n : ℕ, (a n).1 ≤ (b n).1 ∧ (b n).2 ≤ (a n).2

  -- The actual geodesic set is compact and closed in the product path topology.
  have hGcompact : IsCompact G := isCompact_locallyRightmostGeodesics ω u
  have hGclosed : IsClosed G := hGcompact.isClosed
  have hFsubsetG : F ⊆ G := fun γ hγ => hvalid γ hγ
  have hKsubsetG : K ⊆ G := closure_minimal hFsubsetG hGclosed
  have hKcompact : IsCompact K :=
    hGcompact.of_isClosed_subset isClosed_closure hKsubsetG
  have hKnonempty : K.Nonempty := hne.mono subset_closure
  have hKvalid : ∀ γ ∈ K, IsLocallyRightmostGeodesic ω u γ :=
    fun γ hγ => hKsubsetG hγ

  -- The southeast order is closed at every finite path coordinate.
  have hRclosedLower (a : ℕ → Lattice) : IsClosed {b | R b a} := by
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
  have hRclosedUpper (a : ℕ → Lattice) : IsClosed {b | R a b} := by
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

  -- Totality on actual same-root geodesics supplies finite minima.
  have hRrefl : ∀ a ∈ K, R a a := by
    intro a _ n
    exact ⟨le_rfl, le_rfl⟩
  have hRtrans : ∀ a ∈ K, ∀ b ∈ K, ∀ c ∈ K,
      R a b → R b c → R a c := by
    intro a _ b _ c _ hab hbc n
    exact ⟨(hab n).1.trans (hbc n).1, (hbc n).2.trans (hab n).2⟩
  have hRtotal : ∀ a ∈ K, ∀ b ∈ K, R a b ∨ R b a := by
    intro a ha b hb
    have hroot : a 0 = b 0 := (hKvalid a ha).1.trans (hKvalid b hb).1.symm
    rcases pathSoutheastLE_total_of_isLocallyRightmostGeodesic
      ω u a b (hKvalid a ha) (hKvalid b hb) with hab | hba
    · exact Or.inl ((pathSoutheastLE_iff_all_times_of_same_root a b hroot).mp hab)
    · exact Or.inr ((pathSoutheastLE_iff_all_times_of_same_root b a hroot.symm).mp hba)

  -- Every lower bound of F remains a lower bound of its closure.
  have hqLowerK : ∀ γ ∈ K, R q γ := by
    have hFsubsetCone : F ⊆ {γ | R q γ} := by
      intro γ hγ
      have hroot : q 0 = γ 0 := hqvalid.1.trans (hvalid γ hγ).1.symm
      exact (pathSoutheastLE_iff_all_times_of_same_root q γ hroot).mp
        (hqlower γ hγ)
    exact fun γ hγ => (closure_minimal hFsubsetCone (hRclosedUpper q)) hγ

  -- A compact total family has a least member. The GLB property identifies it with q.
  obtain ⟨m, hmK, hmLeast⟩ := least_member_of_compact_total K R
    hKcompact hKnonempty hRrefl hRtrans hRtotal
    (fun a _ => hRclosedLower a)
  have hmq : pathSoutheastLE m q := by
    apply hqgreatest m (hKvalid m hmK)
    intro γ hγ
    have hroot : m 0 = γ 0 := (hKvalid m hmK).1.trans (hvalid γ hγ).1.symm
    exact (pathSoutheastLE_iff_all_times_of_same_root m γ hroot).mpr
      (hmLeast γ (subset_closure hγ))
  have hqm : pathSoutheastLE q m := by
    have hroot : q 0 = m 0 := hqvalid.1.trans (hKvalid m hmK).1.symm
    exact (pathSoutheastLE_iff_all_times_of_same_root q m hroot).mpr
      (hqLowerK m hmK)
  have hqm_eq : q = m := by
    have hroot : q 0 = m 0 := hqvalid.1.trans (hKvalid m hmK).1.symm
    have hforward := (pathSoutheastLE_iff_all_times_of_same_root q m hroot).mp hqm
    have hbackward := (pathSoutheastLE_iff_all_times_of_same_root m q hroot.symm).mp hmq
    funext n
    exact Prod.ext (le_antisymm (hforward n).1 (hbackward n).1)
      (le_antisymm (hbackward n).2 (hforward n).2)
  have hqK : q ∈ closure F := by
    rw [hqm_eq]
    exact hmK

  -- First countability of the countable product gives a sequence in F.
  obtain ⟨γ, hγF, hγlim⟩ := (mem_closure_iff_seq_limit).mp hqK
  let ρ : ℕ → (ℕ → Lattice) := Nat.rec (γ 0) fun n prev =>
    if pathSoutheastLE (γ (n + 1)) prev then γ (n + 1) else prev
  have hρzero : ρ 0 = γ 0 := rfl
  have hρsucc (n : ℕ) :
      ρ (n + 1) =
        if pathSoutheastLE (γ (n + 1)) (ρ n) then γ (n + 1) else ρ n := rfl
  have hρF : ∀ n : ℕ, ρ n ∈ F := by
    intro n
    induction n with
    | zero => simpa only [hρzero] using hγF 0
    | succ n ih =>
      rw [hρsucc]
      split_ifs with h
      · exact hγF (n + 1)
      · exact ih
  have hρdec : ∀ n : ℕ, pathSoutheastLE (ρ (n + 1)) (ρ n) := by
    intro n
    rw [hρsucc]
    split_ifs with h
    · exact h
    · exact (pathSoutheastLE_iff_all_times_of_same_root (ρ n) (ρ n) rfl).mpr
        (fun _ => ⟨le_rfl, le_rfl⟩)
  have hρbelowγ : ∀ n : ℕ, pathSoutheastLE (ρ n) (γ n) := by
    intro n
    cases n with
    | zero =>
      rw [hρzero]
      exact (pathSoutheastLE_iff_all_times_of_same_root (γ 0) (γ 0) rfl).mpr
        (fun _ => ⟨le_rfl, le_rfl⟩)
    | succ n =>
      rw [hρsucc]
      by_cases h : pathSoutheastLE (γ (n + 1)) (ρ n)
      · rw [ite_eq_left h]
        exact (pathSoutheastLE_iff_all_times_of_same_root
          (γ (n + 1)) (γ (n + 1)) rfl).mpr (fun _ => ⟨le_rfl, le_rfl⟩)
      · rw [ite_eq_right h]
        rcases pathSoutheastLE_total_of_isLocallyRightmostGeodesic
          ω u (ρ n) (γ (n + 1)) (hvalid (ρ n) (hρF n))
          (hvalid (γ (n + 1)) (hγF (n + 1))) with hle | hle
        · exact hle
        · exact False.elim (h hle)

  -- The order sandwich collapses at each discrete coordinate, hence in the product.
  have hρlim : Tendsto ρ atTop (𝓝 q) := by
    apply tendsto_pi_nhds.mpr
    intro k
    have hγk : Tendsto (fun n => γ n k) atTop (𝓝 (q k)) :=
      ((continuous_apply k).tendsto q).comp hγlim
    have hγeq : ∀ᶠ n in atTop, γ n k = q k := by
      rw [nhds_discrete Lattice] at hγk
      exact Filter.tendsto_pure.mp hγk
    apply tendsto_nhds_of_eventually_eq
    filter_upwards [hγeq] with n hn
    have hroot₁ : q 0 = (ρ n) 0 := hqvalid.1.trans (hvalid (ρ n) (hρF n)).1.symm
    have hroot₂ : (ρ n) 0 = (γ n) 0 :=
      (hvalid (ρ n) (hρF n)).1.trans (hvalid (γ n) (hγF n)).1.symm
    have hlow := (pathSoutheastLE_iff_all_times_of_same_root q (ρ n) hroot₁).mp
      (hqlower (ρ n) (hρF n)) k
    have hupp := (pathSoutheastLE_iff_all_times_of_same_root (ρ n) (γ n) hroot₂).mp
      (hρbelowγ n) k
    have hfst : (γ n k).1 = (q k).1 := congrArg Prod.fst hn
    have hsnd : (γ n k).2 = (q k).2 := congrArg Prod.snd hn
    have hfirst : (ρ n k).1 ≤ (q k).1 := by simpa only [hfst] using hupp.1
    have hsecond : (q k).2 ≤ (ρ n k).2 := by simpa only [hsnd] using hupp.2
    apply Prod.ext
    · exact le_antisymm hfirst hlow.1
    · exact le_antisymm hlow.2 hsecond
  exact ⟨ρ, hρF, hρdec, hρlim⟩

end LPP.Busemann
