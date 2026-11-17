/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Busemann.Geometry.GreatestGeodesicExtension
public import Busemann.Geometry.GeodesicPrefixMeasurability
public import Busemann.Frozen.Definitions.ForwardWeightSigma
public import Mathlib.MeasureTheory.MeasurableSpace.Pi
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.Tactic

@[expose] public section

open MeasureTheory LPPDifferentiability

namespace LPP.Busemann

/-- Each fixed finite prefix determines a unique forward-measurable path-valued
map: the greatest genuine extension when realized, and the published east-axis
ray otherwise. Strong Existence, lines 725–732 and 1483. -/
theorem exists_unique_measurable_greatest_geodesic_prefix_extension
    (u : Lattice) (d : ℕ × ℕ) (p : Path u d) :
    let A : Set Environment := {ω |
      ∃ γ : ℕ → Lattice, IsLocallyRightmostGeodesic ω u γ ∧
        ∀ k : Fin (d.1 + d.2 + 1), p.vertex k = γ k.val}
    ∃! ρ : Environment → (ℕ → Lattice),
      @Measurable Environment (ℕ → Lattice) (forwardWeightSigma u)
        (inferInstance : MeasurableSpace (ℕ → Lattice)) ρ ∧
      ∀ ω : Environment,
        (ω ∈ A →
          IsLocallyRightmostGeodesic ω u (ρ ω) ∧
          (∀ k : Fin (d.1 + d.2 + 1), ρ ω k.val = p.vertex k) ∧
          ∀ γ : ℕ → Lattice,
            IsLocallyRightmostGeodesic ω u γ →
            (∀ k : Fin (d.1 + d.2 + 1), γ k.val = p.vertex k) →
            pathSoutheastLE γ (ρ ω)) ∧
        (ω ∉ A → ∀ n : ℕ, ρ ω n = u + ((n : ℤ), (0 : ℤ))) := by
  classical
  let A : Set Environment := {ω | ∃ γ : ℕ → Lattice,
    IsLocallyRightmostGeodesic ω u γ ∧
      ∀ k : Fin (d.1 + d.2 + 1), p.vertex k = γ k.val}
  have hA : @MeasurableSet Environment (forwardWeightSigma u) A :=
    measurableSet_realized_locallyRightmostGeodesic_prefix u d p
  have hnonempty (ω : Environment) (hω : ω ∈ A) :
      ∃ γ : ℕ → Lattice, IsLocallyRightmostGeodesic ω u γ ∧
        ∀ k : Fin (d.1 + d.2 + 1), γ k.val = p.vertex k := by
    obtain ⟨γ, hγ, ht⟩ := hω
    exact ⟨γ, hγ, fun k => (ht k).symm⟩
  let ρ : Environment → ℕ → Lattice := fun ω =>
    if hω : ω ∈ A then
      Classical.choose (exists_unique_greatest_locallyRightmostGeodesic_extension
        ω u d p (hnonempty ω hω))
    else fun n => u + ((n : ℤ), (0 : ℤ))
  have hchosen (ω : Environment) (hω : ω ∈ A) :
      IsLocallyRightmostGeodesic ω u (ρ ω) ∧
        (∀ k : Fin (d.1 + d.2 + 1), ρ ω k.val = p.vertex k) ∧
        ∀ γ : ℕ → Lattice, IsLocallyRightmostGeodesic ω u γ →
          (∀ k : Fin (d.1 + d.2 + 1), γ k.val = p.vertex k) →
          pathSoutheastLE γ (ρ ω) := by
    simpa only [ρ, dite_eq_left hω] using
      (Classical.choose_spec (exists_unique_greatest_locallyRightmostGeodesic_extension
        ω u d p (hnonempty ω hω))).1
  have haxis (ω : Environment) (hω : ω ∉ A) (n : ℕ) :
      ρ ω n = u + ((n : ℤ), (0 : ℤ)) := by simp only [ρ, dite_eq_right hω]
  -- Each candidate event records one actual long finite prefix and its extension.
  let L := d.1 + d.2
  let C (e : ℕ × ℕ) (q : Path u e) : Set Environment := {ω |
    ∃ γ : ℕ → Lattice, IsLocallyRightmostGeodesic ω u γ ∧
      ∀ i : Fin (e.1 + e.2 + 1), q.vertex i = γ i.val}
  have hC (e : ℕ × ℕ) (q : Path u e) :
      @MeasurableSet Environment (forwardWeightSigma u) (C e q) :=
    measurableSet_realized_locallyRightmostGeodesic_prefix u e q
  let Test (n : ℕ) (z : ℤ) (e : ℕ × ℕ) (q : Path u e) : Set Environment :=
    if h : n ≤ e.1 + e.2 ∧ L ≤ e.1 + e.2 then
      if (∀ k : Fin (d.1 + d.2 + 1),
            q.vertex ⟨k.val, by have hk := k.isLt; dsimp only [L] at h; omega⟩ = p.vertex k) ∧
          z ≤ (q.vertex ⟨n, by omega⟩).1 then C e q else ∅
    else ∅
  have hTest (n : ℕ) (z : ℤ) (e : ℕ × ℕ) (q : Path u e) :
      @MeasurableSet Environment (forwardWeightSigma u) (Test n z e q) := by
    let : MeasurableSpace Environment := forwardWeightSigma u
    dsimp only [Test]
    split_ifs
    · exact hC e q
    · exact MeasurableSet.empty
    · exact MeasurableSet.empty
  -- Greatestness turns a coordinate threshold into a countable union of tests.
  have hthreshold (n : ℕ) (z : ℤ) :
      {ω : Environment | ω ∈ A ∧ z ≤ (ρ ω n).1} =
        ⋃ e : ℕ × ℕ, ⋃ q : Path u e, Test n z e q := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion]
    constructor
    · rintro ⟨hω, hz⟩
      have hρ := hchosen ω hω
      let T := max n L + 1
      have hs := hρ.1.2.2 0 T (by dsimp [T]; omega)
      rw [hρ.1.1] at hs
      obtain ⟨e, q, hlen, htrace, hweight, hgreat⟩ := hs
      have hlen' : n ≤ e.1 + e.2 ∧ L ≤ e.1 + e.2 := by dsimp [T] at hlen; omega
      have hcompat : ∀ k : Fin (d.1 + d.2 + 1),
          q.vertex ⟨k.val, by have hk := k.isLt; dsimp only [L] at hlen'; omega⟩ = p.vertex k := by
        intro k
        rw [htrace]
        simpa only [Nat.zero_add] using hρ.2.1 k
      have hn : z ≤ (q.vertex ⟨n, by omega⟩).1 := by
        rw [htrace]
        simpa only [Nat.zero_add] using hz
      refine ⟨e, q, ?_⟩
      simp only [Test, dite_eq_left hlen']
      split_ifs with hgood
      · exact ⟨ρ ω, hρ.1, fun i => by simpa only [Nat.zero_add] using htrace i⟩
      · exact (hgood ⟨hcompat, hn⟩).elim
    · rintro ⟨e, q, hq⟩
      by_cases he : n ≤ e.1 + e.2 ∧ L ≤ e.1 + e.2
      · simp only [Test, dite_eq_left he] at hq
        split_ifs at hq with hc
        · obtain ⟨hcompat, hz⟩ := hc
          obtain ⟨γ, hγ, htrace⟩ := hq
          have hω : ω ∈ A := by
            refine ⟨γ, hγ, ?_⟩
            intro k
            exact (hcompat k).symm.trans (htrace ⟨k.val, by have hk := k.isLt; dsimp only [L] at he; omega⟩)
          have hρ := hchosen ω hω
          have hγp : ∀ k : Fin (d.1 + d.2 + 1), γ k.val = p.vertex k := by
            intro k
            exact (htrace ⟨k.val, by have hk := k.isLt; dsimp only [L] at he; omega⟩).symm.trans (hcompat k)
          have horder := hρ.2.2 γ hγ hγp n n (by rw [hγ.1, hρ.1.1])
          refine ⟨hω, ?_⟩
          have hqγ := htrace ⟨n, by omega⟩
          exact le_trans (by simpa only [hqγ] using hz) horder.1
        · exact hq.elim
      · simp only [Test, dite_eq_right he, Set.mem_empty_iff_false] at hq
  have hfirst (n : ℕ) : @Measurable Environment ℤ (forwardWeightSigma u) _
      (fun ω => (ρ ω n).1) := by
    apply measurable_of_Ici
    intro z
    have hUnion : @MeasurableSet Environment (forwardWeightSigma u)
        (⋃ e : ℕ × ℕ, ⋃ q : Path u e, Test n z e q) :=
      MeasurableSet.iUnion fun e => MeasurableSet.iUnion fun q => hTest n z e q
    have hpre : {ω : Environment | z ≤ (ρ ω n).1} =
        (⋃ e : ℕ × ℕ, ⋃ q : Path u e, Test n z e q) ∪
          (Aᶜ ∩ {ω : Environment | z ≤ (u + ((n : ℤ), (0 : ℤ))).1}) := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_union, Set.mem_inter_iff, Set.mem_compl_iff,
        ← hthreshold]
      by_cases hω : ω ∈ A
      · simp [hω]
      · simp [hω, haxis ω hω n]
    change @MeasurableSet Environment (forwardWeightSigma u)
      {ω : Environment | z ≤ (ρ ω n).1}
    rw [hpre]
    exact hUnion.union (hA.compl.inter (MeasurableSet.const _))
  have hlevel (ω : Environment) (n : ℕ) :
      (ρ ω n).1 + (ρ ω n).2 = u.1 + u.2 + (n : ℤ) := by
    by_cases hω : ω ∈ A
    · have hρ := (hchosen ω hω).1
      induction n with
      | zero => simp [hρ.1]
      | succ n ih =>
        rcases hρ.2.1 n with h | h <;>
          have hx := congrArg Prod.fst h <;>
          have hy := congrArg Prod.snd h <;>
          simp only [Prod.fst_add, Prod.snd_add] at hx hy <;>
          simp only [Nat.cast_add, Nat.cast_one] <;> omega
    · rw [haxis ω hω n]
      simp only [Prod.fst_add, Prod.snd_add, add_zero]
      omega
  have hmeas : @Measurable Environment (ℕ → Lattice) (forwardWeightSigma u)
      (inferInstance : MeasurableSpace (ℕ → Lattice)) ρ := by
    let : MeasurableSpace Environment := forwardWeightSigma u
    apply measurable_pi_iff.mpr
    intro n
    have hs : @Measurable Environment ℤ (forwardWeightSigma u) _
        (fun ω => (ρ ω n).2) := by
      have heq : (fun ω => (ρ ω n).2) =
          fun ω => u.1 + u.2 + (n : ℤ) - (ρ ω n).1 := by
        funext ω
        have h := hlevel ω n
        omega
      rw [heq]
      exact measurable_const.sub (hfirst n)
    exact (hfirst n).prodMk hs
  refine ⟨ρ, ⟨hmeas, ?_⟩, ?_⟩
  · intro ω
    exact ⟨hchosen ω, haxis ω⟩
  · intro σ hσ
    funext ω
    by_cases hω : ω ∈ A
    · have hs := (hσ.2 ω).1 hω
      have hu := (Classical.choose_spec (exists_unique_greatest_locallyRightmostGeodesic_extension
        ω u d p (hnonempty ω hω))).2
      simpa only [ρ, dite_eq_left hω] using hu (σ ω) hs
    · funext n
      exact ((hσ.2 ω).2 hω n).trans (haxis ω hω n).symm

end LPP.Busemann
