/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Busemann.Geometry.GeodesicPrefixMeasurability
public import Busemann.Geometry.GeodesicCompactness

import LPP_Foundations.Model.Paths.Fintype
import Mathlib.Topology.Compactness.Compact

@[expose] public section
open MeasureTheory LPPDifferentiability
namespace LPP.Busemann

private theorem forwardWeightSigma_le_ambient (v : Lattice) :
    forwardWeightSigma v ≤ (inferInstance : MeasurableSpace Environment) := by
  unfold forwardWeightSigma
  have hCone : Measurable (fun ω : Environment =>
      fun x : {x : Lattice // v ≤ x} => ω x.val) := by
    apply measurable_pi_iff.mpr
    intro x
    exact measurable_pi_apply x.val
  exact hCone.comap_le

private theorem measurableSet_fixed_aligned_coalescing_mate
    (v : Lattice) (m n : ℕ) :
    MeasurableSet {a : Environment × (ℕ → Lattice) |
      ∃ π : ℕ → Lattice,
        IsLocallyRightmostGeodesic a.1 v π ∧
        ∀ k : ℕ, a.2 (m + k) = π (n + k)} := by
  classical
  let Test (K : ℕ) : Set (Environment × (ℕ → Lattice)) :=
    {a | ∃ (d : ℕ × ℕ) (p : Path v d),
      d.1 + d.2 = n + K + 1 ∧
      (∃ π : ℕ → Lattice,
        IsLocallyRightmostGeodesic a.1 v π ∧
        ∀ i : Fin (d.1 + d.2 + 1), p.vertex i = π i.val) ∧
      ∀ i : Fin (d.1 + d.2 + 1), n ≤ i.val → i.val ≤ n + K →
        p.vertex i = a.2 (m + (i.val - n))}
  have hPrefix (d : ℕ × ℕ) (p : Path v d) :
      MeasurableSet {a : Environment × (ℕ → Lattice) |
        ∃ π : ℕ → Lattice,
          IsLocallyRightmostGeodesic a.1 v π ∧
          ∀ i : Fin (d.1 + d.2 + 1), p.vertex i = π i.val} := by
    have hForward := measurableSet_realized_locallyRightmostGeodesic_prefix v d p
    have hAmbient : MeasurableSet {ω : Environment |
        ∃ π : ℕ → Lattice,
          IsLocallyRightmostGeodesic ω v π ∧
          ∀ i : Fin (d.1 + d.2 + 1), p.vertex i = π i.val} :=
      (forwardWeightSigma_le_ambient v) _ hForward
    exact hAmbient.preimage measurable_fst
  have hMatch (K : ℕ) (d : ℕ × ℕ) (p : Path v d) :
      MeasurableSet {a : Environment × (ℕ → Lattice) |
        ∀ i : Fin (d.1 + d.2 + 1), n ≤ i.val → i.val ≤ n + K →
          p.vertex i = a.2 (m + (i.val - n))} := by
    have hSet : {a : Environment × (ℕ → Lattice) |
        ∀ i : Fin (d.1 + d.2 + 1), n ≤ i.val → i.val ≤ n + K →
          p.vertex i = a.2 (m + (i.val - n))} =
      ⋂ i : Fin (d.1 + d.2 + 1),
        {a : Environment × (ℕ → Lattice) |
          n ≤ i.val → i.val ≤ n + K →
            p.vertex i = a.2 (m + (i.val - n))} := by
      ext a
      simp
    rw [hSet]
    apply MeasurableSet.iInter
    intro i
    by_cases hni : n ≤ i.val
    · by_cases hik : i.val ≤ n + K
      · have hEq : {a : Environment × (ℕ → Lattice) |
            n ≤ i.val → i.val ≤ n + K →
              p.vertex i = a.2 (m + (i.val - n))} =
            {a : Environment × (ℕ → Lattice) |
              p.vertex i = a.2 (m + (i.val - n))} := by
          ext a
          simp [hni, hik]
        rw [hEq]
        exact measurableSet_eq_fun measurable_const
          ((measurable_pi_apply (m + (i.val - n))).comp measurable_snd)
      · have hEq : {a : Environment × (ℕ → Lattice) |
            n ≤ i.val → i.val ≤ n + K →
              p.vertex i = a.2 (m + (i.val - n))} = Set.univ := by
          ext a
          simp [hik]
        rw [hEq]
        exact MeasurableSet.univ
    · have hEq : {a : Environment × (ℕ → Lattice) |
          n ≤ i.val → i.val ≤ n + K →
            p.vertex i = a.2 (m + (i.val - n))} = Set.univ := by
        ext a
        simp [hni]
      rw [hEq]
      exact MeasurableSet.univ
  have hTest (K : ℕ) : MeasurableSet (Test K) := by
    have hSet : Test K = ⋃ d : ℕ × ℕ, ⋃ p : Path v d,
        {a : Environment × (ℕ → Lattice) |
          d.1 + d.2 = n + K + 1 ∧
          (∃ π : ℕ → Lattice,
            IsLocallyRightmostGeodesic a.1 v π ∧
            ∀ i : Fin (d.1 + d.2 + 1), p.vertex i = π i.val) ∧
          ∀ i : Fin (d.1 + d.2 + 1), n ≤ i.val → i.val ≤ n + K →
            p.vertex i = a.2 (m + (i.val - n))} := by
      ext a
      simp only [Test, Set.mem_ofPred_eq, Set.mem_iUnion]
    rw [hSet]
    apply MeasurableSet.iUnion
    intro d
    apply MeasurableSet.iUnion
    intro p
    exact (MeasurableSet.const _).inter ((hPrefix d p).inter (hMatch K d p))
  have hFinite (a : Environment × (ℕ → Lattice)) (K : ℕ) :
      a ∈ Test K ↔
      ∃ π : ℕ → Lattice,
        IsLocallyRightmostGeodesic a.1 v π ∧
        ∀ j : Fin (K + 1), a.2 (m + j.val) = π (n + j.val) := by
    constructor
    · rintro ⟨d, p, hd, ⟨π, hGeo, hVertex⟩, hTrace⟩
      refine ⟨π, hGeo, ?_⟩
      intro j
      let i : Fin (d.1 + d.2 + 1) := ⟨n + j.val, by omega⟩
      have hi := hTrace i (by dsimp [i]; omega) (by dsimp [i]; omega)
      have hindex : m + (i.val - n) = m + j.val := by dsimp [i]; omega
      rw [hindex] at hi
      exact hi.symm.trans (hVertex i)
    · rintro ⟨π, hGeo, hTrace⟩
      rcases hGeo.1 with rfl
      have hPositive : 0 < n + K + 1 := by omega
      obtain ⟨d, p, hd, hVertex, _hWeight, _hMax⟩ :=
        hGeo.2.2 0 (n + K + 1) hPositive
      refine ⟨d, p, hd, ⟨π, hGeo, ?_⟩, ?_⟩
      · intro i
        simpa only [zero_add] using hVertex i
      · intro i hni hik
        let j : Fin (K + 1) := ⟨i.val - n, by omega⟩
        have h := hTrace j
        have hindex : n + j.val = i.val := by dsimp [j]; omega
        have hmindex : m + j.val = m + (i.val - n) := rfl
        rw [hmindex, hindex] at h
        have hv : p.vertex i = π i.val := by
          simpa only [zero_add] using hVertex i
        exact hv.trans h.symm
  have hEvent : {a : Environment × (ℕ → Lattice) |
      ∃ π : ℕ → Lattice,
        IsLocallyRightmostGeodesic a.1 v π ∧
        ∀ k : ℕ, a.2 (m + k) = π (n + k)} = ⋂ K, Test K := by
    ext a
    simp only [Set.mem_ofPred_eq, Set.mem_iInter]
    constructor
    · rintro ⟨π, hGeo, hTrace⟩ K
      exact (hFinite a K).2 ⟨π, hGeo, fun j => hTrace j.val⟩
    · intro hAll
      let G : Set (ℕ → Lattice) :=
        {π | IsLocallyRightmostGeodesic a.1 v π}
      let C (K : ℕ) : Set (ℕ → Lattice) :=
        {π | ∀ j : Fin (K + 1), a.2 (m + j.val) = π (n + j.val)}
      let S (K : ℕ) : Set (ℕ → Lattice) := G ∩ C K
      have hCclosed (K : ℕ) : IsClosed (C K) := by
        have hCeq : C K = ⋂ j : Fin (K + 1),
            {π : ℕ → Lattice | a.2 (m + j.val) = π (n + j.val)} := by
          ext π
          simp [C]
        rw [hCeq]
        exact isClosed_iInter fun j =>
          isClosed_eq continuous_const (continuous_apply (n + j.val))
      have hGcompact : IsCompact G :=
        isCompact_locallyRightmostGeodesics a.1 v
      have hSclosed (K : ℕ) : IsClosed (S K) :=
        hGcompact.isClosed.inter (hCclosed K)
      have hSnonempty (K : ℕ) : (S K).Nonempty := by
        obtain ⟨π, hGeo, hTrace⟩ := (hFinite a K).1 (hAll K)
        exact ⟨π, hGeo, hTrace⟩
      have hSnested (K : ℕ) : S (K + 1) ⊆ S K := by
        intro π hπ
        refine ⟨hπ.1, ?_⟩
        intro j
        exact hπ.2 ⟨j.val, by omega⟩
      have hScompact : IsCompact (S 0) :=
        hGcompact.inter_right (hCclosed 0)
      obtain ⟨π, hπ⟩ :=
        hScompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
          S hSnested hSnonempty hSclosed
      have hπall (K : ℕ) : π ∈ S K := Set.mem_iInter.mp hπ K
      refine ⟨π, (hπall 0).1, ?_⟩
      intro k
      exact (hπall k).2 ⟨k, by omega⟩
  rw [hEvent]
  exact MeasurableSet.iInter hTest

/-- A raw ray has some locally rightmost geodesic mate from another signed
root with an aligned common tail: a Borel event in environment and raw ray.
Strong Existence, lm:coal, public source lines 939–961. -/
theorem measurableSet_exists_coalescing_locallyRightmost_mate
    (u v : Lattice) :
    MeasurableSet
      {a : Environment × (ℕ → Lattice) |
        ∃ π : ℕ → Lattice,
          IsLocallyRightmostGeodesic a.1 v π ∧
          ∃ m n : ℕ,
            u.1 + u.2 + (m : ℤ) = v.1 + v.2 + (n : ℤ) ∧
            ∀ k : ℕ, a.2 (m + k) = π (n + k)} := by
  classical
  have hSet : {a : Environment × (ℕ → Lattice) |
        ∃ π : ℕ → Lattice,
          IsLocallyRightmostGeodesic a.1 v π ∧
          ∃ m n : ℕ,
            u.1 + u.2 + (m : ℤ) = v.1 + v.2 + (n : ℤ) ∧
            ∀ k : ℕ, a.2 (m + k) = π (n + k)} =
      ⋃ m : ℕ, ⋃ n : ℕ,
        {a : Environment × (ℕ → Lattice) |
          u.1 + u.2 + (m : ℤ) = v.1 + v.2 + (n : ℤ) ∧
          ∃ π : ℕ → Lattice,
            IsLocallyRightmostGeodesic a.1 v π ∧
            ∀ k : ℕ, a.2 (m + k) = π (n + k)} := by
    ext a
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion]
    constructor
    · rintro ⟨π, hGeo, m, n, hAlign, hTail⟩
      exact ⟨m, n, hAlign, π, hGeo, hTail⟩
    · rintro ⟨m, n, hAlign, π, hGeo, hTail⟩
      exact ⟨π, hGeo, m, n, hAlign, hTail⟩
  rw [hSet]
  apply MeasurableSet.iUnion
  intro m
  apply MeasurableSet.iUnion
  intro n
  exact (MeasurableSet.const _).inter
    (measurableSet_fixed_aligned_coalescing_mate v m n)

end LPP.Busemann
