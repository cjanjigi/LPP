/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Differentiability.Probability.TiltStripBadSites
public import Differentiability.Probability.TopRestrictedConcentration
import Mathlib.Tactic

/-!
# Endpoints of paths in the closed tilt strip

A path in the closed tilt strip is described by its two endpoints. This file
rewrites the full-strip event as a finite union over pairs of endpoints, and
identifies the event for each pair.
-/

public section
noncomputable section
open MeasureTheory Filter Set
namespace LPPDifferentiability

/-- The full-strip path event is exactly a finite union over its endpoint slices.
Every vertex is constrained, including the terminal vertex. -/
theorem closed_strip_top_event_eq_endpoint_union
    (M : EReal) (a s b : ℝ) (n : ℕ) :
    let slice : ℤ → Finset Lattice := fun k => (Finset.Icc
      (Int.ceil (a * (k : ℝ) - 8 * s))
      (Int.floor (a * (k : ℝ) + 8 * s))).image (fun i => (i, k - i))
    let R : Finset Lattice := (Finset.Icc (0 : ℤ) (n : ℤ)).biUnion slice
    {ω : Environment | ∃ u : Lattice,
      ∃ q : Σ i : Fin (n + 1), Path u (i.val, n - i.val),
        (∀ j, 0 ≤ (q.2.vertex j).1 + (q.2.vertex j).2 ∧
          (q.2.vertex j).1 + (q.2.vertex j).2 ≤ (n : ℤ) ∧
          |(1-a) * ((q.2.vertex j).1 : ℝ) - a * ((q.2.vertex j).2 : ℝ)| ≤ 8*s) ∧
        b < ((q.2.collectedSites.filter (fun z => (ω z : EReal) = M)).card : ℝ)} =
      ⋃ uv ∈ slice 0 ×ˢ slice (n : ℤ),
        {ω : Environment | ∃ d : ℕ × ℕ, ∃ p : Path uv.1 d,
          uv.2 = uv.1 + ((d.1 : ℤ), (d.2 : ℤ)) ∧
          (∀ j, p.vertex j ∈ R) ∧
          b < ((p.collectedSites.filter (fun z => (ω z : EReal) = M)).card : ℝ)} := by
  classical
  intro slice R
  ext ω
  simp only [Set.mem_ofPred_eq, Set.mem_iUnion]
  constructor
  · rintro ⟨u, q, hstrip, hcount⟩
    let d : ℕ × ℕ := (q.1.val, n - q.1.val)
    let v : Lattice := u + ((d.1 : ℤ), (d.2 : ℤ))
    have hlen : d.1 + d.2 = n := by
      dsimp only [d]
      exact Nat.add_sub_of_le (by have h := q.1.isLt; omega)
    have hu0 := Path.start_level_zero_of_closed_strip q
      (fun j => ⟨(hstrip j).1, (hstrip j).2.1⟩)
    have hurho := (hstrip 0).2.2
    rw [q.2.start] at hurho
    have hvlevel : v.1 + v.2 = (n : ℤ) := by
      change u.1 + (d.1 : ℤ) + (u.2 + (d.2 : ℤ)) = (n : ℤ)
      have hc : (d.1 : ℤ) + (d.2 : ℤ) = (n : ℤ) := by exact_mod_cast hlen
      omega
    have hvrho := (hstrip (Fin.last (d.1 + d.2))).2.2
    rw [q.2.finish] at hvrho
    refine ⟨(u, v), Finset.mem_product.mpr
      ⟨(tiltStripLevelSlice_mem_iff a s 0 u).2 ⟨hu0, hurho⟩,
        (tiltStripLevelSlice_mem_iff a s (n : ℤ) v).2 ⟨hvlevel, hvrho⟩⟩,
      d, q.2, rfl, ?_, hcount⟩
    intro j
    exact (tiltStripRegion_mem_iff a s n _).2 (hstrip j)
  · rintro ⟨⟨u, v⟩, huv, ⟨i, k⟩, p, hv, hp, hcount⟩
    obtain ⟨hu, hvSlice⟩ := Finset.mem_product.mp huv
    have hu0 := ((tiltStripLevelSlice_mem_iff a s 0 u).1 hu).1
    have hvn := ((tiltStripLevelSlice_mem_iff a s (n : ℤ) v).1 hvSlice).1
    have hlen : i + k = n := by
      have h₁ := congrArg Prod.fst hv
      have h₂ := congrArg Prod.snd hv
      simp only [Prod.fst_add, Prod.snd_add] at h₁ h₂
      omega
    have hk : k = n - i := by omega
    subst k
    refine ⟨u, ⟨⟨i, by omega⟩, p⟩, ?_, hcount⟩
    intro j
    exact (tiltStripRegion_mem_iff a s n _).1 (hp j)

/-- Ordered integer endpoints determine a unique natural displacement. This
identifies their path event with the fixed-displacement concentration event. -/
theorem endpoint_top_event_eq_of_le
    (M : EReal) (R : Finset Lattice) (u v : Lattice) (b : ℝ) (huv : u ≤ v) :
    {ω : Environment | ∃ d : ℕ × ℕ, ∃ p : Path u d,
      v = u + ((d.1 : ℤ), (d.2 : ℤ)) ∧ (∀ j, p.vertex j ∈ R) ∧
      b < ((p.collectedSites.filter (fun z => (ω z : EReal) = M)).card : ℝ)} =
    {ω : Environment | ∃ p : Path u ((v.1-u.1).toNat, (v.2-u.2).toNat),
      (∀ j, p.vertex j ∈ R) ∧
      b < ((p.collectedSites.filter (fun z => (ω z : EReal) = M)).card : ℝ)} := by
  classical
  ext ω
  constructor
  · rintro ⟨d, p, hv, hp, hc⟩
    have h₁ := congrArg Prod.fst hv
    have h₂ := congrArg Prod.snd hv
    simp only [Prod.fst_add, Prod.snd_add] at h₁ h₂
    have hd : d = ((v.1-u.1).toNat, (v.2-u.2).toNat) := by
      apply Prod.ext <;> dsimp only <;> omega
    subst d
    exact ⟨p, hp, hc⟩
  · rintro ⟨p, hp, hc⟩
    refine ⟨_, p, ?_, hp, hc⟩
    apply Prod.ext <;> simp only [Prod.fst_add, Prod.snd_add]
    · have h := huv.1
      omega
    · have h := huv.2
      omega

/-- An unordered pair has no up-right path and its endpoint event is empty. -/
theorem endpoint_top_event_eq_empty_of_not_le
    (M : EReal) (R : Finset Lattice) (u v : Lattice) (b : ℝ) (huv : ¬u ≤ v) :
    {ω : Environment | ∃ d : ℕ × ℕ, ∃ p : Path u d,
      v = u + ((d.1 : ℤ), (d.2 : ℤ)) ∧ (∀ j, p.vertex j ∈ R) ∧
      b < ((p.collectedSites.filter (fun z => (ω z : EReal) = M)).card : ℝ)} = ∅ := by
  classical
  apply Set.eq_empty_iff_forall_notMem.mpr
  rintro ω ⟨d, _p, hv, _hp, _hc⟩
  apply huv
  rw [hv]
  exact ⟨by dsimp only [Prod.fst_add]; omega,
    by dsimp only [Prod.snd_add]; omega⟩

/-- Two ordered endpoints in the slices give the displacement length and the
transverse bound used in the paper, with no endpoint reduction assumed. -/
theorem tilt_strip_endpoint_displacement_bounds
    (a s : ℝ) (n : ℕ) (u v : Lattice) (huv : u ≤ v)
    (hu : u.1 + u.2 = 0 ∧ |(1-a)*(u.1 : ℝ)-a*(u.2 : ℝ)| ≤ 8*s)
    (hv : v.1 + v.2 = (n : ℤ) ∧ |(1-a)*(v.1 : ℝ)-a*(v.2 : ℝ)| ≤ 8*s) :
    let d : ℕ × ℕ := ((v.1-u.1).toNat, (v.2-u.2).toNat)
    d.1 + d.2 = n ∧ |(1-a)*(d.1 : ℝ)-a*(d.2 : ℝ)| ≤ 16*s := by
  intro d
  have hd₁ : (d.1 : ℤ) = v.1-u.1 := Int.toNat_of_nonneg (sub_nonneg.mpr huv.1)
  have hd₂ : (d.2 : ℤ) = v.2-u.2 := Int.toNat_of_nonneg (sub_nonneg.mpr huv.2)
  constructor
  · have h0 := hu.1
    have hn := hv.1
    omega
  · have hr₁ : (d.1 : ℝ) = (v.1 : ℝ)-(u.1 : ℝ) := by exact_mod_cast hd₁
    have hr₂ : (d.2 : ℝ) = (v.2 : ℝ)-(u.2 : ℝ) := by exact_mod_cast hd₂
    rw [hr₁, hr₂]
    have heq : (1-a)*((v.1 : ℝ)-(u.1 : ℝ))-a*((v.2 : ℝ)-(u.2 : ℝ)) =
        ((1-a)*(v.1 : ℝ)-a*(v.2 : ℝ))-((1-a)*(u.1 : ℝ)-a*(u.2 : ℝ)) := by ring
    rw [heq]
    exact (abs_sub _ _).trans (by linarith [hu.2, hv.2])

end LPPDifferentiability
end
