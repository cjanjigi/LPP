/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Differentiability.Model.HeavyAttachmentTubeGeometry
public import Differentiability.Model.Paths.FiniteMaskGreedyFamily
import Mathlib.Tactic

/-! Finite observation of all source events and their local active conditions. -/
public section
namespace LPPDifferentiability
open scoped Classical

/-- Construct the starting interval, source region, and observation
region for a supplied finite net. The common-net theorem supplies that net.
The source events E1, E2 and E3 imply the active conditions of the greedy family;
this is a conditional deterministic statement, with no probability claim. -/
theorem exists_heavy_attachment_observation_geometry
    (a D s kappa lo hi : ℝ) (I : ℤ) (K M : ℕ) (v : Fin (M+1) → Lattice)
    (ha : 0 < a) (ha1 : a < 1) (hD : 1 ≤ D) (hs : 4 ≤ s)
    (hkappa : 0 < kappa) (hkappaCap : kappa ≤ (1/16:ℝ))
    (hlohi : lo ≤ hi) (hwidth : hi-lo ≤ D*s)
    (hcut : 2*(K:ℝ)+5 ≤ (Nat.ceil (kappa*s):ℝ)) :
    let m := Nat.ceil (kappa*s)
    let rho := fun z : Lattice => (1-a)*(z.1:ℝ)-a*(z.2:ℝ)
    let L := 4*K+4
    ∃ J Q R : Finset Lattice,
      (∀ u, u ∈ J ↔ u.1+u.2=I ∧ rho u ∈ Set.Icc lo hi) ∧
      (J.card:ℝ) ≤ D*s+1 ∧
      (∀ z, z ∈ Q ↔ I ≤ z.1+z.2 ∧ z.1+z.2 ≤ I+(m:ℤ) ∧
        lo-(m:ℝ)-(K:ℝ)-2 ≤ rho z ∧ rho z ≤ hi+(m:ℝ)+(K:ℝ)+2) ∧
      (Q.card:ℝ) ≤ 4*D*s^2 ∧
      (∀ z, z ∈ R ↔ z ∈ Q ∨ z ∈ J ∨
        ∃ j, z ∈ Set.Icc (v j-((L:ℤ),(L:ℤ))) (v j)) ∧
      (∀ (u : Lattice) (d : ℕ × ℕ),
        ((Q.filter (fun z => |rho z-(rho u+
          ((z.1+z.2-I:ℤ):ℝ)*((1-a)*(d.1:ℝ)-a*(d.2:ℝ))/(m:ℝ))| ≤
            (K:ℝ)+2)).card:ℝ) ≤ (2*(K:ℝ)+5)*((m+1:ℕ):ℝ)) ∧
      (∀ (u : Lattice), u ∈ J → ∀ (d : ℕ × ℕ) (j : Fin (M+1)),
        d.1+d.2=m → u+((d.1:ℤ),(d.2:ℤ))=v j →
        ∃ (_ : ∀ z ∈ Set.Icc u (u+((d.1:ℤ),(d.2:ℤ))), z ∈ R)
          (hboxR : ∀ z ∈ Set.Icc
            (u+((d.1:ℤ),(d.2:ℤ))-((L:ℤ),(L:ℤ)))
            (u+((d.1:ℤ),(d.2:ℤ))), z ∈ R),
        ∀ mask : R → Bool,
        let V := {z : Lattice | ∃ hz : z ∈ R, mask ⟨z,hz⟩=true}
        (∀ z ∈ Q, ∀ w ∈ Q, z ∈ V → w ∈ V → z ≠ w →
          ¬ (|(z.1:ℝ)-(w.1:ℝ)|+|(z.2:ℝ)-(w.2:ℝ)| ≤ 2)) →
        (∀ z ∈ J, z ∉ V) →
        (∀ j z, z ∈ Set.Icc (v j-((L:ℤ),(L:ℤ))) (v j) → z ∉ V) →
        ((Q.filter (fun z => |rho z-(rho u+
          ((z.1+z.2-I:ℤ):ℝ)*((1-a)*(d.1:ℝ)-a*(d.2:ℝ))/(m:ℝ))| ≤
            (K:ℝ)+2)).filter (fun z => z ∈ V)).card < K →
        u ∉ V ∧
        (∀ z ∈ Set.Icc u (u+((d.1:ℤ),(d.2:ℤ))),
          ∀ w ∈ Set.Icc u (u+((d.1:ℤ),(d.2:ℤ))),
          z ∈ V → w ∈ V → z ≠ w →
          ¬ (|(z.1:ℝ)-(w.1:ℝ)|+|(z.2:ℝ)-(w.2:ℝ)| ≤ 2)) ∧
        (∀ z (hz : z ∈ Set.Icc
          (u+((d.1:ℤ),(d.2:ℤ))-((L:ℤ),(L:ℤ)))
          (u+((d.1:ℤ),(d.2:ℤ)))), mask ⟨z,hboxR z hz⟩=false) ∧
        ((Finset.Icc u (u+((d.1:ℤ),(d.2:ℤ)))).filter (fun z => z ∈ V ∧
          |(z.1:ℝ)-(u.1:ℝ)-((z.1+z.2-(u.1+u.2):ℤ):ℝ)*
            ((d.1:ℝ)/(d.1+d.2:ℕ))| ≤ (K:ℝ)+2)).card < K) := by
  classical
  intro m rho L
  obtain ⟨J, hJ, hJcard⟩ := exists_finset_level_interval a lo hi I hlohi
  obtain ⟨Q, hQ, hQcard, hrectQ, hSigma⟩ :=
    exists_heavy_attachment_tube_geometry a D s kappa lo hi I K
      ha ha1 hD hs hkappa hkappaCap hlohi hwidth hcut
  let boxes : Finset Lattice := (Finset.univ : Finset (Fin (M+1))).biUnion
    (fun j => Finset.Icc (v j-((L:ℤ),(L:ℤ))) (v j))
  let R := Q ∪ J ∪ boxes
  have hR (z : Lattice) : z ∈ R ↔ z ∈ Q ∨ z ∈ J ∨
      ∃ j, z ∈ Set.Icc (v j-((L:ℤ),(L:ℤ))) (v j) := by
    simp only [R, boxes, Finset.mem_union, Finset.mem_biUnion,
      Finset.mem_univ, true_and, Finset.mem_Icc, Set.mem_Icc, or_assoc]
  refine ⟨J, Q, R, hJ, by linarith, hQ, hQcard, hR, hSigma, ?_⟩
  intro u hu d j hd hend
  have hrect (z : Lattice) (hz : z ∈ Set.Icc u (u+((d.1:ℤ),(d.2:ℤ)))) : z ∈ Q :=
    hrectQ u d ((hJ u).1 hu).1 ((hJ u).1 hu).2 hd z hz
  have hrectR (z : Lattice) (hz : z ∈ Set.Icc u (u+((d.1:ℤ),(d.2:ℤ)))) : z ∈ R :=
    (hR z).2 (Or.inl (hrect z hz))
  have hboxR (z : Lattice) (hz : z ∈ Set.Icc
      (u+((d.1:ℤ),(d.2:ℤ))-((L:ℤ),(L:ℤ)))
      (u+((d.1:ℤ),(d.2:ℤ)))) : z ∈ R := by
    apply (hR z).2
    exact Or.inr (Or.inr ⟨j, by simpa only [hend] using hz⟩)
  refine ⟨hrectR, hboxR, ?_⟩
  intro mask V hE1 hE2J hE2box hE3
  have hm : 0 < m := by
    have hK0 : (0:ℝ) ≤ K := Nat.cast_nonneg K
    have hh : (0:ℝ) < m := by linarith [hcut]
    exact_mod_cast hh
  have hTube := heavy_attachment_greedy_tube_subset a I m K Q u d
    ((hJ u).1 hu).1 hd hm hrect
  refine ⟨hE2J u hu, ?_, ?_, ?_⟩
  · intro z hz w hw
    exact hE1 z (hrect z hz) w (hrect w hw)
  · intro z hz
    have hsafe := hE2box j z (by simpa only [hend] using hz)
    cases hbit : mask ⟨z,hboxR z hz⟩ with
    | false => rfl
    | true => exact (hsafe ⟨hboxR z hz, hbit⟩).elim
  · apply lt_of_le_of_lt (Finset.card_le_card ?_) hE3
    intro z hz
    obtain ⟨hzrect, hzbad, hzdev⟩ := Finset.mem_filter.mp hz
    have hzSigma := hTube (Finset.mem_filter.mpr ⟨hzrect, hzdev⟩)
    exact Finset.mem_filter.mpr ⟨hzSigma, hzbad⟩

end LPPDifferentiability
