/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Differentiability.Model.HeavyAttachmentNetGeometry
import Mathlib.Tactic

/-! The backward common net, obtained by finite reflection. -/
public section
namespace LPPDifferentiability

/-- Reflection changes the sign of the transverse coordinate. -/
theorem backward_heavy_transverse_neg (a : ℝ) (z : Lattice) :
    (1-a)*((-z).1:ℝ)-a*((-z).2:ℝ) =
      -((1-a)*(z.1:ℝ)-a*(z.2:ℝ)) := by
  simp only [Prod.fst_neg, Prod.snd_neg, Int.cast_neg]
  ring

/-- Reflection reverses a directed rectangle, including its boundary. -/
theorem backward_heavy_neg_mem_Icc (x y z : Lattice) :
    -z ∈ Set.Icc (-y) (-x) ↔ z ∈ Set.Icc x y := by
  change ((-y.1 ≤ -z.1 ∧ -y.2 ≤ -z.2) ∧
    (-z.1 ≤ -x.1 ∧ -z.2 ≤ -x.2)) ↔
      ((x.1 ≤ z.1 ∧ x.2 ≤ z.2) ∧ (z.1 ≤ y.1 ∧ z.2 ≤ y.2))
  omega

/-- One lower net, with increasing original transverse order, is chosen
before every endpoint of the upper interval. -/
theorem exists_backward_heavy_attachment_common_net
    (a D s kappa lo hi : ℝ) (I : ℤ)
    (ha : 0 < a) (ha1 : a < 1) (hD : 1 ≤ D) (hs : 4 ≤ s)
    (hkappa : 0 < kappa) (hkappaCap : kappa ≤ (1/16:ℝ))
    (hlohi : lo ≤ hi) (hwidth : hi-lo ≤ D*s)
    (hspacing : 1 ≤ min a (1-a)*(Nat.ceil (kappa*s):ℝ)/4) :
    let m := Nat.ceil (kappa*s)
    let rho := fun z : Lattice => (1-a)*(z.1:ℝ)-a*(z.2:ℝ)
    ∃ (J : Finset Lattice) (M : ℕ) (w : Fin (M+1) → Lattice),
      (∀ u, u ∈ J ↔ u.1+u.2=I ∧ rho u ∈ Set.Icc lo hi) ∧
      (J.card:ℝ) ≤ D*s+1 ∧
      1 ≤ M ∧ Function.Injective w ∧
      (∀ j, (w j).1+(w j).2=I-(m:ℤ) ∧
        rho (w j) ∈ Set.Icc (lo-(1-a)*(m:ℝ)) (hi+a*(m:ℝ))) ∧
      (∀ (j : ℕ) (hj : j < M),
        min a (1-a)*(m:ℝ)/4 ≤
          rho (w ⟨j+1, by omega⟩)-rho (w ⟨j, by omega⟩) ∧
        rho (w ⟨j+1, by omega⟩)-rho (w ⟨j, by omega⟩) ≤
          min a (1-a)*(m:ℝ)/2) ∧
      (∀ j, (rho (w j) ≤ lo-(1-a)*(m:ℝ)+min a (1-a)*(m:ℝ)/2) ↔ j.val=0) ∧
      (∀ j, (hi+a*(m:ℝ)-min a (1-a)*(m:ℝ)/2 ≤ rho (w j)) ↔ j.val=M) ∧
      rho (w ⟨0, by omega⟩) ≤ lo-(1-a)*(m:ℝ)+min a (1-a)*(m:ℝ)/2 ∧
      hi+a*(m:ℝ)-min a (1-a)*(m:ℝ)/2 ≤ rho (w ⟨M, by omega⟩) ∧
      (M+1:ℝ) < 4*(hi-lo+(m:ℝ))/(min a (1-a)*(m:ℝ)) ∧
      (M+1:ℝ) ≤ 8*D/(min a (1-a)*kappa)+2 ∧
      (∀ u ∈ J, ∃ (j : Fin (M+1)) (d : ℕ × ℕ),
        d.1+d.2=m ∧ w j+((d.1:ℤ),(d.2:ℤ))=u ∧
        (d.1:ℝ)/(m:ℝ) ∈ Set.Icc (1/4) (3/4) ∧
        |rho (u-w j)| ≤ (m:ℝ)) := by
  classical
  intro m rho
  obtain ⟨Jf, M, v, hJf, hJcard, hM, hinj, hnet, hgap, hfirstOnly,
      hlastOnly, hfirst, hlast, hcard, hbound, hattach⟩ :=
    exists_heavy_attachment_common_net a D s kappa (-hi) (-lo) (-I)
      ha ha1 hD hs hkappa hkappaCap (by linarith) (by linarith) hspacing
  let J := Jf.image (fun z => -z)
  let w : Fin (M+1) → Lattice := fun j => -v j.rev
  have hneg (z : Lattice) : rho (-z) = -rho z := backward_heavy_transverse_neg a z
  have hJmem (u : Lattice) : u ∈ J ↔ -u ∈ Jf := by
    simp only [J, Finset.mem_image]
    constructor
    · rintro ⟨z, hz, heq⟩
      simpa only [← heq, neg_neg] using hz
    · intro hu
      exact ⟨-u, hu, neg_neg u⟩
  have hJ (u : Lattice) : u ∈ J ↔ u.1+u.2=I ∧ rho u ∈ Set.Icc lo hi := by
    rw [hJmem, hJf]
    change ((-u).1+(-u).2= -I ∧ rho (-u) ∈ Set.Icc (-hi) (-lo)) ↔ _
    simp only [Prod.fst_neg, Prod.snd_neg, hneg, Set.mem_Icc]
    constructor <;> rintro ⟨hlevel, hlo, hhi⟩
    · exact ⟨by omega, by linarith, by linarith⟩
    · exact ⟨by omega, by linarith, by linarith⟩
  have hw (j : Fin (M+1)) : rho (w j) = -rho (v j.rev) := hneg _
  have hfirstW (j : Fin (M+1)) :
      (rho (w j) ≤ lo-(1-a)*(m:ℝ)+min a (1-a)*(m:ℝ)/2) ↔ j.val=0 := by
    rw [hw]
    have hh := hlastOnly j.rev
    have hrev : j.rev.val=M ↔ j.val=0 := by simp only [Fin.val_rev]; omega
    rw [← hrev, ← hh]
    constructor <;> intro h <;> linarith only [h]
  have hlastW (j : Fin (M+1)) :
      (hi+a*(m:ℝ)-min a (1-a)*(m:ℝ)/2 ≤ rho (w j)) ↔ j.val=M := by
    rw [hw]
    have hh := hfirstOnly j.rev
    have hrev : j.rev.val=0 ↔ j.val=M := by simp only [Fin.val_rev]; omega
    rw [← hrev, ← hh]
    constructor <;> intro h <;> linarith only [h]
  refine ⟨J, M, w, hJ, ?_, hM, ?_, ?_, ?_, hfirstW, hlastW,
    (hfirstW _).2 rfl, (hlastW _).2 rfl, ?_, hbound, ?_⟩
  · have hc : J.card=Jf.card := Finset.card_image_of_injective _ neg_injective
    rw [hc]
    exact hJcard
  · intro j k hjk
    exact Fin.rev_injective (hinj (neg_injective hjk))
  · intro j
    obtain ⟨hl, hlo, hhi⟩ := hnet j.rev
    refine ⟨?_, ?_, ?_⟩
    · dsimp only [w]
      simp only [Prod.fst_neg, Prod.snd_neg]
      omega
    · rw [hw]; linarith only [hhi]
    · rw [hw]; linarith only [hlo]
  · intro j hj
    let k : ℕ := M-1-j
    have hk : k < M := by dsimp only [k]; omega
    have he₁ : (⟨j+1, by omega⟩ : Fin (M+1)).rev = ⟨k, by omega⟩ := by
      apply Fin.ext; simp only [Fin.val_rev]; dsimp only [k]; omega
    have he₂ : (⟨j, by omega⟩ : Fin (M+1)).rev = ⟨k+1, by omega⟩ := by
      apply Fin.ext; simp only [Fin.val_rev]; dsimp only [k]; omega
    rw [hw, hw, he₁, he₂]
    obtain ⟨hl, hh⟩ := hgap k hk
    constructor <;> linarith only [hl, hh]
  · convert hcard using 1; ring
  · intro u hu
    obtain ⟨j, d, hd, hend, hcentral, habs⟩ := hattach (-u) ((hJmem u).1 hu)
    have hendW : w j.rev+((d.1:ℤ),(d.2:ℤ))=u := by
      dsimp only [w]
      rw [Fin.rev_rev]
      apply Prod.ext
      · have hh := congrArg Prod.fst hend
        simp only [Prod.fst_add, Prod.fst_neg] at hh ⊢
        omega
      · have hh := congrArg Prod.snd hend
        simp only [Prod.snd_add, Prod.snd_neg] at hh ⊢
        omega
    refine ⟨j.rev, d, hd, hendW, hcentral, ?_⟩
    have heq : u-w j.rev = v j- -u := by
      dsimp only [w]
      rw [Fin.rev_rev]
      abel
    rw [heq]
    exact habs

end LPPDifferentiability
