/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Differentiability.Model.BackwardHeavyAttachmentNetGeometry
public import Differentiability.Model.HeavyAttachmentObservationRegion
import Mathlib.Tactic

/-! Reflection of the source region, its tubes and the finite mask events. -/
public section
namespace LPPDifferentiability
open scoped Classical

theorem backward_heavy_mem_neg_image (S : Finset Lattice) (z : Lattice) :
    z ∈ S.image (fun x => -x) ↔ -z ∈ S := by
  constructor
  · rintro hz
    obtain ⟨x, hx, heq⟩ := Finset.mem_image.mp hz
    simpa only [← heq, neg_neg] using hx
  · intro hz
    exact Finset.mem_image.mpr ⟨-z, hz, neg_neg z⟩

/-- Exact finite reflection preserves filtered cardinalities. -/
theorem backward_heavy_reflected_filter_card (S T : Finset Lattice)
    (p q : Lattice → Prop) (hS : ∀ z, z ∈ S ↔ -z ∈ T)
    (hp : ∀ z, p z ↔ q (-z)) :
    (S.filter p).card=(T.filter q).card := by
  classical
  have heq : S.filter p=(T.filter q).image (fun z => -z) := by
    ext z
    rw [backward_heavy_mem_neg_image, Finset.mem_filter, Finset.mem_filter,
      hS, hp]
  rw [heq, Finset.card_image_of_injective _ neg_injective]

/-- The reflected segment has the negative deviation, with the same positive
displacement vector and signed level increment. -/
theorem backward_heavy_deviation_neg (a : ℝ) (I : ℤ) (u z : Lattice)
    (d : ℕ × ℕ) (m : ℕ) :
    (1-a)*((-z).1:ℝ)-a*((-z).2:ℝ)-
      ((1-a)*((-u).1:ℝ)-a*((-u).2:ℝ)+
        (((-z).1+(-z).2-(-I):ℤ):ℝ)*
          ((1-a)*(d.1:ℝ)-a*(d.2:ℝ))/(m:ℝ)) =
    -((1-a)*(z.1:ℝ)-a*(z.2:ℝ)-
      ((1-a)*(u.1:ℝ)-a*(u.2:ℝ)+
        ((z.1+z.2-I:ℤ):ℝ)*
          ((1-a)*(d.1:ℝ)-a*(d.2:ℝ))/(m:ℝ))) := by
  simp only [Prod.fst_neg, Prod.snd_neg, Int.cast_neg, Int.cast_add, Int.cast_sub]
  ring

theorem backward_heavy_distance_neg (z x : Lattice) :
    |((-z).1:ℝ)-((-x).1:ℝ)|+|((-z).2:ℝ)-((-x).2:ℝ)| =
      |(z.1:ℝ)-(x.1:ℝ)|+|(z.2:ℝ)-(x.2:ℝ)| := by
  simp only [Prod.fst_neg, Prod.snd_neg, Int.cast_neg, neg_sub_neg,
    abs_sub_comm]

/-- The backward source sets and the local active conditions.
The supplied lower net may be the one constructed by the common-net theorem.
Every lower-net forward box belongs to R, including sites outside Q. -/
theorem exists_backward_heavy_attachment_observation_geometry
    (a D s kappa lo hi : ℝ) (I : ℤ) (K M : ℕ) (w : Fin (M+1) → Lattice)
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
      (∀ z, z ∈ Q ↔ I-(m:ℤ) ≤ z.1+z.2 ∧ z.1+z.2 ≤ I ∧
        lo-(m:ℝ)-(K:ℝ)-2 ≤ rho z ∧ rho z ≤ hi+(m:ℝ)+(K:ℝ)+2) ∧
      (Q.card:ℝ) ≤ 4*D*s^2 ∧
      (∀ z, z ∈ R ↔ z ∈ Q ∨ z ∈ J ∨
        ∃ j, z ∈ Set.Icc (w j) (w j+((L:ℤ),(L:ℤ)))) ∧
      (∀ (u : Lattice) (d : ℕ × ℕ),
        ((Q.filter (fun z => |rho z-(rho u+
          ((z.1+z.2-I:ℤ):ℝ)*((1-a)*(d.1:ℝ)-a*(d.2:ℝ))/(m:ℝ))| ≤
            (K:ℝ)+2)).card:ℝ) ≤ (2*(K:ℝ)+5)*((m+1:ℕ):ℝ)) ∧
      (∀ (u : Lattice), u ∈ J → ∀ (d : ℕ × ℕ) (j : Fin (M+1)),
        d.1+d.2=m → w j+((d.1:ℤ),(d.2:ℤ))=u →
        ∃ (_ : ∀ z ∈ Set.Icc (u-((d.1:ℤ),(d.2:ℤ))) u, z ∈ R)
          (hboxR : ∀ z ∈ Set.Icc (u-((d.1:ℤ),(d.2:ℤ)))
            (u-((d.1:ℤ),(d.2:ℤ))+((L:ℤ),(L:ℤ))), z ∈ R),
        ∀ mask : R → Bool,
        let V := {z : Lattice | ∃ hz : z ∈ R, mask ⟨z,hz⟩=true}
        (∀ z ∈ Q, ∀ x ∈ Q, z ∈ V → x ∈ V → z ≠ x →
          ¬ (|(z.1:ℝ)-(x.1:ℝ)|+|(z.2:ℝ)-(x.2:ℝ)| ≤ 2)) →
        (∀ z ∈ J, z ∉ V) →
        (∀ j z, z ∈ Set.Icc (w j) (w j+((L:ℤ),(L:ℤ))) → z ∉ V) →
        ((Q.filter (fun z => |rho z-(rho u+
          ((z.1+z.2-I:ℤ):ℝ)*((1-a)*(d.1:ℝ)-a*(d.2:ℝ))/(m:ℝ))| ≤
            (K:ℝ)+2)).filter (fun z => z ∈ V)).card < K →
        u ∉ V ∧
        (∀ z ∈ Set.Icc (u-((d.1:ℤ),(d.2:ℤ))) u,
          ∀ x ∈ Set.Icc (u-((d.1:ℤ),(d.2:ℤ))) u,
          z ∈ V → x ∈ V → z ≠ x →
          ¬ (|(z.1:ℝ)-(x.1:ℝ)|+|(z.2:ℝ)-(x.2:ℝ)| ≤ 2)) ∧
        (∀ z (hz : z ∈ Set.Icc (u-((d.1:ℤ),(d.2:ℤ)))
          (u-((d.1:ℤ),(d.2:ℤ))+((L:ℤ),(L:ℤ)))), mask ⟨z,hboxR z hz⟩=false) ∧
        ((Finset.Icc (u-((d.1:ℤ),(d.2:ℤ))) u).filter (fun z => z ∈ V ∧
          |(z.1:ℝ)-(u.1:ℝ)-((z.1+z.2-(u.1+u.2):ℤ):ℝ)*
            ((d.1:ℝ)/(d.1+d.2:ℕ))| ≤ (K:ℝ)+2)).card < K) := by
  classical
  intro m rho L
  let v : Fin (M+1) → Lattice := fun j => -w j
  obtain ⟨Jf, Qf, Rf, hJf, hJcard, hQf, hQcard, hRf, hSigmaf, hlocalf⟩ :=
    exists_heavy_attachment_observation_geometry a D s kappa (-hi) (-lo) (-I) K M v
      ha ha1 hD hs hkappa hkappaCap (by linarith) (by linarith) hcut
  let J := Jf.image (fun z => -z)
  let Q := Qf.image (fun z => -z)
  let R := Rf.image (fun z => -z)
  have hJmem := backward_heavy_mem_neg_image Jf
  have hQmem := backward_heavy_mem_neg_image Qf
  have hRmem := backward_heavy_mem_neg_image Rf
  have hneg (z : Lattice) : rho (-z) = -rho z := backward_heavy_transverse_neg a z
  have hbox (j : Fin (M+1)) (z : Lattice) :
      -z ∈ Set.Icc (v j-((L:ℤ),(L:ℤ))) (v j) ↔
        z ∈ Set.Icc (w j) (w j+((L:ℤ),(L:ℤ))) := by
    dsimp only [v]
    rw [show -w j-((L:ℤ),(L:ℤ))= -(w j+((L:ℤ),(L:ℤ))) by abel]
    exact backward_heavy_neg_mem_Icc _ _ _
  have hJ (u : Lattice) : u ∈ J ↔ u.1+u.2=I ∧ rho u ∈ Set.Icc lo hi := by
    rw [hJmem, hJf]
    change ((-u).1+(-u).2= -I ∧ rho (-u) ∈ Set.Icc (-hi) (-lo)) ↔ _
    simp only [Prod.fst_neg, Prod.snd_neg, hneg, Set.mem_Icc]
    constructor <;> rintro ⟨hl, hlo, hhi⟩
    · exact ⟨by omega, by linarith, by linarith⟩
    · exact ⟨by omega, by linarith, by linarith⟩
  have hQ (z : Lattice) : z ∈ Q ↔ I-(m:ℤ) ≤ z.1+z.2 ∧ z.1+z.2 ≤ I ∧
      lo-(m:ℝ)-(K:ℝ)-2 ≤ rho z ∧ rho z ≤ hi+(m:ℝ)+(K:ℝ)+2 := by
    rw [hQmem, hQf]
    change (-I ≤ (-z).1+(-z).2 ∧ (-z).1+(-z).2 ≤ -I+(m:ℤ) ∧
      -hi-(m:ℝ)-(K:ℝ)-2 ≤ rho (-z) ∧ rho (-z) ≤ -lo+(m:ℝ)+(K:ℝ)+2) ↔ _
    simp only [Prod.fst_neg, Prod.snd_neg, hneg]
    constructor <;> rintro ⟨hl, hh, hlo, hhi⟩
    · exact ⟨by omega, by omega, by linarith, by linarith⟩
    · exact ⟨by omega, by omega, by linarith, by linarith⟩
  have hR (z : Lattice) : z ∈ R ↔ z ∈ Q ∨ z ∈ J ∨
      ∃ j, z ∈ Set.Icc (w j) (w j+((L:ℤ),(L:ℤ))) := by
    rw [hRmem, hRf]
    change (-z ∈ Qf ∨ -z ∈ Jf ∨
      ∃ j, -z ∈ Set.Icc (v j-((L:ℤ),(L:ℤ))) (v j)) ↔ _
    simp only [← hQmem, ← hJmem, hbox]
    rfl
  have hdev (u z : Lattice) (d : ℕ × ℕ) :
      |rho (-z)-(rho (-u)+(((-z).1+(-z).2-(-I):ℤ):ℝ)*
        ((1-a)*(d.1:ℝ)-a*(d.2:ℝ))/(m:ℝ))| =
      |rho z-(rho u+((z.1+z.2-I:ℤ):ℝ)*
        ((1-a)*(d.1:ℝ)-a*(d.2:ℝ))/(m:ℝ))| := by
    rw [backward_heavy_deviation_neg, abs_neg]
  have hSigma (u : Lattice) (d : ℕ × ℕ) :=
    backward_heavy_reflected_filter_card Q Qf
      (fun z => |rho z-(rho u+((z.1+z.2-I:ℤ):ℝ)*
        ((1-a)*(d.1:ℝ)-a*(d.2:ℝ))/(m:ℝ))| ≤ (K:ℝ)+2)
      (fun z => |rho z-(rho (-u)+((z.1+z.2-(-I):ℤ):ℝ)*
        ((1-a)*(d.1:ℝ)-a*(d.2:ℝ))/(m:ℝ))| ≤ (K:ℝ)+2)
      hQmem (fun z => by rw [hdev])
  refine ⟨J, Q, R, hJ, ?_, hQ, ?_, hR, ?_, ?_⟩
  · rw [Finset.card_image_of_injective _ neg_injective]
    exact hJcard
  · rw [Finset.card_image_of_injective _ neg_injective]
    exact hQcard
  · intro u d
    rw [hSigma]
    exact hSigmaf (-u) d
  · intro u hu d j hd hend
    have hw : u-((d.1:ℤ),(d.2:ℤ))=w j := by rw [← hend]; abel
    have hendf : -u+((d.1:ℤ),(d.2:ℤ))=v j := by
      dsimp only [v]
      rw [← hend]
      abel
    obtain ⟨hrectfR, hboxfR, hactivef⟩ := hlocalf (-u) ((hJmem u).1 hu) d j hd hendf
    have hrectneg (z : Lattice) :
        -z ∈ Set.Icc (-u) (-u+((d.1:ℤ),(d.2:ℤ))) ↔
          z ∈ Set.Icc (u-((d.1:ℤ),(d.2:ℤ))) u := by
      rw [show -u+((d.1:ℤ),(d.2:ℤ))= -(u-((d.1:ℤ),(d.2:ℤ))) by abel]
      exact backward_heavy_neg_mem_Icc _ _ _
    have hrectR (z : Lattice) (hz : z ∈ Set.Icc (u-((d.1:ℤ),(d.2:ℤ))) u) : z ∈ R :=
      (hRmem z).2 (hrectfR (-z) ((hrectneg z).2 hz))
    have hboxR (z : Lattice) (hz : z ∈ Set.Icc (u-((d.1:ℤ),(d.2:ℤ)))
        (u-((d.1:ℤ),(d.2:ℤ))+((L:ℤ),(L:ℤ)))) : z ∈ R :=
      (hR z).2 (Or.inr (Or.inr ⟨j, by simpa only [hw] using hz⟩))
    refine ⟨hrectR, hboxR, ?_⟩
    intro mask V hE1 hE2J hE2box hE3
    let maskf : Rf → Bool := fun z => mask ⟨-z.val,
      (hRmem (-z.val)).2 (by simpa only [neg_neg] using z.property)⟩
    let Vf := {z : Lattice | ∃ hz : z ∈ Rf, maskf ⟨z,hz⟩=true}
    have hV (z : Lattice) : z ∈ V ↔ -z ∈ Vf := by
      constructor
      · rintro ⟨hz, hb⟩
        refine ⟨(hRmem z).1 hz, ?_⟩
        simpa only [maskf, neg_neg] using hb
      · rintro ⟨hz, hb⟩
        refine ⟨(hRmem z).2 hz, ?_⟩
        simpa only [maskf, neg_neg] using hb
    have hE1f : ∀ z ∈ Qf, ∀ x ∈ Qf, z ∈ Vf → x ∈ Vf → z ≠ x →
        ¬ (|(z.1:ℝ)-(x.1:ℝ)|+|(z.2:ℝ)-(x.2:ℝ)| ≤ 2) := by
      intro z hz x hx hzbad hxbad hne hdist
      apply hE1 (-z) ((hQmem (-z)).2 (by simpa only [neg_neg] using hz))
        (-x) ((hQmem (-x)).2 (by simpa only [neg_neg] using hx))
        ((hV (-z)).2 (by simpa only [neg_neg] using hzbad))
        ((hV (-x)).2 (by simpa only [neg_neg] using hxbad))
        (fun h => hne (neg_injective h))
      simpa only [backward_heavy_distance_neg] using hdist
    have hE2Jf : ∀ z ∈ Jf, z ∉ Vf := by
      intro z hz hb
      exact hE2J (-z) ((hJmem (-z)).2 (by simpa only [neg_neg] using hz))
        ((hV (-z)).2 (by simpa only [neg_neg] using hb))
    have hE2boxf : ∀ j z, z ∈ Set.Icc (v j-((L:ℤ),(L:ℤ))) (v j) → z ∉ Vf := by
      intro k z hz hb
      apply hE2box k (-z) ((hbox k (-z)).1 (by simpa only [neg_neg] using hz))
      exact (hV (-z)).2 (by simpa only [neg_neg] using hb)
    have hE3f : ((Qf.filter (fun z => |rho z-(rho (-u)+
        ((z.1+z.2-(-I):ℤ):ℝ)*((1-a)*(d.1:ℝ)-a*(d.2:ℝ))/(m:ℝ))| ≤
          (K:ℝ)+2)).filter (fun z => z ∈ Vf)).card < K := by
      apply lt_of_le_of_lt (Finset.card_le_card_of_injOn (fun z => -z) ?_
        neg_injective.injOn) hE3
      intro z hz
      obtain ⟨hztube, hzbad⟩ := Finset.mem_filter.mp hz
      obtain ⟨hzQ, hzdev⟩ := Finset.mem_filter.mp hztube
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_filter.mpr ⟨(hQmem (-z)).2 (by
        simpa only [neg_neg] using hzQ), ?_⟩,
        (hV (-z)).2 (by simpa only [neg_neg] using hzbad)⟩
      have hh := hdev u (-z) d
      simp only [neg_neg] at hh
      rw [← hh]
      exact hzdev
    have hf := hactivef maskf hE1f hE2Jf hE2boxf hE3f
    have hm : 0 < m := by
      have hh : (0:ℝ) < m := by linarith [(Nat.cast_nonneg K : (0:ℝ) ≤ K)]
      exact_mod_cast hh
    have hrectQ (z : Lattice) (hz : z ∈ Set.Icc (u-((d.1:ℤ),(d.2:ℤ))) u) : z ∈ Q := by
      have hul : (-u).1+(-u).2= -I := by
        have hh := ((hJ u).1 hu).1
        simp only [Prod.fst_neg, Prod.snd_neg]
        omega
      have hb := heavy_attachment_rectangle_bounds a (-hi) (-lo) (-I) m K (-u) (-z) d
        ha ha1 hul (by change -hi ≤ rho (-u); rw [hneg]; linarith [((hJ u).1 hu).2.2])
        (by change rho (-u) ≤ -lo; rw [hneg]; linarith [((hJ u).1 hu).2.1])
        hd ((hrectneg z).2 hz)
      exact (hQmem z).2 ((hQf (-z)).2 hb)
    refine ⟨(fun hb => hf.1 ((hV u).1 hb)), ?_, ?_, ?_⟩
    · intro z hz x hx hzbad hxbad hne hdist
      exact hE1 z (hrectQ z hz) x (hrectQ x hx) hzbad hxbad hne hdist
    · intro z hz
      have hsafe := hE2box j z (by simpa only [hw] using hz)
      cases hb : mask ⟨z,hboxR z hz⟩ with
      | false => rfl
      | true => exact (hsafe ⟨hboxR z hz, hb⟩).elim
    · apply lt_of_le_of_lt (Finset.card_le_card ?_) hE3
      intro z hz
      obtain ⟨hzrect, hzbad, hzdev⟩ := Finset.mem_filter.mp hz
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_filter.mpr ⟨hrectQ z (Finset.mem_Icc.mp hzrect), ?_⟩, hzbad⟩
      rw [heavy_attachment_deviation_identity a I u z d m ((hJ u).1 hu).1 hd hm]
      exact hzdev

end LPPDifferentiability
