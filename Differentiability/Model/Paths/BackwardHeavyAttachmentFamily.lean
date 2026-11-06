/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Differentiability.Model.BackwardHeavyAttachmentNetGeometry
public import Differentiability.Model.BackwardHeavyAttachmentObservationGeometry
public import Differentiability.Model.Paths.BackwardMaskGreedyFamily

/-! A common-net family of backward heavy-tail attachments. -/

public section
open scoped Classical
namespace LPPDifferentiability

/-- Construct one net before all starts, then the same greedy family for every
observed mask. The conditions E1, E2 and E3 of Section B.2 of the differentiability preprint imply
local activity and vertex safety. -/
theorem exists_backward_heavy_attachment_family
    (a D s kappa lo hi : ℝ) (I : ℤ) (K : ℕ)
    (ha : 0 < a) (ha1 : a < 1) (hD : 1 ≤ D) (hs : 4 ≤ s)
    (hkappa : 0 < kappa) (hkappaCap : kappa ≤ (1/16:ℝ))
    (hlohi : lo ≤ hi) (hwidth : hi-lo ≤ D*s)
    (hspacing : 1 ≤ min a (1-a)*(Nat.ceil (kappa*s):ℝ)/4)
    (hK : 2 ≤ K) (hcut : 2*K+5 ≤ Nat.ceil (kappa*s))
    (hboxcut : 4*K+4 ≤ Nat.ceil (kappa*s)) :
    let m := Nat.ceil (kappa*s)
    let rho := fun z : Lattice => (1-a)*(z.1:ℝ)-a*(z.2:ℝ)
    let L := 4*K+4
    ∃ (J : Finset Lattice) (M : ℕ) (w : Fin (M+1) → Lattice)
      (Q R : Finset Lattice) (j : J → Fin (M+1)) (d : J → ℕ × ℕ),
      (∀ u, u ∈ J ↔ u.1+u.2=I ∧ rho u ∈ Set.Icc lo hi) ∧
      (J.card:ℝ) ≤ D*s+1 ∧
      1 ≤ M ∧ Function.Injective w ∧
      (∀ k, (w k).1+(w k).2=I-(m:ℤ) ∧
        rho (w k) ∈ Set.Icc (lo-(1-a)*(m:ℝ)) (hi+a*(m:ℝ))) ∧
      (∀ (k : ℕ) (hk : k < M),
        min a (1-a)*(m:ℝ)/4 ≤ rho (w ⟨k+1, by omega⟩)-rho (w ⟨k, by omega⟩) ∧
        rho (w ⟨k+1, by omega⟩)-rho (w ⟨k, by omega⟩) ≤ min a (1-a)*(m:ℝ)/2) ∧
      (∀ k, (rho (w k) ≤ lo-(1-a)*(m:ℝ)+min a (1-a)*(m:ℝ)/2) ↔ k.val=0) ∧
      (∀ k, (hi+a*(m:ℝ)-min a (1-a)*(m:ℝ)/2 ≤ rho (w k)) ↔ k.val=M) ∧
      rho (w ⟨0, by omega⟩) ≤ lo-(1-a)*(m:ℝ)+min a (1-a)*(m:ℝ)/2 ∧
      hi+a*(m:ℝ)-min a (1-a)*(m:ℝ)/2 ≤ rho (w ⟨M, by omega⟩) ∧
      (M+1:ℝ) < 4*(hi-lo+(m:ℝ))/(min a (1-a)*(m:ℝ)) ∧
      (M+1:ℝ) ≤ 8*D/(min a (1-a)*kappa)+2 ∧
      (∀ z, z ∈ Q ↔ I-(m:ℤ) ≤ z.1+z.2 ∧ z.1+z.2 ≤ I ∧
        lo-(m:ℝ)-(K:ℝ)-2 ≤ rho z ∧ rho z ≤ hi+(m:ℝ)+(K:ℝ)+2) ∧
      (Q.card:ℝ) ≤ 4*D*s^2 ∧
      (∀ z, z ∈ R ↔ z ∈ Q ∨ z ∈ J ∨
        ∃ k, z ∈ Set.Icc (w k) (w k+((L:ℤ),(L:ℤ)))) ∧
      (∀ u, (d u).1+(d u).2=m ∧ w (j u)+(((d u).1:ℤ),((d u).2:ℤ))=u.val ∧
        ((d u).1:ℝ)/(m:ℝ) ∈ Set.Icc (1/4) (3/4) ∧ |rho (u.val-w (j u))| ≤ (m:ℝ)) ∧
      (∀ u : J, ((Q.filter (fun z => |rho z-(rho u.val+
        ((z.1+z.2-I:ℤ):ℝ)*((1-a)*((d u).1:ℝ)-a*((d u).2:ℝ))/(m:ℝ))| ≤
          (K:ℝ)+2)).card:ℝ) ≤ (2*(K:ℝ)+5)*((m+1:ℕ):ℝ)) ∧
      ∃ (_hrect : ∀ (u : J) z, z ∈ Set.Icc (u.val-(((d u).1:ℤ),((d u).2:ℤ))) u.val → z ∈ R)
        (hbox : ∀ (u : J) z, z ∈ Set.Icc
          (u.val-(((d u).1:ℤ),((d u).2:ℤ)))
          (u.val-(((d u).1:ℤ),((d u).2:ℤ))+((L:ℤ),(L:ℤ))) → z ∈ R),
      let V := fun mask : R → Bool => {z : Lattice | ∃ hz : z ∈ R, mask ⟨z,hz⟩=true}
      let active := fun (mask : R → Bool) (u : J) =>
        u.val ∉ V mask ∧
        (∀ z ∈ Set.Icc (u.val-(((d u).1:ℤ),((d u).2:ℤ))) u.val,
          ∀ w ∈ Set.Icc (u.val-(((d u).1:ℤ),((d u).2:ℤ))) u.val,
          z ∈ V mask → w ∈ V mask → z ≠ w →
          ¬ (|(z.1:ℝ)-(w.1:ℝ)|+|(z.2:ℝ)-(w.2:ℝ)| ≤ 2)) ∧
        (∀ z (hz : z ∈ Set.Icc
          (u.val-(((d u).1:ℤ),((d u).2:ℤ)))
          (u.val-(((d u).1:ℤ),((d u).2:ℤ))+((L:ℤ),(L:ℤ)))), mask ⟨z,hbox u z hz⟩=false) ∧
        ((Finset.Icc (u.val-(((d u).1:ℤ),((d u).2:ℤ))) u.val).filter
          (fun z => z ∈ V mask ∧
            |(z.1:ℝ)-(u.val.1:ℝ)-((z.1+z.2-(u.val.1+u.val.2):ℤ):ℝ)*
              (((d u).1:ℝ)/((d u).1+(d u).2:ℕ))| ≤ (K:ℝ)+2)).card < K
      let sourceGood := fun mask : R → Bool =>
        (∀ z ∈ Q, ∀ w ∈ Q, z ∈ V mask → w ∈ V mask → z ≠ w →
          ¬ (|(z.1:ℝ)-(w.1:ℝ)|+|(z.2:ℝ)-(w.2:ℝ)| ≤ 2)) ∧
        (∀ z ∈ J, z ∉ V mask) ∧
        (∀ k z, z ∈ Set.Icc (w k) (w k+((L:ℤ),(L:ℤ))) → z ∉ V mask) ∧
        (∀ u : J, ((Q.filter (fun z => |rho z-(rho u.val+
          ((z.1+z.2-I:ℤ):ℝ)*((1-a)*((d u).1:ℝ)-a*((d u).2:ℝ))/(m:ℝ))| ≤
            (K:ℝ)+2)).filter (fun z => z ∈ V mask)).card < K)
      (∀ u, u.val-(((d u).1:ℤ),((d u).2:ℤ))=w (j u)) ∧
      ∃ qforward : (mask : R → Bool) → (u : J) → Path (-u.val) (d u),
      ∃ qback : (mask : R → Bool) → (u : J) → Path (w (j u)) (d u),
        (∀ mask u i, (qback mask u).vertex i = -((qforward mask u).vertex i.rev)) ∧
        ∃ (hmem : ∀ mask u i, (qback mask u).vertex i ∈ R),
        (∀ mask u, (qback mask u).vertex (Fin.last ((d u).1+(d u).2))=u.val) ∧
        (∀ mask u, active mask u → ∀ i, (qback mask u).vertex i ∉ V mask) ∧
        (∀ mask, sourceGood mask → ∀ u, active mask u ∧
          (∀ i, mask ⟨(qback mask u).vertex i, hmem mask u i⟩=false)) := by
  classical
  intro m rho L
  obtain ⟨J, M, w, hJ, hJcard, hM, hinj, hnet, hgap, hfirstOnly, hlastOnly,
    hfirst, hlast, hcard, huniform, htargets⟩ :=
    exists_backward_heavy_attachment_common_net a D s kappa lo hi I ha ha1 hD hs hkappa
      hkappaCap hlohi hwidth hspacing
  obtain ⟨J', Q, R, hJ', _, hQ, hQcard, hR, hSigma, hgeometry⟩ :=
    exists_backward_heavy_attachment_observation_geometry a D s kappa lo hi I K M w
      ha ha1 hD hs hkappa hkappaCap hlohi hwidth (by exact_mod_cast hcut)
  have heq : J' = J := by
    ext u
    exact (hJ' u).trans (hJ u).symm
  subst J'
  choose j d hd using fun u : J => htargets u.val u.property
  choose hrect hbox hlocal using fun u : J =>
    hgeometry u.val u.property (d u) (j u) (hd u).1 (hd u).2.1
  refine ⟨J, M, w, Q, R, j, d, hJ, hJcard, hM, hinj, hnet, hgap,
    hfirstOnly, hlastOnly, hfirst, hlast, hcard, huniform, hQ, hQcard, hR, hd,
    fun u => hSigma u.val (d u), hrect, hbox, ?_⟩
  intro V active sourceGood
  have hlen (u : J) : (d u).1+(d u).2=m := (hd u).1
  have hstart (u : J) : u.val-(((d u).1:ℤ),((d u).2:ℤ))=w (j u) := by
    rw [← (hd u).2.1, add_sub_cancel_right]
  obtain ⟨qforward, qb, hreverse, hmem, hgood⟩ :=
    GreedyAttachment.exists_backward_finite_mask_greedy_family
      R (fun u : J => u.val) d K hK (fun u => by rw [hlen]; exact hboxcut)
      (fun u => by simpa only [hlen] using (hd u).2.2.1.1)
      (fun u => by simpa only [hlen] using (hd u).2.2.1.2) hrect hbox
  let qback (mask : R → Bool) (u : J) : Path (w (j u)) (d u) := {
    vertex := (qb mask u).vertex
    start := (qb mask u).start.trans (hstart u)
    finish := by rw [← hstart u]; exact (qb mask u).finish
    step := (qb mask u).step }
  refine ⟨hstart, qforward, qback, hreverse, hmem, ?_, hgood, ?_⟩
  · intro mask u
    exact (qback mask u).finish.trans (hd u).2.1
  · intro mask hsource u
    have hactive : active mask u := hlocal u mask hsource.1 hsource.2.1
      hsource.2.2.1 (hsource.2.2.2 u)
    refine ⟨hactive, ?_⟩
    intro i
    cases hbit : mask ⟨(qback mask u).vertex i, _⟩ with
    | false => rfl
    | true => exact (hgood mask u hactive i ⟨hmem mask u i, hbit⟩).elim

end LPPDifferentiability
