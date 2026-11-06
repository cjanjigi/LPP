/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Differentiability.Probability.BackwardHeavyAttachmentSourceEvents

/-! Literal source events and finite observations of the original field. -/

public section
open MeasureTheory Set
namespace LPPDifferentiability

/-- Exact observation equivalence, including endpoint box sites outside Q. -/
theorem backward_heavy_attachment_source_event_mask_iff
    (T : ℝ) (Q J R : Finset Lattice) (M K L : ℕ)
    (v : Fin (M+1) → Lattice) (Sigma : J → Finset Lattice)
    (hQ : ∀ z ∈ Q, z ∈ R) (hJ : ∀ z ∈ J, z ∈ R)
    (hbox : ∀ k z, z ∈ Set.Icc (v k) (v k+((L:ℤ),(L:ℤ))) → z ∈ R)
    (hSigma : ∀ u, Sigma u ⊆ Q) (ω : Environment) :
    let N := Finset.univ.image v
    let pairFailure : Set Environment := ⋃ uv ∈
      (Q.product Q).filter (fun uv => uv.1 ≠ uv.2 ∧
        |(uv.1.1 : ℝ)-(uv.2.1 : ℝ)|+|(uv.1.2 : ℝ)-(uv.2.2 : ℝ)| ≤ 2),
      {ω : Environment | ω uv.1 < -T ∧ ω uv.2 < -T}
    let boxSafe : Set Environment := {ω : Environment | ∀ z ∈
      J ∪ N.biUnion (fun w : Lattice =>
        Finset.Icc w.1 (w.1+(L:ℤ)) ×ˢ Finset.Icc w.2 (w.2+(L:ℤ))), -T ≤ ω z}
    let countFailure : Set Environment := {ω : Environment | ∃ u ∈ J.attach,
      K ≤ ((Sigma u).filter (fun z => ω z < -T)).card}
    let G := pairFailureᶜ ∩ boxSafe ∩ countFailureᶜ
    let mask := fun z : R => if ω z.val < -T then true else false
    let V := {z : Lattice | ∃ hz : z ∈ R, mask ⟨z,hz⟩=true}
    ω ∈ G ↔
      (∀ z ∈ Q, ∀ w ∈ Q, z ∈ V → w ∈ V → z ≠ w →
        ¬ (|(z.1:ℝ)-(w.1:ℝ)|+|(z.2:ℝ)-(w.2:ℝ)| ≤ 2)) ∧
      (∀ z ∈ J, z ∉ V) ∧
      (∀ k z, z ∈ Set.Icc (v k) (v k+((L:ℤ),(L:ℤ))) → z ∉ V) ∧
      (∀ u : J, ((Sigma u).filter (fun z => z ∈ V)).card < K) := by
  classical
  intro N pairFailure boxSafe countFailure G mask V
  have hbit (z : Lattice) (hz : z ∈ R) : z ∈ V ↔ ω z < -T := by
    constructor
    · rintro ⟨_, h⟩
      simpa only [mask, ite_eq_left_iff, Bool.false_eq_true, imp_false, not_not] using h
    · intro h
      exact ⟨hz, by simp only [mask, ite_eq_left h]⟩
  have hpair : ω ∈ pairFailureᶜ ↔
      ∀ z ∈ Q, ∀ w ∈ Q, z ∈ V → w ∈ V → z ≠ w →
        ¬ (|(z.1:ℝ)-(w.1:ℝ)|+|(z.2:ℝ)-(w.2:ℝ)| ≤ 2) := by
    simp only [pairFailure, mem_compl_iff, mem_iUnion, mem_ofPred_eq,
      Finset.mem_filter]
    constructor
    · intro h z hz w hw hzbad hwbad hne hclose
      exact h ⟨(z,w), ⟨⟨Finset.mem_product.mpr ⟨hz,hw⟩,hne,hclose⟩,
        (hbit z (hQ z hz)).mp hzbad, (hbit w (hQ w hw)).mp hwbad⟩⟩
    · rintro h ⟨⟨z,w⟩, ⟨⟨hzw,hne,hclose⟩,hzbad,hwbad⟩⟩
      obtain ⟨hz,hw⟩ := Finset.mem_product.mp hzw
      exact h z hz w hw ((hbit z (hQ z hz)).mpr hzbad)
        ((hbit w (hQ w hw)).mpr hwbad) hne hclose
  have hboxmem (z : Lattice) : z ∈ N.biUnion (fun w : Lattice =>
      Finset.Icc w.1 (w.1+(L:ℤ)) ×ˢ Finset.Icc w.2 (w.2+(L:ℤ))) ↔
      ∃ k, z ∈ Set.Icc (v k) (v k+((L:ℤ),(L:ℤ))) := by
    simp only [Finset.mem_biUnion, N, Finset.mem_image, Finset.mem_univ,
      true_and, Finset.mem_product, Finset.mem_Icc, Prod.fst_add, Prod.snd_add,
      Set.mem_Icc, Prod.le_def]
    aesop
  have hsafe : ω ∈ boxSafe ↔ (∀ z ∈ J, z ∉ V) ∧
      (∀ k z, z ∈ Set.Icc (v k) (v k+((L:ℤ),(L:ℤ))) → z ∉ V) := by
    change (∀ z ∈ J ∪ _, -T ≤ ω z) ↔ _
    simp only [Finset.mem_union, hboxmem]
    constructor
    · intro h
      exact ⟨fun z hz hv => (not_lt.mpr (h z (Or.inl hz))) ((hbit z (hJ z hz)).mp hv),
        fun k z hz hv => (not_lt.mpr (h z (Or.inr ⟨k,hz⟩)))
          ((hbit z (hbox k z hz)).mp hv)⟩
    · rintro ⟨h₁,h₂⟩ z (hz | ⟨k,hz⟩)
      · exact not_lt.mp (fun h => h₁ z hz ((hbit z (hJ z hz)).mpr h))
      · exact not_lt.mp (fun h => h₂ k z hz ((hbit z (hbox k z hz)).mpr h))
  have hfilters (u : J) : (Sigma u).filter (fun z => ω z < -T) =
      (Sigma u).filter (fun z => z ∈ V) := by
    apply Finset.filter_congr
    intro z hz
    exact (hbit z (hQ z (hSigma u hz))).symm
  have hcount : ω ∈ countFailureᶜ ↔
      ∀ u : J, ((Sigma u).filter (fun z => z ∈ V)).card < K := by
    simp only [countFailure, mem_compl_iff, mem_ofPred_eq, hfilters,
      not_exists, Finset.mem_attach, true_and, not_le]
  change (ω ∈ pairFailureᶜ ∧ ω ∈ boxSafe) ∧ ω ∈ countFailureᶜ ↔ _
  rw [hpair, hsafe, hcount]
  tauto

end LPPDifferentiability
end
