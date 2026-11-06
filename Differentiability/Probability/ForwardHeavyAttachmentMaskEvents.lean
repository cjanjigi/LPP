/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Differentiability.Probability.HeavyAttachmentSourceEvents

/-!
# Geometric failure events and their finite observations

This file shows that the geometric good event, described with the full environment, is the same
event as the one described by the finite observation of the environment on the relevant sites.
It also combines the geometric bound with the bound on the weight failure event.
-/

public section
open MeasureTheory Set
namespace LPPDifferentiability

/-- The good event is exactly the event described by the observed mask, including the sites of the
endpoint boxes outside `Q`. -/
theorem heavy_attachment_source_event_mask_iff
    (T : ℝ) (Q J R : Finset Lattice) (M K L : ℕ)
    (v : Fin (M+1) → Lattice) (Sigma : J → Finset Lattice)
    (hQ : ∀ z ∈ Q, z ∈ R) (hJ : ∀ z ∈ J, z ∈ R)
    (hbox : ∀ k z, z ∈ Set.Icc (v k-((L:ℤ),(L:ℤ))) (v k) → z ∈ R)
    (hSigma : ∀ u, Sigma u ⊆ Q) (ω : Environment) :
    let N := Finset.univ.image v
    let pairFailure : Set Environment := ⋃ uv ∈
      (Q.product Q).filter (fun uv => uv.1 ≠ uv.2 ∧
        |(uv.1.1 : ℝ)-(uv.2.1 : ℝ)|+|(uv.1.2 : ℝ)-(uv.2.2 : ℝ)| ≤ 2),
      {ω : Environment | ω uv.1 < -T ∧ ω uv.2 < -T}
    let boxSafe : Set Environment := {ω : Environment | ∀ z ∈
      J ∪ N.biUnion (fun w : Lattice =>
        Finset.Icc (w.1-(L:ℤ)) w.1 ×ˢ Finset.Icc (w.2-(L:ℤ)) w.2), -T ≤ ω z}
    let countFailure : Set Environment := {ω : Environment | ∃ u ∈ J.attach,
      K ≤ ((Sigma u).filter (fun z => ω z < -T)).card}
    let G := pairFailureᶜ ∩ boxSafe ∩ countFailureᶜ
    let mask := fun z : R => if ω z.val < -T then true else false
    let V := {z : Lattice | ∃ hz : z ∈ R, mask ⟨z,hz⟩=true}
    ω ∈ G ↔
      (∀ z ∈ Q, ∀ w ∈ Q, z ∈ V → w ∈ V → z ≠ w →
        ¬ (|(z.1:ℝ)-(w.1:ℝ)|+|(z.2:ℝ)-(w.2:ℝ)| ≤ 2)) ∧
      (∀ z ∈ J, z ∉ V) ∧
      (∀ k z, z ∈ Set.Icc (v k-((L:ℤ),(L:ℤ))) (v k) → z ∉ V) ∧
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
      Finset.Icc (w.1-(L:ℤ)) w.1 ×ˢ Finset.Icc (w.2-(L:ℤ)) w.2) ↔
      ∃ k, z ∈ Set.Icc (v k-((L:ℤ),(L:ℤ))) (v k) := by
    simp only [Finset.mem_biUnion, N, Finset.mem_image, Finset.mem_univ,
      true_and, Finset.mem_product, Finset.mem_Icc, Prod.fst_sub, Prod.snd_sub,
      Set.mem_Icc, Prod.le_def]
    aesop
  have hsafe : ω ∈ boxSafe ↔ (∀ z ∈ J, z ∉ V) ∧
      (∀ k z, z ∈ Set.Icc (v k-((L:ℤ),(L:ℤ))) (v k) → z ∉ V) := by
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

/-- If `G` has probability at least `1 - c` and `E` has probability at most `w`, then `G` minus `E`
is measurable and has probability at least `max 0 (1 - (c + w))`. -/
theorem measureReal_inter_compl_ge_max_zero
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (G E : Set Environment)
    (hG : MeasurableSet G) (hE : MeasurableSet E) (c w : ℝ)
    (hgeom : 1-c ≤ (environmentLaw μ).real G)
    (hweight : (environmentLaw μ).real E ≤ w) :
    MeasurableSet (G ∩ Eᶜ) ∧
      max 0 (1-(c+w)) ≤ (environmentLaw μ).real (G ∩ Eᶜ) := by
  have hmeas := hG.inter hE.compl
  refine ⟨hmeas, max_le measureReal_nonneg ?_⟩
  have hsub : G ⊆ (G ∩ Eᶜ) ∪ E := by
    intro ω hω
    by_cases h : ω ∈ E
    · exact Or.inr h
    · exact Or.inl ⟨hω,h⟩
  have hbound := (measureReal_mono (μ := environmentLaw μ) hsub).trans (measureReal_union_le (G ∩ Eᶜ) E)
  linarith only [hgeom, hweight, hbound]

end LPPDifferentiability
end
