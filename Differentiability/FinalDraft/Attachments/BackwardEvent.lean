/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Differentiability.FinalDraft.Attachments.Event
public import Differentiability.FinalDraft.Attachments.NetCardinality
import Differentiability.Model.BackwardHeavyAttachmentObservationGeometry
import Differentiability.Model.Paths.BackwardMaskGreedyFamily
import Differentiability.Probability.BackwardHeavyAttachmentMaskEvents
import Mathlib.Tactic

/-! The backward good event for a prescribed net in the proof of Lemma B.3. -/

public section

open MeasureTheory Set
open scoped ENNReal

namespace LPPDifferentiability

/-- Use the supplied lower net to route one attachment per interval site and
apply the geometric and weight failure estimates to this family. -/
theorem exists_backward_prescribed_attachment_event
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (T p b t : ℝ)
    (hp : 1 < p) (hT : 0 < T) (hthreshold : (2 : ℝ≥0∞)⁻¹ ≤ μ (Set.Ici (-T)))
    (hb : 0 < b) (ht : 0 < t)
    (hmoment : (∫⁻ x, ENNReal.ofReal ((max (-x) 0)^p) ∂μ) < ∞)
    (a D s kappa lo hi : ℝ) (I : ℤ) (K M : ℕ) (v : Fin (M + 1) → Lattice)
    (ha : 0 < a) (ha1 : a < 1) (hD : 1 ≤ D) (hs : 4 ≤ s)
    (hkappa : 0 < kappa) (hkappaCap : kappa ≤ 1 / 16)
    (hlohi : lo ≤ hi) (hwidth : hi - lo ≤ D * s)
    (hK : 2 ≤ K) (hcut : 2 * K + 5 ≤ Nat.ceil (kappa * s))
    (hboxcut : 4 * K + 4 ≤ Nat.ceil (kappa * s))
    (hmS : (Nat.ceil (kappa * s) : ℝ) ≤ s) :
    let m := Nat.ceil (kappa * s)
    let B := 8 * D / (min a (1 - a) * kappa) + 2
    IsLevelAttachmentNet a m (I - (m : ℤ)) (lo - (1 - a) * (m : ℝ)) (hi + a * (m : ℝ)) v →
    ∃ A : Set Environment, MeasurableSet A ∧
      max 0 (1 - attachmentFailureBound μ D s B m K T p b t) ≤ (environmentLaw μ).real A ∧
      ∀ ω ∈ A, ∀ u : Lattice, u.1 + u.2 = I → attachmentTransverse a u ∈ Icc lo hi →
        ∃ (j : Fin (M + 1)) (d : ℕ × ℕ), d.1 + d.2 = m ∧
          ∃ q : Path (v j) d, q.vertex (Fin.last (d.1 + d.2)) = u ∧
            -2 * (∫ y, max (-y) 0 ∂μ) * m - (K - 1 : ℕ) * T - t ≤ pathWeight ω q ∧
            |attachmentTransverse a (u - v j)| ≤ (m : ℝ) := by
  classical
  intro m B hnet
  let L := 4 * K + 4
  have hspos : 0 < s := by linarith only [hs]
  have hmR : 0 < (m : ℝ) := (mul_pos hkappa hspos).trans_le (Nat.le_ceil _)
  have hm : 0 < m := Nat.cast_pos.mp hmR
  have hDs : s ≤ D * s := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hD hspos.le
  have htheta : 0 < min a (1 - a) := lt_min ha (sub_pos.mpr ha1)
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  let N := Finset.univ.image v
  have hNcard : (N.card : ℝ) ≤ B :=
    hnet.card_image_le_of_scale ha ha1 hD hspos hkappa
      (by linarith only [hlohi, hmR]) (by linarith only [hwidth, hmS, hDs])
  have hcutR : 2 * (K : ℝ) + 5 ≤ (m : ℝ) := by exact_mod_cast hcut
  obtain ⟨J, Q, R, hJ, hJcard, _, hQcard, hR, hSigma, hgeometry⟩ :=
    exists_backward_heavy_attachment_observation_geometry a D s kappa lo hi I K M v
      ha ha1 hD hs hkappa hkappaCap hlohi hwidth hcutR
  choose j d hd using fun u : J => hnet.exists_backward_middle ha ha1 hm u.val
    ((hJ u.val).mp u.property).1 ((hJ u.val).mp u.property).2
  choose hrect hbox hlocal using fun u : J =>
    hgeometry u.val u.property (d u) (j u) (hd u).1 (hd u).2.1
  have hlen (u : J) : (d u).1 + (d u).2 = m := (hd u).1
  have hstart (u : J) : u.val - (((d u).1 : ℤ), ((d u).2 : ℤ)) = v (j u) := by
    rw [← (hd u).2.1, add_sub_cancel_right]
  obtain ⟨_, q, _, hmem, hgood⟩ := GreedyAttachment.exists_backward_finite_mask_greedy_family
    R (fun u : J => u.val) d K hK (fun u => by rw [hlen]; exact hboxcut)
    (fun u => by simpa only [hlen] using (hd u).2.2.1.1)
    (fun u => by simpa only [hlen] using (hd u).2.2.1.2) hrect hbox
  let Sigma (u : J) := Q.filter (fun z =>
    |attachmentTransverse a z - (attachmentTransverse a u.val +
      ((z.1 + z.2 - I : ℤ) : ℝ) * ((1 - a) * ((d u).1 : ℝ) - a * ((d u).2 : ℝ)) /
        (m : ℝ))| ≤ (K : ℝ) + 2)
  have hSigmacap (u : J) : (Sigma u).card ≤ (2 * K + 5) * (m + 1) := by
    have h : ((Sigma u).card : ℝ) ≤ ((((2 * K + 5) * (m + 1)) : ℕ) : ℝ) := by
      calc
        _ ≤ (2 * (K : ℝ) + 5) * ((m + 1 : ℕ) : ℝ) := hSigma u.val (d u)
        _ = _ := by push_cast; ring
    exact Nat.cast_le.mp h
  let pairFailure : Set Environment := ⋃ uv ∈
    (Q.product Q).filter (fun uv => uv.1 ≠ uv.2 ∧
      |(uv.1.1 : ℝ) - (uv.2.1 : ℝ)| + |(uv.1.2 : ℝ) - (uv.2.2 : ℝ)| ≤ 2),
    {ω : Environment | ω uv.1 < -T ∧ ω uv.2 < -T}
  let boxSafe : Set Environment := {ω : Environment | ∀ z ∈
    J ∪ N.biUnion (fun w : Lattice =>
      Finset.Icc w.1 (w.1 + (L : ℤ)) ×ˢ Finset.Icc w.2 (w.2 + (L : ℤ))), -T ≤ ω z}
  let countFailure : Set Environment := {ω : Environment | ∃ u ∈ J.attach,
    K ≤ ((Sigma u).filter (fun z => ω z < -T)).card}
  let G := pairFailureᶜ ∩ boxSafe ∩ countFailureᶜ
  let mask (ω : Environment) (z : R) := if ω z.val < -T then true else false
  have hG : MeasurableSet G :=
    (measurable_and_measureReal_backward_heavy_attachment_event_ge μ T Q J N Sigma K L
      ((2 * K + 5) * (m + 1)) hSigmacap).1
  have hgeom :=
    measureReal_backward_heavy_attachment_event_ge_of_source_caps μ T Q J N Sigma K m D s B
      hD hspos.le hB hQcard hJcard hNcard hSigmacap
  have hQsub (z : Lattice) (hz : z ∈ Q) : z ∈ R := (hR z).mpr (Or.inl hz)
  have hJsub (z : Lattice) (hz : z ∈ J) : z ∈ R := (hR z).mpr (Or.inr (Or.inl hz))
  have hboxsub (k : Fin (M + 1)) (z : Lattice) (hz : z ∈ Set.Icc (v k) (v k + ((L : ℤ), (L : ℤ)))) :
      z ∈ R := (hR z).mpr (Or.inr (Or.inr ⟨k, hz⟩))
  let V (bits : R → Bool) := {z : Lattice | ∃ hz : z ∈ R, bits ⟨z, hz⟩ = true}
  let good (bits : R → Bool) :=
    (∀ z ∈ Q, ∀ w ∈ Q, z ∈ V bits → w ∈ V bits → z ≠ w →
      ¬ (|(z.1 : ℝ) - (w.1 : ℝ)| + |(z.2 : ℝ) - (w.2 : ℝ)| ≤ 2)) ∧
    (∀ z ∈ J, z ∉ V bits) ∧
    (∀ k z, z ∈ Set.Icc (v k) (v k + ((L : ℤ), (L : ℤ))) → z ∉ V bits) ∧
    (∀ u : J, ((Sigma u).filter (fun z => z ∈ V bits)).card < K)
  have hequiv (ω : Environment) : ω ∈ G ↔ good (mask ω) :=
    backward_heavy_attachment_source_event_mask_iff T Q J R M K L v Sigma
      hQsub hJsub hboxsub (fun _ => Finset.filter_subset _ _) ω
  have hsafe (ω : Environment) (hω : ω ∈ G) (u : J) (i : Fin ((d u).1 + (d u).2 + 1)) :
      -T ≤ ω ((q (mask ω) u).vertex i) := by
    have hsource := (hequiv ω).mp hω
    have haLocal := hlocal u (mask ω) hsource.1 hsource.2.1 hsource.2.2.1 (hsource.2.2.2 u)
    have hnotBad := hgood (mask ω) u haLocal i
    apply le_of_not_gt
    intro hiBad
    exact hnotBad ⟨hmem (mask ω) u i, by simp only [mask, ite_eq_left hiBad]⟩
  let pT := μ.real (Iio (-T))
  let c := 48 * D * s^2 * pT^2 +
    (D * s + 1 + B * ((4 * K + 5 : ℕ) : ℝ)^2) * pT +
    (D * s + 1) * (((((2 * K + 5) * (m + 1) : ℕ) : ℝ) * pT)^K)
  have hc : 1 - c ≤ (environmentLaw μ).real G := by
    exact hgeom
  obtain ⟨A, hA, hprob, hweight⟩ :=
    exists_attachment_weight_event μ T p b t hp hT hthreshold hb ht hmoment J R m K
      (by omega) (fun u => u.val - (((d u).1 : ℤ), ((d u).2 : ℤ))) d q hlen hmem c (D * s + 1)
      hJcard G hG hc good hequiv hsafe
  refine ⟨A, hA, hprob, ?_⟩
  intro ω hω u hu hcoord
  let uJ : J := ⟨u, (hJ u).mpr ⟨hu, hcoord⟩⟩
  refine ⟨j uJ, d uJ, hlen uJ, ?_⟩
  let path := q (mask ω) uJ
  let p : Path (v (j uJ)) (d uJ) := {
    vertex := path.vertex
    start := path.start.trans (hstart uJ)
    finish := by rw [← hstart uJ]; exact path.finish
    step := path.step }
  exact ⟨p, p.finish.trans (hd uJ).2.1, hweight ω hω uJ, (hd uJ).2.2.2⟩

end LPPDifferentiability
