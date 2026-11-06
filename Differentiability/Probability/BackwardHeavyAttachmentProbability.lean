/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Differentiability.Probability.BackwardHeavyAttachmentFamilyWeights
public import Differentiability.Probability.BackwardHeavyAttachmentMaskEvents
public import Differentiability.Probability.ForwardHeavyAttachmentMaskEvents

/-!
# Backward attachment probabilities

For the backward attachments of Lemma B.3 of the differentiability preprint,
choose one lower net and one family of paths. Intersect the geometric good
event with the event that every path in that family has enough weight.

## References

- C. Janjigian, F. Rassoul-Agha and T. Seppäläinen,
  *Differentiability of the shape function in the planar corner growth model*, preprint.
-/

public section
open MeasureTheory
open scoped Classical ENNReal
namespace LPPDifferentiability

/-- Construct one common lower net and backward family, and intersect the literal
source good event with the complement of that same family's weight failure. -/
theorem exists_backward_heavy_attachment_probability
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (T p b t : ℝ)
    (hp : 1 < p) (hT : 0 < T)
    (hthreshold : (2 : ℝ≥0∞)⁻¹ ≤ μ (Set.Ici (-T))) (hb : 0 < b) (ht : 0 < t)
    (hmoment : (∫⁻ x, ENNReal.ofReal ((max (-x) 0)^p) ∂μ) < ∞)
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
    let B := 8*D/(min a (1-a)*kappa)+2
    let pT := μ.real (Set.Iio (-T))
    let C1 := ∫ y, max (-y) 0 ∂μ
    let Cp := ∫ y, (max (-y) 0)^p ∂μ
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
          (∀ i, mask ⟨(qback mask u).vertex i, hmem mask u i⟩=false)) ∧
        let Sigma := fun u : J => Q.filter (fun z => |rho z-(rho u.val+
          ((z.1+z.2-I:ℤ):ℝ)*((1-a)*((d u).1:ℝ)-a*((d u).2:ℝ))/(m:ℝ))| ≤ (K:ℝ)+2)
        let N := Finset.univ.image w
        let pairFailure : Set Environment := ⋃ uv ∈
          (Q.product Q).filter (fun uv => uv.1 ≠ uv.2 ∧
            |(uv.1.1:ℝ)-(uv.2.1:ℝ)|+|(uv.1.2:ℝ)-(uv.2.2:ℝ)| ≤ 2),
          {ω : Environment | ω uv.1 < -T ∧ ω uv.2 < -T}
        let boxSafe : Set Environment := {ω : Environment | ∀ z ∈
          J ∪ N.biUnion (fun w : Lattice =>
            Finset.Icc w.1 (w.1+(L:ℤ)) ×ˢ Finset.Icc w.2 (w.2+(L:ℤ))), -T ≤ ω z}
        let countFailure : Set Environment := {ω : Environment | ∃ u ∈ J.attach,
          K ≤ ((Sigma u).filter (fun z => ω z < -T)).card}
        let G := pairFailureᶜ ∩ boxSafe ∩ countFailureᶜ
        let mask := fun ω : Environment => fun z : R => if ω z.val < -T then true else false
        let E := {ω : Environment | ∃ u : J, decide (active (mask ω) u)=true ∧
          pathWeight ω (qback (mask ω) u) < -2*C1*(m:ℝ)-(K-1:ℕ)*T-t}
        MeasurableSet G ∧ (∀ ω, ω ∈ G ↔ sourceGood (mask ω)) ∧
        MeasurableSet E ∧ MeasurableSet (G ∩ Eᶜ) ∧
        (environmentLaw μ).real (G ∩ Eᶜ) ≥
          max 0 (1-(48*D*s^2*pT^2 + (D*s+1+B*(((L+1:ℕ):ℝ)^2))*pT +
            (D*s+1)*((((2*K+5)*(m+1):ℕ):ℝ)*pT)^K +
            (D*s+1)*((2*m*Cp*b^(-p))^K+
              Real.exp (-t^2/(2*b*(2*C1*m+t/3)))))) ∧
        (∀ ω, ω ∈ G ∩ Eᶜ → ∀ u : J,
          (qback (mask ω) u).vertex 0=w (j u) ∧
          (qback (mask ω) u).vertex (Fin.last ((d u).1+(d u).2))=u.val ∧
          (∀ i, -T ≤ ω ((qback (mask ω) u).vertex i)) ∧
          pathWeight ω (qback (mask ω) u) ≥ -2*C1*(m:ℝ)-(K-1:ℕ)*T-t) := by
  classical
  intro m rho L B pT C1 Cp
  obtain ⟨J, M, w, Q, R, j, d, hJ, hJcard, hM, hinj, hnet, hgap,
    hfirstOnly, hlastOnly, hfirst, hlast, hcard, huniform, hQ, hQcard, hR,
    hd, hSigma, hrect, hbox, hstart, qforward, qback, hreverse, hmem,
    hend, hgood, hsource, hEmeas, hEbound, hweights⟩ :=
    exists_backward_heavy_attachment_family_weight_bound μ T p b t hp hT
      hthreshold hb ht hmoment a D s kappa lo hi I K ha ha1 hD hs hkappa
      hkappaCap hlohi hwidth hspacing hK hcut hboxcut
  refine ⟨J, M, w, Q, R, j, d, hJ, hJcard, hM, hinj, hnet, hgap,
    hfirstOnly, hlastOnly, hfirst, hlast, hcard, huniform, hQ, hQcard, hR,
    hd, hSigma, hrect, hbox, ?_⟩
  intro V active sourceGood
  refine ⟨hstart, qforward, qback, hreverse, hmem, hend, hgood, hsource, ?_⟩
  intro Sigma N pairFailure boxSafe countFailure G mask E
  have hQsub (z : Lattice) (hz : z ∈ Q) : z ∈ R := (hR z).mpr (Or.inl hz)
  have hJsub (z : Lattice) (hz : z ∈ J) : z ∈ R := (hR z).mpr (Or.inr (Or.inl hz))
  have hboxsub (k : Fin (M+1)) (z : Lattice)
      (hz : z ∈ Set.Icc (w k) (w k+((L:ℤ),(L:ℤ)))) : z ∈ R :=
    (hR z).mpr (Or.inr (Or.inr ⟨k,hz⟩))
  have hSigmasub (u : J) : Sigma u ⊆ Q := Finset.filter_subset _ _
  have hequiv (ω : Environment) : ω ∈ G ↔ sourceGood (mask ω) :=
    backward_heavy_attachment_source_event_mask_iff T Q J R M K L w Sigma
      hQsub hJsub hboxsub hSigmasub ω
  have hSigmacap (u : J) : (Sigma u).card ≤ (2*K+5)*(m+1) := by
    have h : ((Sigma u).card:ℝ) ≤ (((2*K+5)*(m+1):ℕ):ℝ) := by
      calc
        _ ≤ (2*(K:ℝ)+5)*((m+1:ℕ):ℝ) := hSigma u
        _ = _ := by push_cast; ring
    exact Nat.cast_le.mp h
  have hNcard : (N.card:ℝ) ≤ B := by
    have hn : N.card = M+1 := by
      change (Finset.univ.image w).card = M+1
      rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
    rw [hn]
    simpa only [B, Nat.cast_add, Nat.cast_one] using huniform
  have hB : 0 ≤ B := by
    have hm : 0 < min a (1-a) := lt_min ha (sub_pos.mpr ha1)
    dsimp only [B]
    positivity
  have hgeom : 1-(48*D*s^2*pT^2+(D*s+1+B*(((L+1:ℕ):ℝ)^2))*pT+
      (D*s+1)*((((2*K+5)*(m+1):ℕ):ℝ)*pT)^K) ≤ (environmentLaw μ).real G := by
    have h := measureReal_backward_heavy_attachment_event_ge_of_source_caps μ T Q J N
      Sigma K m D s B hD (by linarith only [hs]) hB hQcard hJcard hNcard hSigmacap
    simpa only [L, Nat.add_assoc] using h
  have hGmeas : MeasurableSet G :=
    (measurable_and_measureReal_backward_heavy_attachment_event_ge μ T Q J N Sigma K L
      ((2*K+5)*(m+1)) hSigmacap).1
  have hweight : (environmentLaw μ).real E ≤
      (D*s+1)*((2*m*Cp*b^(-p))^K+Real.exp (-t^2/(2*b*(2*C1*m+t/3)))) := by
    apply hEbound.trans
    apply mul_le_mul_of_nonneg_right hJcard
    exact add_nonneg (pow_nonneg (by positivity) _) (Real.exp_nonneg _)
  have hjoint := measureReal_inter_compl_ge_max_zero μ G E hGmeas hEmeas
    (48*D*s^2*pT^2+(D*s+1+B*(((L+1:ℕ):ℝ)^2))*pT+
      (D*s+1)*((((2*K+5)*(m+1):ℕ):ℝ)*pT)^K)
    ((D*s+1)*((2*m*Cp*b^(-p))^K+Real.exp (-t^2/(2*b*(2*C1*m+t/3)))))
    hgeom hweight
  refine ⟨hGmeas, hequiv, hEmeas, hjoint.1, hjoint.2, ?_⟩
  intro ω hω u
  have hsrc := (hequiv ω).mp hω.1
  refine ⟨(qback (mask ω) u).start, hend (mask ω) u, ?_, hweights ω hω.2 hsrc u⟩
  intro i
  have hclear := (hsource (mask ω) hsrc u).2 i
  by_contra h
  have hbad : ω ((qback (mask ω) u).vertex i) < -T := lt_of_not_ge h
  simp only [mask, ite_eq_left hbad, Bool.true_eq_false] at hclear

end LPPDifferentiability
end
