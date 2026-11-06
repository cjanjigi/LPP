/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Differentiability.Probability.ForwardHeavyAttachmentFamilyWeights
public import Differentiability.Probability.ForwardHeavyAttachmentMaskEvents

/-!
# Forward attachment probabilities

For the forward attachments of Lemma B.3 of the differentiability preprint,
choose one net and one family of paths. Intersect the geometric good event
with the event that every path in that family has enough weight.

## References

- C. Janjigian, F. Rassoul-Agha and T. Seppäläinen,
  *Differentiability of the shape function in the planar corner growth model*, preprint.
-/

public section
open MeasureTheory Set
open scoped Classical ENNReal
namespace LPPDifferentiability

/-- Construct a single actual common net and family, and intersect the literal
source good event with the complement of that same family's weight failure. -/
theorem exists_forward_heavy_attachment_probability
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
    ∃ (J : Finset Lattice) (M : ℕ) (v : Fin (M+1) → Lattice)
      (Q R : Finset Lattice) (j : J → Fin (M+1)) (d : J → ℕ × ℕ),
      (∀ u, u ∈ J ↔ u.1+u.2=I ∧ rho u ∈ Set.Icc lo hi) ∧
      (J.card:ℝ) ≤ D*s+1 ∧
      1 ≤ M ∧ Function.Injective v ∧
      (∀ k, (v k).1+(v k).2=I+(m:ℤ) ∧
        rho (v k) ∈ Set.Icc (lo-a*(m:ℝ)) (hi+(1-a)*(m:ℝ))) ∧
      (∀ (k : ℕ) (hk : k < M),
        min a (1-a)*(m:ℝ)/4 ≤ rho (v ⟨k+1, by omega⟩)-rho (v ⟨k, by omega⟩) ∧
        rho (v ⟨k+1, by omega⟩)-rho (v ⟨k, by omega⟩) ≤ min a (1-a)*(m:ℝ)/2) ∧
      (∀ k, (rho (v k) ≤ lo-a*(m:ℝ)+min a (1-a)*(m:ℝ)/2) ↔ k.val=0) ∧
      (∀ k, (hi+(1-a)*(m:ℝ)-min a (1-a)*(m:ℝ)/2 ≤ rho (v k)) ↔ k.val=M) ∧
      rho (v ⟨0, by omega⟩) ≤ lo-a*(m:ℝ)+min a (1-a)*(m:ℝ)/2 ∧
      hi+(1-a)*(m:ℝ)-min a (1-a)*(m:ℝ)/2 ≤ rho (v ⟨M, by omega⟩) ∧
      (M+1:ℝ) < 4*(hi-lo+(m:ℝ))/(min a (1-a)*(m:ℝ)) ∧
      (M+1:ℝ) ≤ 8*D/(min a (1-a)*kappa)+2 ∧
      (∀ z, z ∈ Q ↔ I ≤ z.1+z.2 ∧ z.1+z.2 ≤ I+(m:ℤ) ∧
        lo-(m:ℝ)-(K:ℝ)-2 ≤ rho z ∧ rho z ≤ hi+(m:ℝ)+(K:ℝ)+2) ∧
      (Q.card:ℝ) ≤ 4*D*s^2 ∧
      (∀ z, z ∈ R ↔ z ∈ Q ∨ z ∈ J ∨
        ∃ k, z ∈ Set.Icc (v k-((L:ℤ),(L:ℤ))) (v k)) ∧
      (∀ u, (d u).1+(d u).2=m ∧ u.val+(((d u).1:ℤ),((d u).2:ℤ))=v (j u) ∧
        ((d u).1:ℝ)/(m:ℝ) ∈ Set.Icc (1/4) (3/4) ∧ |rho (v (j u)-u.val)| ≤ (m:ℝ)) ∧
      (∀ u : J, ((Q.filter (fun z => |rho z-(rho u.val+
        ((z.1+z.2-I:ℤ):ℝ)*((1-a)*((d u).1:ℝ)-a*((d u).2:ℝ))/(m:ℝ))| ≤
          (K:ℝ)+2)).card:ℝ) ≤ (2*(K:ℝ)+5)*((m+1:ℕ):ℝ)) ∧
      ∃ (hrect : ∀ (u : J) z, z ∈ Set.Icc u.val
          (u.val+(((d u).1:ℤ),((d u).2:ℤ))) → z ∈ R)
        (hbox : ∀ (u : J) z, z ∈ Set.Icc
          (u.val+(((d u).1:ℤ),((d u).2:ℤ))-((L:ℤ),(L:ℤ)))
          (u.val+(((d u).1:ℤ),((d u).2:ℤ))) → z ∈ R),
      let V := fun mask : R → Bool => {z : Lattice | ∃ hz : z ∈ R, mask ⟨z,hz⟩=true}
      let active := fun (mask : R → Bool) (u : J) =>
        u.val ∉ V mask ∧
        (∀ z ∈ Set.Icc u.val (u.val+(((d u).1:ℤ),((d u).2:ℤ))),
          ∀ w ∈ Set.Icc u.val (u.val+(((d u).1:ℤ),((d u).2:ℤ))),
          z ∈ V mask → w ∈ V mask → z ≠ w →
          ¬ (|(z.1:ℝ)-(w.1:ℝ)|+|(z.2:ℝ)-(w.2:ℝ)| ≤ 2)) ∧
        (∀ z (hz : z ∈ Set.Icc
          (u.val+(((d u).1:ℤ),((d u).2:ℤ))-((L:ℤ),(L:ℤ)))
          (u.val+(((d u).1:ℤ),((d u).2:ℤ)))), mask ⟨z,hbox u z hz⟩=false) ∧
        ((Finset.Icc u.val (u.val+(((d u).1:ℤ),((d u).2:ℤ)))).filter
          (fun z => z ∈ V mask ∧
            |(z.1:ℝ)-(u.val.1:ℝ)-((z.1+z.2-(u.val.1+u.val.2):ℤ):ℝ)*
              (((d u).1:ℝ)/((d u).1+(d u).2:ℕ))| ≤ (K:ℝ)+2)).card < K
      let sourceGood := fun mask : R → Bool =>
        (∀ z ∈ Q, ∀ w ∈ Q, z ∈ V mask → w ∈ V mask → z ≠ w →
          ¬ (|(z.1:ℝ)-(w.1:ℝ)|+|(z.2:ℝ)-(w.2:ℝ)| ≤ 2)) ∧
        (∀ z ∈ J, z ∉ V mask) ∧
        (∀ k z, z ∈ Set.Icc (v k-((L:ℤ),(L:ℤ))) (v k) → z ∉ V mask) ∧
        (∀ u : J, ((Q.filter (fun z => |rho z-(rho u.val+
          ((z.1+z.2-I:ℤ):ℝ)*((1-a)*((d u).1:ℝ)-a*((d u).2:ℝ))/(m:ℝ))| ≤
            (K:ℝ)+2)).filter (fun z => z ∈ V mask)).card < K)
      ∃ q : (mask : R → Bool) → (u : J) → Path u.val (d u),
        (∀ mask u, ¬ active mask u → q mask u = horizontalFirst u.val (d u)) ∧
        (∀ mask u i, (q mask u).vertex i ∈ R) ∧
        (∀ mask u, (q mask u).vertex (Fin.last ((d u).1+(d u).2))=v (j u)) ∧
        (∀ mask u, active mask u →
          (∀ (i : ℕ) (hi : i ≤ (d u).1+(d u).2-L),
            (q mask u).vertex ⟨i, by omega⟩ =
              GreedyAttachment.vertex u.val (((d u).1:ℝ)/((d u).1+(d u).2:ℕ)) (V mask) i) ∧
          (∀ i, (q mask u).vertex i ∉ V mask)) ∧
        (∀ mask, sourceGood mask → ∀ u, active mask u ∧
          (∀ i, mask ⟨(q mask u).vertex i, hrect u _ ((q mask u).vertex_mem_Icc i)⟩=false)) ∧
        let Sigma := fun u : J => Q.filter (fun z => |rho z-(rho u.val+
          ((z.1+z.2-I:ℤ):ℝ)*((1-a)*((d u).1:ℝ)-a*((d u).2:ℝ))/(m:ℝ))| ≤ (K:ℝ)+2)
        let N := Finset.univ.image v
        let pairFailure : Set Environment := ⋃ uv ∈
          (Q.product Q).filter (fun uv => uv.1 ≠ uv.2 ∧
            |(uv.1.1:ℝ)-(uv.2.1:ℝ)|+|(uv.1.2:ℝ)-(uv.2.2:ℝ)| ≤ 2),
          {ω : Environment | ω uv.1 < -T ∧ ω uv.2 < -T}
        let boxSafe : Set Environment := {ω : Environment | ∀ z ∈
          J ∪ N.biUnion (fun w : Lattice =>
            Finset.Icc (w.1-(L:ℤ)) w.1 ×ˢ Finset.Icc (w.2-(L:ℤ)) w.2), -T ≤ ω z}
        let countFailure : Set Environment := {ω : Environment | ∃ u ∈ J.attach,
          K ≤ ((Sigma u).filter (fun z => ω z < -T)).card}
        let G := pairFailureᶜ ∩ boxSafe ∩ countFailureᶜ
        let mask := fun ω : Environment => fun z : R => if ω z.val < -T then true else false
        let E := {ω : Environment | ∃ u : J, decide (active (mask ω) u)=true ∧
          pathWeight ω (q (mask ω) u) < -2*C1*(m:ℝ)-(K-1:ℕ)*T-t}
        MeasurableSet G ∧ (∀ ω, ω ∈ G ↔ sourceGood (mask ω)) ∧
        MeasurableSet E ∧ MeasurableSet (G ∩ Eᶜ) ∧
        (environmentLaw μ).real (G ∩ Eᶜ) ≥
          max 0 (1-(48*D*s^2*pT^2 + (D*s+1+B*(((L+1:ℕ):ℝ)^2))*pT +
            (D*s+1)*((((2*K+5)*(m+1):ℕ):ℝ)*pT)^K +
            (D*s+1)*((2*m*Cp*b^(-p))^K+
              Real.exp (-t^2/(2*b*(2*C1*m+t/3)))))) ∧
        (∀ ω, ω ∈ G ∩ Eᶜ → ∀ u : J,
          (q (mask ω) u).vertex (Fin.last ((d u).1+(d u).2))=v (j u) ∧
          (∀ i, -T ≤ ω ((q (mask ω) u).vertex i)) ∧
          pathWeight ω (q (mask ω) u) ≥ -2*C1*(m:ℝ)-(K-1:ℕ)*T-t) := by
  classical
  intro m rho L B pT C1 Cp
  obtain ⟨J, M, v, Q, R, j, d, hJ, hJcard, hM, hinj, hnet, hgap,
    hfirstOnly, hlastOnly, hfirst, hlast, hcard, huniform, hQ, hQcard, hR,
    hd, hSigma, hrect, hbox, q, hinactive, hmem, hend, hgood, hsource,
    hEmeas, hEbound, hweights⟩ :=
    exists_forward_heavy_attachment_family_weight_bound μ T p b t hp hT
      hthreshold hb ht hmoment a D s kappa lo hi I K ha ha1 hD hs hkappa
      hkappaCap hlohi hwidth hspacing hK hcut hboxcut
  refine ⟨J, M, v, Q, R, j, d, hJ, hJcard, hM, hinj, hnet, hgap,
    hfirstOnly, hlastOnly, hfirst, hlast, hcard, huniform, hQ, hQcard, hR,
    hd, hSigma, hrect, hbox, ?_⟩
  intro V active sourceGood
  refine ⟨q, hinactive, hmem, hend, hgood, hsource, ?_⟩
  intro Sigma N pairFailure boxSafe countFailure G mask E
  have hQsub (z : Lattice) (hz : z ∈ Q) : z ∈ R := (hR z).mpr (Or.inl hz)
  have hJsub (z : Lattice) (hz : z ∈ J) : z ∈ R := (hR z).mpr (Or.inr (Or.inl hz))
  have hboxsub (k : Fin (M+1)) (z : Lattice)
      (hz : z ∈ Set.Icc (v k-((L:ℤ),(L:ℤ))) (v k)) : z ∈ R :=
    (hR z).mpr (Or.inr (Or.inr ⟨k,hz⟩))
  have hSigmasub (u : J) : Sigma u ⊆ Q := Finset.filter_subset _ _
  have hequiv (ω : Environment) : ω ∈ G ↔ sourceGood (mask ω) :=
    heavy_attachment_source_event_mask_iff T Q J R M K L v Sigma
      hQsub hJsub hboxsub hSigmasub ω
  have hSigmacap (u : J) : (Sigma u).card ≤ (2*K+5)*(m+1) := by
    have h : ((Sigma u).card:ℝ) ≤ (((2*K+5)*(m+1):ℕ):ℝ) := by
      calc
        _ ≤ (2*(K:ℝ)+5)*((m+1:ℕ):ℝ) := hSigma u
        _ = _ := by push_cast; ring
    exact Nat.cast_le.mp h
  have hNcard : (N.card:ℝ) ≤ B := by
    have hn : N.card = M+1 := by
      change (Finset.univ.image v).card = M+1
      rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
    rw [hn]
    simpa only [B, Nat.cast_add, Nat.cast_one] using huniform
  have hB : 0 ≤ B := by
    have hm : 0 < min a (1-a) := lt_min ha (sub_pos.mpr ha1)
    dsimp only [B]
    positivity
  have hgeom := measureReal_heavy_attachment_event_ge_of_source_caps μ T Q J N
    Sigma K L m D s B hD (by linarith only [hs]) hB hQcard hJcard hNcard hSigmacap
  have hGmeas : MeasurableSet G :=
    (measurable_and_measureReal_heavy_attachment_event_ge μ T Q J N Sigma K L
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
  refine ⟨hend (mask ω) u, ?_, hweights ω hω.2 hsrc u⟩
  intro i
  have hclear := (hsource (mask ω) hsrc u).2 i
  by_contra h
  have hbad : ω ((q (mask ω) u).vertex i) < -T := lt_of_not_ge h
  simp only [mask, ite_eq_left hbad, Bool.true_eq_false] at hclear

end LPPDifferentiability
end
