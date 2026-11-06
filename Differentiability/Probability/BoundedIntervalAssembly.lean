/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Differentiability.Model.LevelIntervalAttachments
public import Differentiability.Model.Paths.AttachmentTube
public import LPP_Foundations.Model.Paths.WeightConcat
public import Differentiability.Analysis.AttachmentShapeComparison
public import Differentiability.Analysis.AttachmentNetCardinality
public import Differentiability.Probability.IntervalNetProbability
import Mathlib.Tactic

/-!
# Weight and tube bounds for an assembled path

Concatenate the initial attachment, central path and final attachment in
the proof of Lemma 3.2 of the differentiability preprint. The same path
satisfies both the weight estimate and the bound on its distance from the
line segment between the endpoints.

## References

- C. Janjigian, F. Rassoul-Agha and T. Seppäläinen,
  *Differentiability of the shape function in the planar corner growth model*, preprint.
-/
public section
open MeasureTheory Set
open scoped NNReal
namespace LPPDifferentiability

/-- Reindex an actual finishing path by the canonical natural displacement,
retaining its weight and every vertex property. -/
theorem exists_canonical_path_of_finish (ω : Environment) (u v : Lattice)
    (d : ℕ × ℕ) (p : Path u d) (hf : p.vertex (Fin.last (d.1+d.2))=v)
    (b : ℝ) (R : Lattice → Prop) (hb : b≤pathWeight ω p)
    (hR : ∀ i, R (p.vertex i)) :
    ∃ q : Path u ((v.1-u.1).toNat,(v.2-u.2).toNat),
      q.vertex (Fin.last ((v.1-u.1).toNat+(v.2-u.2).toNat))=v ∧
      b≤pathWeight ω q ∧ ∀ i, R (q.vertex i) := by
  have hfinish := p.finish.symm.trans hf
  have h1 : (d.1:ℤ)=v.1-u.1 := by
    have h := congrArg Prod.fst hfinish
    simp only [Prod.fst_add] at h
    omega
  have h2 : (d.2:ℤ)=v.2-u.2 := by
    have h := congrArg Prod.snd hfinish
    simp only [Prod.snd_add] at h
    omega
  have hd : d=((v.1-u.1).toNat,(v.2-u.2).toNat) := by
    ext <;> simp only [← h1,← h2,Int.toNat_natCast]
  subst d
  exact ⟨p,hf,hb,hR⟩

/-- The three source pieces yield one actual path with both claimed estimates.
All weight bounds refer to this same random environment. -/
theorem exists_joined_bounded_interval_path
    (ω : Environment) (u uHat vHat v : Lattice) (d₁ d₂ d₃ : ℕ × ℕ) (m : ℕ)
    (p : Path u d₁) (q : Path uHat d₂) (r : Path vHat d₃)
    (hU : uHat=u+((d₁.1:ℤ),(d₁.2:ℤ)))
    (hVHat : vHat=uHat+((d₂.1:ℤ),(d₂.2:ℤ)))
    (hV : v=vHat+((d₃.1:ℤ),(d₃.2:ℤ)))
    (hpLen : d₁.1+d₁.2=m) (hrLen : d₃.1+d₃.2=m)
    (L mean original middle η δ s : ℝ)
    (hloss : 2*(m:ℝ)*(L+|mean|)≤η*s/4)
    (hshape : original-2*L*(m:ℝ)≤middle)
    (hp : (m:ℝ)*mean-η*s/4≤pathWeight ω p)
    (hq : middle-η*s/4≤pathWeight ω q)
    (hr : (m:ℝ)*mean-η*s/4≤pathWeight ω r)
    (hmTube : (m:ℝ)≤δ*s/2)
    (hqTube : ∀ i, ∃ t : ℝ, 0≤t ∧ t≤1 ∧
      |((q.vertex i).1:ℝ)-((1-t)*(uHat.1:ℝ)+t*(vHat.1:ℝ))|+
      |((q.vertex i).2:ℝ)-((1-t)*(uHat.2:ℝ)+t*(vHat.2:ℝ))|≤δ*s/2) :
    ∃ joined : Path u ((v.1-u.1).toNat,(v.2-u.2).toNat),
      joined.vertex (Fin.last ((v.1-u.1).toNat+(v.2-u.2).toNat))=v ∧
      original-η*s≤pathWeight ω joined ∧ ∀ i, ∃ t : ℝ, 0≤t ∧ t≤1 ∧
        |((joined.vertex i).1:ℝ)-((1-t)*(u.1:ℝ)+t*(v.1:ℝ))|+
        |((joined.vertex i).2:ℝ)-((1-t)*(u.2:ℝ)+t*(v.2:ℝ))|≤δ*s := by
  subst uHat
  subst vHat
  subst v
  let joined := p.concat (q.concat r)
  have hgeometry := concat_three_attachments_within_tube _ _ _ _ d₁ d₂ d₃ m
    p q r rfl rfl rfl hpLen hrLen δ s hmTube hqTube
  have hweight : original-η*s≤pathWeight ω joined := by
    dsimp only [joined]
    rw [pathWeight_concat,pathWeight_concat]
    have hmean : -(m:ℝ)*|mean|≤(m:ℝ)*mean := by
      have h := mul_le_mul_of_nonneg_left (neg_abs_le mean) (Nat.cast_nonneg m)
      nlinarith only [h]
    nlinarith only [hloss,hshape,hp,hq,hr,hmean]
  exact exists_canonical_path_of_finish ω _ _ _ joined hgeometry.2 _
    (fun z : Lattice => ∃ t : ℝ, 0≤t ∧ t≤1 ∧
      |(z.1:ℝ)-((1-t)*(u.1:ℝ)+t*((u+((d₁.1:ℤ),(d₁.2:ℤ))+
        ((d₂.1:ℤ),(d₂.2:ℤ))+((d₃.1:ℤ),(d₃.2:ℤ))).1:ℝ))|+
      |(z.2:ℝ)-((1-t)*(u.2:ℝ)+t*((u+((d₁.1:ℤ),(d₁.2:ℤ))+
        ((d₂.1:ℤ),(d₂.2:ℤ))+((d₃.1:ℤ),(d₃.2:ℤ))).2:ℝ))|≤δ*s)
    hweight hgeometry.1

/-- The final all-endpoint event is measurable, including empty intervals. -/
theorem measurableSet_all_interval_paths (g : Quadrant → ℝ)
    (a η δ s lo hi lo' hi' : ℝ) (I J : ℤ) :
    MeasurableSet {ω : Environment | ∀ u v : Lattice,
      (u.1+u.2=I ∧ (1-a)*(u.1:ℝ)-a*(u.2:ℝ) ∈ Icc lo hi) →
      (v.1+v.2=J ∧ (1-a)*(v.1:ℝ)-a*(v.2:ℝ) ∈ Icc lo' hi') →
      ∃ q : Path u ((v.1-u.1).toNat,(v.2-u.2).toNat),
        q.vertex (Fin.last ((v.1-u.1).toNat+(v.2-u.2).toNat))=v ∧
        g (((v.1-u.1).toNat:ℝ≥0),((v.2-u.2).toNat:ℝ≥0))-η*s≤pathWeight ω q ∧
        ∀ i, ∃ t : ℝ, 0≤t ∧ t≤1 ∧
          |((q.vertex i).1:ℝ)-((1-t)*(u.1:ℝ)+t*(v.1:ℝ))|+
          |((q.vertex i).2:ℝ)-((1-t)*(u.2:ℝ)+t*(v.2:ℝ))|≤δ*s} := by
  classical
  rw [ofPred_forall]
  apply MeasurableSet.iInter fun u => ?_
  rw [ofPred_forall]
  apply MeasurableSet.iInter fun v => ?_
  by_cases hU : u.1+u.2=I ∧ (1-a)*(u.1:ℝ)-a*(u.2:ℝ) ∈ Icc lo hi
  · by_cases hV : v.1+v.2=J ∧ (1-a)*(v.1:ℝ)-a*(v.2:ℝ) ∈ Icc lo' hi'
    · simp only [hU,hV,and_self,true_implies]
      let d : ℕ × ℕ := ((v.1-u.1).toNat,(v.2-u.2).toNat)
      by_cases hfinish : u+((d.1:ℤ),(d.2:ℤ))=v
      · have heq : {ω : Environment | ∃ q : Path u d,
            q.vertex (Fin.last (d.1+d.2))=v ∧
            g ((d.1:ℝ≥0),(d.2:ℝ≥0))-η*s≤pathWeight ω q ∧
            ∀ i, ∃ t : ℝ, 0≤t ∧ t≤1 ∧
              |((q.vertex i).1:ℝ)-((1-t)*(u.1:ℝ)+t*(v.1:ℝ))|+
              |((q.vertex i).2:ℝ)-((1-t)*(u.2:ℝ)+t*(v.2:ℝ))|≤δ*s} =
          {ω : Environment | ∃ q : Path u d,
            g ((d.1:ℝ≥0),(d.2:ℝ≥0))-η*s≤pathWeight ω q ∧
            ∀ i, ∃ t : ℝ, 0≤t ∧ t≤1 ∧
              |((q.vertex i).1:ℝ)-((1-t)*(u.1:ℝ)+t*(v.1:ℝ))|+
              |((q.vertex i).2:ℝ)-((1-t)*(u.2:ℝ)+t*(v.2:ℝ))|≤δ*s} := by
          ext ω
          constructor
          · rintro ⟨q,_,hw,ht⟩; exact ⟨q,hw,ht⟩
          · rintro ⟨q,hw,ht⟩; exact ⟨q,q.finish.trans hfinish,hw,ht⟩
        change MeasurableSet {ω : Environment | ∃ q : Path u d, _}
        rw [heq]
        exact measurableSet_exists_path_weight_property u d
          (g ((d.1:ℝ≥0),(d.2:ℝ≥0))-η*s)
          (fun z : Lattice => ∃ t : ℝ, 0≤t ∧ t≤1 ∧
            |(z.1:ℝ)-((1-t)*(u.1:ℝ)+t*(v.1:ℝ))|+
            |(z.2:ℝ)-((1-t)*(u.2:ℝ)+t*(v.2:ℝ))|≤δ*s)
      · have he : {ω : Environment | ∃ q : Path u d,
            q.vertex (Fin.last (d.1+d.2))=v ∧
            g ((d.1:ℝ≥0),(d.2:ℝ≥0))-η*s≤pathWeight ω q ∧
            ∀ i, ∃ t : ℝ, 0≤t ∧ t≤1 ∧
              |((q.vertex i).1:ℝ)-((1-t)*(u.1:ℝ)+t*(v.1:ℝ))|+
              |((q.vertex i).2:ℝ)-((1-t)*(u.2:ℝ)+t*(v.2:ℝ))|≤δ*s} = ∅ := by
          ext ω
          simp only [mem_ofPred_eq,mem_empty_iff_false,iff_false,not_exists]
          intro q hq
          exact hfinish (q.finish.symm.trans hq.1)
        change MeasurableSet {ω : Environment | ∃ q : Path u d, _}
        rw [he]
        exact MeasurableSet.empty
    · simp only [hV,false_implies,implies_true]
      exact MeasurableSet.univ
  · simp only [hU,false_implies]
    exact MeasurableSet.univ

/-- The written net construction at one scale. All extra premises here are
produced uniformly inside the final bounded-law theorem. -/
theorem bounded_intervals_at_scale
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (g : Quadrant → ℝ)
    (a D theta η δ M L kappa s : ℝ) (m : ℕ)
    (ha : 0<a) (ha1 : a<1) (hD : 1≤D) (ht : 0<theta)
    (hη : 0<η) (hM : 0<M) (hs : 0<s) (hκ : 0<kappa)
    (hb : ∀ᵐ x ∂μ, |x|≤M) (hm0 : 0<m) (hms : (m:ℝ)≤s)
    (hmκ : kappa*s≤(m:ℝ)) (hspacing : 1≤min a (1-a)*(m:ℝ)/4)
    (hcut1 : 2*(m:ℝ)≤s/4)
    (hcut2 : 2*(m:ℝ)*(1+min a (1-a)-theta/2)≤theta/2*s)
    (hloss : 2*(m:ℝ)*(L+|∫ x : ℝ, x ∂μ|)≤η*s/4)
    (htube : (m:ℝ)≤δ*s/2)
    (hcompare : ∀ d e f : ℕ × ℕ,
      s≤((d.1+d.2:ℕ):ℝ) → ((d.1+d.2:ℕ):ℝ)≤D*s →
      |(1-a)*(d.1:ℝ)-a*(d.2:ℝ)|≤(min a (1-a)-theta)*((d.1+d.2:ℕ):ℝ) →
      e.1+e.2=m → f.1+f.2=m →
      g ((d.1:ℝ≥0),(d.2:ℝ≥0))-2*L*(m:ℝ)≤
        g (((d-e-f).1:ℝ≥0),((d-e-f).2:ℝ≥0)))
    (pT : ℝ → ℝ) (hpT : ∀ t, 0≤pT t ∧ pT t≤1)
    (htravel : ∀ (u : Lattice) (d : ℕ × ℕ),
      s/2≤((d.1+d.2:ℕ):ℝ) → ((d.1+d.2:ℕ):ℝ)≤D*s →
      |(1-a)*(d.1:ℝ)-a*(d.2:ℝ)|≤(min a (1-a)-theta/2)*((d.1:ℝ)+(d.2:ℝ)) →
      MeasurableSet {ω : Environment | ∃ q : Path u d,
        g ((d.1:ℝ≥0),(d.2:ℝ≥0))-η*s/4≤pathWeight ω q ∧
        ∀ i, ∃ t : ℝ, 0≤t ∧ t≤1 ∧
          |((q.vertex i).1:ℝ)-((u.1:ℝ)+t*(d.1:ℝ))|+
          |((q.vertex i).2:ℝ)-((u.2:ℝ)+t*(d.2:ℝ))|≤δ*s/2} ∧
      pT (s/2)≤(environmentLaw μ).real {ω : Environment | ∃ q : Path u d,
        g ((d.1:ℝ≥0),(d.2:ℝ≥0))-η*s/4≤pathWeight ω q ∧
        ∀ i, ∃ t : ℝ, 0≤t ∧ t≤1 ∧
          |((q.vertex i).1:ℝ)-((u.1:ℝ)+t*(d.1:ℝ))|+
          |((q.vertex i).2:ℝ)-((u.2:ℝ)+t*(d.2:ℝ))|≤δ*s/2})
    (I J : ℤ) (lo hi lo' hi' : ℝ) (hw : lo≤hi) (hw' : lo'≤hi')
    (hwidth : hi-lo≤D*s) (hwidth' : hi'-lo'≤D*s)
    (hlo : s≤((J-I:ℤ):ℝ)) (hhi : ((J-I:ℤ):ℝ)≤D*s)
    (hcone : ∀ u v : Lattice,
      (u.1+u.2=I ∧ (1-a)*(u.1:ℝ)-a*(u.2:ℝ) ∈ Icc lo hi) →
      (v.1+v.2=J ∧ (1-a)*(v.1:ℝ)-a*(v.2:ℝ) ∈ Icc lo' hi') →
      |(1-a)*((v.1:ℝ)-(u.1:ℝ))-a*((v.2:ℝ)-(u.2:ℝ))|≤
        (min a (1-a)-theta)*((J-I:ℤ):ℝ)) :
    let E : Set Environment := {ω | ∀ u v : Lattice,
      (u.1+u.2=I ∧ (1-a)*(u.1:ℝ)-a*(u.2:ℝ) ∈ Icc lo hi) →
      (v.1+v.2=J ∧ (1-a)*(v.1:ℝ)-a*(v.2:ℝ) ∈ Icc lo' hi') →
      ∃ q : Path u ((v.1-u.1).toNat,(v.2-u.2).toNat),
        q.vertex (Fin.last ((v.1-u.1).toNat+(v.2-u.2).toNat))=v ∧
        g (((v.1-u.1).toNat:ℝ≥0),((v.2-u.2).toNat:ℝ≥0))-η*s≤pathWeight ω q ∧
        ∀ i, ∃ t : ℝ, 0≤t ∧ t≤1 ∧
          |((q.vertex i).1:ℝ)-((1-t)*(u.1:ℝ)+t*(v.1:ℝ))|+
          |((q.vertex i).2:ℝ)-((1-t)*(u.2:ℝ)+t*(v.2:ℝ))|≤δ*s}
    max 0 (min 1 (1-(2*D*s+2)*Real.exp (-η^2*s/(32*M^2))-
      (4*(D/kappa+1)/min a (1-a))^2*(1-pT (s/2))))≤(environmentLaw μ).real E := by
  classical
  intro E
  let b := max 0 (min 1 (1-(2*D*s+2)*Real.exp (-η^2*s/(32*M^2))-
    (4*(D/kappa+1)/min a (1-a))^2*(1-pT (s/2))))
  have hb1 : b≤1 := max_le zero_le_one (min_le_left _ _)
  obtain ⟨A,hA,hAc⟩ := exists_finset_level_interval a lo hi I hw
  obtain ⟨B,hB,hBc⟩ := exists_finset_level_interval a lo' hi' J hw'
  by_cases hne : A.Nonempty ∧ B.Nonempty
  swap
  · have he : E=univ := Set.eq_univ_of_forall fun ω u v hu hv => by
      exact False.elim (hne ⟨⟨u,(hA u).2 hu⟩,⟨v,(hB v).2 hv⟩⟩)
    rw [he,probReal_univ]
    exact hb1
  have hnea : ∃ u : Lattice, u.1+u.2=I ∧ (1-a)*(u.1:ℝ)-a*(u.2:ℝ) ∈ Icc lo hi :=
    ⟨hne.1.choose,(hA _).1 hne.1.choose_spec⟩
  have hneb : ∃ v : Lattice, v.1+v.2=J ∧ (1-a)*(v.1:ℝ)-a*(v.2:ℝ) ∈ Icc lo' hi' :=
    ⟨hne.2.choose,(hB _).1 hne.2.choose_spec⟩
  obtain ⟨K,N,_hK,hNinj,hN,hNc,hNa⟩ := exists_forward_net_attachments a ha ha1 m hspacing I lo hi hw
  obtain ⟨K',N',_hK',hN'inj,hN',hN'c,hN'a⟩ := exists_backward_net_attachments a ha ha1 m hspacing J lo' hi' hw'
  let C := 4*(D/kappa+1)/min a (1-a)
  have htheta0 : 0<min a (1-a) := lt_min ha (by linarith)
  have hD0 : 0≤D := zero_le_one.trans hD
  have hC0 : 0≤C := by dsimp [C]; positivity
  have hcount (T : ℕ) (net : Fin (T+1) → Lattice) (hinj : Function.Injective net)
      (w : ℝ) (hwidth : w≤D*s) (hc : (T+1:ℝ)<4*(w+m)/(min a (1-a)*m)) :
      (T+1:ℝ)≤C := by
    have hh := attachment_net_card_bound D s kappa (min a (1-a)) m (w+m)
      (Finset.univ.image net) hD hs hκ htheta0 hmκ (by linarith) (by simpa [Finset.card_image_of_injective _ hinj] using hc)
    simpa [Finset.card_image_of_injective _ hinj,C] using hh
  have hcount1 := hcount K N hNinj _ hwidth hNc
  have hcount2 := hcount K' N' hN'inj _ hwidth' hN'c
  have hatt1' (u : A) : ∃ j d p, d.1+d.2=m ∧
      (p : Path u.val d).vertex (Fin.last (d.1+d.2))=N j ∧
      |(1-a)*(((N j-u.val).1:ℤ):ℝ)-a*(((N j-u.val).2:ℤ):ℝ)|≤(m:ℝ) :=
    hNa u ((hA u).1 u.property).1 ((hA u).1 u.property).2
  have hatt2' (v : B) : ∃ j d p, d.1+d.2=m ∧
      (p : Path (N' j) d).vertex (Fin.last (d.1+d.2))=v.val ∧
      |(1-a)*(((v.val-N' j).1:ℤ):ℝ)-a*(((v.val-N' j).2:ℤ):ℝ)|≤(m:ℝ) :=
    hN'a v ((hB v).1 v.property).1 ((hB v).1 v.property).2
  choose j₁ d₁ p₁ hl₁ hf₁ _ht₁ using hatt1'
  choose j₃ d₃ p₃ hl₃ hf₃ _ht₃ using hatt2'
  let starts : A ⊕ B → Lattice := Sum.elim (fun u => u.val) (fun v => N' (j₃ v))
  let disps : A ⊕ B → ℕ × ℕ := Sum.elim d₁ d₃
  let paths : (x : A ⊕ B) → Path (starts x) (disps x) := fun x => match x with
    | .inl u => p₁ u
    | .inr v => p₃ v
  have hlen (x : A ⊕ B) : (disps x).1+(disps x).2=m := by cases x <;> simp [disps,hl₁,hl₃]
  have hcard : (Fintype.card (A ⊕ B):ℝ)≤2*D*s+2 := by
    simp only [Fintype.card_sum,Fintype.card_coe,Nat.cast_add]
    linarith only [hAc,hBc,hwidth,hwidth']
  obtain ⟨hattMeas,hattProb⟩ := bounded_attachment_family_probability μ starts disps paths m hlen
    hD hM hη hs hb hm0 hms hcard
  let dnet (x : Fin (K+1) × Fin (K'+1)) : ℕ × ℕ :=
    (((N' x.2).1-(N x.1).1).toNat,((N' x.2).2-(N x.1).2).toNat)
  have hpair (x : Fin (K+1) × Fin (K'+1)) := expanded_interval_pair_displacement
    a theta s D lo hi lo' hi' I J m ha ha1 ht hs hnea hneb hlo hhi hcone
    hcut1 hcut2 (N x.1) (N' x.2) (hN x.1) (hN' x.2)
  let T (x : Fin (K+1) × Fin (K'+1)) : Set Environment := {ω | ∃ q : Path (N x.1) (dnet x),
    g (((dnet x).1:ℝ≥0),((dnet x).2:ℝ≥0))-η*s/4≤pathWeight ω q ∧
    ∀ i, ∃ t : ℝ, 0≤t ∧ t≤1 ∧
      |((q.vertex i).1:ℝ)-(((N x.1).1:ℝ)+t*((dnet x).1:ℝ))|+
      |((q.vertex i).2:ℝ)-(((N x.1).2:ℝ)+t*((dnet x).2:ℝ))|≤δ*s/2}
  have htrav (x : Fin (K+1) × Fin (K'+1)) : MeasurableSet (T x) ∧ pT (s/2)≤(environmentLaw μ).real (T x) :=
    htravel _ _ (hpair x).2.1 (hpair x).2.2.1 (hpair x).2.2.2
  have hcards : (Fintype.card (Fin (K+1) × Fin (K'+1)):ℝ)≤C^2 := by
    simpa only [Fintype.card_prod,Fintype.card_fin,Nat.cast_mul,Nat.cast_add,Nat.cast_one,pow_two] using
      mul_le_mul hcount1 hcount2 (by positivity) hC0
  obtain ⟨hnetMeas,hnetProb⟩ := finite_family_success_probability (environmentLaw μ) T
    (fun x => (htrav x).1) (pT (s/2)) (C^2) (hpT (s/2)).2 hcards (fun x => (htrav x).2)
  have hgood := intersection_success_probability (environmentLaw μ) _ _ hattMeas hnetMeas
    ((2*D*s+2)*Real.exp (-η^2*s/(32*M^2))) (C^2*(1-pT (s/2)))
    ((le_max_right _ _).trans hattProb) hnetProb
  apply (show b≤max 0 (1-(2*D*s+2)*Real.exp (-η^2*s/(32*M^2))-C^2*(1-pT (s/2))) from
    max_le_max_left _ (min_le_right _ _)).trans
  apply hgood.trans
  apply measureReal_mono ?_ (measure_ne_top _ _)
  rintro ω ⟨hattach,hnet⟩ u v hu hv
  let U : A := ⟨u,(hA u).2 hu⟩
  let V : B := ⟨v,(hB v).2 hv⟩
  let x : Fin (K+1) × Fin (K'+1) := (j₁ U,j₃ V)
  obtain ⟨q,hq,hqt⟩ := mem_iInter.mp hnet x
  have hU : N (j₁ U)=u+(((d₁ U).1:ℤ),((d₁ U).2:ℤ)) := (hf₁ U).symm.trans (p₁ U).finish
  have hV : v=N' (j₃ V)+(((d₃ V).1:ℤ),((d₃ V).2:ℤ)) := (hf₃ V).symm.trans (p₃ V).finish
  have hMid : N' (j₃ V)=N (j₁ U)+(((dnet x).1:ℤ),((dnet x).2:ℤ)) := (hpair x).1.symm
  have hlevel : (v.1:ℝ)+(v.2:ℝ)-(u.1:ℝ)-(u.2:ℝ)=((J-I:ℤ):ℝ) := by
    have h1 : (u.1:ℝ)+(u.2:ℝ)=(I:ℝ) := by exact_mod_cast hu.1
    have h2 : (v.1:ℝ)+(v.2:ℝ)=(J:ℝ) := by exact_mod_cast hv.1
    push_cast; linarith only [h1,h2]
  have hord : u≤v := level_cone_order a theta u v ht
    (by exact_mod_cast (show 0≤(v.1:ℝ)+(v.2:ℝ)-(u.1:ℝ)-(u.2:ℝ) by rw [hlevel]; linarith))
    (by rw [hlevel]; exact hcone u v hu hv)
  let d : ℕ × ℕ := ((v.1-u.1).toNat,(v.2-u.2).toNat)
  obtain ⟨_hend,hd1,hd2⟩ := ordered_lattice_displacement u v hord
  have hdlen : ((d.1+d.2:ℕ):ℝ)=((J-I:ℤ):ℝ) := by
    simp only [d,Nat.cast_add,hd1,hd2]; linarith only [hlevel]
  have hdc : |(1-a)*(d.1:ℝ)-a*(d.2:ℝ)|≤(min a (1-a)-theta)*((d.1+d.2:ℕ):ℝ) := by
    rw [hdlen]; simpa only [d,hd1,hd2] using hcone u v hu hv
  have hmid : d-d₁ U-d₃ V=dnet x := by
    have h1 := congrArg Prod.fst hU
    have h2 := congrArg Prod.snd hU
    have h3 := congrArg Prod.fst hV
    have h4 := congrArg Prod.snd hV
    have h5 := congrArg Prod.fst hMid
    have h6 := congrArg Prod.snd hMid
    simp only [Prod.fst_add,Prod.snd_add] at h1 h2 h3 h4 h5 h6
    ext <;> simp only [d,Prod.fst_sub,Prod.snd_sub] <;> omega
  have hshape := hcompare d (d₁ U) (d₃ V) (by rw [hdlen]; exact hlo)
    (by rw [hdlen]; exact hhi) hdc (hl₁ U) (hl₃ V)
  rw [hmid] at hshape
  have hqTube : ∀ i, ∃ t : ℝ, 0≤t ∧ t≤1 ∧
      |((q.vertex i).1:ℝ)-((1-t)*((N (j₁ U)).1:ℝ)+t*((N' (j₃ V)).1:ℝ))|+
      |((q.vertex i).2:ℝ)-((1-t)*((N (j₁ U)).2:ℝ)+t*((N' (j₃ V)).2:ℝ))|≤δ*s/2 := by
    intro i
    obtain ⟨t,ht0,ht1,htube'⟩ := hqt i
    dsimp only [x] at htube'
    refine ⟨t,ht0,ht1,?_⟩
    convert htube' using 1; rw [hMid]; simp only [x,Prod.fst_add,Prod.snd_add,Int.cast_add,Int.cast_natCast]; ring
  exact exists_joined_bounded_interval_path ω u _ _ v _ _ _ m (p₁ U) q (p₃ V)
    hU hMid hV (hl₁ U) (hl₃ V) L _ _ _ η δ s hloss hshape
    (hattach (.inl U)) hq (hattach (.inr V)) htube hqTube

end LPPDifferentiability
