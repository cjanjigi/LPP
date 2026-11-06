/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Differentiability.Probability.BoundedIntervalAssembly
import Mathlib.Tactic

/-!
# Interval assembly for heavy attachments

The assembly of the endpoint events over an interval, from the same nets and random
attachments as the single-scale estimates.
-/
public section
open MeasureTheory Set
open scoped NNReal
namespace LPPDifferentiability

/-- At one scale, the attachment witnesses and the netpair travel events
produce the all-endpoint event. The final theorem supplies every helper premise. -/
theorem heavy_intervals_at_scale
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (g : Quadrant → ℝ)
    (a D theta η δ L s Bcap : ℝ) (m : ℕ)
    (ha : 0<a) (ha1 : a<1) (ht : 0<theta) (hs : 0<s)
    (hBcap : 0≤Bcap)
    (hcut1 : 2*(m:ℝ)≤s/4)
    (hcut2 : 2*(m:ℝ)*(1+min a (1-a)-theta/2)≤theta/2*s)
    (hloss : 2*L*(m:ℝ)≤η*s/4) (htube : (m:ℝ)≤δ*s/2)
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
    (I J : ℤ) (lo hi lo' hi' : ℝ)
    (hlo : s≤((J-I:ℤ):ℝ)) (hhi : ((J-I:ℤ):ℝ)≤D*s)
    (hcone : ∀ u v : Lattice,
      (u.1+u.2=I ∧ (1-a)*(u.1:ℝ)-a*(u.2:ℝ) ∈ Icc lo hi) →
      (v.1+v.2=J ∧ (1-a)*(v.1:ℝ)-a*(v.2:ℝ) ∈ Icc lo' hi') →
      |(1-a)*((v.1:ℝ)-(u.1:ℝ))-a*((v.2:ℝ)-(u.2:ℝ))|≤
        (min a (1-a)-theta)*((J-I:ℤ):ℝ))
    (A B : Finset Lattice)
    (hA : ∀ u, u ∈ A ↔ u.1+u.2=I ∧ (1-a)*(u.1:ℝ)-a*(u.2:ℝ) ∈ Icc lo hi)
    (hB : ∀ v, v ∈ B ↔ v.1+v.2=J ∧ (1-a)*(v.1:ℝ)-a*(v.2:ℝ) ∈ Icc lo' hi')
    (K K' : ℕ) (N : Fin (K+1) → Lattice) (N' : Fin (K'+1) → Lattice)
    (hN : ∀ k, (N k).1+(N k).2=I+(m:ℤ) ∧
      (1-a)*((N k).1:ℝ)-a*((N k).2:ℝ) ∈ Icc (lo-a*m) (hi+(1-a)*m))
    (hN' : ∀ k, (N' k).1+(N' k).2=J-(m:ℤ) ∧
      (1-a)*((N' k).1:ℝ)-a*((N' k).2:ℝ) ∈ Icc (lo'-(1-a)*m) (hi'+a*m))
    (hcount1 : (K+1:ℝ)≤Bcap) (hcount2 : (K'+1:ℝ)≤Bcap)
    (j₁ : A → Fin (K+1)) (j₃ : B → Fin (K'+1))
    (d₁ : A → ℕ × ℕ) (d₃ : B → ℕ × ℕ)
    (p₁ : Environment → (u : A) → Path u.val (d₁ u))
    (p₃ : Environment → (v : B) → Path (N' (j₃ v)) (d₃ v))
    (hd₁ : ∀ u, (d₁ u).1+(d₁ u).2=m ∧ u.val+(((d₁ u).1:ℤ),((d₁ u).2:ℤ))=N (j₁ u))
    (hd₃ : ∀ v, (d₃ v).1+(d₃ v).2=m ∧ N' (j₃ v)+(((d₃ v).1:ℤ),((d₃ v).2:ℤ))=v.val)
    (Af Ab : Set Environment) (hAf : MeasurableSet Af) (hAb : MeasurableSet Ab)
    (pf pb : ℝ) (hpf : pf≤(environmentLaw μ).real Af) (hpb : pb≤(environmentLaw μ).real Ab)
    (hweight₁ : ∀ ω, ω ∈ Af → ∀ u, -η*s/4≤pathWeight ω (p₁ ω u))
    (hweight₃ : ∀ ω, ω ∈ Ab → ∀ v, -η*s/4≤pathWeight ω (p₃ ω v)) :
    let E : Set Environment := {ω | ∀ u v : Lattice,
      (u.1+u.2=I ∧ (1-a)*(u.1:ℝ)-a*(u.2:ℝ) ∈ Icc lo hi) →
      (v.1+v.2=J ∧ (1-a)*(v.1:ℝ)-a*(v.2:ℝ) ∈ Icc lo' hi') →
      ∃ q : Path u ((v.1-u.1).toNat,(v.2-u.2).toNat),
        q.vertex (Fin.last ((v.1-u.1).toNat+(v.2-u.2).toNat))=v ∧
        g (((v.1-u.1).toNat:ℝ≥0),((v.2-u.2).toNat:ℝ≥0))-η*s≤pathWeight ω q ∧
        ∀ i, ∃ t : ℝ, 0≤t ∧ t≤1 ∧
          |((q.vertex i).1:ℝ)-((1-t)*(u.1:ℝ)+t*(v.1:ℝ))|+
          |((q.vertex i).2:ℝ)-((1-t)*(u.2:ℝ)+t*(v.2:ℝ))|≤δ*s}
    max 0 (min 1 (1-((1-pf)+(1-pb))-Bcap^2*(1-pT (s/2))))≤(environmentLaw μ).real E := by
  classical
  intro E
  let b := max 0 (min 1 (1-((1-pf)+(1-pb))-Bcap^2*(1-pT (s/2))))
  have hb1 : b≤1 := max_le zero_le_one (min_le_left _ _)
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
  have hcards : (Fintype.card (Fin (K+1) × Fin (K'+1)):ℝ)≤Bcap^2 := by
    simpa only [Fintype.card_prod,Fintype.card_fin,Nat.cast_mul,Nat.cast_add,Nat.cast_one,pow_two] using
      mul_le_mul hcount1 hcount2 (by positivity) hBcap
  obtain ⟨hnetMeas,hnetProb⟩ := finite_family_success_probability (environmentLaw μ) T
    (fun x => (htrav x).1) (pT (s/2)) (Bcap^2) (hpT (s/2)).2 hcards (fun x => (htrav x).2)
  have hattProb := intersection_success_probability (environmentLaw μ) Af Ab hAf hAb
    (1-pf) (1-pb) (by linarith only [hpf]) (by linarith only [hpb])
  have hgood := intersection_success_probability (environmentLaw μ) (Af ∩ Ab) _
    (hAf.inter hAb) hnetMeas ((1-pf)+(1-pb)) (Bcap^2*(1-pT (s/2)))
    (by linarith only [(le_max_right _ _).trans hattProb]) hnetProb
  apply (show b≤max 0 (1-((1-pf)+(1-pb))-Bcap^2*(1-pT (s/2))) from
    max_le_max_left _ (min_le_right _ _)).trans
  apply hgood.trans
  apply measureReal_mono ?_ (measure_ne_top _ _)
  rintro ω ⟨hattach,hnet⟩ u v hu hv
  let U : A := ⟨u,(hA u).2 hu⟩
  let V : B := ⟨v,(hB v).2 hv⟩
  let x : Fin (K+1) × Fin (K'+1) := (j₁ U,j₃ V)
  obtain ⟨q,hq,hqt⟩ := mem_iInter.mp hnet x
  have hU : N (j₁ U)=u+(((d₁ U).1:ℤ),((d₁ U).2:ℤ)) := (hd₁ U).2.symm
  have hV : v=N' (j₃ V)+(((d₃ V).1:ℤ),((d₃ V).2:ℤ)) := (hd₃ V).2.symm
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
    (by rw [hdlen]; exact hhi) hdc (hd₁ U).1 (hd₃ V).1
  rw [hmid] at hshape
  have hqTube : ∀ i, ∃ t : ℝ, 0≤t ∧ t≤1 ∧
      |((q.vertex i).1:ℝ)-((1-t)*((N (j₁ U)).1:ℝ)+t*((N' (j₃ V)).1:ℝ))|+
      |((q.vertex i).2:ℝ)-((1-t)*((N (j₁ U)).2:ℝ)+t*((N' (j₃ V)).2:ℝ))|≤δ*s/2 := by
    intro i
    obtain ⟨t,ht0,ht1,htube'⟩ := hqt i
    dsimp only [x] at htube'
    refine ⟨t,ht0,ht1,?_⟩
    have h1 : (1-t)*((N (j₁ U)).1:ℝ)+t*((N' (j₃ V)).1:ℝ)=
        ((N (j₁ U)).1:ℝ)+t*((dnet x).1:ℝ) := by
      rw [hMid]
      simp only [Prod.fst_add,Int.cast_add,Int.cast_natCast]
      ring
    have h2 : (1-t)*((N (j₁ U)).2:ℝ)+t*((N' (j₃ V)).2:ℝ)=
        ((N (j₁ U)).2:ℝ)+t*((dnet x).2:ℝ) := by
      rw [hMid]
      simp only [Prod.snd_add,Int.cast_add,Int.cast_natCast]
      ring
    simpa only [h1,h2] using htube'
  exact exists_joined_bounded_interval_path ω u _ _ v _ _ _ m (p₁ ω U) q (p₃ ω V)
    hU hMid hV (hd₁ U).1 (hd₃ V).1 L 0 _ _ η δ s
    (by simpa only [abs_zero,add_zero] using (show 2*(m:ℝ)*L≤η*s/4 by nlinarith only [hloss])) hshape
    (by simpa only [mul_zero,zero_sub,neg_mul,neg_div] using hweight₁ ω hattach.1 U) hq
    (by simpa only [mul_zero,zero_sub,neg_mul,neg_div] using hweight₃ ω hattach.2 V) htube hqTube

end LPPDifferentiability
