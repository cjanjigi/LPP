/-
Copyright (c) 2026 Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Janjigian, Firas Rassoul-Agha, Timo Seppäläinen
-/
module

public import Differentiability.Probability.HeavyIntervalAssembly
public import Differentiability.Probability.ForwardHeavyAttachmentAsymptotics
public import Differentiability.Probability.BackwardHeavyAttachmentAsymptotics
public import Differentiability.Analysis.HeavyIntervalScales
import Mathlib.Tactic

/-!
# Simultaneous general-weight level intervals

Lemma B.2 of the differentiability preprint extends the level-interval
connection estimate to general weights. One shape function and one success
probability work for every deterministic pair of level intervals.

## References

- C. Janjigian, F. Rassoul-Agha and T. Seppäläinen,
  *Differentiability of the shape function in the planar corner growth model*, preprint.
-/
public section
open MeasureTheory Filter Set
open scoped Topology NNReal ENNReal
namespace LPPDifferentiability

private theorem heavy_interval_success_function (B : ℝ) (pf pb pT : ℝ → ℝ)
    (hf : Tendsto pf atTop (𝓝 1)) (hb : Tendsto pb atTop (𝓝 1))
    (ht : Tendsto pT atTop (𝓝 1)) :
    (∀ s, 0≤max 0 (min 1 (1-((1-pf s)+(1-pb s))-B^2*(1-pT (s/2)))) ∧
      max 0 (min 1 (1-((1-pf s)+(1-pb s))-B^2*(1-pT (s/2))))≤1) ∧
    Tendsto (fun s => max 0 (min 1 (1-((1-pf s)+(1-pb s))-B^2*(1-pT (s/2)))))
      atTop (𝓝 1) := by
  refine ⟨fun _ => ⟨le_max_left _ _,max_le zero_le_one (min_le_left _ _)⟩,?_⟩
  have hhalf : Tendsto (fun s : ℝ => s/2) atTop atTop :=
    tendsto_id.atTop_div_const (by norm_num)
  have hfull : Tendsto (fun s => 1-((1-pf s)+(1-pb s))-B^2*(1-pT (s/2)))
      atTop (𝓝 (1-((1-1)+(1-1))-B^2*(1-1))) := (tendsto_const_nhds.sub
    ((tendsto_const_nhds.sub hf).add (tendsto_const_nhds.sub hb))).sub
      ((tendsto_const_nhds.sub (ht.comp hhalf)).const_mul (B^2))
  have hh := (tendsto_const_nhds (x := (0:ℝ))).max
    ((tendsto_const_nhds (x := (1:ℝ))).min hfull)
  simpa only [sub_self,add_zero,mul_zero,sub_zero,min_self,max_eq_right zero_le_one] using hh

/-- One unique actual shape and one success function work for every deterministic
signed pair of closed level intervals at all sufficiently large scales. -/
theorem exists_unique_shape_with_general_intervals
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hneg : ∃ p : ℝ, 1<p ∧
      (∫⁻ x, ENNReal.ofReal ((max (-x) 0)^p) ∂μ)<∞)
    (hpos : (∫⁻ t in Ioi (0:ℝ), (μ (Ioi t))^(1/2:ℝ))<∞) :
    ∃! g : Quadrant → ℝ,
      Continuous g ∧
      (∀ (c : ℝ≥0) (x : Quadrant), g (c*x.1,c*x.2)=(c:ℝ)*g x) ∧
      (∀ (x y : Quadrant) (r t : ℝ≥0), r+t=1 →
        (r:ℝ)*g x+(t:ℝ)*g y≤g (r*x.1+t*y.1,r*x.2+t*y.2)) ∧
      (∀ᵐ ω ∂environmentLaw μ, ∀ ε : ℝ, 0<ε →
        ∃ N : ℕ, 1≤N ∧ ∀ d : ℕ × ℕ, N≤d.1+d.2 →
          |lastPassage ω 0 d-g ((d.1:ℝ≥0),(d.2:ℝ≥0))|≤ε*((d.1+d.2:ℕ):ℝ)) ∧
      (∀ a : ℝ, 0<a → a<1 → ∀ D : ℝ, 1≤D →
        ∀ theta : ℝ, 0<theta → theta<min a (1-a) →
        ∀ η δ : ℝ, 0<η → 0<δ → ∃ s1 : ℝ, 1≤s1 ∧ ∃ p : ℝ → ℝ,
          (∀ s, 0≤p s ∧ p s≤1) ∧ Tendsto p atTop (𝓝 1) ∧
          ∀ (s : ℝ) (I J : ℤ) (lo hi lo' hi' : ℝ), s1≤s → I<J →
            lo≤hi → lo'≤hi' → s≤((J-I:ℤ):ℝ) → ((J-I:ℤ):ℝ)≤D*s →
            hi-lo≤D*s → hi'-lo'≤D*s →
            (∀ u v : Lattice,
              (u.1+u.2=I ∧ (1-a)*(u.1:ℝ)-a*(u.2:ℝ) ∈ Icc lo hi) →
              (v.1+v.2=J ∧ (1-a)*(v.1:ℝ)-a*(v.2:ℝ) ∈ Icc lo' hi') →
              |(1-a)*((v.1:ℝ)-(u.1:ℝ))-a*((v.2:ℝ)-(u.2:ℝ))|≤
                (min a (1-a)-theta)*((J-I:ℤ):ℝ)) →
            let E : Set Environment := {ω | ∀ u v : Lattice,
              (u.1+u.2=I ∧ (1-a)*(u.1:ℝ)-a*(u.2:ℝ) ∈ Icc lo hi) →
              (v.1+v.2=J ∧ (1-a)*(v.1:ℝ)-a*(v.2:ℝ) ∈ Icc lo' hi') →
              ∃ q : Path u ((v.1-u.1).toNat,(v.2-u.2).toNat),
                q.vertex (Fin.last ((v.1-u.1).toNat+(v.2-u.2).toNat))=v ∧
                g (((v.1-u.1).toNat:ℝ≥0),((v.2-u.2).toNat:ℝ≥0))-η*s≤pathWeight ω q ∧
                ∀ i, ∃ t : ℝ, 0≤t ∧ t≤1 ∧
                  |((q.vertex i).1:ℝ)-((1-t)*(u.1:ℝ)+t*(v.1:ℝ))|+
                  |((q.vertex i).2:ℝ)-((1-t)*(u.2:ℝ)+t*(v.2:ℝ))|≤δ*s}
            MeasurableSet E ∧ p s≤(environmentLaw μ).real E) := by
  obtain ⟨g,hg,_hu⟩ := exists_unique_shape_with_travel μ hneg hpos
  obtain ⟨_g0,_hg0,hunique⟩ := exists_unique_shape_of_negative_moment_and_positive_tail μ hneg hpos
  obtain ⟨p0,hp0,hmoment⟩ := hneg
  refine ⟨g,⟨hg.1,hg.2.1,hg.2.2.1,hg.2.2.2.1,?_⟩,?_⟩
  · intro a ha ha1 D hD theta ht hti η δ hη hδ
    obtain ⟨L,hL,hcompare⟩ := attachment_shape_comparison g hg.1 hg.2.2.1 hg.2.1 a theta ha ha1 ht hti
    obtain ⟨sT,_hsT,pT,hpT,htT,htravel⟩ :=
      hg.2.2.2.2 a ha ha1 (2*D) (by linarith) (theta/2) (by positivity) (by linarith) (η/2) δ (by positivity) hδ
    let C1 : ℝ := ∫ x, max (-x) 0 ∂μ
    have hC1 : 0≤C1 := integral_nonneg fun _ => le_max_right _ _
    let r : ℝ := L+C1
    let kappa : ℝ := min (theta/16) (min (δ/4) (η/(16*(r+1))))
    let cutoff : ℝ := max 1 (max (4/(min a (1-a)*kappa))
      (max 16 (max (16/theta) (max (16*r/η) (4/δ)))))
    obtain ⟨hκ,_hκθ,hκ16,_hκδ,_hκη,hκC1,hcutoff1,_hcutL,hscales⟩ :=
      heavy_interval_scale_bounds a theta δ η L C1 ha ha1 ht hti hδ hη hL hC1
    obtain ⟨_Kf,_hKf,_hKfp,pf,htf,hfcuts⟩ :=
      exists_forward_heavy_attachment_asymptotics μ p0 a D η kappa hp0 ⟨ha,ha1⟩ hD hη hκ hκ16 hmoment hκC1
    obtain ⟨_Kb,_hKb,_hKbp,pb,htb,hbcuts⟩ :=
      exists_backward_heavy_attachment_asymptotics μ p0 a D η kappa hp0 ⟨ha,ha1⟩ hD hη hκ hκ16 hmoment hκC1
    obtain ⟨sF,hF⟩ := eventually_atTop.1 hfcuts
    obtain ⟨sB,hB⟩ := eventually_atTop.1 hbcuts
    let Bcap : ℝ := 8*D/(min a (1-a)*kappa)+2
    have hBcap : 0≤Bcap := by
      have htheta : 0<min a (1-a) := lt_min ha (sub_pos.mpr ha1)
      dsimp only [Bcap]
      positivity
    let p : ℝ → ℝ := fun s => max 0 (min 1 (1-((1-pf s)+(1-pb s))-Bcap^2*(1-pT (s/2))))
    have hp := heavy_interval_success_function Bcap pf pb pT htf htb htT
    refine ⟨max cutoff (max (2*sT) (max sF sB)),hcutoff1.trans (le_max_left _ _),p,hp.1,hp.2,?_⟩
    intro s I J lo hi lo' hi' hs _hIJ hw hw' hlo hhi hwidth hwidth' hcone E
    have hcuts : cutoff≤s ∧ 2*sT≤s ∧ sF≤s ∧ sB≤s := by
      simpa only [max_le_iff] using hs
    have hs0 : 0<s := lt_of_lt_of_le zero_lt_one (hcutoff1.trans hcuts.1)
    obtain ⟨_hmlo,_hmhi,_hspacing,hcut1,hcut2,_hbudget,htube,_hms,hloss⟩ := hscales s hcuts.1
    let m := Nat.ceil (kappa*s)
    obtain ⟨_hpf0,_hpf1,hforward⟩ := hF s hcuts.2.2.1
    obtain ⟨_hpb0,_hpb1,hbackward⟩ := hB s hcuts.2.2.2
    obtain ⟨A,K,N,j₁,d₁,hA,_hAc,_hK,_hNinj,hN,_hgap,_hfirstOnly,_hlastOnly,
      _hfirst,_hlast,_hcard,hcount1,hd₁,p₁,Af,hAf,hpf,_hfinish₁,hweight₁⟩ := hforward I lo hi hw hwidth
    obtain ⟨B,K',N',j₃,d₃,hB',_hBc,_hK',_hN'inj,hN',_hgap',_hfirstOnly',_hlastOnly',
      _hfirst',_hlast',_hcard',hcount2,hd₃,p₃,Ab,hAb,hpb,_hfinish₃,hweight₃⟩ := hbackward J lo' hi' hw' hwidth'
    have hcomp : ∀ d e f : ℕ × ℕ,
        s≤((d.1+d.2:ℕ):ℝ) → ((d.1+d.2:ℕ):ℝ)≤D*s →
        |(1-a)*(d.1:ℝ)-a*(d.2:ℝ)|≤(min a (1-a)-theta)*((d.1+d.2:ℕ):ℝ) →
        e.1+e.2=m → f.1+f.2=m →
        g ((d.1:ℝ≥0),(d.2:ℝ≥0))-2*L*(m:ℝ)≤
          g (((d-e-f).1:ℝ≥0),((d-e-f).2:ℝ≥0)) := by
      intro d e f hdlo hdhi hc he hf
      exact (hcompare s D hs0 hD (d.1+d.2) d e f m rfl hdlo hdhi hc he hf hcut1 hcut2).2.2
    refine ⟨measurableSet_all_interval_paths g a η δ s lo hi lo' hi' I J,?_⟩
    have hLoss : 2*L*(m:ℝ)≤η*s/4 := by nlinarith only [hloss]
    apply heavy_intervals_at_scale μ g a D theta η δ L s Bcap m ha ha1 ht hs0 hBcap
      hcut1 hcut2 hLoss htube hcomp pT hpT ?_ I J lo hi lo' hi' hlo hhi hcone
      A B hA hB' K K' N N' hN hN' hcount1 hcount2 j₁ j₃ d₁ d₃ p₁ p₃
      (fun u => ⟨(hd₁ u).1,(hd₁ u).2.1⟩) (fun v => ⟨(hd₃ v).1,(hd₃ v).2.1⟩)
      Af Ab hAf hAb (pf s) (pb s) hpf hpb hweight₁ hweight₃
    intro u d hdlo hdhi hc
    have hh := htravel (s/2) u d (by linarith only [hcuts.2.1]) hdlo (by convert hdhi using 1; ring) hc
    simpa only [show (η/2)*(s/2)=η*s/4 by ring,show δ*(s/2)=δ*s/2 by ring] using hh
  · intro f hf
    exact (hunique f ⟨hf.1,hf.2.1,hf.2.2.1,hf.2.2.2.1⟩).trans
      (hunique g ⟨hg.1,hg.2.1,hg.2.2.1,hg.2.2.2.1⟩).symm

end LPPDifferentiability
